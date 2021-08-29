package vexriscv.plugin

import vexriscv._
import spinal.core._
import spinal.lib._
import spinal.lib.com.uart._

import scala.collection.mutable
import spinal.lib.com.eth._ 

trait InterfaceKind
object UART extends InterfaceKind
object FT245ASY extends InterfaceKind
object ETH100MII extends InterfaceKind

object WrStates extends SpinalEnum {
    val idle, wrsetup, wractive = newElement()
  }


case class MacEthTx(p : MacEthParameter,
                  txCd : ClockDomain) extends Component {
  val io = new Bundle {
    val phy = master(PhyIo(p.phy))
    val ctrl = MacEthCtrl(p)
  }

  val ctrlClockDomain = this.clockDomain


  val txReset = ResetCtrl.asyncAssertSyncDeassert(
    input = ClockDomain.current.isResetActive || io.ctrl.tx.flush,
    clockDomain = txCd
  )
  val txClockDomain = txCd.copy(reset = txReset)

  val txFrontend = new Area{
    val buffer = MacTxBuffer(
      pushCd = ctrlClockDomain.copy(softReset = io.ctrl.tx.flush),
      popCd = txClockDomain,
      pushWidth = p.rxDataWidth,
      popWidth = p.phy.txDataWidth,
      byteSize = p.txBufferByteSize
    )
    buffer.io.push.stream << io.ctrl.tx.stream
    buffer.io.push.availability <> io.ctrl.tx.availability
  }

  val txBackend = txClockDomain on new Area{
    val aligner = MacTxAligner(dataWidth = p.phy.rxDataWidth)
    aligner.io.input << txFrontend.buffer.io.pop.stream
    aligner.io.enable := BufferCC(io.ctrl.tx.alignerEnable)

    val crc = MacTxCrc(dataWidth = p.phy.txDataWidth)
    crc.io.input << aligner.io.output

    val header = MacTxHeader(dataWidth = p.phy.txDataWidth)
    header.io.input << crc.io.output
    header.io.output >> io.phy.tx


    txFrontend.buffer.io.pop.redo := False
    txFrontend.buffer.io.pop.commit := RegNext(header.io.output.lastFire) init(False)
  }
}

case class Ftxd() extends Bundle with IMasterSlave {
  val data = out Bits(8 bits)
  val xwr = out Bool()
  val txe = in Bool()
  override def asMaster(): Unit = {
    in(data)
    in(xwr)
    out(txe)
  }

}


case class FPar(){
  val frq = ClockDomain.current.frequency.getValue.toDouble
  val wrsetup = (5e-9*frq + 1).toInt 
  val wrpulse = (30e-9*frq + 1).toInt
}
 

class Ft245(p: FPar = FPar()) extends Component{
  val io = new Bundle{
    val ftxd = Ftxd()
    val tx = slave Stream (Bits(8 bit))
  }
 
  

 val fsm = new Area {

      import WrStates._
      val cntNext = UInt(Math.max(log2Up(p.wrsetup), log2Up(p.wrpulse)) + 1 bit)
      val cnt = RegNext(cntNext) init(0)
      when(cnt =/= 0) { 
        cntNext := cnt - 1
       } otherwise {
        cntNext := 0
       }
      val state = Reg(WrStates()) init (idle)
      io.tx.ready := False
      io.ftxd.data := io.tx.payload
      io.ftxd.xwr := True
      switch(state) {
        is(idle) {
          when(io.tx.valid && !io.ftxd.txe) {
            state := wrsetup
            cntNext := p.wrsetup - 1
          }
        }
        is(wrsetup) {
          when(cnt === 0) {
           state := wractive
           cntNext := p.wrpulse - 1
          }
        }
        is(wractive) {
          io.ftxd.xwr := False
          when(cnt === 0) {
           io.tx.ready := True
           state :=idle
          }
        }
      }
  }
}




case class CRam(wordWidth: Int, wordCount: Int, inCount: Int, outCount: Int) extends BlackBox {

    // SpinalHDL will lock at Generic classes to get attributes which
    // should be used ad VHDL gererics / Verilog parameter
    val generic = new Generic {
      val wordCount = CRam.this.wordCount
      val wordWidth = CRam.this.wordWidth
      val inCount = CRam.this.inCount
      val outCount = CRam.this.outCount
    }

    // Define io of the VHDL entiry / Verilog module
    val io = new Bundle {
      val clk = in Bool ()
      val wr = in Bool()
      val mask  = in Bits (inCount bit)
      val wr_addr = in UInt (log2Up(wordCount) bit)
      val wrdata = in Bits (wordWidth*inCount bit)
      val rd_addr = in UInt (log2Up(wordCount) bit)
      val rddata = out Bits (wordWidth*outCount bit)
    }

    //Map the current clock domain to the io.clk pin
    mapClockDomain(clock=io.clk)
  }


class StreamFifoVar[T <: Data](dataType: HardType[T], depth: Int, inmaxsize: Int=2, outsize: Int=2) extends Component {
  require(depth >= 0)
  require(depth>inmaxsize)
  
  val io = new Bundle {
    val push = slave Stream (Vec(dataType, inmaxsize))
    val incnt = in UInt(log2Up(inmaxsize + 1) bits)
    val pop = master Stream (Vec(dataType, outsize))
    val flush = in Bool() default(False)
  }

  
  val logic = (depth > 1) generate new Area {
    val ram = new CRam(dataType.getBitsWidth, depth, inmaxsize, outsize)
    val pushPtr = Counter(depth)
    val popPtr = Counter(depth)
    val ptrMatch = pushPtr === popPtr
    val pushing = io.push.fire
    val popping = io.pop.fire
    val empty = ptrMatch
    val full = Bool
    val pushov = Reg(Bool) init(False)
    val popov = Reg(Bool) init(False)
    
    val ptrDif = pushPtr - popPtr
    io.push.ready := !full
    io.pop.valid := !empty && !RegNext(popPtr.valueNext === pushPtr, False)
    for (i <- 0 until outsize) {
       io.pop.payload(i).assignFrom(ram.io.rddata.asBits.subdivideIn(outsize slices)(i))
    }
    ram.io.rd_addr := popPtr.valueNext
    ram.io.wr_addr := pushPtr.value
    ram.io.wrdata := Cat(io.push.payload)
    ram.io.mask := 0
    ram.io.wr :=False
   
    when(pushing) {
      for (i <- 0 until inmaxsize) {
         when(i < io.incnt) {ram.io.mask(i) := True}
       }
       ram.io.wr := True
       pushPtr.valueNext := pushPtr.value + io.incnt
       when(pushPtr.valueNext < pushPtr.value) {pushov := !pushov}
    }
   
    when(popping) {
      popPtr.valueNext := popPtr.value + outsize
      when(popPtr.valueNext < popPtr.value) {popov := !popov}
    }
    
    when(pushov ^ popov) { 
      full := pushPtr.value > popPtr.value
    } otherwise {
      full := pushPtr.value < popPtr.value
    }
    
    when(io.flush){
      pushov := False
      popov := False
      pushPtr.clear()
      popPtr.clear()
    }
  }
}


class TracePlugin(Tinterface: InterfaceKind = UART, regcount: Int = 1, slicebits : Int = 8) extends Plugin[VexRiscv]{
  import Riscv._
  import CsrAccess._ 
  var uart : Uart = null
  var ftxd: Ftxd = null
  var miitx : MiiTx = null
  var csel : Bits = null
  

  
  override def setup(pipeline: VexRiscv): Unit = {
  }

  override def build(pipeline: VexRiscv): Unit = {
  import pipeline._
  import pipeline.config._
  import Riscv._ 
  
  val csrService = pipeline.service(classOf[CsrInterface])
  val lastStage = pipeline.stages.last
  val msample = pipeline plug new Area { 
   
    val msamplesel = RegInit(Vec.tabulate(regcount)(i=>B(i+12,5 bits)))
    val triggeradr = Reg(Bits(32 bits)) init(0)
    val triggered = Reg(Bool) init(False)
    val msamplecmd = Reg(Bits(32 bits))
    val coresel = Reg(Bits(4 bits))
    val wordcount = regcount + 1
    val regslices = 32 / slicebits
    val headerslices = 8 / slicebits
    csrService.w(CSR.MSAMPLE, msamplecmd)
    for (i <- 0 until regcount ) {
        csrService.w(CSR.MSAMPLESEL, i*5 -> msamplesel(i))
    }
    csrService.w(CSR.MSAMPLEADR, triggeradr)
    csrService.w(CSR.MSAMPLECSEL, coresel)
    csel = out(Bits(4 bits))
    csel := coresel
    val inmaxsize = if(Tinterface == `ETH100MII`) wordcount*(regslices + headerslices) + 1 
      else wordcount*(regslices + headerslices)

    
    val fifo = new StreamFifoVar(Bits(slicebits bits), depth = 32, inmaxsize = inmaxsize, outsize=1 )
    
    val insCounter = Reg(UInt(32 bits)) init(0)
    val lastinsCounter = Reg(UInt(32 bits)) init(0)
    insCounter := insCounter + 1
    val regFile = RegInit(Vec.tabulate(regcount)(i=>B(0,32 bits)))
    val oldregFile = RegInit(Vec.tabulate(regcount)(i=>B(0,32 bits)))
    val data = Vec(Bits(32 bits), wordcount)
    val res = Vec(Bits(slicebits bits), inmaxsize)
    var sizeacc = Vec(UInt(log2Up(wordcount*(regslices + headerslices)) bits), wordcount + 1)
    val size = Vec(UInt(slicebits bits), wordcount)
    val header = Vec(Bits(8 bits), wordcount)
    sizeacc(0) := U(0)
    res.map(_ := B"d0")
    for (i <- 0 until wordcount ) {
      if(i==0) {
       data(i) := (insCounter - lastinsCounter).asBits
       header(i)(7 downto 4) := B"1000"
      } else {
        data(i) := oldregFile(U(i - 1).resized) ^ regFile(U(i - 1).resized)
        header(i)(7 downto 4) := U(i - 1).asBits.resized
      }
        size(i) := (OHToUInt(OHMasking.last(data(i))) >>  log2Up(slicebits)).resized
        header(i)(3 downto 0) := size(i).asBits.resized
       
      for(j<- 0 until headerslices) {
           if(Tinterface == `ETH100MII`) res((sizeacc(i) + j + 1).resized) := header(i).subdivideIn(slicebits bits)(j) 
           else res((sizeacc(i) + j).resized) := header(i).subdivideIn(slicebits bits)(j) 
      }
      for (j<- 0 until regslices) {
           when (j < (size(i) + 1)) {
             if(Tinterface == `ETH100MII`) res((sizeacc(i) + j + headerslices + 1).resized) := data(i).subdivideIn(slicebits bits)(j)
             else res((sizeacc(i) + j + headerslices).resized) := data(i).subdivideIn(slicebits bits)(j)
           }
       }
      sizeacc(i+1) := (sizeacc(i) + size(i) + headerslices + 1).resized
    }
    res.allowOverride
    if(Tinterface == `ETH100MII`)  {
      res(0) := (sizeacc(wordcount) << log2Up(slicebits)).asBits.resized
      fifo.io.incnt := (sizeacc(wordcount) + 1).resized
    } else {
      fifo.io.incnt := (sizeacc(wordcount)).resized
    }
    fifo.io.push.payload := res
    fifo.io.push.valid := False
   

    fifo.io.flush := ClockDomain.current.isResetActive
   
    csrService.onWrite(CSR.MSAMPLE) {
    for (i <- 0 until regcount ) {
       oldregFile(i) := regFile(i)
     }
     lastinsCounter:=insCounter
     fifo.io.push.valid := True
    }
    triggered := False
    when(lastStage.arbitration.isFiring && (lastStage.input(PC).asBits === triggeradr) && (triggered === False)) {
       for (i <- 0 until regcount ) {
        oldregFile(i) := regFile(i)
       }
       lastinsCounter:=insCounter
       fifo.io.push.valid := True
       triggered := True
    }
    
    val tdata = Stream(Bits(8 bits))
    tdata.payload := Cat(fifo.io.pop.payload)
    tdata.valid := fifo.io.pop.valid
    fifo.io.pop.ready := tdata.ready
    
    if(Tinterface == `ETH100MII`) {
    miitx = master(MiiTx(
        MiiTxParameter(
          dataWidth = 4,
          withEr    = true
        )))
    
    val p = MacEthParameter(
     phy = PhyParameter(
        txDataWidth = 4,
        rxDataWidth = 4
      ),
      rxDataWidth = 8,
      rxBufferByteSize = 16,
      txDataWidth = 8,
      txBufferByteSize = 256
    )
    
    val rxclk = in(Bool)
    val txclk = in(Bool)
    val txCd = ClockDomain(miitx.CLK)
    val mac = new MacEthTx(p, txCd)
    tdata >-> mac.io.ctrl.tx.stream
    mac.io.ctrl.tx.flush := False
    mac.io.ctrl.tx.alignerEnable := False
      txCd.copy(reset = mac.txReset) on {
        miitx.EN := RegNext(mac.io.phy.tx.valid)
        miitx.D := RegNext(mac.io.phy.tx.data)
        mac.io.phy.tx.ready := True 
        miitx.ER := False
      }
    
     
   } 
   else if (Tinterface == `FT245ASY`) {
     ftxd = Ftxd()
     val ftdi = new Ft245()
     ftdi.io.ftxd <> ftxd
     tdata >-> ftdi.io.tx
   }
   else {
     uart = master(Uart()) 
    
     val uartCtrl: UartCtrl = UartCtrl(
     config = UartCtrlInitConfig(
      baudrate = 6250000, //3686400
     dataLength = 7,  // 8 bits
     parity = UartParityType.NONE,
     stop = UartStopType.TWO
      )
    )
    uartCtrl.io.uart <> uart
    tdata >-> uartCtrl.io.write
   }
   
    val writeStage = stages.last

        //Write register file
    writeStage plug new Area {
       import writeStage._

      for (i <- 0 until regcount ) {
        when(output(REGFILE_WRITE_VALID) && arbitration.isFiring && (msamplesel(i) ===  output(INSTRUCTION)(rdRange))) {
            regFile(U(i).resized):=output(REGFILE_WRITE_DATA)
        }
      }
     }
   }
 }
}