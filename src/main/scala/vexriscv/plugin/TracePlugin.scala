package vexriscv.plugin

import vexriscv._
import spinal.core._
import spinal.lib._
import spinal.lib.com.uart._

import scala.collection.mutable
import spinal.lib.com.eth._ 

case class Dpram(wordWidth: Int, wordCount: Int) extends BlackBox {

    val generic = new Generic {
      val wordCount = Dpram.this.wordCount
      val wordWidth = Dpram.this.wordWidth
    }

    // Define io of the VHDL entiry / Verilog module
    val io = new Bundle {
      val clk = in Bool ()
      val wr_a = in Bool ()
      val adr_a = in UInt (log2Up(wordCount) bit)
      val wrdata_a = in Bits (wordWidth bit) 
      val rddata_a = out Bits (wordWidth bit)
      val wr_b = in Bool ()
      val adr_b = in UInt (log2Up(wordCount) bit)
      val wrdata_b = in Bits (wordWidth bit)
      val rddata_b = out Bits (wordWidth bit)
    }

    //Map the current clock domain to the io.clk pin
    mapClockDomain(clock=io.clk)
  }
 

object CamStates extends SpinalEnum {
    val idle, del1, del2, write1, write2 = newElement()
  } 

class Cam(dataw: Int, depth: Int, slices: Int) extends Component {
  val adrw =log2Up(depth)
  val slicesize = dataw / slices
  val io = new Bundle {
  	val data = in Bits(dataw bits)
  	val adr = in UInt(adrw bits)
  	val wen = in Bool()
  	val del = in Bool()
  	val busy = out Bool()
  	val mat = out Bool()
  	val mdata = in Bits(dataw bits)
  	val matadr = out UInt(adrw bits)
  }
  val logic = new Area {
  	val eram = Mem(Bits(dataw bits), depth).generateAsBlackBox
  	val eramwe = Reg(Bool()) init(False)
  	val edata = eram.readWriteSync(address=io.adr, data=io.data, enable=True, write=eramwe)
  	val sbits = Reg(Bits(depth bits)) init(0)
  	val ebits = Reg(Bits(depth bits)) init(0)
  	val rdporta = Vec(Bits(depth bits), slices)
  	val rdportall = Bits(depth bits)
  	val rdportb = Vec(Bits(depth bits), slices)
  	val dpramwe = Reg(Bool()) init(False)
  	val adrreg = Reg(UInt(adrw bits))
  	val delreg = Reg(Bool()) init(False)
  	for (i <- 0 until slices ) { 
        val dpram = Dpram(depth, 1<<slicesize)
        dpram.io.adr_a := io.mdata.subdivideIn(slicesize bits)(i).asUInt
        rdporta(i) := dpram.io.rddata_a
        dpram.io.adr_b := edata.subdivideIn(slicesize bits)(i).asUInt
        rdportb(i) := dpram.io.rddata_b
        dpram.io.wrdata_b := rdportb(i) & ~ebits | sbits
        dpram.io.wr_b := dpramwe
        dpram.io.wr_a := False
        dpram.io.wrdata_a := 0
        
  	}
  	rdportall := rdporta.reduce(_ & _)
  	io.mat := rdportall =/= 0
  	io.matadr := OHToUInt(OHMasking.first(rdportall)).resized
    
  
  val fsm = new Area {
  import CamStates._
  val state = Reg(CamStates()) init (idle)
  dpramwe := False
  eramwe := False
  sbits := 0
  switch(state) {
        is(idle) {
          adrreg := io.adr
          delreg := io.del  
          when(io.wen) {
            state := del1
          }
        }
        is(del1) {
           state := del2
        }
        is(del2) { 
           ebits := (U(1) << adrreg).asBits       
           state := write1
           dpramwe := True
           eramwe := True

           when(delreg) {
           	 state:=idle
           }
        }
        is(write1) {
        	state := write2
        }
        is(write2) {
            sbits := (U(1) << adrreg).asBits
            dpramwe := True
        	state := idle
        }
        
  }
  io.busy := state =/= idle
 } 
}
}



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


class TracePlugin(Tinterface: InterfaceKind = ETH100MII, regcount: Int = 1) extends Plugin[VexRiscv]{
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
    val tabwrite = RegInit(False)
    val tabbusy = Bool()
    val tabadr = Reg(UInt(16 bits)) init(0)
    val tabdata = Reg(Bits(32 bits)) init(0)
    val triggered = Reg(Bool) init(False)
    val msamplecmd = Reg(Bits(32 bits))
    val coresel = Reg(Bits(4 bits)) init(0)
    val wordcount = regcount + 1 // registers + timestamp
    assert(wordcount % 2 == 0)
    csrService.w(CSR.MSAMPLE, msamplecmd)
    for (i <- 0 until regcount ) {
        csrService.w(CSR.MSAMPLESEL, i*5 -> msamplesel(i))
    }
    
    csrService.w(CSR.MSAMPLETABCFG, 0 -> tabwrite, 16 -> tabadr)
    csrService.r(CSR.MSAMPLETABCFG, 8 -> tabbusy)
    csrService.w(CSR.MSAMPLETABDAT, tabdata)
    
    tabwrite clearWhen(tabbusy)
    val cam = new Cam(dataw = 32, depth = 64, slices=4)
    cam.io.wen := tabwrite
    cam.io.adr := tabadr.resized
    cam.io.data := tabdata
    cam.io.del := False
    tabbusy := cam.io.busy
    cam.io.mdata := lastStage.input(PC).asBits
  
    csrService.w(CSR.MSAMPLECSEL, coresel)
    csel = out(Bits(4 bits))
    csel := coresel
    val headerofs = if(Tinterface == `ETH100MII`) 1 else 0
    val inmaxsize = wordcount*4 + wordcount/2 + 1 + headerofs
    
    val fifo = new StreamFifoVar(Bits(8 bits), depth = 32, inmaxsize = inmaxsize, outsize=1 )
    
    val insCounter = Reg(UInt(32 bits)) init(0)
    val lastinsCounter = Reg(UInt(32 bits)) init(0)
    insCounter := insCounter + 1
    val regFile = RegInit(Vec.tabulate(regcount)(i=>B(0,32 bits)))
    val oldregFile = RegInit(Vec.tabulate(regcount)(i=>B(0,32 bits)))
    val data = Vec(Bits(32 bits), wordcount)
    val res = Vec(Bits(8 bits), inmaxsize)
    var sizeacc = Vec(UInt(log2Up(wordcount*4) bits), wordcount + 1)
    val size = Vec(UInt(4 bits), wordcount)
    sizeacc(0) := U(0)
    res.map(_ := B"d0")
    for (i <- 0 until wordcount ) {
      if(i==0) {
       data(i) := (insCounter - lastinsCounter).asBits
      } else {
        data(i) := oldregFile(U(i - 1).resized) ^ regFile(U(i - 1).resized)
      }
      size(i) := ((OHToUInt(OHMasking.last(data(i))).resize(6) + U"6'd7") >>  3).resized
      for (j<- 0 until 4) {
           when (j < (size(i))) {
             res((sizeacc(i) + j + wordcount/2 + 1 + headerofs).resized) := data(i).subdivideIn(8 bits)(j)
           }
       }
      sizeacc(i+1) := (sizeacc(i)  + size(i)).resized
    }
    if(Tinterface == `ETH100MII`)  {
      res(0) := (1 + wordcount/2  + sizeacc(wordcount)  << 3).asBits.resized
    } 
    res(headerofs)(7 downto 4) := wordcount
    res(headerofs)(3 downto 0) := cam.io.matadr.asBits(3 downto 0)
    for(i <- 0 until wordcount/2) {
    	res(headerofs + 1 + i)(7 downto 4) := size(i*2 + 1).asBits
    	res(headerofs + 1 + i)(3 downto 0) :=  size(i*2).asBits
    }
    
    res.allowOverride
    
    fifo.io.incnt :=  (headerofs + 1 + wordcount/2 + sizeacc(wordcount)).resized
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
    when((lastStage.arbitration.isFiring && cam.io.mat) && (triggered === False)) {
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