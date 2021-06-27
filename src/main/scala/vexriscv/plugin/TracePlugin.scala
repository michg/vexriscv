package vexriscv.plugin

import vexriscv._
import spinal.core._
import spinal.lib._
import spinal.lib.com.uart._

import scala.collection.mutable

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


class TracePlugin(regcount: Int = 1, slicebits : Int = 8) extends Plugin[VexRiscv]{
  import Riscv._
  import CsrAccess._ 
  var uart : Uart = null
  
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
    val triggeradr = Reg(Bits(32 bits))
    val triggered = Reg(Bool) init(False)
    val msamplecmd = Reg(Bits(32 bits))
    val wordcount = regcount + 1
    val regslices = 32 / slicebits
    val headerslices = 8 / slicebits
    csrService.w(CSR.MSAMPLE, msamplecmd)
    for (i <- 0 until regcount ) {
        csrService.w(CSR.MSAMPLESEL, i*5 -> msamplesel(i))
    }
    csrService.w(CSR.MSAMPLEADR, triggeradr)
    val fifo = new StreamFifoVar(Bits(slicebits bits), depth = 32, inmaxsize = wordcount*(regslices + headerslices), outsize=1 )
    
    val insCounter = Reg(UInt(32 bits)) init(0)
    val lastinsCounter = Reg(UInt(32 bits)) init(0)
    insCounter := insCounter + 1
    val regFile = RegInit(Vec.tabulate(regcount)(i=>B(0,32 bits)))
    val oldregFile = RegInit(Vec.tabulate(regcount)(i=>B(0,32 bits)))
    val data = Vec(Bits(32 bits), wordcount)
    val res = Vec(Bits(slicebits bits), wordcount*(regslices + headerslices))
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
           res((sizeacc(i) + j).resized) := header(i).subdivideIn(slicebits bits)(j)
      }
      for (j<- 0 until regslices) {
           when (j < (size(i) + 1)) {
             res((sizeacc(i) + j + headerslices).resized) := data(i).subdivideIn(slicebits bits)(j)
           }
       }
      sizeacc(i+1) := (sizeacc(i) + size(i) + headerslices + 1).resized
    }
    fifo.io.incnt := sizeacc(wordcount)
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
    
    uart = master(Uart()).setName("uart") 
    
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