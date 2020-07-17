package scalaam.util

import java.io.{BufferedWriter, FileWriter}
import java.text.SimpleDateFormat
import java.util.Calendar

object Reader {

  def loadFile(file: String): String = {
    val fHandle = scala.io.Source.fromFile(file)
    val content = fHandle.getLines().mkString("\n")
    fHandle.close()
    content
  }

}

/**
 * Utility to write to plain text files. Can also be modifief to write to csv files using
 * a CSVWriter, CSVWriter.NO_QUOTE_CHARACTER and the writeNext method.
 */
object Writer {

  type Writer = BufferedWriter

  private val  calendar: Calendar         = Calendar.getInstance()
  private val    format: SimpleDateFormat = new SimpleDateFormat("yyyy-MM-dd-HH:mm:ss")

  private var defaultWriter: Writer = _
  var report: Boolean = false

  def open(path: String): Writer =
    new BufferedWriter(new FileWriter(path))

  def openTimeStamped(dir: String, file: String): Writer =
    open(dir + format.format(calendar.getTime) + "_" + file)

  def close(writer: Writer): Unit = writer.close()

  def setDefaultWriter(writer: Writer): Unit = defaultWriter = writer
  def closeDefaultWriter(): Unit = defaultWriter.close()

  def  enableReporting(): Unit = report = true
  def disableReporting(): Unit = report = false

  // Avoid output being buffered.
  def write(writer: Writer, data: String): String = {
    writer.write(data)
    writer.flush()
    if (report) {
      System.out.print(data)
      System.out.flush()
    }
    data
  }

  def writeln(writer: Writer, data: String): String = write(writer, data + "\n")

  def write(data: String = "\n"): String = write(defaultWriter, data)
  def writeln(data: String = "\n"): String = writeln(defaultWriter, data)

  def writeErr(writer: Writer, data: String): String = {
    System.err.print(data)
    System.err.flush()
    writer.write(data)
    writer.flush()
    data
  }

  def writeErrln(writer: Writer, data: String): String = writeErr(writer, data + "\n")

  def writeErr(data: String = "\n"): String = writeErr(defaultWriter, data)
  def writeErrln(data: String = "\n"): String = writeErrln(defaultWriter, data)

}