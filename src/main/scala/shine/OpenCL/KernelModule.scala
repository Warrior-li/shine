package shine.OpenCL

import shine.OpenCL.AST.Kernel
import shine.{C, OpenCL}

// A OpenCL KernelModule consists of a set of kernels and their
// dependencies (i.e. declarations)
case class KernelModule(decls: Seq[C.AST.Decl],
                        kernels: Seq[Kernel]) {
  def compose(other: KernelModule): KernelModule =
    KernelModule((decls ++ other.decls).distinct, kernels ++ other.kernels)

  def codeOverride(): Option[String] = None
}

object KernelModule {
  def compose(ms: Seq[KernelModule]): KernelModule = ms.reduce(_ compose _)

  def translationToString(m: KernelModule): String = {
    m.codeOverride().getOrElse {
      val decls = m.decls.map(OpenCL.AST.Printer(_)).filter(_.nonEmpty)
      val kernels = m.kernels.map(k => OpenCL.AST.Printer(k.code)).filter(_.nonEmpty)
      Seq(decls.mkString("\n"), kernels.mkString("\n"))
        .filter(_.nonEmpty)
        .mkString("\n\n")
    }
  }
}
