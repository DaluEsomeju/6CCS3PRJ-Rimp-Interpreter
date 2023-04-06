// Abstract syntax trees for the Simp and Rimp languages
//Programs in SIMP are commands (C) or integer expressions (E).

 class Prog {
  def to_Iexp = this match {
    case i: IExp => i
    case _ => throw new Exception("Not an integer expression" + this)
  }

  def to_Cmd = this match {
    case c: Cmd => c
    case _ => throw new Exception("Not a command" + this)
  }
 }


abstract class Cmd extends Prog //command
abstract class IExp  extends Prog //integer expression


type Block = List[Cmd] 

def block_to_string(bl: Block) : String = bl match {
  case Nil => ""
  case c::Nil => c.toString
  case c::cs => c.toString + "; " + block_to_string(cs)
}

case object Skip extends Cmd
case class If(a: IExp, bl1: Block, bl2: Block) extends Cmd {
  override def toString = "if (" + a + ") then {" + block_to_string(bl1) + "} else {" + block_to_string(bl2) + "}"
}
case class While(b: IExp, bl: Block) extends Cmd {
  override def toString = "while (" + b + ") do {" + block_to_string(bl) + "}"
}
case class Assign(v: Var, a: IExp) extends Cmd {
  override def toString = v + " := " + a
}
case class RevAssign(v: Var, a: IExp) extends Cmd  {
  override def toString = v + " =: " + a
}


case class Var(s: String) extends IExp {
  override def toString = s match {
    case null => ""
    case _ => s
  }
}
case class Num(i: Int) extends IExp {
  override def toString = i.toString
}
case class Aop(o: String, a1: IExp, a2: IExp) extends IExp {
  override def toString =   a1 + " " + o + " " + a2 
}
case class Bop(o: String, a1: IExp, a2: IExp) extends IExp {
  override def toString =  a1 + " " + o + " " + a2 
}
case class Not(a: IExp) extends IExp {
  override def toString = "¬" + a
}
case class DRefr(s: String) extends IExp //dereference written as !s in the parser
{
  override def toString = "!" + s
}

//not used in the parser, but used in the interpreter for convenience

//take a string and format it so it is underlined when printed
def underline(s: String) = "\u001b[4m" + s + "\u001b[0m"

//Underlined versions of expressions used to keep track of the control stack and the back stack
case class ULVar(s: String) extends IExp {  //underlined variable 
  override def toString = underline(s)
}
case class ULNum(i: Int) extends IExp {  //underlined number 
  override def toString = underline(i.toString)
}
case class ULAop(o: String, a1: IExp, a2: IExp) extends IExp{
  override def toString = underline( a1 + " " + o + " " + a2 )
}
case class ULBop(o: String, a1: IExp, a2: IExp) extends IExp {
  override def toString = underline( a1 + " " + o + " " + a2 )
}
case class ULNot(a: IExp) extends IExp {
  override def toString = underline("¬" + a)
}
case class ULDRefr(s: String) extends IExp {  //underlined dereference 
  override def toString = underline("!" + s)
}

case object EmptyExp extends IExp {  //empty expression label for convenience on the control stack 
  override def toString = ""
}

case object NegExp extends IExp {  //negative empty expression label for convenience on the back stack 
  override def toString = "neg"
}

case object ULNegExp extends IExp {  //underlined negative empty expression label  for convenience on the back stack 
  override def toString = underline("neg")
}

case object AssignLabel extends Cmd {  //assign label for convenience on the control stack 
  override def toString = "asgn"
}

case object RevAssignLabel extends Cmd {  //reverse assign label for convenience on the control stack 
  override def toString = "asgnr"
}

case object ProgSeqLabel extends Cmd {  //sequence label for convenience on the control stack 
  override def toString = "seq"
}

case object SemiLabel extends Cmd {  //semicolon label to separate commands in a sequence 
  override def toString = ";"
}

case object IfLabel extends Cmd {  //if label for convenience on the control stack 
  override def toString = "if"
}

case object ULIfLabel extends Cmd {  //underlined if label for convenience on the control stack 
  override def toString = underline("if")
}

case object ConditionLabel extends Cmd {  //condition label for convenience on the control stack 
  override def toString = "cond"
}

case object ULConditionLabel extends Cmd {  //underlined condition label for convenience on the control stack 
  override def toString = underline("cond")
}


case class WhileLabel(index : Int) extends Cmd {  //while label for convenience on the control stack 
  override def toString = "while"
}

case class ULWhileLabel(index : Int) extends Cmd {  //underlined while label for convenience on the control stack 
  override def toString = underline("while")
}

case class LoopLabel(index : Int) extends Cmd {  //loop label for convenience on the control stack 
  override def toString = "loop"
}

case class ULLoopLabel(index : Int) extends Cmd {  //underlined loop label for convenience on the control stack 
  override def toString = underline("loop")
}

case class EndWhileLabel(index : Int) extends Cmd {  //end while label for convenience on the control stack 
  override def toString = underline("endwhile")
}


case class  ProgBl (bl: Block) extends Prog //program block to keep track of the block of a program
{
  override def toString = block_to_string(bl)
}

case class ProgSeq(p1: Prog, p2: Prog) extends Prog //program sequence
{
  override def toString = p1.toString + " ; " + p2.toString
}

