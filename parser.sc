// A parser for the SIMP language
//================================
//
// call with 
//
//     amm fun_parser.sc fact.simp
//
//     amm fun_parser.sc defs.simp
//
// this will generate a parse-tree from a list
// of tokens

import scala.language.implicitConversions    
import scala.language.reflectiveCalls

import $file.lexer, lexer._ 


// Parser combinators
//    type parameter I needs to be of Seq-type
//
abstract class Parser[I, T](implicit ev: I => Seq[_]) {
  def parse(ts: I): Set[(T, I)]

  def parse_single(ts: I) : T = 
    parse(ts).partition(_._2.isEmpty) match {
      case (good, _) if !good.isEmpty => good.head._1
      case (_, err) => { 
        if (err.isEmpty) println("Parse Error: unexpected end of input because of empty set")
        else
	println (s"Parse Error\n${err.minBy(_._2.length)}") ; sys.exit(-1) }
    }
}

// convenience for writing grammar rules
case class ~[+A, +B](_1: A, _2: B)

class SeqParser[I, T, S](p: => Parser[I, T], 
                         q: => Parser[I, S])(implicit ev: I => Seq[_]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) = 
    for ((head1, tail1) <- p.parse(sb); 
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I, T](p: => Parser[I, T], 
                      q: => Parser[I, T])(implicit ev: I => Seq[_]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)   
}

class FunParser[I, T, S](p: => Parser[I, T], 
                         f: T => S)(implicit ev: I => Seq[_]) extends Parser[I, S] {
  def parse(sb: I) = 
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

// convenient combinators
implicit def ParserOps[I, T](p: Parser[I, T])(implicit ev: I => Seq[_]) = new {
  def || (q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

def ListParser[I, T, S](p: => Parser[I, T], 
                        q: => Parser[I, S])(implicit ev: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)) ==> { case x ~ _ ~ z => x :: z : List[T] } ||
  (p ==> ((s) => List(s)))
}


case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) = TokParser(t)

implicit def TokOps(t: Token) = new {
  def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](t, q)
  def ==>[S] (f: => Token => S) = new FunParser[List[Token], Token, S](t, f)
  def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](t, q)
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_NUM(n)::ts => Set((n, ts)) 
    case _ => Set ()
  }
}

case object IdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object DRefrParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_DREF(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}



// Abstract syntax trees for the Simp language
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


case object Skip extends Cmd
case class If(a: IExp, bl1: Block, bl2: Block) extends Cmd
case class While(b: IExp, bl: Block) extends Cmd
case class Assign(v: Var, a: IExp) extends Cmd
case class RevAssign(v: Var, a: IExp) extends Cmd 


case class Var(s: String) extends IExp
case class Num(i: Int) extends IExp
case class Aop(o: String, a1: IExp, a2: IExp) extends IExp
case class Bop(o: String, a1: IExp, a2: IExp) extends IExp
case class Not(a: IExp) extends IExp
case class DRefr(s: String) extends IExp //dereference written as !s

//not used in the parser, but used in the interpreter for convenience

//take a string and format it so it is underlined when printed
def underline(s: String) = "\u001b[4m" + s + "\u001b[0m"

//Underlined versions of expressions used to keep track of the control stack and the back stack
case class ULVar(s: String) extends IExp {  //underlined variable 
  override def toString = "Var(" + underline(s) + ")"
}
case class ULNum(i: Int) extends IExp {  //underlined number 
  override def toString = "Num(" + underline(i.toString) + ")"
}
case class ULAop(o: String, a1: IExp, a2: IExp) extends IExp{
  override def toString = "Aop(" + underline(o) + ", " + a1 + ", " + a2 + ")"
}
case class ULBop(o: String, a1: IExp, a2: IExp) extends IExp {
  override def toString = "Bop(" + underline(o) + ", " + a1 + ", " + a2 + ")"
}
case class ULNot(a: IExp) extends IExp {
  override def toString = "Not(" + a + ")"
}
case class ULDRefr(s: String) extends IExp {  //underlined dereference 
  override def toString = "DRefr( " + underline(s) + " )"
}

case object EmptyExp extends IExp {  //empty expression label for convenience on the control stack 
  override def toString = "exp"
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


case class  ProgBl (bl: Block) extends Prog //program block to keep track of the block of a program

case class ProgSeq(p1: Prog, p2: Prog) extends Prog //program sequence



// Grammar Rules for the Simp language

//Programs in SIMP are commands (C) or integer expressions (E).

//C ::= skip | if E then C else C | while E do C | s := E

//P ::= C | E

//op ::= + | - | * | / | % | < | <= | > | >= | == | !=

//E ::= n | s | E op E | (E) | ¬E


//integer expressions
//E ::= !var | n | E op E | ¬E | (E)
lazy val IExp : Parser[List[Token], IExp] = 
  ( T_OP("¬") ~ IExp) ==> { case x ~ y => Not(y): IExp } ||
   ( T_OP("~") ~ IExp) ==> { case x ~ y => Not(y): IExp } ||  L 
lazy val L: Parser[List[Token], IExp] =  //logical expressions
  (T ~ T_OP("+") ~ IExp) ==> { case x ~ _ ~ z => Aop("+", x, z): IExp } ||
  (T ~ T_OP("-") ~ IExp) ==> { case x ~ _ ~ z => Aop("-", x, z): IExp } || 
  (T ~ T_OP("<") ~ IExp) ==> { case x ~ _ ~ z => Bop("<", x, z): IExp } ||
  (T ~ T_OP("<=") ~ IExp) ==> { case x ~ _ ~ z => Bop("<=", x, z): IExp } ||
  (T ~ T_OP(">") ~ IExp) ==> { case x ~ _ ~ z => Bop(">", x, z): IExp } ||
  (T ~ T_OP(">=") ~ IExp) ==> { case x ~ _ ~ z => Bop(">=", x, z): IExp } ||
  (T ~ T_OP("=") ~ IExp) ==> { case x ~ _ ~ z => Bop("==", x, z): IExp } ||  
  (T ~ T_OP("∧") ~ IExp) ==> { case x ~ _ ~ z => Bop("&&", x, z): IExp } || T
lazy val T: Parser[List[Token], IExp] =  //term expressions
  (F ~ T_OP("*") ~ L) ==> { case x ~ _ ~ z => Aop("*", x, z): IExp } || 
  (F ~ T_OP("/") ~ L) ==> { case x ~ _ ~ z => Aop("/", x, z): IExp } ||  F

lazy val F: Parser[List[Token], IExp] =   //factor expressions
  ( T_LPAREN ~ IExp ~ T_RPAREN ) ==> { case x ~ y ~ z => y :IExp } ||
  NumParser ==> { case x => Num(x) :IExp } || 
  (DRefrParser) ==> { case x => DRefr(x) :IExp } 

//C ::= skip | l := E | if E then C else C | while E do C | (C)
lazy val SingleCmd : Parser[List[Token], Cmd] = 
  (T_SKIP) ==> { case _=> Skip: Cmd } ||
  (T_LPAREN ~ SingleCmd ~ T_RPAREN) ==> { case x ~ y ~ z => y: Cmd } ||
  (IdParser ~ T_OP(":=") ~ IExp) ==> { case x ~ _ ~ y => Assign(Var(x), y): Cmd } ||
  (T_KWD("if") ~ IExp ~ T_KWD("then") ~ ListParser(AllCmds, T_SEMI) ~ T_KWD("else") ~  ListParser(AllCmds, T_SEMI)) ==> { case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Cmd } ||
  //if then with no else, in this case the else is skip
  (T_KWD("if") ~ IExp ~ T_KWD("then") ~  ListParser(AllCmds, T_SEMI) ) ==> { case _ ~ x ~ _ ~ y  => If(x, y, List(Skip)): Cmd } 


lazy val WhileCmd : Parser[List[Token], Cmd] = 
  (T_KWD("while") ~ IExp ~ T_KWD("do") ~ ListParser(AllCmds, T_SEMI)) ==> { case _ ~ x ~ _ ~ y => While(x, y): Cmd }||
  //While in parenthesis
   (T_LPAREN ~ WhileCmd ~ T_RPAREN) ==> { case x ~ y ~ z => y: Cmd } 

 lazy val AllCmds : Parser[List[Token], Cmd] =
  (WhileCmd) ==> { case x => x: Cmd } ||
  (SingleCmd) ==> { case x => x: Cmd }


  //seq of commands ending with a command
  lazy val SeqCmd : Parser[List[Token], List[Cmd]] =
  (ListParser(SingleCmd, T_SEMI)  ~ T_SEMI ~ WhileCmd) ==> { case x ~ _ ~ y => x :+ y: List[Cmd] } ||
  (ListParser(SingleCmd, T_SEMI)  ~ T_SEMI ~ SingleCmd) ==> { case x ~ _ ~ y => x :+ y: List[Cmd] } 


lazy val Prog : Parser [List[Token], List[Prog]] =
  (SeqCmd) ==> { case x => x : List[Prog] } ||
  (WhileCmd) ==> { case x => List(x) : List[Prog] } ||
  (SingleCmd) ==> { case x => List(x) : List[Prog] } ||
  (IExp) ==> { case x => List(x) : List[Prog] } 




// Reading tokens and Writing parse trees

// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
// import os._


def parse_tks(tks: List[Token]) : List[Prog] = 
  Prog.parse_single(tks)


@main
def main(fname: String) : Unit = {
  val tks = tokenise(os.read(os.pwd / fname))
  println(parse_tks(tks))
}


