//translate from simp to rimp 
//making simp reversible by adding appropriate changes to while loops and if condition statements


import scala.language.implicitConversions
import scala.language.reflectiveCalls

import $file.lexer, lexer._
import $file.parser, parser._

var counter = -1
def new_variable_string : String = {
  counter = counter + 1
  "x_" + counter.toString
}

def new_counter_string : String = {
  counter = counter + 1
  "counter_" + counter.toString
}


def translate_if (i : Cmd) : Block = i match {
    case If (e , c1, c2 ) => {
        val translation = translate_exp(e)
        val assignments = translation._2.map( x => Assign(Var(x._2), x._1)).toList
         assignments ++ List(If(translation._1, translate_block(c1), translate_block(c2))) 
    }

    case _ => List(i)

}


def translate_while (i : Cmd) : Block = i match {
    case While (e , c1) => {
        var counter_string = new_counter_string
        val init_counter = Assign(Var(counter_string), Num(0))

        init_counter :: While(e, translate_block(c1) ++ List(Assign(Var(counter_string), Aop("+", DRefr(counter_string), Num(1))))) :: Nil
    }

    case _ => List(i)

}


//E ::= !l | n | E op E | ¬E
def translate_exp (e : IExp) : (IExp , Map [DRefr, String]) = e match {
    case DRefr (s) => {
        val new_variable = new_variable_string
        (DRefr(new_variable), Map (DRefr(s) -> new_variable))
    }
    case Num (i) => (Num(i), Map())
    case Aop (o, a1, a2) => {
        val translation1 = translate_exp(a1)
        val translation2 = translate_exp(a2)

       (Aop(o, translation1._1, translation2._1) , (translation1._2 ++ translation2._2))
    }
    case Bop (o, a1, a2) => {
        val translation1 = translate_exp(a1)
        val translation2 = translate_exp(a2)  

       (Bop(o, translation1._1, translation2._1) , (translation1._2 ++ translation2._2))
    }
    case Not (a) => {
        val translation = translate_exp(a)
        (Not(translation._1), translation._2)
    }
}



//translate all statements in a block
def translate_block (bl :Block) : Block = {
    bl match {
        case Nil => Nil
        case x :: xs => x match {
            case If (e , c1, c2 ) => translate_if(x) ++ translate_block(xs)
            case While (e , c1) => translate_while(x) ++ translate_block(xs)
            case _ => x :: translate_block(xs)
        }
    }
}



//translate all statements in a program
def translate_prog (prog :List[Prog]) : List[Prog] = {
    prog match {
        case Nil => Nil
        case x :: xs => x match {
            case If (e , c1, c2 ) => translate_if(If (e , c1, c2 )) ++ translate_prog(xs)
            case While (e , c1) => translate_while(While (e , c1)) ++ translate_prog(xs)
            case _ => x :: translate_prog(xs)
        }
    }
}



@main
def main(filename: String): Unit = {
  val tokens = tokenise(os.read(os.pwd / filename))
  val tree = Prog.parse_single(tokens)
  print ("initial tree: " +  "\n" + tree + "\n")
  println (" \n")
   val result = translate_prog(tree)
   print ("revrsible tree: " +  "\n" + result + "\n")

}
