import scala.language.implicitConversions
import scala.language.reflectiveCalls

import $file.lexer, lexer._
import $file.parser, parser._

import $file.translate, translate._
import $file.trees , trees._
//program inverter for Rimp language


var rev_counter = -1
def new_rev_counter : (String, Int) = {
  rev_counter = rev_counter + 1
  val current_counter = rev_counter
  ("counter_" + counter.toString, current_counter)
}

var while_counters_map = Map[Cmd , String]()



def rev_exp (e : IExp) : IExp = e match {
    case _ => e
}


def rev_cmd (c : Cmd) : Cmd = c match {
    case Assign (v, e) => RevAssign(v, rev_exp(e))
    case RevAssign (v, e) => Assign(v, rev_exp(e))
    case Skip => Skip
    case If (e, c1, c2) => If(rev_exp(e), rev_block(c1), rev_block(c2))
    //while !counteri > 0 do rev(C)
    case While (e, c1) =>  {
        e match {
            
            case Bop (">", DRefr(var_name), Num(0)) => {
                //this is the case where a while loop contains a counter
                //check if the counter is in the table
                if (var_name.contains("counter_")) {
                    //get the expression from the table
                    val e = indextable(var_name)
                    //return the while loop with the expression from the table
                    While (e, rev_block(c1))
                }
                else {
                //this is the case where a while loop contains a greater than operator but no counter
                val (counter_string, counter_int) = new_rev_counter
                indextable = indextable + (counter_string -> e)
                 While (Bop(">", DRefr(counter_string), Num(0)), rev_block(c1) )
                }
            }
            case _ =>
                    //check if the expression is in the table values 
                    if (indextable.values.exists(_ == e)) {
                        //get the counter from the table
                        val counter_string = indextable.filter(_._2 == e).keys.head
                        //return the while loop with the counter from the table
                        While (Bop(">", DRefr(counter_string), Num(0)), rev_block(c1))
                    }
                    else {
                        //create a new counter
                        val (counter_string, counter_int) = new_rev_counter
                        //add the counter to the table
                        indextable = indextable + (counter_string -> e)
                        //return the while loop with the new counter
                        While (Bop(">", DRefr(counter_string), Num(0)), rev_block(c1))
                    }
        }

    }
}


def rev_block (b : Block) : Block = b match {
    case Nil => Nil
    case c::cs => rev_block(cs) :+ (rev_cmd(c))
}


def rev_prog (p:List[Prog]) : List[Prog] = p match {
    case Nil => Nil
    case c::cs => c.isInstanceOf[Cmd] match {
        case true => rev_prog(cs) :+ (rev_cmd(c.asInstanceOf[Cmd]))
        case false => rev_prog(cs) :+ (rev_exp(c.asInstanceOf[IExp]))
    }
}




@main
def main(filename: String): Unit = {
  val tokens = tokenise(os.read(os.pwd / filename))
  val tree = Prog.parse_single(tokens)
  val rev_tree = translate_prog(tree)
  val result = rev_prog(rev_tree)
  val original = rev_prog(result)
    print ("reversed tree ==> " + rev_tree + "\n")
    print ("\n\n\n")
    print ("result ==> " + result + "\n")
    print ("\n\n\n")
    print ("reversed result ==> " + original + "\n")

}