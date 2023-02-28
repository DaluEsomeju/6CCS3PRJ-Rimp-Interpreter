// An abstract syntax machine for the RIMP language
import $file.lexer, lexer._
import $file.translate, translate._
import $file.invert, invert._
import $file.interpret, interpret._
import $file.parser, parser._



//v ::= 0 | +(n, v) 
class Rval   {
    def toInt : Int = this match {
        case RvZero => 0
        case RvPair(n, r) => if (n == 0)  throw new Exception("n can not be 0") else n + r.toInt
    }

    def getN : Int = this match {
        case RvZero => throw new Exception("not an RvPair")
        case RvPair(n, r) => n
    }

    def getV : Rval = this match {
        case RvZero => throw new Exception("not an RvPair")
        case RvPair(n, r) => r
    }
}


case object RvZero extends Rval // 0

case class RvPair (n : Int , r : Rval) extends Rval   // +(n, r) //n can not be 0


def int_to_rval (n : Int) : Rval = {
    if (n == 0) RvZero
    else {
        RvPair(n, RvZero)
    }
}



type Renv = Map[String, (Int , Rval)] //maps each variable to a pair (k, v ) where  v is a RVal k is v.toInt


//underline expression function from Iexp to Iexp
//take an expression and return an expression

def underline_exp (e : IExp) : IExp = e match {
    case Num (n) => ULNum(n)
    case DRefr (s) => ULDRefr(s)
    case Not (e) => ULNot(e)
    case Aop (o, e1, e2) => ULAop(o, e1, e2)
    case Bop (o, e1, e2) => ULBop(o, e1, e2)
    case _ => e
}

def remove_underline (e : IExp) : IExp = e match {
    case ULNum (n) => Num(n)
    case ULDRefr (s) => DRefr(s)
    case ULNot (e) => Not(e)
    case ULAop (o, e1, e2) => Aop(o, e1, e2)
    case ULBop (o, e1, e2) => Bop(o, e1, e2)
    case _ => e
}

def eval_rexp (e: Prog, env: Renv) :Int = e match { //same as simp except for the case of DRefr 
    case Num (n) => n
    case ULNum (n) => n
    case DRefr (s) => env(s)._1
    case ULDRefr (s) => env(s)._1
    case Not (e) => if (eval_rexp(e, env) == 0) 1 else 0
    case ULNot (e) => if (eval_rexp(e, env) == 0) 1 else 0
    case Aop (o, e1, e2) => o match {
        case "+" => eval_rexp(e1, env) + eval_rexp(e2, env)
        case "-" => eval_rexp(e1, env) - eval_rexp(e2, env)
        case "*" => eval_rexp(e1, env) * eval_rexp(e2, env)
        case "/" => eval_rexp(e1, env) / eval_rexp(e2, env)
        case _ => throw new Exception("Unknown operator")
    }

    case ULAop (o, e1, e2) => o match {
        case "+" => eval_rexp(e1, env) + eval_rexp(e2, env)
        case "-" => eval_rexp(e1, env) - eval_rexp(e2, env)
        case "*" => eval_rexp(e1, env) * eval_rexp(e2, env)
        case "/" => eval_rexp(e1, env) / eval_rexp(e2, env)
        case _ => throw new Exception("Unknown operator")
    }

   case Bop (o, e1, e2) => o match {
        case "<" => if (eval_rexp(e1, env) < eval_rexp(e2, env)) 1 else 0
        case ">" => if (eval_rexp(e1, env) > eval_rexp(e2, env)) 1 else 0
        case "&&" => if (eval_rexp(e1, env) == 1 && eval_rexp(e2, env) == 1) 1 else 0
        case "==" => if (eval_rexp(e1, env) == eval_rexp(e2, env)) 1 else 0
        case _ => throw new Exception("Unknown operator")
    }

    case ULBop (o, e1, e2) => o match {
        case "<" => if (eval_rexp(e1, env) < eval_rexp(e2, env)) 1 else 0
        case ">" => if (eval_rexp(e1, env) > eval_rexp(e2, env)) 1 else 0
        case "&&" => if (eval_rexp(e1, env) == 1 && eval_rexp(e2, env) == 1) 1 else 0
        case "==" => if (eval_rexp(e1, env) == eval_rexp(e2, env)) 1 else 0
        case _ => throw new Exception("Unknown operator")
    }

    case _ => throw new Exception("Unknown expression")

}


//RConfigurations are quadruples of stacks: (Control, Results,  RMemory , Backtrack)

//Control is a stack of Progs
// Results is a stack of Progs
// RMemory is a map from variables to pairs (k, v) where v is a Rval and k is v.toInt
// Backtrack is a stack of Progs

type RConfig = (List[Prog], List[Prog], Renv, List[Prog])


def rconfig_to_string (c : RConfig) : String = c match {
    case (cs, rs, renv, bs) => "Control: "  + cs +  "\n" + " Results: " + rs + "\n" + " Store: " + renv + "\n" + " Backtrack: " + bs + "\n"
    case _ => "Error 1"
}

def init_config (tree : List [Prog]) : RConfig = (tree, Nil, init_renv(tree), Nil)

//initial RMemory is a map from variables to pairs (k, v) where v is a RvZero and k is 0
//go through the tree and find all the variables and add them to the RMemory

def init_renv(tree : List[Prog]) : Renv = tree match {
    case Nil => Map()
   case Assign (Var (s), e) :: rest => Map(s -> (0, RvZero)) ++ init_renv(rest)
    case _ :: rest => init_renv(rest)
}

//switch the backtracking stack with the control stack
def switch (c : RConfig) : RConfig = c match {
    case (cs, rs, renv, bs) => (bs, rs, renv, cs)
    case _ => throw new Exception("Error 2")
}


//The transition relation is a function from rconfigurations to rconfigurations
//The transition relation is a partial function, so we use Option[RConfig]

//transition from a configuration to a new configuration 
def step_revexp (c : RConfig) :Option[RConfig] = c match {
    case (Num(n) :: cs, rs, renv, bs) => Some(cs, Num(n) :: rs, renv, ULNum(n) :: bs)
    case (ULNum(n) :: bs, rs, renv, cs) => Some(bs, rs.tail, renv, Num(n) :: cs)
    case (DRefr(s) :: cs, rs, renv, bs) => {
        val result = renv(s)._1
        val new_rs = Num(result) :: rs
        Some(cs, new_rs, renv, ULDRefr(s) :: bs)
    }

    case (ULDRefr(s)::bs, rs, renv, cs) => {
        Some(bs, rs.tail, renv , DRefr(s) :: cs)
    }


    case (Aop(o, EmptyExp , EmptyExp):: cs, rs , renv , bs ) => {
        val n2 = rs.head.to_Iexp
        val n1 = rs.tail.head.to_Iexp
        val new_rs = Num(eval_rexp(ULAop(o, n1,n2), renv)) :: rs.drop(2) //n = n1 o n2 on top of the rs stack
        val e2 = bs.head.to_Iexp
        val e1 = bs.tail.head.to_Iexp
        val new_bs = ULAop(o, remove_underline(e1), remove_underline(e2)) :: bs.drop(5)
        Some(cs, new_rs, renv, new_bs)
    }

    case (ULAop(o, EmptyExp , EmptyExp):: bs, rs , renv ,  cs ) => {
        val e2 = cs.head.to_Iexp
        val e1 = cs.tail.head.to_Iexp
        val new_cs = Aop(o, remove_underline(e1), remove_underline (e2)) :: cs.drop(5)
        val new_rs = rs.drop(3)
        Some(bs, new_rs, renv, new_cs)
    }


    case (Aop(o, e1, e2) :: cs, rs, renv, bs)=>{
        val expressions = e1 :: List (e2)
        val underlined_expressions = underline_exp(e1) :: List (underline_exp(e2))
        val top_of_control = expressions ::: List(Aop(o, EmptyExp, EmptyExp))
        val top_of_backtrack = EmptyExp :: underlined_expressions 
        Some(top_of_control ::: cs, rs, renv, top_of_backtrack ::: bs)
   }

    case (ULAop(o, e1, e2) :: cs, rs, renv, bs)=>{
        val expressions = e1 :: List (e2)
        val underlined_expressions = underline_exp(e1) :: List (underline_exp(e2))
        val top_of_control = expressions ::: List(ULAop(o, EmptyExp, EmptyExp))
        val top_of_backtrack = EmptyExp :: underlined_expressions
        Some(top_of_control ::: cs, rs, renv, top_of_backtrack ::: bs)
   }   


   case (EmptyExp :: bs , rs, renv, cs) =>  {
        val e1 = cs.head.to_Iexp
        val e2 = cs.tail.head.to_Iexp
        val op = cs.tail.tail.head
        val new_exp = op match {
            case Aop(o, EmptyExp, EmptyExp) => Aop(o,remove_underline(e1), remove_underline(e2))
            case Bop(o, EmptyExp, EmptyExp) => Bop(o, remove_underline(e1), remove_underline(e2))
            case _ => throw new Exception("Error op not found " + op)
        }
        val new_cs = new_exp :: cs.drop(3)
        Some(bs, rs, renv, new_cs)
    }


    case (Bop(o, EmptyExp , EmptyExp):: cs, rs , renv , bs ) => {
        val n2 = rs.head.to_Iexp
        val n1 = rs.tail.head.to_Iexp
        val new_rs = Num(eval_rexp(ULBop(o,n1,n2), renv)) :: rs.drop(2) //n = n1 o n2 on top of the rs stack
        val e2 = bs.head.to_Iexp
        val e1 = bs.tail.head.to_Iexp
        val new_bs = ULBop(o, remove_underline(e1), remove_underline(e2)) :: bs.drop(5)
        Some(cs, new_rs, renv, new_bs)
    } 

     case (ULBop(o, EmptyExp , EmptyExp):: bs, rs , renv ,  cs ) => {
        val e2 = cs.head.to_Iexp
        val e1 = cs.tail.head.to_Iexp
        val new_cs = Bop(o, remove_underline(e1), remove_underline (e2)) :: cs.drop(5)
        val new_rs = rs.drop(3)
        Some(bs, new_rs, renv, new_cs)
    }
    

    case (Bop(o, e1, e2) :: cs, rs, renv, bs)=>{
        val expressions = e1 :: List (e2)
        val underlined_expressions = underline_exp(e1) :: List (underline_exp(e2))
        val top_of_control = expressions ::: List(Bop(o, EmptyExp, EmptyExp))
        val top_of_backtrack = EmptyExp :: underlined_expressions 
        Some(top_of_control ::: cs, rs, renv, top_of_backtrack ::: bs)
   }

    case (ULBop(o, e1, e2) :: cs, rs, renv, bs)=>{
        val expressions = e1 :: List (e2)
        val underlined_expressions = underline_exp(e1) :: List (underline_exp(e2))
        val top_of_control = expressions ::: List(ULBop(o, EmptyExp, EmptyExp))
        val top_of_backtrack = EmptyExp :: underlined_expressions 
        Some(top_of_control ::: cs, rs, renv, top_of_backtrack ::: bs)
    }

    case (Not(EmptyExp) :: cs, rs, renv, bs) => {
        val n = rs.head
        val result = eval_rexp(n, renv)
        val not_result = if (result == 0) 1 else 0
        val new_rs = Num(not_result) :: rs.drop(1)
        val e1 = remove_underline(bs.head.to_Iexp)
        val new_bs = ULNot(e1) :: bs.drop(3)
        Some(cs, new_rs, renv, new_bs)

   }

   case (ULNot(EmptyExp) :: bs, rs, renv, cs) => {
        val exp = cs.head.to_Iexp
        val new_rs = rs.drop(2)
        val new_cs = Not(remove_underline(exp)) :: cs.drop(3) 
        Some(bs, new_rs, renv, new_cs)
   }
   

   case (Not(e) :: cs, rs, renv, bs) => {
        val top_of_control = e :: List(Not(EmptyExp))
        val top_of_backtrack = NegExp :: List(underline_exp(e))
        Some(top_of_control ::: cs, rs, renv, top_of_backtrack ::: bs)
         
   }

   case (ULNot(e) :: cs, rs, renv, bs) => {
        val top_of_control = e :: List(ULNot(EmptyExp))
        val top_of_backtrack = ULNegExp :: List(underline_exp(e))
        Some(top_of_control ::: cs, rs, renv, top_of_backtrack ::: bs)

   }

   case (NegExp :: bs, rs, renv, cs) => {
       val e = cs.head.to_Iexp
        val new_cs = Not(e) :: cs.drop(1)
        Some(cs, rs, renv, new_cs)
   }

    case (ULNegExp :: bs, rs, renv, cs) => {
         val e = cs.head.to_Iexp
          val new_cs = ULNot(e) :: bs.drop(1)
          Some(bs, rs, renv, new_cs)
    }

   case (Nil , rs, renv, bs) => None

   case _ => None

}



def step_revcmd (c :RConfig) : Option [RConfig] = c match {
   case (Skip :: cs, rs, renv, bs) => Some(cs, rs, renv, Skip :: bs)

    case (Assign(Var(null), EmptyExp) :: cs, rs, renv, bs) => {
        val n2 = rs.head.to_Iexp match {
            case Num(x) => x
            case _ => throw new Exception("Invalid number")
        }
        val n1 = rs.tail.head.to_Iexp match {
            case Num(x) => x
            case _ => throw new Exception("Invalid number")
        }
        val var_name = rs.tail.tail.head match {
            case Var(x) => x
            case _ => throw new Exception("Invalid variable")
        }

        val n = n1 - n2

        val exp = bs.drop(3).head.to_Iexp
        
        val new_rs = rs.drop(3)

        val v = renv(var_name)._2

        val new_renv = renv + (var_name -> (n1 , RvPair(n, v)))

        val new_bs = RevAssign(Var(var_name), exp) :: bs.drop(4)

        Some(cs, new_rs, new_renv, new_bs)

    }
   
    case (Assign(Var(x), e) :: cs, rs, renv, bs) => {
                val top_of_control = e :: List(DRefr(x), Assign(Var(null), EmptyExp))
                val new_rs = Var(x) :: rs
                val top_of_backtrack = AssignLabel :: List(e)

                Some(top_of_control ::: cs, new_rs, renv, top_of_backtrack ::: bs)
            }


    case (AssignLabel :: bs, rs, renv, cs) => {
        val e = cs.head.to_Iexp
        val x = rs.head match {
            case Var(y) => Var(y)
            case _ => throw new Exception("Invalid variable")
        }
        val new_rs = rs.drop(1)
        val new_cs = Assign(x, e) :: cs.drop(3)
        Some(bs, new_rs, renv, new_cs)
    }

     case (RevAssignLabel :: bs, rs, renv, cs) => {
        val new_bs = bs.drop(2)
        val new_rs = rs.drop(1)

        val e = cs.head.to_Iexp
        val var_name = rs.head match {
            case Var(y) => y
            case _ => throw new Exception("Invalid variable")
        }

        val (number, rvalue) = renv(var_name)

        val n = bs.head.to_Iexp match {
            case Num(x) => x
            case _ => throw new Exception("Invalid number")
        }

        val new_renv = renv + (var_name -> ((number + n , rvalue)))

        val new_cs = RevAssign(Var(var_name), e) :: cs.drop(3)

        Some(new_bs, new_rs, new_renv, new_cs)

     }

     case (RevAssign(Var(null), EmptyExp) :: cs, rs, renv, bs) => {
        val var_name = rs.tail.tail.head match {
            case Var(x) => x
            case _ => throw new Exception("Invalid variable")
        }
        val exp = bs.drop(4).head.to_Iexp
        
        val new_rs = rs.drop(3)

        val new_bs = Assign(Var(var_name), exp) :: bs.drop(5)

        Some(cs, new_rs, renv, new_bs)

     }

    case (RevAssign(Var(x), e) :: cs, rs, renv, bs) => {
                val top_of_control = e :: List(DRefr(x), RevAssign(Var(null), EmptyExp))
                val new_rs = Var(x) :: rs

                val (number, rvalue) = renv(x)
                val n = number - rvalue.getN


                val new_renv = renv + (x -> (n, rvalue.getV))

                val top_of_backtrack = RevAssignLabel :: List(Num(n) , e)

                Some(top_of_control ::: cs, new_rs, new_renv, top_of_backtrack ::: bs)
            }

}

               


//call step_revexp with the initial rconfig until the control stack is empty
//print each step
//return the final rconfig

def rstep_all (c :RConfig) : RConfig = {
    println (rconfig_to_string(c))
    c match {
    case (cs, rs, renv, bs) => {
        cs match {
            case Nil => c
            case x :: xs => x.isInstanceOf[Cmd] match {
                case true => rstep_all(step_revcmd(c).get)
                case false => rstep_all(step_revexp(c).get)
            }
        }
       }
    }
}



// @main
// def main(filename: String): Unit = {
//   val tokens = tokenise(os.read(os.pwd / filename))
//   val tree = Prog.parse_single(tokens)
//   val rimp_tree = translate_prog(tree)
//  // val result = rev_prog(rev_tree)
//     print ("rimp tree ==> " + rimp_tree + "\n")
//     val config = init_config(rimp_tree)
//     val switched = switch(rstep_all(config))
//     print ("switched config ==> " + rconfig_to_string(switched) + "\n")

//     println ("running in reverse " + "\n")

//     rstep_all(switched)



// }


//test 

val tokens = tokenise(os.read(os.pwd / "test.simp"))
val tree = Prog.parse_single(tokens)
val rimp_tree = translate_prog(tree)
   print ("rimp tree ==> " + rimp_tree + "\n")
   val config = init_config(rimp_tree)
   println ("initial config ==> " + rconfig_to_string(config) + "\n")
   val switched = switch(rstep_all(config))
    print ("switched config ==> " + rconfig_to_string(switched) + "\n")

    println ("running in reverse " + "\n")

    rstep_all(switched)