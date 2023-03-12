
// an abstract syntax machine for the SIMP language  


import $file.parser , parser._
import $file.lexer, lexer._ 
import $file.trees , trees._

type Env = Map[String, Int]

//P ::= C | E
// C ::= skip | l := E | C; C | if E then C else C | while E do C
// E ::= !l | n | E op E | ¬E
// op ::= + | − | ∗ | / | > | < | = | ∧

def eval_exp (e: Prog, env: Env): Int = e match {
  case Num(n) => n
  case Aop("+", e1, e2) => eval_exp(e1, env) + eval_exp(e2, env)
  case Aop("-", e1, e2) => eval_exp(e1, env) - eval_exp(e2, env)
  case Aop("*", e1, e2) => eval_exp(e1, env) * eval_exp(e2, env)
  case Aop("/", e1, e2) => eval_exp(e1, env) / eval_exp(e2, env)
  case Bop(">", e1, e2) => if (eval_exp(e1, env) > eval_exp(e2, env)) 1 else 0
  case Bop("<", e1, e2) => if (eval_exp(e1, env) < eval_exp(e2, env)) 1 else 0
  case Bop("==", e1, e2) => if (eval_exp(e1, env) == eval_exp(e2, env)) 1 else 0
  case Bop("&&", e1, e2) => if (eval_exp(e1, env) == 1 && eval_exp(e2, env) == 1) 1 else 0
  case Not(e) => if (eval_exp(e, env) == 1) 0 else 1
  case DRefr(s) => env(s)
}


def eval_cmd (c: Prog, env: Env): Env = c match {
  case Skip => env
  case Assign(Var(s), e) => env + (s -> eval_exp(e, env))
  case If(e, bl1, bl2) => if (eval_exp(e, env) == 1) eval_block(bl1, env) else eval_block(bl2, env)
  case While(e, bl) => if (eval_exp(e, env) == 1) eval_cmd(While(e, bl), eval_block(bl, env)) else env
  case _ => env
}

def eval_block (bl: List[Prog], env: Env): Env = bl match {
  case Nil => env
  case c::cs => eval_block(cs, eval_cmd(c, env))
}





//A configuration is a triple of stacks: (Control, Results, Memory)
//Control is a stack of Progs
//Results is a stack of Progs
//Memory is a map from variables to integers

type Config = (List[Prog], List[Prog], Env)

//to string function for Config
def config_to_string (c : Config) : String = c match {
  case (cs, rs, env) => "Control: "  + cs +  "\n" + " Results: " + rs + "\n" + " Memory: " + env + "\n"
  case _ => "Error"
}


//Initial Configuration is (P, [], [])
def init_config (tree : List [Prog]) : Config = (tree, List(), Map())

//final configuration contains the env in the memory

//The transition relation is a function from configurations to configurations
//The transition relation is a partial function, so we use Option[Config]

def step_command (c : Config) : Option[Config] = c match {
  case (Skip::cs, rs, env) => Some(cs, rs, env)

    case (AssignLabel::cs, Num(n)::Var(s):: rs, env) => {

    val new_rs = rs
    val new_env = env + (s -> n)
    Some(cs, new_rs, new_env)

  }
  
  case (Assign(Var(s), e)::cs, rs, env) => {
                      val top_of_stack = e :: List(AssignLabel)
                      val new_rs = (Var(s)) :: rs
                      Some(top_of_stack ::: cs, new_rs , env)
                }


  case (IfLabel::cs , Num (n) :: ProgBl(bl1) :: ProgBl(bl2) :: rs, env) => {
    //num is the result of the expression
    if (n == 0) Some (bl2 ::: cs, rs, env)
    else Some (bl1 ::: cs, rs, env)
    
  }              

  case (If(e, bl1, bl2)::cs, rs, env) => {
    val top_of_stack = e :: List(IfLabel)
    val new_rs = ProgBl(bl1) :: List (ProgBl(bl2)) ::: rs

    Some (top_of_stack ::: cs, new_rs, env)
  }


    case (While (EmptyExp, Nil)::cs , Num (n) :: rs, env) => {
    val cond = rs.head
    val bl = rs.tail match {
      case ProgBl(bl) :: rs => bl
      case _ => Nil
    }

    val new_rs = rs.tail.tail
    

    if (n == 0) Some (cs, new_rs, env) //remove the while and the block because the condition is false
    else {

    val cond_exp = cond match { 
      case Bop(op, e1, e2) => Bop(op, e1, e2)
      case Not(e) => Not(e)
    }

    val top_of_stack = bl ::: List(While(cond_exp, bl))
     Some (top_of_stack ::: cs, new_rs, env)
    }
    
  }

  case (While(e, bl)::cs, rs, env) => { 
    val top_of_stack = e :: List(While(EmptyExp, Nil))
    val new_rs = e :: List(ProgBl(bl)) ::: rs
    Some (top_of_stack ::: cs, new_rs, env)
  }



  case (Nil, rs, env) => None
  case _ => None
}

def step_exp (c : Config) : Option[Config] = c match {

  case (Num(n)::cs, rs, env) => Some(cs,Num(n) :: rs, env)

    case (Not(EmptyExp)::cs, e::rs, env) => {
    val result = eval_exp(e, env)
    val not_result = if (result == 0) 1 else 0
    val new_rs = Num(not_result) :: rs
    Some(cs, new_rs, env)
  }

  case (Not (e)::cs, rs, env) => {
    val top_of_stack = e :: List(Not(EmptyExp))
    Some(top_of_stack ::: cs, rs, env)
  }


    case (Aop(op, EmptyExp, EmptyExp)::cs, e2::e1::rs, env) => {
    val exp1 = eval_exp(e1, env)
    val exp2 = eval_exp(e2, env)
    val result = eval_exp(Aop (op, Num(exp1), Num(exp2)), env)
    val new_rs = Num(result) :: rs
    Some(cs, new_rs, env)
  }

  case (Aop(op, e1, e2)::cs, rs, env) => {
    val expressions = e1 :: List(e2)
    val top_of_stack = expressions ::: List(Aop(op, EmptyExp, EmptyExp))
    Some(top_of_stack ::: cs, rs, env)
  }
 
  case (Bop(op, EmptyExp, EmptyExp)::cs, e2::e1::rs, env) => {
    val exp1 = eval_exp(e1, env)
    val exp2 = eval_exp(e2, env)
    val result = eval_exp(Bop(op, Num(exp1), Num(exp2)), env)
    val new_rs = Num(result) :: rs
    Some(cs, new_rs, env)
  }

  case (Bop(op, e1, e2)::cs, rs, env) => {
    val expressions = e1 :: List(e2)
    val top_of_stack = expressions ::: List(Bop(op, EmptyExp, EmptyExp))
    Some(top_of_stack ::: cs, rs, env)
  }


  case (DRefr(s)::cs, rs, env) => {
    val result = env(s)
    val new_rs = Num(result) :: rs
    Some(cs, new_rs, env)
  }

  case _ => None
}


//function step
//takes a configuration and returns a new configuration
//if the top of the stack is a command, then step the command
//if the top of the stack is an expression, then step the expression

def step (c : Config) : Option[Config] = c match {
  case (c::cs, rs, env) => c.isInstanceOf[Cmd] match {
    case true => step_command(c::cs, rs, env)
    case false => step_exp(c::cs, rs, env)
  }

  case _ => None
}


//call step repeatedly until a final configuration is reached
//print the configuration after each step
def interpret (c : Config) : Config = {
  println(config_to_string(c))
  step(c) match {
    case Some(c1) => interpret(c1)
    case None => c
    case _ => throw new Exception("Error")
  }
}

@main
def main(filename: String): Unit = {
  val tokens = tokenise(os.read(os.pwd / filename))
  val tree = Prog.parse_single(tokens)
  val env = Map[String, Int]()
  val interpretation = interpret(init_config(tree))
}


//test 

// val tokens = tokenise(os.read(os.pwd / "test.simp"))
// val tree = Prog.parse_single(tokens)
// val env = Map[String, Int]()
// //call step once on the tree
// val testresult = step_command(init_config(tree))

// //get the results stack
// val testresultstack = testresult match {
//   case Some(c) => c._2
//   case None => List()
// }

// //get the top of the results stack

// val testresulttop = testresultstack match {
//   case Nil => None
//   case x::xs => Some(x)
// }

// println(testresulttop)

// //convert the result to a string and print it
// val testresultstring = testresult match {
//   case Some(c) => config_to_string(c)
//   case None => "None"
// }

// println(testresultstring)

