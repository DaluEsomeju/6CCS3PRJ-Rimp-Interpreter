# Abstract Machine for RIMP

The goal of this project is to implement an abstract machine for a small programming language called RIMP. This is accomplished using several scripts (modules):

- lexer.sc: Lexer for SIMP
- parser.sc: Parser for SIMP
- trees.sc: Contains abstract syntax tree classes for SIMP/RIMP
- interpret.sc: Abstract machine for SIMP programs
- translate.sc: Translate SIMP to RIMP
- invert.sc: Program inverter for RIMP programs
- rimp-interpret.sc: Abstract machine for RIMP programs

The project also contains ".simp" files which are example programs that can be executed by the Scala scripts (trees.sc only contains classes and does not contain a main method to be executed).
test.simp is intended to be a file in which users can write their own programs to be testesd.


## Prerequisites

- A Mac or Linux-based system
- Scala 2.x (any version of Scala 2, but not Scala 3)
- Ammonite REPL 3.0.0-M0 for Scala 2.13


## Installation

1. Open the zip file and extract its contents.
2. Navigate to the extracted folder, making sure all files are in the same directory.

3. Install Scala: You'll need any version of Scala 2 (not Scala 3) to run this project. You can download it from the official Scala website:
   [Scala Download Page](https://www.scala-lang.org/download/)

4. Install Ammonite REPL: This project requires a Mac or Linux-based system. Install the standalone Ammonite 3.0.0-M0 executable for Scala 2.13 using the following command:
 sudo sh -c '(echo "#!/usr/bin/env sh" && curl -L https://github.com/com-lihaoyi/Ammonite/releases/download/3.0.0-M0/2.13-3.0.0-M0) > /usr/local/bin/amm && chmod +x /usr/local/bin/amm' && amm

## Usage

To run the code, use the Ammonite REPL with the appropriate script and provide a `.simp` file as an argument. Make sure the `.simp` file is in the same directory as the Scala scripts.

For example, to perform lexical analysis on a file called `example.simp`, use the following command:

amm lexer.sc example.simp


This command will run the `lexer.sc` script with the `example.simp` file, performing lexical analysis on the contents of the file.

Similarly, you can use other scripts like `parser.sc`, `interpret.sc`, `translate.sc`, `invert.sc`, and `rimp-interpret.sc` with the appropriate `.simp` file as needed.




