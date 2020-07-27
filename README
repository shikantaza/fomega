fomega is an interpreter for the F-omega language, written in OCaml.

Refer to the INSTALL file for instructions for building fomega.

In addition to interpretation of F-omega expressions, fomega provides convenience commands to define terms/tyes and to create term/type judgements. Type 'help' at the interpretr prompt for the syntax of these commands.

A sample fomega session (edited for clarity):

(base) ~/rajesh/code/ocaml$ ./fomega
Welcome to the fomega interpreter. Type 'help' to display the available commands, 'quit' to exit the interpreter.
fomega> defvar pair /\X:*./\Y:*.\x:X.\y:Y./\R:*.\p:X->Y->R.(p x y)

fomega> defvar first /\X:*./\Y:*.\p:\/R:*.(X->Y->R)->R.(p X \x:X.\y:Y.x)

fomega> A : *           

fomega> B : *

fomega> defvar pab pair A B

fomega> defvar fab first A B

fomega> a : A

fomega> b : B

fomega> fab (pab a b)
a : A

fomega> quit
Bye
(base) ~/rajesh/code/ocaml$