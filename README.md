#DFTA
DFTA implements an optimised algorithm for Determinisation and Completion of Finite Tree Automata.

## Finite Tree Automata (FTA) determinisation
### Implementation
DFTA is written in Java and is developed using Netbeans IDE (8.0.1) and uses JRE 8.

### Usage
java -jar DFTA.jar 

### Input
The input is a file containing an FTA

An FTA is specified as:

*Final States \< states separated by space \>.*
*Transitions.*

*functorName(\< states separated by comma \>) -> \<state\>.*


For example: 

*Final States q47 q5.*

*Transitions.*

*yblack(q1,q19) -> q22.*
*yblack(q9,q9) -> q18.*

##Reference
An Optimised Algorithm for Determinisation and Completion of Finite Tree Automata.
by John P. Gallagher, Mai Ajspur and Bishoksan Kafle.
http://arxiv.org/abs/1511.03595

##Contact  
John Gallagher (jpg@ruc.dk)
