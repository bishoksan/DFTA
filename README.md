#DFTA
DFTA implements an optimised algorithm for Determinisation and Completion of Finite Tree Automata.

## Finite Tree Automata (FTA) determinisation

Usage:
java -jar DFTA.jar [-help][-h] 

java -jar DFTA.jar <ftafile> [-text][-dc][-show][-any][-datalog][-o <outfile>]

-help, -h -- print this message and ignore any other arguments

-text     -- use the textbook algorithm (default is optimised algorithm)

-any      -- compute complete DFTA (default is no completion)

-dc       -- compute don't cares (default is no don't cares). Option ignored if '-any' not present

-show     -- display output (default is no display)

-o <file> -- send output to file

-datalog  -- write output in Datalog format

##Reference
An Optimised Algorithm for Determinisation and Completion of Finite Tree Automata.
by John P. Gallagher, Mai Ajspur and Bishoksan Kafle.
http://arxiv.org/abs/1511.03595

##Contact  
John Gallagher (jpg@ruc.dk)
