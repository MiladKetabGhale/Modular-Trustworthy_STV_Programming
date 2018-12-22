Please note that the contributors are improving this framework further. If you wished to test the software, git clone any commit made before Dec 15th 2018.

This repository hosts a modular framework for STV Calculi.

To obtain executable Haskell program that correctly computes election results for some input ballots, you need to do the following instructions;

1. Clone this repository into a local repository in your system by following the instructions as below :

1.1. click on the green botton "clone or download" located in this repository on the right side of the webpage. This way, you copy the link of this repository.

1.2. open a terminal in your linux shell. 

1.3. git clone (paste the link copied in the above step), in the terminal and press Return.

1.3. Go into the repository, which is now existing in your system under the directory name "Modular-STVCalculi".

1.4. Once you are in the directory specified in the 1.3, do the following commands;

1.4.1 To obtain Coq executable code, run the command "make Makefile.coq". Then run the command "make". After this, run the command "make move". 

1.4.2 To clean the files made in the above steps, first run the command "make clean". Then run the command "make clear".
