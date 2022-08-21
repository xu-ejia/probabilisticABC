# probabilisticABC  
The probabilistic ABC system is an extension of the ABC system.  
The implementation is mainly written in Python in "pabcMain.ipynb".   
".pl" Prolog programmes are from the original ABC system.  

# Run  
Jupyter Notebook 6.4.8, Python 3.9.10 and SWI-Prolog version 8.4.1.  
Step 1: Download all files.  
Step 2: Replace the files in the " data " folder with your input files. Otherwise, the example will be used as the input. The example is the Swan theory.  
Step 3: Run script abctMain.ipynb.  

# Input Files  
The sample of input files is given in the folder "data".  
proba_input.owl: assertations in the input theory with probabilities.  
proba_rule.owl: rules in the input theory with probabilities.  
true.txt: the true set in the preferred structure.  
false.txt: the false set in the preferred structure.  
meta.txt: recording features about repairing.  
