# *Compilation*
`make`  
If you want to delete the files created by `make`, you can use:  
`make clean`  
# *Execution example*
In order to execute our Mini SMT Solver a file `file.cnfuf`, you can use:  
`./msmts test.cnfuf`  
# *Mini SMT Solver*
## SAT Solver
Our SAT Solver uses the CDCL + Resolution + Learning + Restart techniques. We have also implemented the VSIDS heuristic as presented in the 3rd part of the paper *Chaff: Engineering an Efficient SAT Solver*, Moskewicz et al., 2001. Sadly, we didn't have enough time to implement the two watched literals method.  
However, we were impressed by the performance of our initial SAT Solver on 3-SAT formulas:

| Number of clauses in 3-SAT formula | Time when SAT | Time when UNSAT |
|:---:|:---:|:---:|
| 50 | 1 - 10 sec | < 0.5 sec |
| 100 | 50 - 200 sec | < 5 sec |

For this benchmark, we have used a online random SAT generator (available at: [Tough SAT Project](https://toughsat.appspot.com/)).
## Equality Theory
For the equality theory, we've used the structure:  
```ocaml
type theory = {
	eq: PUF.t; 
	(* Persistent Union-Find for the equality hypotheses. *)
	neq: ISet.t PArr.t 
	(* Persistent Array that associates to each representative of a class in the Union-Find structure, the representatives of classes with which it cannot merge because of difference hypotheses. *)
}
```  
Each time two clases are merged in the Union-Find we have to update the representatives of all concerned parties in the Array. Thus we have a worst case complexity for merge (addition of an equality hypothesis) of __O(log* N + NDiff * (log* N + log N))__ where we note __log*__ the iterated logarithm function and __NDiff__ the number of difference hypotheses. When we add a difference hypothesis, the complexity is __O(log* N + log N)__.  
## Final Program
In order to combine the SAT Solver and the Equality Theory, we have inspired ourselves from CDCL(T). We have added a T-PROPAGATE technique which tries to deduce the value of a literal from the current state of the theory. We don't need a T-CONFLICT technique because all of our functions take care not to add to the model literals that would contradict the equality / difference contraints.  
# Verification
We've implemented a random `.cnfuf` generator in C and we've tested the performance of our Mini SMT Solver on multiple test-cases. Initially, we also had a verifier which tested whether our model is a solution for the given SAT formula, but we've eventually abandoned it.
