# Formalization of the FLP Impossibility Theorem with Coq interactive theorem prover


Model is following  [original paper](http://cs-www.cs.yale.edu/homes/arvind/cs425/doc/fischer.pdf) .

Other constructive proofs: [http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.7907&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.7907&rep=rep1&type=pdf),
 [http://www.cs.cornell.edu/courses/cs7412/2011sp/ConsensusRebecca.pdf](http://www.cs.cornell.edu/courses/cs7412/2011sp/ConsensusRebecca.pdf),
but this is the first with source code published! Also proof of lemma3 is different from all the previous proofs. 
 
 Paper is coming! Hope to publish it in a peer-reviewed journal.

##Model & it's axiomatics

Messages are skipped at all(so they are needed for better understanding only, while for proof's sake we can have a talk only about system's state transitions).

Process is the inductive set:

`Inductive Process := | FinishedProcess: Binary -> Process | proceed: nat -> Process.`

then configuration is just a list of processes:

`Definition Configuration := list Process.`

Events are enumerated with naturals numbers, with two (abstract) functions for transition from one configuration to another, and to choose process by event:

`Parameter eventFn : Configuration -> nat -> Configuration. Parameter chooseFn : Configuration -> nat -> Process.`

We can compare processes by using chooseFn:

`Axiom Decidability: forall cfg n1 n2, chooseFn cfg n1 = chooseFn cfg n2 \/ chooseFn cfg n1 <> chooseFn cfg n2.`

and as eventFn is abstract, it seems 'run' function using eventFn needs for following axioms to be commutative:

`Axiom RunCommutativity: forall cfg s1 s2, run (run cfg s1) s2 = run cfg (s1 ++ s2).`

`Axiom RunCommutativity2: forall cfg step s, run (run cfg [step]) s = run cfg (step :: s).`

Other axioms are following original paper pretty directly:

* Partially correct protocol could decides on a single value only: 

`Axiom Consistency: forall cfg, ~(decidedValue cfg true /\ decidedValue cfg false).`
  
    

* There's no change in value after consideration(termination property of a consensus algorithm):

`Axiom Termination: forall cfg b step, decidedValue cfg b -> decidedValue (eventFn cfg step) b.`
    
  
    
* "By the total correctness of P, and the fact that there are always admissible runs, V > 0"

`Axiom Correctness: forall cfg, bivalent cfg \/ univalent cfg.`
  
     
  
* As messaging is asynchronous, we can swap two events involving different processes:

`Axiom Async1: forall cfg step1 step2, (chooseFn cfg step1) <> (chooseFn cfg step2) -> run cfg ([step1;step2]) = run cfg ([step2;step1]).`

Please note, there's no any limitation on synchronicity inside a process.
  
  
* Initial configuration properties, i.e. both values are reachable from it

`Axiom InitialNoConsensus: ~decided InitialConfiguration. Axiom TrueReacheable: exists s1, decidedValue (run InitialConfiguration s1) true. Axiom FalseReacheable: exists s2, decidedValue (run InitialConfiguration s2) false.`
  
  
      
While original proof considering set of applicable messages, my proof uses only randomStep function returning some possible event to happen in current configuration, and AnotherProcessStepExists axiom stating any process can make a step in any round(in my formulation, if some process is involved in any step, there's other step for other process).

`Axiom AnotherProcessStepExists: forall cfg step, exists step0, chooseFn cfg step <> chooseFn cfg step0.`

`Parameter randomStep: Configuration -> nat.`
  
That's all! There are two other axioms which could be (and will be if so) proven probably, but anyway there's no doubt in them:

`Axiom Correctness6: forall cfg s, univalent_true cfg -> univalent_true (run cfg s).`

`Axiom Correctness7: forall cfg s, univalent_false cfg -> univalent_false (run cfg s).`
 
 
 
 **Thank you for reading this! And I would be happy to get feedback / reviews on it!**
