(** FLP Impossibility Proof **)
(** Made after original paper http://cs-www.cs.yale.edu/homes/arvind/cs425/doc/fischer.pdf **) 
(** described more informally in the awesome blogpost http://the-paper-trail.org/blog/a-brief-tour-of-flp-impossibility/ **)
(** also constructive proofs: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.7907&rep=rep1&type=pdf **)
(** and http://www.cs.cornell.edu/courses/cs7412/2011sp/ConsensusRebecca.pdf **)


Require Import Arith.
Require Import List.

Set Implicit Arguments.
Import ListNotations.


Definition Binary := bool.


Inductive Process: Set := 
| FinishedProcess: Binary -> Process
| FailedProcess
| proceed: nat -> Process. 

Definition failedProcess(p:Process):bool := match p with
| FailedProcess => true
| _ => false
end.

Definition finishedIn(b:Binary)(p:Process):bool := match p with
| FinishedProcess b => true
| _ => false
end.


Definition Configuration := list Process.

Definition decidedValue(cfg:Configuration)(b:Binary):Prop := 
In (FinishedProcess b) cfg.

Definition decided(cfg:Configuration):Prop := decidedValue cfg true \/ decidedValue cfg false.


Axiom Consistency: forall cfg, ~(decidedValue cfg true /\ decidedValue cfg false).


(** A particular execution, defined by a possibly infinite sequence of events from 
a starting configuration C is called a schedule and the sequence of steps taken 
to realise the schedule is a run **)
Definition Schedule := list nat.


Parameter chooseFn : Configuration -> nat -> Process.

(** Configuration transition function **)
Parameter eventFn : Configuration -> nat -> Configuration.



(** There's no change in deciding value **)
Axiom Termination: forall cfg b msg, decidedValue cfg b -> decidedValue (eventFn cfg msg) b.


Lemma Termination_1: forall cfg msg, decided cfg -> decided (eventFn cfg msg).
Proof.
intros.
pose proof Termination as T.
unfold decided.
unfold decided in H.
intuition.
Qed.


Fixpoint run (cfg:Configuration)(s:Schedule): Configuration :=
match s with
| nil => cfg
| cons msg t => eventFn (run cfg t) msg
end.  



Lemma Termination_2: forall cfg b s, decidedValue cfg b -> decidedValue (run cfg s) b.
Proof.
intros.
pose proof Termination as T.
unfold run.
induction s.
trivial.
auto.
Qed.


(** An admissible run is one where at most one process is faulty 
(and every message is eventually delivered) **)
Definition admissible(cfg:Configuration)(s:Schedule): Prop := 
    length (filter failedProcess (run cfg s)) <= 1.


Axiom OneFaultMax: forall (cfg:Configuration)(s:Schedule), admissible cfg s.


(** We say that a run is deciding provided that some process eventually decides according 
to the properties of consensus **)
Definition deciding(cfg:Configuration)(s:Schedule): Prop := decided (run cfg s).

Hypothesis InitialConfiguration: Configuration.


Axiom InitialNoConsensus: ~decided InitialConfiguration.
Axiom TrueReacheable: exists s1, decidedValue (run InitialConfiguration s1) true.
Axiom FalseReacheable: exists s2, decidedValue (run InitialConfiguration s2) false.



Definition univalent_true(cfg:Configuration):= 
(exists s1, decidedValue(run cfg s1) true) /\ ~(exists s2, decidedValue (run cfg s2) false).

Definition univalent_false(cfg:Configuration):= 
(exists s1, decidedValue(run cfg s1) false) -> ~(exists s2, decidedValue (run cfg s2) true).

Definition univalent(cfg:Configuration):= univalent_true cfg \/ univalent_false cfg.

Definition bivalent(cfg:Configuration):= (~ decided cfg) /\
  (exists s1, decidedValue(run cfg s1) false) /\ 
  (exists s2, decidedValue (run cfg s2) true).


(** "By the total correctness of P, and the fact that there are always 
admissible runs, V > 0" **)
Axiom Correctness2: forall cfg, bivalent cfg \/ univalent cfg.



Lemma BivNotUn: forall cfg, bivalent cfg -> ~ univalent cfg.
Proof.
intros.
unfold bivalent in H.
unfold univalent.
unfold univalent_true.
unfold univalent_false.
tauto.
Qed.


(** Lemma 2 from original paper **)
Theorem FLP_Lemma2: bivalent(InitialConfiguration).
Proof.
pose proof InitialNoConsensus as I.
pose proof TrueReacheable as T.
pose proof FalseReacheable as F.
unfold bivalent.
intuition.
Qed.


(** todo: prove it **)
Axiom OneStepLemma: forall cfg, bivalent cfg -> exists msg, bivalent (run cfg [msg]).


(** todo: should be proven using OneStepLemma **)
Axiom FLP_Lemma3: forall cfg, bivalent cfg -> forall m, exists s, length s > m -> bivalent (run cfg s).











(** THEOREM 1. No consensus protocol is totally correct in spite of one fault. **)

Theorem FLP_main: forall m, exists s, length s > m -> ~ deciding InitialConfiguration s.
Proof.
intros m.
pose proof FLP_Lemma2 as FL2.
pose proof FLP_Lemma3 as FL3.
specialize (FL3 InitialConfiguration).
intuition.
specialize (H m).
destruct H.
apply ex_intro with (x:=x).
unfold deciding.
generalize dependent H.
unfold bivalent.
unfold decided.
tauto.
Qed.













