(** FLP Impossibility Proof **)
(** Made after original paper http://cs-www.cs.yale.edu/homes/arvind/cs425/doc/fischer.pdf **) 
(** described more informally in the awesome blogpost http://the-paper-trail.org/blog/a-brief-tour-of-flp-impossibility/ **)
(** also constructive proofs: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.7907&rep=rep1&type=pdf **)
(** and http://www.cs.cornell.edu/courses/cs7412/2011sp/ConsensusRebecca.pdf **)


Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical.

Set Implicit Arguments.
Import ListNotations.

Definition Binary := bool.

Inductive Process: Set := 
| FinishedProcess: Binary -> Process
| proceed: nat -> Process. 


Definition finishedIn(b:Binary)(p:Process):bool := match p with
| FinishedProcess b => true
| _ => false
end.

Definition Configuration := list Process.

Axiom CfgSize: forall cfg:Configuration, length cfg >= 2.

Definition decidedValue(cfg:Configuration)(b:Binary):Prop := In (FinishedProcess b) cfg.

Definition decided(cfg:Configuration):Prop := decidedValue cfg true \/ decidedValue cfg false.


Axiom Consistency: forall cfg, ~(decidedValue cfg true /\ decidedValue cfg false).


(** A particular execution, defined by a possibly infinite sequence of events from 
a starting configuration C is called a schedule and the sequence of steps taken 
to realise the schedule is a run **)
Definition Schedule := list nat.


Parameter chooseFn : Configuration -> nat -> Process.

(** Parameter sameProcess: Process -> Process -> Prop. **)

Axiom chooseIn : forall cfg msg, In (chooseFn cfg msg) cfg.

Axiom stepForEveryProcess1: forall cfg p, In p cfg -> exists msg, chooseFn cfg msg = p.
Axiom stepForEveryProcess2: forall cfg p, In p cfg -> exists msg, chooseFn cfg msg <> p.

(** Configuration transition function **)
Parameter eventFn : Configuration -> nat -> Configuration.



(** There's no change in deciding value **)
Axiom Termination: forall cfg b msg, decidedValue cfg b -> decidedValue (eventFn cfg msg) b.


Fixpoint run (cfg:Configuration)(s:Schedule): Configuration :=
match s with
| nil => cfg
| cons msg t => eventFn (run cfg t) msg
end.  


Lemma Termination1: forall cfg b s, decidedValue cfg b -> decidedValue (run cfg s) b.
Proof.
intros.
pose proof Termination as T.
unfold run.
induction s.
trivial.
auto.
Qed.

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
  (exists s1, decidedValue(run cfg s1) false) /\ ~(exists s2, decidedValue (run cfg s2) true).

Definition univalent(cfg:Configuration):= univalent_true cfg \/ univalent_false cfg.

Definition bivalent(cfg:Configuration):= (~ decided cfg) /\
  (exists s1, decidedValue (run cfg s1) false) /\ (exists s2, decidedValue (run cfg s2) true).



(** "By the total correctness of P, and the fact that there are always admissible runs, V > 0" **)
Axiom Correctness: forall cfg, bivalent cfg \/ univalent cfg.



Lemma UnNotBiv: forall cfg, univalent cfg <-> ~ bivalent cfg.
Proof.
intros cfg.
unfold bivalent.
unfold univalent.
unfold univalent_true.
unfold univalent_false.
pose proof Correctness as C.
specialize (C cfg).
tauto.
Qed.



Lemma BivNotUn: forall cfg, bivalent cfg <-> ~ univalent cfg.
Proof.
intros.
unfold bivalent.
unfold univalent.
unfold univalent_true.
unfold univalent_false.
pose proof Correctness as C.
specialize (C cfg).
tauto.
Qed.



Lemma BivalentPaths: forall cfg, bivalent cfg -> (~ decided cfg) /\
  (exists s1, univalent_false(run cfg s1)) /\ 
  (exists s2, univalent_true(run cfg s2)).
Proof.
intros cfg.
pose proof Consistency as C.
pose proof Termination1 as T.
unfold bivalent. unfold univalent_false. unfold univalent_true.
intuition.
destruct H.
destruct H2.
exists x.
specialize (T (run cfg x) false).
intuition.
exists [].
trivial.
destruct H2.
specialize(T x1).
intuition.
generalize dependent H2. generalize dependent H3.
specialize (C (run (run cfg x) x1)).
tauto.
destruct H.
destruct H2.
exists x0.
specialize (T (run cfg x0) true).
intuition.
exists [].
trivial.
destruct H2.
specialize (C (run (run cfg x0) x1)).
auto.
Qed.

Lemma UnFNotBiv: forall cfg, univalent_false cfg -> ~ bivalent cfg.
Proof.
intros cfg.
pose proof Correctness as C.
specialize (C cfg).
pose proof BivalentPaths as B.
specialize (B cfg).
unfold univalent in C.
unfold univalent_false.
unfold bivalent.
unfold univalent_false in C.
unfold univalent_true in C.
unfold bivalent in C.
unfold univalent_false in B.
unfold univalent_true in B.
unfold bivalent in B.
tauto.
Qed.

Lemma UnTNotBiv: forall cfg, univalent_true cfg -> ~ bivalent cfg.
Proof.
intros cfg.
pose proof Correctness as C.
specialize (C cfg).
pose proof BivalentPaths as B.
specialize (B cfg).
unfold univalent in C.
unfold univalent_true.
unfold bivalent.
unfold univalent_false in C.
unfold univalent_true in C.
unfold bivalent in C.
unfold univalent_false in B.
unfold univalent_true in B.
unfold bivalent in B.
tauto.
Qed.



Lemma Correctness2: forall cfg, univalent_true cfg -> univalent_false cfg -> False.
Proof.
intros.
unfold univalent_true in H.
destruct H.
unfold univalent_false in H0.
destruct H.
destruct H0.
destruct H0.
destruct H1.
exists x0.
trivial.
Qed.

Lemma Correctness3: forall cfg, univalent_false cfg -> univalent_true cfg -> False.
Proof.
intros.
unfold univalent_false in H.
destruct H.
unfold univalent_true in H0.
destruct H.
destruct H0.
destruct H0.
destruct H1.
exists x0.
trivial.
Qed.

(** todo: prove ? **)
Axiom Correctness4: forall cfg s, univalent_false cfg -> ~ univalent_true (run cfg s).
Axiom Correctness5: forall cfg s, univalent_true cfg -> ~ univalent_false (run cfg s).

Axiom Correctness6: forall cfg s, univalent_true cfg -> univalent_true (run cfg s).
Axiom Correctness7: forall cfg s, univalent_false cfg -> univalent_false (run cfg s).

Axiom Async1: forall cfg msg1 msg2, (chooseFn cfg msg1) <>  (chooseFn cfg msg2) -> 
  run cfg ([msg1;msg2]) = run cfg ([msg2;msg1]).

(** todo: proove? **)
Axiom RunCommutativity: forall cfg msg s, run (run cfg [msg]) s = run cfg (msg :: s).


Axiom Decidability: forall cfg n1 n2, chooseFn cfg n1 = chooseFn cfg n2 \/ chooseFn cfg n1 <> chooseFn cfg n2.


Lemma OneStepLemmaP1: forall cfg msg1 msg2, 
  chooseFn cfg msg1 <> chooseFn cfg msg2 /\ 
    univalent_false (run cfg [msg1]) /\
    univalent_true (run cfg [msg2])-> False.
Proof.
intuition.
pose proof RunCommutativity as RC.
specialize(RC cfg).
pose proof Async1 as A1.
specialize(A1 cfg msg1 msg2).
pose proof Correctness6 as C6.
pose proof Correctness7 as C7.
specialize (C6 (run cfg [msg2]) [msg1]).
rewrite RC in C6.
specialize (C7 (run cfg [msg1]) [msg2]).
rewrite RC in C7.
intuition.
rewrite H1 in H3.
pose proof Correctness3 as C3.
specialize(C3 (run cfg [msg2; msg1])).
tauto.
Qed.

Lemma OneStepLemmaP2: forall cfg msg1 msg2,  
    univalent_false (run cfg [msg1]) /\
    univalent_true (run cfg [msg2]) -> chooseFn cfg msg1 = chooseFn cfg msg2.
Proof.
intros cfg msg1 msg2.
pose proof OneStepLemmaP1 as P1.
specialize(P1 cfg msg1 msg2).
tauto.
Qed.

(** todo: rename Message -> Step, msg -> step **)
Axiom AnotherProcessStep: forall cfg msg, exists msg0, chooseFn cfg msg <> chooseFn cfg msg0. 
Parameter randomApplicableStep: Configuration -> nat.


Axiom OneStepLemma: forall cfg, bivalent cfg -> exists msg, bivalent (run cfg [msg]).


Theorem FLP_Lemma3: forall cfg, bivalent cfg -> forall m, exists s, length s > m -> bivalent (run cfg s).
Proof.
intros. 
pose proof OneStepLemma as O. 
specialize (O cfg).
intuition.
destruct H0.
exists [x]. 
intros. 
apply H0.
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