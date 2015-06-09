(** FLP Impossibility Proof **)
(** Made after original paper http://cs-www.cs.yale.edu/homes/arvind/cs425/doc/fischer.pdf **) 
(** described more informally in the awesome blogpost http://the-paper-trail.org/blog/a-brief-tour-of-flp-impossibility/ **)
(** Some constructive proofs existed before, e. g. **)
(** http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.7907&rep=rep1&type=pdf **)
(** and http://www.cs.cornell.edu/courses/cs7412/2011sp/ConsensusRebecca.pdf **)

(** Unlike previous constructive proofs, this one has the same model as the original paper **)
(** But instead of Lemma3, it has own constructive small-step proof of bivalent run existence **)

Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical.

Set Implicit Arguments.
Import ListNotations.

Definition Binary := bool.

Inductive Process := 
| FinishedProcess: Binary -> Process 
| proceed: nat -> Process. 


Definition finishedIn(b:Binary)(p:Process):bool := match p with
| FinishedProcess b => true
| _ => false
end.

Definition Configuration := list Process.

Definition decidedValue(cfg:Configuration)(b:Binary):Prop := In (FinishedProcess b) cfg.

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


Fixpoint run (cfg:Configuration)(s:Schedule): Configuration :=
match s with
| nil => cfg
| cons step t => eventFn (run cfg t) step
end.

(** todo: proove? **)
Axiom RunCommutativity: forall cfg s1 s2, run (run cfg s1) s2 = run cfg (s1 ++ s2).
Axiom RunCommutativity2: forall cfg step s, run (run cfg [step]) s = run cfg (step :: s).


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


Lemma BivalentPaths: forall cfg, bivalent cfg ->
  (exists s1, univalent_false(run cfg (s1))) /\ 
  (exists s2, univalent_true(run cfg (s2))).
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



Lemma BivalentPaths2: forall cfg, bivalent cfg ->
  (exists st1 s1, univalent_false(run cfg (st1::s1))) /\ 
  (exists st2 s2, univalent_true(run cfg (st2::s2))).
Proof.
intros cfg.
pose proof BivalentPaths as BP.
specialize(BP cfg).
intuition.
destruct H1.
destruct x.
firstorder.
firstorder.
destruct H2.
destruct x.
firstorder.
firstorder.
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

Lemma Correctness4: forall cfg s, univalent_false cfg -> ~ univalent_true (run cfg s).
Proof.
intros cfg s.
unfold univalent_false.
unfold univalent_true.
intuition.
destruct H.
pose proof RunCommutativity as RC.
specialize (RC cfg s x).
rewrite RC in H.
generalize dependent H.
firstorder.
Qed.


Lemma Correctness5: forall cfg s, univalent_true cfg -> ~ univalent_false (run cfg s).
Proof.
intros cfg s.
unfold univalent_false.
unfold univalent_true.
intuition.
destruct H.
pose proof RunCommutativity as RC.
specialize (RC cfg s x).
rewrite RC in H.
generalize dependent H.
firstorder.
Qed.

Axiom Correctness6: forall cfg s, univalent_true cfg -> univalent_true (run cfg s).
Axiom Correctness7: forall cfg s, univalent_false cfg -> univalent_false (run cfg s).


Lemma Correctness8: forall cfg st s, univalent_false (run cfg (st :: s)) -> 
  bivalent (run cfg [st]) \/ univalent_false (run cfg [st]).
Proof.
intros.
pose proof Correctness as C.
specialize(C (run cfg [st])).
unfold univalent in C.
destruct C.
tauto.
pose proof Correctness5 as C5.
specialize(C5 (run cfg [st]) s).
intuition.
pose proof RunCommutativity2 as RC2.
specialize(RC2 cfg st s).
rewrite RC2 in H0.
tauto.
Qed.


Lemma Correctness9: forall cfg st s, univalent_true (run cfg (st :: s)) -> bivalent (run cfg [st]) \/ univalent_true (run cfg [st]).
Proof.
intros.
pose proof Correctness as C.
specialize(C (run cfg [st])).
unfold univalent in C.
destruct C.
tauto.
pose proof Correctness4 as C4.
specialize(C4 (run cfg [st]) s).
intuition.
pose proof RunCommutativity2 as RC2.
specialize(RC2 cfg st s).
rewrite RC2 in H0.
tauto.
Qed.



Axiom Async1: forall cfg step1 step2, (chooseFn cfg step1) <>  (chooseFn cfg step2) -> 
  run cfg ([step1;step2]) = run cfg ([step2;step1]).



Axiom Decidability: forall cfg n1 n2, chooseFn cfg n1 = chooseFn cfg n2 \/ chooseFn cfg n1 <> chooseFn cfg n2.


Lemma OneStepLemmaP1: forall cfg step1 step2, 
  chooseFn cfg step1 <> chooseFn cfg step2 /\ 
    univalent_false (run cfg [step1]) /\
    univalent_true (run cfg [step2])-> False.
Proof.
intuition.
pose proof RunCommutativity2 as RC.
specialize(RC cfg).
pose proof Async1 as A1.
specialize(A1 cfg step1 step2).
pose proof Correctness6 as C6.
pose proof Correctness7 as C7.
specialize (C6 (run cfg [step2]) [step1]).
rewrite RC in C6.
specialize (C7 (run cfg [step1]) [step2]).
rewrite RC in C7.
intuition.
rewrite H1 in H3.
pose proof Correctness3 as C3.
specialize(C3 (run cfg [step2; step1])).
tauto.
Qed.

Lemma OneStepLemmaP2: forall cfg step1 step2,  
    univalent_false (run cfg [step1]) /\
    univalent_true (run cfg [step2]) -> chooseFn cfg step1 = chooseFn cfg step2.
Proof.
intros cfg step1 step2.
pose proof OneStepLemmaP1 as P1.
specialize(P1 cfg step1 step2).
tauto.
Qed.


Axiom AnotherProcessStepExists: forall cfg step, exists step0, chooseFn cfg step <> chooseFn cfg step0. 
Parameter randomStep: Configuration -> nat.


Lemma BivNotUnTAndUnF: forall cfg, bivalent cfg <-> ~ univalent_true cfg /\ ~ univalent_false cfg.
Proof.
intros.
intuition.
(** CASE: univalent_true cfg **)
pose proof UnTNotBiv as UT.
specialize(UT cfg).
tauto.
(** CASE: univalent_false cfg **)
pose proof UnFNotBiv as UF.
specialize(UF cfg).
tauto.
(** CASE: opposite direction **)
apply BivNotUn.
unfold univalent.
tauto.
Qed.

Lemma OtherBivalent: forall cfg step1 step2, (chooseFn cfg step1 = chooseFn cfg step2 /\ 
  univalent_true (run cfg [step1]) /\ univalent_false (run cfg [step2])) -> 
  forall step, chooseFn cfg step <> chooseFn cfg step1 -> bivalent (run cfg [step]).
Proof.
intuition.
apply BivNotUn.
unfold univalent.
pose proof OneStepLemmaP1 as P1.
intuition.
(** CASE : univalent_true (run cfg [step]) **)
assert(P1T := P1 cfg step2 step).
rewrite H0 in H1.
auto.
(** CASE : univalent_false (run cfg [step]) **)
assert(P1H := P1 cfg step step1).
auto.
Qed. 


(** only the same process could goes to univalent_true & univalent_false states, so we choose another process and
it must be bivalent as proven by the OtherBivalent lemma **)

Lemma OneStepLemmaP3: forall cfg step1 step2, univalent_true (run cfg [step1]) /\ univalent_false (run cfg [step2]) -> 
  exists step: nat, bivalent (run cfg [step]).  
Proof.
intros.
pose proof OneStepLemmaP2 as P2.
specialize(P2 cfg step2 step1).
intuition.
assert(AP := AnotherProcessStepExists cfg step1).
destruct AP.
pose proof OtherBivalent as OB.
specialize (OB cfg step1 step2).
intuition.
rewrite H in H3.
intuition.
specialize(H3 x).
intuition.
exists x.
assumption.
Qed.

(** The main lemma, named OneStepLemma after Constable's paper **)

Theorem OneStepLemma: forall cfg, bivalent cfg -> exists step, bivalent (run cfg [step]).
Proof.
intros.
assert(S := randomStep cfg).
pose proof Correctness as C.
specialize(C (run cfg [S])). 
intuition. 
(** CASE: bivalent (run cfg [S]) **)
exists S.
assumption.
(** CASE: bivalent (run cfg [S])  proven **)
unfold univalent in H0.
pose proof BivalentPaths2 as B2.
specialize(B2 cfg).
destruct H0.

(** CASE: univalent_true (run cfg [S]) - follow univalent_false path then if processes are different **)
intuition.
destruct H2.
(** if there are some steps before entering univalent_false, enter first one if processes are different or step
with other process (it should be bivalent if protocol is partially correct) **)
destruct H1.
pose proof Correctness8 as C8.
specialize(C8 cfg x x0).
intuition.
exists x.
trivial.
pose proof OneStepLemmaP3 as P3.
specialize(P3 cfg S x).
tauto.

(** CASE: univalent_false (run cfg [S]) - symmetrical to previous **)
intuition.
destruct H3.
destruct H1.
pose proof Correctness9 as C9.
specialize(C9 cfg x x0).
intuition.
exists x.
trivial.
pose proof OneStepLemmaP3 as P3.
specialize(P3 cfg x S).
tauto.
Qed.

(** Not strictly corresponding to the original paper, as there's no any 
process & event considered **)

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


(** Initial Configuration & its properties **)

Parameter InitialConfiguration: Configuration.

Axiom InitialNoConsensus: ~decided InitialConfiguration.
Axiom TrueReacheable: exists s1, decidedValue (run InitialConfiguration s1) true.
Axiom FalseReacheable: exists s2, decidedValue (run InitialConfiguration s2) false.

(** Lemma 2 from original paper **)
(** Initial configuration is bivalent **)
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