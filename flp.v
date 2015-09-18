(** FLP Impossibility Proof **)

(** Done by Alexander Chepurnoy **)
(** Public domain **)

(** Made after original paper http://cs-www.cs.yale.edu/homes/arvind/cs425/doc/fischer.pdf **) 
(** described more informally in the awesome blogpost http://the-paper-trail.org/blog/a-brief-tour-of-flp-impossibility/ **)
(** Some constructive proofs existed before, e. g. **)
(** http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.7907&rep=rep1&type=pdf **)
(** and http://www.cs.cornell.edu/courses/cs7412/2011sp/ConsensusRebecca.pdf **)

(** Unlike previous proofs, this one has the same model as the original paper **)
(** But instead of Lemma3, it has own constructive small-step proof of a bivalent run existence **)

Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical.

Set Implicit Arguments.
Import ListNotations.

Definition Binary := bool.

(** "Processes are modeled as automata (with possibly infinitely many states)" 
    For our purposes it's enough to enumerate states with some natural numbers, 
encoding process identificator within a number as well, so there's bidirectional 
injective mapping (process_id, state) <-> nat **) 

(** Definition ProcessState := nat. **)

Parameter Process: Set. 

Definition Step := nat.

Definition Configuration := list Step.

(** Abstract function returning True if some process(es) in configuration reached 
final state associated with given binary value **)
Parameter decidedValue: Configuration -> Binary -> Prop.

Definition decides(cfg:Configuration):Prop := decidedValue cfg true \/ decidedValue cfg false.

(** No two processes decide differently **)
Axiom Agreement: forall cfg, ~(decidedValue cfg true /\ decidedValue cfg false).


Parameter processId: Step -> Process.


(** Configuration transition function **) 
Definition stepFn(cfg:Configuration)(step:Step):Configuration := cfg ++ [step].

(** There's no change in deciding value **)
Axiom Termination: forall cfg b step, decidedValue cfg b -> decidedValue (stepFn cfg step) b.


(** A particular execution, defined by a possibly infinite sequence of events from 
a starting configuration C is called a schedule and the sequence of steps taken 
to realise the schedule is a run **)

Definition Schedule := list Step.

Fixpoint run (cfg:Configuration)(s:Schedule): Configuration :=
match s with
| nil => cfg
| cons step t => stepFn (run cfg t) step
end.


Axiom RunCommutativity2: forall cfg step s, run (run cfg [step]) s = run cfg (step :: s).

(** todo: proove? **)
Axiom RunCommutativity: forall cfg s1 s2, run (run cfg s1) s2 = run cfg (s1 ++ s2).



Lemma Termination1: forall cfg b s, decidedValue cfg b -> decidedValue (run cfg s) b.
Proof.
intros.
pose proof Termination as T.
unfold run.
induction s.
trivial.
auto.
Qed.


Definition true_univalent(cfg:Configuration):= 
  (exists s1, decidedValue(run cfg s1) true) /\ ~(exists s2, decidedValue (run cfg s2) false).

Definition false_univalent(cfg:Configuration):= 
  (exists s1, decidedValue(run cfg s1) false) /\ ~(exists s2, decidedValue (run cfg s2) true).

Definition univalent(cfg:Configuration):= true_univalent cfg \/ false_univalent cfg.

Definition bivalent(cfg:Configuration):= (~ decides cfg) /\
  (exists s1, decidedValue (run cfg s1) false) /\ (exists s2, decidedValue (run cfg s2) true).


(** "By the total correctness of P, and the fact that there are always admissible runs, V > 0" **)
Axiom Correctness: forall cfg, bivalent cfg \/ univalent cfg.


Lemma UnNotBiv: forall cfg, univalent cfg <-> ~ bivalent cfg.
Proof.
intros cfg.
unfold bivalent.
unfold univalent.
unfold true_univalent.
unfold false_univalent.
pose proof Correctness as C.
specialize (C cfg).
tauto.
Qed.


Lemma BivNotUn: forall cfg, bivalent cfg <-> ~ univalent cfg.
Proof.
intros.
unfold bivalent.
unfold univalent.
unfold true_univalent.
unfold false_univalent.
pose proof Correctness as C.
specialize (C cfg).
tauto.
Qed.


Lemma BivalentPaths: forall cfg, bivalent cfg ->
  (exists s1, false_univalent(run cfg (s1))) /\ 
  (exists s2, true_univalent(run cfg (s2))).
Proof.
intros cfg.
pose proof Agreement as A.
pose proof Termination1 as T.
unfold bivalent. unfold false_univalent. unfold true_univalent.
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
specialize (A (run (run cfg x) x1)).
tauto.
destruct H.
destruct H2.
exists x0.
specialize (T (run cfg x0) true).
intuition.
exists [].
trivial.
destruct H2.
specialize (A (run (run cfg x0) x1)).
auto.
Qed.



Lemma BivalentPaths2: forall cfg, bivalent cfg ->
  (exists pid1 ps1, false_univalent(run cfg (pid1::ps1))) /\ 
  (exists pid2 ps2, true_univalent(run cfg (pid2::ps2))).
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



Lemma UnFNotBiv: forall cfg, false_univalent cfg -> ~ bivalent cfg.
Proof.
intros cfg.
pose proof Correctness as C.
specialize (C cfg).
pose proof BivalentPaths as B.
specialize (B cfg).
unfold univalent in C.
unfold false_univalent.
unfold bivalent.
unfold false_univalent in C.
unfold true_univalent in C.
unfold bivalent in C.
unfold false_univalent in B.
unfold true_univalent in B.
unfold bivalent in B.
tauto.
Qed.


Lemma UnTNotBiv: forall cfg, true_univalent cfg -> ~ bivalent cfg.
Proof.
intros cfg.
pose proof Correctness as C.
specialize (C cfg).
pose proof BivalentPaths as B.
specialize (B cfg).
unfold univalent in C.
unfold true_univalent.
unfold bivalent.
unfold false_univalent in C.
unfold true_univalent in C.
unfold bivalent in C.
unfold false_univalent in B.
unfold true_univalent in B.
unfold bivalent in B.
tauto.
Qed.



Lemma Correctness2: forall cfg, true_univalent cfg -> false_univalent cfg -> False.
Proof.
intros.
unfold true_univalent in H.
destruct H.
unfold false_univalent in H0.
destruct H.
destruct H0.
destruct H0.
destruct H1.
exists x0.
trivial.
Qed.

Lemma Correctness3: forall cfg, false_univalent cfg -> true_univalent cfg -> False.
Proof.
intros.
unfold false_univalent in H.
destruct H.
unfold true_univalent in H0.
destruct H.
destruct H0.
destruct H0.
destruct H1.
exists x0.
trivial.
Qed.

Lemma Correctness4: forall cfg s, false_univalent cfg -> ~ true_univalent (run cfg s).
Proof.
intros cfg s.
unfold false_univalent.
unfold true_univalent.
intuition.
destruct H.
pose proof RunCommutativity as RC.
specialize (RC cfg s x).
rewrite RC in H.
generalize dependent H.
firstorder.
Qed.


Lemma Correctness5: forall cfg ps, true_univalent cfg -> ~ false_univalent (run cfg ps).
Proof.
intros cfg ps.
unfold false_univalent.
unfold true_univalent.
intuition.
destruct H.
pose proof RunCommutativity as RC.
specialize (RC cfg ps x).
rewrite RC in H.
generalize dependent H.
firstorder.
Qed.

Axiom Correctness6: forall cfg ps, true_univalent cfg -> true_univalent (run cfg ps).
Axiom Correctness7: forall cfg ps, false_univalent cfg -> false_univalent (run cfg ps).


Lemma Lemma3: forall cfg ss, false_univalent (run cfg ss) -> bivalent cfg \/ false_univalent cfg.
Proof.
intros.
pose proof Correctness as C.
specialize(C cfg).
unfold univalent in C.
destruct C.
tauto.
pose proof Correctness5 as C5.
specialize(C5 cfg ss).
intuition.
Qed.

Lemma Lemma3C: forall cfg s ss, false_univalent (run cfg (s :: ss)) -> bivalent (run cfg [s]) \/ false_univalent (run cfg [s]).
Proof.
intros.
pose proof RunCommutativity2 as RC2.
pose proof Lemma3 as L3.
specialize (RC2 cfg s ss).
specialize (L3 (run cfg [s]) ss).
rewrite RC2 in L3.
tauto.
Qed.

Lemma Correctness9: forall cfg pid ps, true_univalent (run cfg (pid :: ps)) -> bivalent (run cfg [pid]) \/ true_univalent (run cfg [pid]).
Proof.
intros.
pose proof Correctness as C.
specialize(C (run cfg [pid])).
unfold univalent in C.
destruct C.
tauto.
pose proof Correctness4 as C4.
specialize(C4 (run cfg [pid]) ps).
intuition.
pose proof RunCommutativity2 as RC2.
specialize(RC2 cfg pid ps).
rewrite RC2 in H0.
tauto.
Qed.



Axiom Async1: forall cfg s1 s2, processId s1 <> processId s2 -> run cfg ([s1;s2]) = run cfg ([s2;s1]).

(**todo: remove
Axiom Decidability: forall pid1 pid2, pid1 = pid2 \/ pid1 <> pid2.
**)

Lemma OneStepLemmaP1: forall cfg s1 s2, 
  processId s1 <> processId s2 /\ 
    false_univalent (run cfg [s1]) /\
    true_univalent (run cfg [s2])-> False.
Proof.
intuition.
pose proof RunCommutativity2 as RC.
specialize(RC cfg).
pose proof Async1 as A1.
specialize(A1 cfg s1 s2).
pose proof Correctness6 as C6.
pose proof Correctness7 as C7.
specialize (C6 (run cfg [s2]) [s1]).
rewrite RC in C6.
specialize (C7 (run cfg [s1]) [s2]).
rewrite RC in C7.
intuition.
rewrite H1 in H3.
pose proof Correctness3 as C3.
specialize(C3 (run cfg [s2; s1])).
tauto.
Qed.

Lemma Lemma1: forall cfg s1 s2,  
    false_univalent (run cfg [s1]) /\
    true_univalent (run cfg [s2]) -> processId s1 = processId s2.
Proof.
intros cfg p1 p2.
pose proof OneStepLemmaP1 as P1.
specialize(P1 cfg p1 p2).
tauto.
Qed.


Axiom AnotherProcessStepExists: forall step, exists step0, processId step <> processId step0. 
Parameter randomStep: Configuration -> Step.


Lemma BivNotUnTAndUnF: forall cfg, bivalent cfg <-> ~ true_univalent cfg /\ ~ false_univalent cfg.
Proof.
intros.
intuition.
(** CASE: true_univalent cfg **)
pose proof UnTNotBiv as UT.
specialize(UT cfg).
tauto.
(** CASE: false_univalent cfg **)
pose proof UnFNotBiv as UF.
specialize(UF cfg).
tauto.
(** CASE: opposite direction **)
apply BivNotUn.
unfold univalent.
tauto.
Qed.

Lemma Lemma2: forall cfg s1 s2, (processId s1 = processId s2 /\ 
  true_univalent (run cfg [s1]) /\ false_univalent (run cfg [s2])) -> 
  forall s, processId s <> processId s1 -> bivalent (run cfg [s]).
Proof.
intuition.
apply BivNotUn.
unfold univalent.
pose proof OneStepLemmaP1 as P1.
intuition.
(** CASE : true_univalent (run cfg [step]) **)
assert(P1T := P1 cfg s2 s).
rewrite H0 in H1.
auto.
(** CASE : false_univalent (run cfg [step]) **)
assert(P1H := P1 cfg s s1).
auto.
Qed. 


(** only the same process could goes to true_univalent & false_univalent states, so if we choose another process
it must be bivalent as proven by the OtherBivalent lemma **)

Lemma OneStepLemmaP3: forall cfg step1 step2, true_univalent (run cfg [step1]) /\ false_univalent (run cfg [step2]) -> 
   exists step: Step, bivalent (run cfg [step]).  
Proof.
intros.
pose proof Lemma1 as P2.
specialize(P2 cfg step2 step1).
intuition.
assert(AP := AnotherProcessStepExists step1).
destruct AP.
pose proof Lemma2 as OB.
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

Lemma Lemma4: forall cfg, bivalent cfg -> exists p, bivalent (run cfg [p]).
Proof.
intros.
assert(rp := randomStep cfg).
pose proof Correctness as C.
specialize(C (run cfg [rp])). 
intuition. 

(** CASE: bivalent (run cfg [rp]) **)
exists rp.
assumption.
(** --CASE: bivalent (run cfg [rp])  proven **)

unfold univalent in H0.
pose proof BivalentPaths2 as B2.
specialize(B2 cfg).
destruct H0.

(** CASE: true_univalent (run cfg [rp]) - follow false_univalent path then if processes are different **)
intuition.
destruct H2.
(** if there are some steps before entering false_univalent, enter first one if processes are different or step
with other process (it should be bivalent if protocol is partially correct) **)
destruct H1.
pose proof Lemma3C as L3.
specialize(L3 cfg x x0).
intuition.
exists x.
trivial.
pose proof OneStepLemmaP3 as P3.
specialize(P3 cfg rp x).
tauto.

(** CASE: false_univalent (run cfg [rp]) - symmetrical to previous **)
intuition.
destruct H3.
destruct H1.
pose proof Correctness9 as C9.
specialize(C9 cfg x x0).
intuition.
exists x.
trivial.
pose proof OneStepLemmaP3 as P3.
specialize(P3 cfg x rp).
tauto.
Qed.

(** Not strictly corresponding to the original paper, as there's no any 
process & event considered **)

Theorem FLP_Lemma4: forall cfg, bivalent cfg -> forall m, exists s, length s > m -> bivalent (run cfg s).
Proof.
intros. 
pose proof Lemma4 as O. 
specialize (O cfg).
intuition.
destruct H0.
exists [x]. 
intros. 
apply H0.
Qed.


(** Initial Configuration & its properties **)

Variable InitialConfiguration: Configuration.

Axiom InitialNoConsensus: ~decides InitialConfiguration.
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

(** We say that a run is deciding provided that some process eventually decides according 
to the properties of consensus. The theorem says the non-deciding run of arbitrary length
is possible **)

Theorem FLP: forall m, exists s, length s > m -> ~ decides (run InitialConfiguration s).
Proof.
intros m.
pose proof FLP_Lemma2 as FL2.
pose proof FLP_Lemma4 as FL4.
specialize (FL4 InitialConfiguration).
intuition.
specialize (H m).
destruct H.
apply ex_intro with (x:=x).
generalize dependent H.
unfold bivalent.
unfold decides.
tauto.
Qed.