(** FLP Impossibility Proof **)
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

Definition ProcessState := nat. 

Definition ProcessId := nat. 

Definition Configuration := list ProcessState.

(** Abstract function returning True if some process(es) in configuration reached 
final state associated with given binary value **)
Parameter decidedValue: Configuration -> Binary -> Prop.

Definition decided(cfg:Configuration):Prop := decidedValue cfg true \/ decidedValue cfg false.

(** No two processes decide differently **)
Axiom Agreement: forall cfg, ~(decidedValue cfg true /\ decidedValue cfg false).


(** Process ID is nat **) 
Parameter processId : ProcessState -> ProcessId.

(** Configuration transition function **)
Parameter stepFn : Configuration -> ProcessId -> Configuration.


(** There's no change in deciding value **)
Axiom Termination: forall cfg b prcId, decidedValue cfg b -> decidedValue (stepFn cfg prcId) b.


(** A particular execution, defined by a possibly infinite sequence of events from 
a starting configuration C is called a schedule and the sequence of steps taken 
to realise the schedule is a run **)
Fixpoint run (cfg:Configuration)(s:list ProcessId): Configuration :=
match s with
| nil => cfg
| cons step t => stepFn (run cfg t) step
end.


Axiom RunCommutativity2: forall cfg prcId s, run (run cfg [prcId]) s = run cfg (prcId :: s).

(** todo: proove? **)
Axiom RunCommutativity: forall cfg s1 s2, run (run cfg s1) s2 = run cfg (s1 ++ s2).



Lemma Termination1: forall cfg b ps, decidedValue cfg b -> decidedValue (run cfg ps) b.
Proof.
intros.
pose proof Termination as T.
unfold run.
induction ps.
trivial.
auto.
Qed.

(** We say that a run is deciding provided that some process eventually decides according 
to the properties of consensus **)
Definition deciding(cfg:Configuration)(ps:list ProcessId): Prop := decided (run cfg ps).


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
  (exists ps1, univalent_false(run cfg (ps1))) /\ 
  (exists ps2, univalent_true(run cfg (ps2))).
Proof.
intros cfg.
pose proof Agreement as A.
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
  (exists pid1 ps1, univalent_false(run cfg (pid1::ps1))) /\ 
  (exists pid2 ps2, univalent_true(run cfg (pid2::ps2))).
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

Lemma Correctness4: forall cfg ps, univalent_false cfg -> ~ univalent_true (run cfg ps).
Proof.
intros cfg ps.
unfold univalent_false.
unfold univalent_true.
intuition.
destruct H.
pose proof RunCommutativity as RC.
specialize (RC cfg ps x).
rewrite RC in H.
generalize dependent H.
firstorder.
Qed.


Lemma Correctness5: forall cfg ps, univalent_true cfg -> ~ univalent_false (run cfg ps).
Proof.
intros cfg ps.
unfold univalent_false.
unfold univalent_true.
intuition.
destruct H.
pose proof RunCommutativity as RC.
specialize (RC cfg ps x).
rewrite RC in H.
generalize dependent H.
firstorder.
Qed.

Axiom Correctness6: forall cfg ps, univalent_true cfg -> univalent_true (run cfg ps).
Axiom Correctness7: forall cfg ps, univalent_false cfg -> univalent_false (run cfg ps).


Lemma Correctness8: forall cfg pid ps, univalent_false (run cfg (pid :: ps)) -> 
  bivalent (run cfg [pid]) \/ univalent_false (run cfg [pid]).
Proof.
intros.
pose proof Correctness as C.
specialize(C (run cfg [pid])).
unfold univalent in C.
destruct C.
tauto.
pose proof Correctness5 as C5.
specialize(C5 (run cfg [pid]) ps).
intuition.
pose proof RunCommutativity2 as RC2.
specialize(RC2 cfg pid ps).
rewrite RC2 in H0.
tauto.
Qed.


Lemma Correctness9: forall cfg pid ps, univalent_true (run cfg (pid :: ps)) -> bivalent (run cfg [pid]) \/ univalent_true (run cfg [pid]).
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



Axiom Async1: forall cfg pid1 pid2, pid1 <>  pid2 -> 
  run cfg ([pid1;pid2]) = run cfg ([pid2;pid1]).

(**todo: remove
Axiom Decidability: forall pid1 pid2, pid1 = pid2 \/ pid1 <> pid2.
**)

Lemma OneStepLemmaP1: forall cfg pid1 pid2, 
  pid1 <> pid2 /\ 
    univalent_false (run cfg [pid1]) /\
    univalent_true (run cfg [pid2])-> False.
Proof.
intuition.
pose proof RunCommutativity2 as RC.
specialize(RC cfg).
pose proof Async1 as A1.
specialize(A1 cfg pid1 pid2).
pose proof Correctness6 as C6.
pose proof Correctness7 as C7.
specialize (C6 (run cfg [pid2]) [pid1]).
rewrite RC in C6.
specialize (C7 (run cfg [pid1]) [pid2]).
rewrite RC in C7.
intuition.
rewrite H1 in H3.
pose proof Correctness3 as C3.
specialize(C3 (run cfg [pid2; pid1])).
tauto.
Qed.

Lemma OneStepLemmaP2: forall cfg pid1 pid2,  
    univalent_false (run cfg [pid1]) /\
    univalent_true (run cfg [pid2]) -> pid1 = pid2.
Proof.
intros cfg p1 p2.
pose proof OneStepLemmaP1 as P1.
specialize(P1 cfg p1 p2).
tauto.
Qed.


(*Axiom AnotherProcessStepExists: forall pid1, exists pid2, pid1 <> pid2. *)

Parameter randomStep: Configuration -> ProcessId.
Parameter anotherProcess: Configuration -> ProcessId -> ProcessId.
Axiom AnotherProcessStepExists: forall cfg p1, anotherProcess cfg p1 <> p1.


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

Lemma OtherBivalent: forall cfg p1 p2, (p1 = p2 /\ 
  univalent_true (run cfg [p1]) /\ univalent_false (run cfg [p2])) -> 
  forall p, p <> p1 -> bivalent (run cfg [p]).
Proof.
intuition.
apply BivNotUn.
unfold univalent.
pose proof OneStepLemmaP1 as P1.
intuition.
(** CASE : univalent_true (run cfg [step]) **)
assert(P1T := P1 cfg p2 p).
rewrite H0 in H1.
auto.
(** CASE : univalent_false (run cfg [step]) **)
assert(P1H := P1 cfg p p1).
auto.
Qed. 


(** only the same process could goes to univalent_true & univalent_false states, so we choose another process and
it must be bivalent as proven by the OtherBivalent lemma **)

Lemma OneStepLemmaP3: forall cfg p1 p2, univalent_true (run cfg [p1]) /\ univalent_false (run cfg [p2]) -> 
  exists p: ProcessId, bivalent (run cfg [p]).  
Proof.
intros.
pose proof OneStepLemmaP2 as P2.
specialize(P2 cfg p2 p1).
intuition.
pose proof AnotherProcessStepExists as APSE.
specialize(APSE cfg p1).
intuition.
pose proof OtherBivalent as OB.
specialize (OB cfg p2 p1).
intuition.
rewrite H in H2.
rewrite H in H1.
intuition.
specialize(H2 (anotherProcess cfg p1)).
intuition.
exists (anotherProcess cfg p1).
assumption.
Qed.

(** The main lemma, named OneStepLemma after Constable's paper **)

Theorem OneStepLemma: forall cfg, bivalent cfg -> exists p, bivalent (run cfg [p]).
Proof.
intros.
assert(rp := randomStep cfg).
pose proof Correctness as C.
specialize(C (run cfg [rp])). 
intuition. 
(** CASE: bivalent (run cfg [rp]) **)
exists rp.
assumption.
(** CASE: bivalent (run cfg [rp])  proven **)
unfold univalent in H0.
pose proof BivalentPaths2 as B2.
specialize(B2 cfg).
destruct H0.

(** CASE: univalent_true (run cfg [rp]) - follow univalent_false path then if processes are different **)
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
specialize(P3 cfg rp x).
tauto.

(** CASE: univalent_false (run cfg [rp]) - symmetrical to previous **)
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
