(** FLP Impossibility Proof **)
(** Made after original paper http://cs-www.cs.yale.edu/homes/arvind/cs425/doc/fischer.pdf **) 
(** described more informally in the awesome blogpost http://the-paper-trail.org/blog/a-brief-tour-of-flp-impossibility/ **)
(** also constructive proofs: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.7907&rep=rep1&type=pdf **)
(** and http://www.cs.cornell.edu/courses/cs7412/2011sp/ConsensusRebecca.pdf **)

Require Import Arith.
Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.ListSet.

Set Implicit Arguments.
Import ListNotations.


Definition Binary := bool.

Inductive Process: Set := 
| FinishedProcess: nat -> Binary -> Process
| proceed: nat -> nat -> Process. 

Definition id(p:Process) := match p with 
| FinishedProcess i _ => i
| proceed i _ => i
end.


Definition same(p1:Process)(p2:Process):Prop := (id p1) = (id p2).


Definition finishedIn(b:Binary)(p:Process):Prop := match p with
| FinishedProcess _ b => True
| _ => False
end.


Definition Configuration := list Process.

Axiom np2: forall cfg:Configuration, length cfg >=2.

Parameter isApplicable : Configuration -> nat -> Prop.

Definition Event := nat.




Fixpoint belongs(p:Process)(cfg:Configuration) := match cfg with
| nil => False
| po :: t => same p po \/ belongs p t
end.


Fixpoint idSubset(pid:nat)(cfg:list Process):= filter(fun p => beq_nat pid (id p )) cfg.

Axiom IdsRight: forall cfg p, belongs p cfg -> length (idSubset (id p) cfg) = 1.

Fixpoint exclude(cfg:Configuration)(ps2:list Process): list Process := match cfg with
| nil => nil
| p :: t => idSubset (id p) ps2 ++ (exclude t ps2)
end. 

(*
Lemma exclude1: forall cfg (p:Process), belongs p cfg -> ~ belongs p (exclude cfg [p]).
Proof.
*)



  
Definition decidedValue(cfg:Configuration)(b:Binary):Prop := 
In True (map (finishedIn b) cfg).

Definition decided(cfg:Configuration):Prop := decidedValue cfg true \/ decidedValue cfg false.


Axiom Consistency: forall cfg, ~(decidedValue cfg true /\ decidedValue cfg false).


Parameter chooseFn : Event -> Process.

Axiom chooseRight: forall cfg msg, belongs (chooseFn msg) cfg.

Parameter updateFn : Process -> nat -> Process.

Axiom updateFn2: forall p msg b, finishedIn b p -> finishedIn b (updateFn p msg).
Axiom updateFn3: forall p msg b, 
    ~finishedIn b p /\ finishedIn b (updateFn p msg) -> ~finishedIn (negb b) (updateFn p msg).


(** Configuration transition function **)
Definition eventFn(cfg:Configuration)(msg:Event):Configuration :=
let p:= chooseFn msg in [updateFn p msg] ++ exclude cfg [p].


(** A particular execution, defined by a possibly infinite sequence of events from 
a starting configuration C is called a schedule and the sequence of steps taken 
to realise the schedule is a run **)
Fixpoint Schedule (cfg:Configuration)(l:set Event): Prop := match l with
| nil => True
| msg :: s => isApplicable cfg msg /\ Schedule (eventFn cfg msg) s
end.



Axiom StableQuorum: forall cfg p msg, belongs p cfg -> belongs p (eventFn cfg msg).


(** There's no change in deciding value **)
(** could be proven now from updateFn2 & StableQuorum **)
Axiom Termination: forall cfg b msg, decidedValue cfg b -> decidedValue (eventFn cfg msg) b.


Lemma Termination_1: forall cfg msg, decided cfg -> decided (eventFn cfg msg).
Proof.
intros.
pose proof Termination as T.
unfold decided.
unfold decided in H.
intuition.
Qed.


Fixpoint run (cfg:Configuration)(s:set nat): Configuration :=
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





(** We say that a run is deciding provided that some process eventually decides according 
to the properties of consensus **)
Definition deciding(cfg:Configuration)(s:set Event): Prop := Schedule cfg s /\ decided (run cfg s).

Hypothesis InitialConfiguration: Configuration.


Axiom InitialNoConsensus: ~decided InitialConfiguration.
Axiom TrueReacheable: exists s1, Schedule InitialConfiguration s1 /\ decidedValue (run InitialConfiguration s1) true.
Axiom FalseReacheable: exists s2, Schedule InitialConfiguration s2 /\ decidedValue (run InitialConfiguration s2) false.



Definition univalent_true(cfg:Configuration):= 
(exists s1, Schedule cfg s1 /\ decidedValue(run cfg s1) true) /\ ~(exists s2, Schedule cfg s2 /\ decidedValue (run cfg s2) false).

Definition univalent_false(cfg:Configuration):= 
(exists s1, Schedule cfg s1 /\ decidedValue(run cfg s1) false) /\ ~(exists s2, Schedule cfg s2 /\ decidedValue (run cfg s2) true).

Definition univalent(cfg:Configuration):= univalent_true cfg \/ univalent_false cfg.

Definition bivalent(cfg:Configuration):= ~ decided cfg /\
  (exists s1, Schedule cfg s1 /\ decidedValue(run cfg s1) false) /\ 
  (exists s2, Schedule cfg s2 /\ decidedValue (run cfg s2) true).


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





(*

Fixpoint ScheduleContains(s:Schedule)(p:Process): Prop := match s with
|nil => False
|msg :: s1 => same p (chooseFn msg) \/ ScheduleContains s1 p
end.

Definition minusSchedule(s:Schedule)(p:Process):Prop := ~ ScheduleContains s p.


*)

Fixpoint allApplicable(cfg:Configuration)(s:set Event) := match s with
| nil => True
| e :: t => isApplicable cfg e /\ allApplicable cfg t
end.


Axiom ArbitraryDelay: forall cfg (s:set Event) e, allApplicable cfg (e::s) -> isApplicable (run cfg s) e.


Parameter GetApplicable: Configuration -> set Event.

Axiom GetApplicableIsApplicable: forall cfg, allApplicable cfg (GetApplicable cfg).


Lemma OneStepLemmaP1: forall cfg msg,  ~ univalent_true (run cfg [msg]).
Proof.
intros.
unfold univalent_true.
tauto.
Qed.


(** todo: prove it **)
Axiom OneStepLemma: forall cfg, bivalent cfg -> exists msg, isApplicable cfg msg /\ bivalent (run cfg [msg]). 


Lemma OneStepLemma2: forall cfg, bivalent cfg -> exists msg, Schedule cfg [msg] /\ bivalent (run cfg [msg]).
Proof.
intros.
pose proof OneStepLemma as O.
specialize (O cfg).
intuition.
destruct H0.
apply ex_intro with (x:=x).
unfold Schedule.
tauto.
Qed.


Theorem FLP_Lemma3: forall cfg, bivalent cfg -> forall m, exists s, length s > m -> Schedule cfg s /\ bivalent (run cfg s).
Proof.
intros; edestruct OneStepLemma2; eauto.
Qed.


(** THEOREM 1. No consensus protocol is totally correct in spite of one fault. **)

Theorem FLP_main: forall m, exists s, length s > m -> Schedule InitialConfiguration s /\ ~ deciding InitialConfiguration s.
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