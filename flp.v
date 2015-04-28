(** FLP Impossibility Proof **)
(** Made after original paper http://cs-www.cs.yale.edu/homes/arvind/cs425/doc/fischer.pdf **) 


Require Export BinPos.
Require Export List.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Lists.List.
Require Export Coq.PArith.Pnat.
Require Export Coq.Lists.ListSet.
Require Export Coq.Classes.EquivDec.
Require Export Coq.Vectors.VectorDef.
Require Export Coq.Vectors.Fin.
Require Export Setoid.


Local Open Scope nat_scope.
Import ListNotations.
Local Open Scope list_scope.


(** Each process p has a one-bit input register x, an output register y with 
values in (b, 0, 1), so (b, f, t) **)
Inductive Register :Type :=
  | b
  | f
  | t.


Definition InternalState:Type := nat.

Definition MessageValue:Type := nat.

Theorem mv_eq_dec : forall x y:MessageValue, {x = y} + {x <> y}.
Proof. intros. auto with *. Qed.

Inductive Message:Type := 
| emptyMessage
| messageValue: MessageValue -> Message.

Parameter numOfProcesses:nat.
Hypothesis np2: numOfProcesses >= 2.

Definition ProcessId := Fin.t numOfProcesses.

Definition Event : Type := prod ProcessId MessageValue.

Record Process : Type := {
   inputRegister : Register;
   outputRegister : Register;
   internalState : InternalState;
   transitionFunction: InternalState -> Message -> prod InternalState (list Event);
   messagesBuffer : set MessageValue 
}.

Definition updateMsgBuf (p:Process)(mb:set MessageValue):Process := 
({|inputRegister := p.(inputRegister); outputRegister := p.(outputRegister);
   internalState := p.(internalState); transitionFunction := p.(transitionFunction);
   messagesBuffer := mb |}).

Definition updateState (p:Process)(msg:Message) : prod Process (list Event):= 
let (newState, evts) := p.(transitionFunction) p.(internalState) msg in 
pair ({|inputRegister := p.(inputRegister); outputRegister := p.(outputRegister);
   internalState := newState; transitionFunction := p.(transitionFunction);
   messagesBuffer := p.(messagesBuffer) |}) evts.

Definition removeMsg (p:Process)(mv:MessageValue):Process := 
   updateMsgBuf p (remove mv_eq_dec  mv p.(messagesBuffer)).
 


Definition decisionState (p:Process) : bool :=
match outputRegister p with
|b => false
|_ => true
end.


Definition Configuration:Type := Vector.t Process numOfProcesses.
Parameter initialConfiguration : Configuration.



Definition NonDeterministicChoice := set MessageValue -> Message.

Variable ndChoiceImpl: NonDeterministicChoice.


Definition updateCfg (c:Configuration)(pid:ProcessId)(fn: Process -> Process) : Configuration :=
replace c pid (fn (nth c pid)).

Definition updateCfgWithEvents (c:Configuration)(pid:ProcessId)(fn: Process -> prod Process (list Event)) : prod (list Event) Configuration :=
let (p, evs) := fn(nth c pid) in pair evs (replace c pid p).

Definition send (cfg:Configuration) (pid:ProcessId) (mv: MessageValue)  : Configuration := 
updateCfg cfg pid (fun p=> let pmsgs : set MessageValue  := messagesBuffer p in
let newmsgs := set_add mv_eq_dec mv pmsgs in updateMsgBuf p newmsgs).


Import VectorNotations.

(** todo: prove the lemma **)
Lemma cfg_replace_replaced: forall pid p (c:Configuration), nth (replace c pid p) pid = p.

(** todo: prove the lemma **)
Lemma cfg_replace_comm: forall pid1 pid2 p1 p2 (c:Configuration), pid1 <> pid2 -> replace (replace c pid1 p1) pid2 p2 = replace (replace c pid2 p2) pid1 p1.

(** todo: prove the lemma **)
Lemma updateCfg_comm: forall p1 p2 pid1 pid2 fn1 fn2 (c:Configuration), 
pid1 <> pid2 -> p1 = fn1 c[@pid1] -> p2 = fn2 c[@pid2] -> updateCfg (updateCfg c pid1 fn1) pid2 fn2 = updateCfg (updateCfg c pid2 fn2) pid1 fn1.

(** todo: prove the lemma **)
Lemma send_length_comm: forall pid1 pid2 m c, pid1 <> pid2 -> send (send c pid2 m) pid1 m  = send (send c pid1 m) pid2 m.


Definition getMessageAndUpdateProcess (p:Process) : prod Process (list Event) := 
let (msg, pp) := (match ndChoiceImpl (messagesBuffer p) with
| emptyMessage => pair emptyMessage p
| messageValue mv =>  pair (messageValue mv) (removeMsg p mv)
end) in updateState pp msg.

(** receive with send **)
Definition receive (cfg:Configuration) (pid:ProcessId) : prod (list Event) Configuration :=
updateCfgWithEvents cfg pid getMessageAndUpdateProcess. 

(** not used, delete? **)
Definition ChooseProcess := Configuration -> ProcessId.
Variable chooseProcessImpl: ChooseProcess.


Definition sendOut(c:Configuration)(evt:Event) : Configuration := send c (fst evt) (snd evt).


Definition step (c:Configuration) : Configuration := 
   let pid := chooseProcessImpl c in 
   let (evts, c1) := receive c pid in
   List.fold_left sendOut evts c1.


Definition Schedule := Configuration -> list Event.

Definition Run := 


(**

LEMMA 1. Suppose that from some configuration C, the schedules s1, s2 lead 
to configurations C1, C2, respectively. If the sets of processes taking steps 
in C1 and C2, respectively, are disjoint, then s2 can be applied to C1 and s1 can be 
applied to C2, and both lead to the same configuration Cf.

**)