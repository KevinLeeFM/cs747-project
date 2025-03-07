Require Import CpdtTactics.
Require Import Ensembles.
Require Import Sets.Finite_sets_facts.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Definition Var := nat.
Definition Addr := nat.
Definition Val := Addr.
Definition AllocSite := nat.

(* Controls types are indexed by a set of the AllocSite it uses as labels.
This is to enforce unique AllocSites when composing statements together. *)
Inductive Control : Ensemble AllocSite -> Type :=
| Skip : Control (Empty_set _)
| Assign : Var -> Var -> Control (Empty_set _)
| Alloc (l : AllocSite) (vto : Var) : Control (Singleton _ l)
| Seq : forall s1 s2,
  Control s1 -> Control s2 -> Disjoint _ s1 s2  -> Control (Union _ s1 s2).

Record HeapObj := HeapObj_Mk {
  HeapObj_val : option Val;
  HeapObj_site : AllocSite
}.

Definition Heap := Addr -> option HeapObj.
Definition Valuation := Var -> option Val.

Record State := State_Mk {
  State_heap : Heap;
  State_valuation : Valuation
}.

(* Inductive StepState (si : Ensemble AllocSite) : Type :=
| StepState_Mk : Control si -> State -> StepState si. *)

Definition EmptyState := State_Mk (fun _ => None) (fun _ => None).

Definition WriteMap {Ret} (f : Var -> Ret) (k : Var) (v : Ret) : Var -> Ret :=
  fun k' => if Nat.eqb k k' then v else f k'.

Definition Unallocated (h : Heap) (addr : Addr) : Prop :=
  h addr = None.

Lemma disjointEmptyLeft : forall {A} (s : Ensemble A),
  Disjoint _ (Empty_set _) s.
Proof.
  intros.
  apply Disjoint_intro.
  unfold not. intros.
  inversion H. inversion H0.
Qed.

Definition SkipLSeq {si} (c : Control si) : Control (Union AllocSite (Empty_set AllocSite) si) := 
  Seq Skip c (disjointEmptyLeft si).

Inductive Step : forall {si_a si_b},
  Control si_a -> State -> Control si_b -> State -> Prop :=
| Step_SeqL : forall
  {si1 si2 si1' : Ensemble AllocSite}
  {s s' : State}
  {c1 : Control si1} {c2 : Control si2} {c1' : Control si1'}
  (dis : Disjoint _ si1 si2)
  (dis' : Disjoint _ si1' si2),
  Step c1 s c1' s' -> Step (Seq c1 c2 dis) s (Seq c1' c2 dis') s'
| Step_SeqR : forall
  {si} {c : Control si} {s : State},
  Step (SkipLSeq c) s c s
| Step_Assign : forall
  {vto vfrom : Var} {h : Heap} {sig sig' : Valuation},
  sig' = WriteMap sig vto (sig vfrom) ->
  Step (Assign vto vfrom) (State_Mk h sig) Skip (State_Mk h sig')
| Step_Alloc : forall
  {l : AllocSite} {addr : Addr} {vto : Var}
  {h h' : Heap}
  {sig sig' : Valuation},
  Unallocated h addr ->
  h' = WriteMap h addr (Some (HeapObj_Mk None l)) ->
  sig' = WriteMap sig vto (Some addr) ->
  Step (Alloc l vto) (State_Mk h sig) Skip (State_Mk h' sig').

Inductive StepClosure : forall {si_a si_b},
  Control si_a -> State -> Control si_b -> State -> Prop :=
| StepClosure_Refl : forall {si} {c : Control si} {s : State},
  StepClosure c s c s
| StepClosure_Step : forall
  {si_a si_b si_c}
  {c1 : Control si_a} {c2 : Control si_b} {c3 : Control si_c}
  {s1 : State} {s2 : State} {s3 : State},
  Step c1 s1 c2 s2 ->
  StepClosure c2 s2 c3 s3 ->
  StepClosure c1 s1 c3 s3.

(* # Concrete pointer analysis *)

Definition PTAnalysis := forall si, Control si -> Var -> AllocSite -> Prop.
(* Arguments PTAnalysis {si}. *)

Definition Reachable {si} (program : Control si) (state : State) : Prop :=
  exists (si' : Ensemble AllocSite) (program' : Control si'),
  StepClosure program EmptyState program' state.

Definition ConcretePointsTo
  [si] (program : Control si) (v : Var) (site : AllocSite) : Prop :=
  exists (s : State) (p : AllocSite),
    Reachable program s /\
    State_valuation s v = Some p /\
    match State_heap s p with
    | Some hObj => HeapObj_site hObj = site
    | None => False
    end.

(* # Abstract pointer analysis *)

Definition SoundApprox
  (concrete : PTAnalysis) (abstract : PTAnalysis) : Prop :=
    forall si (program : Control si) (v : Var) (site : AllocSite),
    concrete si program v site -> abstract si program v site.

(* Generally useful relations *)

Fixpoint PTAlloc {si} (p : Control si) (var : Var) (site : AllocSite) : Prop :=
  match p with
  | Alloc l vto => var = vto /\ site = l
  | Seq fst snd _ => PTAlloc fst var site \/ PTAlloc snd var site
  | _ => False
  end.

Fixpoint PTMove {si} (p : Control si) (vto vfrom : Var) : Prop :=
  match p with
  | Assign vto' vfrom' => vto = vto' /\ vfrom = vfrom'
  | Seq fst snd _ => PTMove fst vto vfrom \/ PTMove snd vto vfrom
  | _ => False
  end.

(* Andersen-style points-to analysis *)

Inductive Andersen : PTAnalysis :=
| Andersen_Alloc : forall {si} {var : Var} {site : AllocSite} {p : Control si},
  PTAlloc p var site -> Andersen p var site
| move : forall {si} {vto vfrom : Var} {site : AllocSite} {p : Control si},
  PTMove p vto vfrom ->
  Andersen p vfrom site ->
  Andersen p vto site.

Lemma skipIsStuck : forall {si} {s s' : State} {p : Control si},
  Step Skip s p s' -> False.
Proof.
  intros.
  inversion H; subst.
Qed.

(* We need two versions of skipDoesNothingClosure,
  - The first converts si into Empty_set _
  - The second converts p into Skip, and s into EmptyState, given si is
    already an Empty_set _.

  They cannot be asserted simultaneously due to type disagreements.
 *)
Lemma skipDoesNothingClosure1 : forall {si} {s s' : State} {p : Control si},
  StepClosure Skip s p s' -> si = Empty_set _.
Proof.
  intros.
  dependent induction H.
  - reflexivity.
  - apply skipIsStuck in H.
    contradiction.
Qed.

Lemma skipDoesNothingClosure2 :
  forall {s s' : State} {p : Control (Empty_set _)},
    StepClosure Skip s p s' -> p = Skip /\ s' = s.
Proof.
  intros.
  dependent induction H.
  - split; reflexivity.
  - apply skipIsStuck in H.
    contradiction.
  Qed.

Lemma skipOnlyReachesEmpty : forall {s : State},
  Reachable Skip s -> s = EmptyState.
Proof.
  intros.
  inversion H. destruct H0.
  pose proof (skipDoesNothingClosure1 H0). subst.
  apply skipDoesNothingClosure2 in H0.
  destruct H0. assumption.
Qed.

Theorem Andersen_sound : SoundApprox ConcretePointsTo Andersen. Proof.
  unfold SoundApprox, ConcretePointsTo.
  intros.
  dependent induction program.
  - destruct H. destruct H. destruct H. destruct H0.
