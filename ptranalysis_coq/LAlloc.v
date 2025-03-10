Require Import CpdtTactics.
Require Import Ensembles.
Require Import Sets.Finite_sets_facts.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ClassicalChoice.
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

(* Print Assumptions proof_irrelevance. *)

(* Inductive StepState (si : Ensemble AllocSite) : Type :=
| StepState_Mk : Control si -> State -> StepState si. *)

Definition EmptyState := State_Mk (fun _ => None) (fun _ => None).

Definition WriteMap {Ret} (f : Var -> Ret) (k : Var) (v : Ret) : Var -> Ret :=
  fun k' => if Nat.eqb k k' then v else f k'.

Definition Unallocated (h : Heap) (addr : Addr) : Prop :=
  h addr = None.

Lemma disjointEmptyL : forall {A} (s : Ensemble A),
  Disjoint _ (Empty_set _) s.
Proof.
  intros.
  apply Disjoint_intro.
  unfold not. intros.
  inversion H. inversion H0.
Qed.

Lemma disjointEmptyR : forall {A} (s : Ensemble A),
  Disjoint _ s (Empty_set _).
Proof.
  intros.
  apply Disjoint_intro.
  unfold not. intros.
  inversion H. inversion H1.
Qed.

Definition SkipLSeq {si} (c : Control si)
  : Control (Union AllocSite (Empty_set AllocSite) si) := 
    Seq Skip c (disjointEmptyL si).

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
| Andersen_Move : forall {si} {vto vfrom : Var} {site : AllocSite} {p : Control si},
  PTMove p vto vfrom ->
  Andersen p vfrom site ->
  Andersen p vto site.

Lemma SkipIsStuck : forall {si} {s s' : State} {p : Control si},
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
Lemma SkipDoesNothingClosure1 : forall {si} {s s' : State} {p : Control si},
  StepClosure Skip s p s' -> si = Empty_set _.
Proof.
  intros.
  dependent induction H.
  - reflexivity.
  - apply SkipIsStuck in H.
    contradiction.
Qed.

Lemma SkipDoesNothingClosure2 :
  forall {s s' : State} {p : Control (Empty_set _)},
    StepClosure Skip s p s' -> p = Skip /\ s' = s.
Proof.
  intros.
  dependent induction H.
  - split; reflexivity.
  - apply SkipIsStuck in H.
    contradiction.
  Qed.

Lemma SkipOnlyReachesEmpty : forall {s : State},
  Reachable Skip s -> s = EmptyState.
Proof.
  intros.
  inversion H. destruct H0.
  pose proof (SkipDoesNothingClosure1 H0). subst.
  apply SkipDoesNothingClosure2 in H0.
  destruct H0. assumption.
Qed.

Lemma SkipNobodyPoints : forall {v : Var} {site : AllocSite},
  ~ConcretePointsTo Skip v site.
Proof.
  unfold not, ConcretePointsTo.
  intros. destruct H. destruct H. destruct H. destruct H0.
  apply SkipOnlyReachesEmpty in H. subst.
  simpl in H0. discriminate.
Qed.

Lemma StepCouldRemoveAllocSite :
  forall {si si'} {s s' : State} {p : Control si} {p' : Control si'},
  Step p s p' s' -> subset si' si.
Proof.
  unfold subset.
  intros.
  dependent induction H.
  - crush. specialize IHStep with x. destruct H0.
    + apply IHStep in H0. left. assumption.
    + right. assumption.
  - right. assumption.
  - assumption.
  - destruct H2.
Qed.

Lemma StepsCouldRemoveAllocSite :
  forall {si si'} {s s' : State} {p : Control si} {p' : Control si'},
  StepClosure p s p' s' -> subset si' si.
Proof.
  intros.
  dependent induction H.
  - unfold subset. intros. assumption.
  - pose proof (StepCouldRemoveAllocSite H).
    unfold subset in *. auto.
Qed.

Lemma SubsetPreservesDisjoint : forall {A} (s1 s2 s3 : Ensemble A),
  subset s1 s2 -> Disjoint _ s2 s3 -> Disjoint _ s1 s3.
Proof.
  intros.
  apply Disjoint_intro.
  inversion H0.
  unfold subset in H. unfold not in *. intros.
  specialize H with x. specialize H1 with x.
  inversion H2. apply H in H3.
  assert (In _ s2 x) as H3'. { apply H3. }
  pose proof (Intersection_intro _ _ _ _ H3' H4).
  contradiction.
Qed.

Lemma StepsPreserveDisjoint : forall
  {si1 si1' si2 : Ensemble AllocSite}
  {s s' : State}
  {c1 : Control si1} {c1' : Control si1'} {c2 : Control si2},
  StepClosure c1 s c1' s' -> Disjoint _ si1 si2 -> Disjoint _ si1' si2.
Proof.
  intros.
  pose proof (StepsCouldRemoveAllocSite H).
  pose proof (SubsetPreservesDisjoint H1 H0).
  assumption.
Qed.

Definition StepToStepClosure : forall
  {si si' : Ensemble AllocSite}
  {s s' : State}
  {p : Control si} {p' : Control si'},
  Step p s p' s' -> StepClosure p s p' s'.
Proof.
  intros.
  eapply StepClosure_Step.
  - exact H.
  - apply StepClosure_Refl.
Qed.

Lemma StepClosure_SeqL : forall
  {si1 si2 si1' : Ensemble AllocSite} {s s' : State}
  {c1 : Control si1} {c2 : Control si2} {c1' : Control si1'}
  (dis : Disjoint _ si1 si2)
  (dis' : Disjoint _ si1' si2),
  StepClosure c1 s c1' s' -> StepClosure (Seq c1 c2 dis) s (Seq c1' c2 dis') s'.
Proof.
  intros.
  dependent induction H.
  - pose proof (proof_irrelevance _ dis dis'). subst.
    apply StepClosure_Refl.
  - eapply Step_SeqL in H as H'.
    eapply StepClosure_Step.
    + exact H'.
    + eapply IHStepClosure.
    Unshelve.
    eapply StepsPreserveDisjoint.
    * apply StepToStepClosure in H. exact H.
    * assumption.
    Unshelve. assumption.
Qed.
  
Lemma ReachablePreservation
  {si si'} {s : State} {p : Control si} {p' : Control si'}
  (dis : Disjoint _ si si') :
  Reachable p s -> Reachable (Seq p p' dis) s.
Proof.
  intros.
  unfold Reachable in *.
  destruct H as [si1]. destruct H as [p1].
  eapply StepsPreserveDisjoint in H as dis'.
  2: { exact dis. }
  (* Witness is just the remainder of the sequence *)
  exists (Union _ si1 si'). exists (Seq p1 p' dis').
  apply StepClosure_SeqL. assumption.
  Unshelve. assumption.
Qed.

(* Lemma PointsToPreservation
  {si si'} {s : State} {p : Control si} {p' : Control si'}
  {v : Var} {site : AllocSite}
  (dis : Disjoint _ si si') :
  ConcretePointsTo p v site -> ConcretePointsTo (Seq p p' dis) v site.
Proof.
   *)

Lemma WriteMapThenRead : forall {Ret} (f : Var -> Ret) (k : Var) (v : Ret),
  WriteMap f k v k = v.
Proof.
  intros.
  unfold WriteMap.
  destruct (Nat.eqb k k) eqn:H.
  - reflexivity.
  - apply Nat.eqb_neq in H. contradiction.
Qed.

(* This lemma is wrong *)
(* Lemma ConcreteAssignPostcondition :
  forall {si} {vto vfrom : Var} {site : AllocSite} {p : Control si},
  ConcretePointsTo p vfrom site ->
  ConcretePointsTo (Seq p (Assign vto vfrom) (disjointEmptyR si)) vto site.
Proof.
  intros.
  unfold ConcretePointsTo in *.
  destruct H as [s1]. destruct H as [site1].
  destruct H as [H1]. destruct H as [H2].
  remember (State_Mk
    (State_heap s1)
    (WriteMap (State_valuation s1) vto (Some site1))
  ) as s2.
  exists s2. exists site1.
  split. 2: {
    split; rewrite Heqs2; simpl.
    - rewrite WriteMapThenRead. reflexivity.
    - assumption.
  }
  unfold Reachable. exists (Empty_set _). exists Skip. *)

(* Lemma PointsToSequenceDecompose {si1 si2} {s : State} {p1 : Control si1} {p2 : Control si2} {v : Var} {site : AllocSite} (dis : Disjoint _ si1 si2) :
  ConcretePointsTo (Seq p1 p2 dis) v site ->
  ConcretePointsTo p1 v site \/ ConcretePointsTo p2 v site \/ (ConcretePointsTo p1 vfrom site /\ PTMove p2 vto vfrom)
Proof.
  intros.
  inversion H as [s1].  *)

(* TODO: AndersenToSequenceDecompose *)

(* Lemma MoveAcrossSequence {si1 si2} {s : State} {p1 : Control si1} {p2 : Control si2} {vto vfrom : Var} {site : AllocSite} (dis : Disjoint _ si1 si2) :
  ConcretePointsTo p1 vfrom site ->
  PTMove p2 vto vfrom -> *)


Theorem Andersen_sound : SoundApprox ConcretePointsTo Andersen. Proof.
  unfold SoundApprox.
  intros.
  dependent induction program.
  4: {
    inversion H as [s]. destruct H0 as [site1]. destruct H0 as [H1]. destruct H0 as [H2].
  }
  - apply SkipNobodyPoints in H. contradiction.
