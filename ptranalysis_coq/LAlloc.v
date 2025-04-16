Require Import CpdtTactics.
Require Import Ensembles.
Require Import Sets.Finite_sets_facts.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ClassicalChoice.
Require Import Lia.
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

Definition EmptyState := State_Mk (fun _ => None) (fun _ => None).

Definition WriteMap {Ret} (f : Var -> Ret) (k : Var) (v : Ret) : Var -> Ret :=
  fun k' => if Nat.eqb k k' then v else f k'.

Definition Unallocated (sig : Valuation) (h : Heap) (addr : Addr) : Prop :=
  h addr = None /\ forall (v : Var), sig v <> Some addr.

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
  Unallocated sig h addr ->
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

Definition Consistent (s : State) : Prop :=
  exists (si : Ensemble AllocSite) (program : Control si), Reachable program s.

Definition ConcreteStatePointsTo
  (s : State) (v : Var) (site : AllocSite) : Prop :=
  exists (p : Addr),
  State_valuation s v = Some p /\
    match State_heap s p with
    | Some hObj => HeapObj_site hObj = site
    | None => False
    end.

Definition ConcretePointsTo
  [si] (program : Control si) (v : Var) (site : AllocSite) : Prop :=
  exists (s : State) (p : AllocSite),
    Reachable program s /\
    ConcreteStatePointsTo s v site.

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
  simpl in H0. destruct H0. discriminate.
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

Lemma WriteMapThenRead : forall {Ret} (f : Var -> Ret) (k : Var) (v : Ret),
  WriteMap f k v k = v.
Proof.
  intros.
  unfold WriteMap.
  destruct (Nat.eqb k k) eqn:H.
  - reflexivity.
  - apply Nat.eqb_neq in H. contradiction.
Qed.

(* PTMoveClosure is an approximated version of ConcreteMoveClosure
   E.g. of things not accounted for:
   - Overwriting a variable v1 with a new value prior to move to v2. The old
   value is still considered moved to v2 even though it didn't happen!
*)
Inductive PTMoveClosure : forall {si}, Control si -> Var -> Var -> Prop :=
| PTMoveClosure_Refl :
    forall {si} (p : Control si) (v : Var), PTMoveClosure p v v
| PTMoveClosure_Trans :
    forall {si} (p : Control si) (vto vinter vfrom : Var),
    PTMoveClosure p vinter vfrom ->
    PTMove p vto vinter ->
    PTMoveClosure p vto vfrom.

(* Keep in mind that the alloc can even come AFTER or DURING the series of moves.
  This analysis is flow-insensitive, so it doesn't matter. *)
Lemma AndersenMoveClosureCarriesAlloc : forall {si} {p : Control si} {vto vfrom : Var} {site : AllocSite},
  PTMoveClosure p vto vfrom ->
  PTAlloc p vfrom site ->
  Andersen p vto site.
Proof.
  intros.
  dependent induction H.
  - econstructor. assumption.
  - apply IHPTMoveClosure in H1 as H2.
    eapply Andersen_Move.
    + exact H0.
    + exact H2.
Qed.

Definition CondReachable {si} (program : Control si) (pre : State) (s : State) : Prop :=
  exists (si' : Ensemble AllocSite) (program' : Control si'),
  StepClosure program pre program' s.

Example ReachableSpecialCase : forall {si} {s : State} {p : Control si},
  Reachable p s = CondReachable p EmptyState s.
Proof.
  intros. unfold Reachable. unfold CondReachable. reflexivity.
Qed.

Lemma PTAllocComposition :
  forall {si1 si2} {p1 : Control si1} {p2 : Control si2} {v : Var} {site : AllocSite} (dis : Disjoint _ si1 si2),
  PTAlloc p1 v site \/ PTAlloc p2 v site <-> PTAlloc (Seq p1 p2 dis) v site.
Proof.
  intros.
  constructor.
  - unfold PTAlloc. crush.
  - unfold PTAlloc. crush.
Qed.

Lemma AllocSuperProgram : forall {si si'} {p : Control si} {p' : Control si'} {v : Var} {site : AllocSite} {s s' : State},
  Step p s p' s' -> PTAlloc p' v site -> PTAlloc p v site.
Proof.
  intros.
  dependent induction H.
  - erewrite <- PTAllocComposition in H0.
    erewrite <- PTAllocComposition.
    destruct H0.
    { apply IHStep in H0. left. assumption. }
    { right. assumption. }
  - unfold SkipLSeq. erewrite <- PTAllocComposition.
    right. assumption.
  - unfold PTAlloc in H0. contradiction.
  - unfold PTAlloc in H2. contradiction.
Qed.

Lemma MovePreservesNoPoints : forall {vto vfrom : Var} {site : AllocSite} {h : Heap} {sig sig' : Valuation},
  (forall v, ~ConcreteStatePointsTo (State_Mk h sig) v site) ->
  sig' = WriteMap sig vto (sig vfrom) ->
  (forall v, ~ConcreteStatePointsTo (State_Mk h sig') v site).
Proof.
  intros. unfold not in *.
  intros.
  unfold ConcreteStatePointsTo in *.
  rewrite H0 in *.
  unfold WriteMap in H1.
  simpl in *.
  destruct (vto =? v) eqn:vcase; subst.
  - specialize H with vfrom. contradiction.
  - specialize H with v. contradiction. 
Qed.

Lemma AllocBeginsNewPointsTo : forall {site : AllocSite} {v : Var} {s1 s2 : State},
  Step (Alloc site v) s1 Skip s2 -> ConcreteStatePointsTo s2 v site.
Proof.
  intros.
  inversion H; subst.
  unfold ConcreteStatePointsTo. exists addr.
  unfold State_valuation. unfold WriteMap. simpl.
  rewrite (Nat.eqb_refl v). rewrite (Nat.eqb_refl addr). simpl. auto.
Qed.

Lemma AllocKillsOldPointsTo : forall {site site' : AllocSite} {v : Var} {s1 s2 : State},
  Step (Alloc site v) s1 Skip s2 ->
  site <> site' -> ~ConcreteStatePointsTo s2 v site'.
Proof.
  unfold not. intros. apply H0.
  inversion H; subst; clear H.
  unfold ConcreteStatePointsTo in *. destruct H1.
  unfold State_valuation in H. unfold WriteMap in H.
  rewrite (Nat.eqb_refl v) in H. destruct H. injection H as H. subst.
  simpl in *. rewrite (Nat.eqb_refl x) in H1. simpl HeapObj_site in H1.
  exact H1.
Qed.

Lemma AssignMovesPointsTo : forall {vto vfrom : Var} {site : AllocSite} {s1 s2 : State},
  Step (Assign vto vfrom) s1 Skip s2 ->
  ConcreteStatePointsTo s1 vfrom site ->
  ConcreteStatePointsTo s2 vto site.
Proof.
  intros.
  inversion H. subst. clear H.
  unfold ConcreteStatePointsTo in *.
  destruct H0 as [addr]. exists addr. destruct H.
  unfold State_valuation in *. unfold WriteMap in *.
  rewrite (Nat.eqb_refl vto). simpl in *.
  split; assumption.
Qed.

Lemma AssignKillsOldVTo : forall {vto vfrom : Var} {site site' : AllocSite} {s1 s2 : State},
  Step (Assign vto vfrom) s1 Skip s2 ->
  ConcreteStatePointsTo s1 vfrom site ->
  site <> site'
  -> ~ConcreteStatePointsTo s2 vto site'.
Proof.
  unfold not. intros.
  apply H1. clear H1.
  inversion H; subst; clear H.
  unfold ConcreteStatePointsTo in *. unfold State_valuation in *.
  unfold State_heap in *. unfold WriteMap in *.
  destruct H0. destruct H. destruct H2. destruct H1.
  rewrite (Nat.eqb_refl vto) in H1.
  rewrite H in *. injection H1 as H1. rewrite H1 in *.
  destruct (h x0); subst.
  - reflexivity.
  - contradiction.
Qed.

Lemma SingletonNotEmpty : forall {U : Type} {x : U},
  Singleton U x <> Empty_set U.
Proof.
  unfold not. intros.
  assert (In U (Singleton U x) x) as H1. { constructor. }
  rewrite H in H1. inversion H1.
Qed.

Lemma SingletonNotEmptyAlt : forall {U : Type} {x : U},
  Empty_set U <> Singleton U x.
Proof.
  intros.
  pose proof (@SingletonNotEmpty U x). auto.
Qed.

(* Due to Control being a dependent type, proving the below 2 theorems turns
  out to be quite non-trivial. *)
Lemma AssignStepToSkip : forall {vto vfrom : Var} {s1 s2 : State} {c2},
  Step (Assign vto vfrom) s1 c2 s2 -> c2 = Skip.
Proof.
  intros.
  inversion H. subst.
  inversion_sigma H2; subst.
  assert (H2_ = eq_refl) as H2eq. { apply UIP. }
  rewrite H2eq. reflexivity.
Qed.

Lemma AllocStepToSkip :
  forall {vto : Var} {site : AllocSite} {s1 s2 : State} {c2},
  Step (Alloc vto site) s1 c2 s2 -> c2 = Skip.
Proof.
  intros.
  inversion H. subst.
  inversion_sigma H4; subst.
  assert (H4_ = eq_refl) as H2eq. { apply UIP. }
  rewrite H2eq. reflexivity.
Qed.

(* Convert a lemma about Step to one about StepClosure. *)
Lemma AssignStepLemmaClosure :
  forall {vto vfrom : Var} {s1 s2 : State} {con : Prop},
  (Step (Assign vto vfrom) s1 Skip s2 -> con) ->
  (StepClosure (Assign vto vfrom) s1 Skip s2 -> con).
Proof.
  intros.
  apply H. clear H.
  dependent induction H0.
  inversion H; subst.
  pose proof (AssignStepToSkip H). subst.
  apply SkipDoesNothingClosure2 in H0 as H0'.
  destruct H0'. subst.
  assumption.
Qed.

Lemma AllocStepLemmaClosure :
  forall {vto vfrom : Var} {s1 s2 : State} {con : Prop},
  (Step (Alloc vto vfrom) s1 Skip s2 -> con) ->
  (StepClosure (Alloc vto vfrom) s1 Skip s2 -> con).
Proof.
  intros.
  apply H. clear H.
  dependent induction H0. { apply SingletonNotEmpty in x0. contradiction. }
  inversion H; subst.
  pose proof (AllocStepToSkip H). subst.
  apply SkipDoesNothingClosure2 in H0 as H0'.
  destruct H0'. subst.
  assumption.
Qed.

(* Head indicates the next instruction to be run for a Control. *)
Inductive Head : forall {isic isih}, Control isic -> Control isih -> Prop :=
| Head_SeqL : forall
    {sic1 sic2 sih} {c1 : Control sic1}
    {c2 : Control sic2} {h : Control sih}
    (dis : Disjoint _ sic1 sic2),
    Head c1 h -> Head (Seq c1 c2 dis) h
| Head_SeqR : forall {sic} {c : Control sic},
    Head (SkipLSeq c) Skip
| Head_Assign : forall {vto vfrom},
    Head (Assign vto vfrom) (Assign vto vfrom)
| Head_Alloc : forall {site} {vto},
    Head (Alloc site vto) (Alloc site vto)
| Head_Skip : Head Skip Skip.

(* This is the same as Step except state information is erased. 

   For LAlloc where a lack of state information still yields determinism,
   Succ always points to one Control.
   For more complicated languages, multiple results are possible.
 *)
Inductive Succ : forall {si sisucc}, Control si -> Control sisucc -> Prop :=
(* Skips are ignored by successor *)
| Succ_SeqL : forall
    {sic1 sic1' sic2}
    {c1 : Control sic1} {c1' : Control sic1'} {c2 : Control sic2}
    (dis : Disjoint _ sic1 sic2)
    (dis' : Disjoint _ sic1' sic2),
    Succ c1 c1' -> Succ (Seq c1 c2 dis) (Seq c1' c2 dis')
| Succ_SeqR : forall {sic sic'} {c : Control sic} {c' : Control sic'},
    Succ (SkipLSeq c) c
| Succ_Alloc : forall {site} {vto}, Succ (Alloc site vto) Skip
| Succ_Assign : forall {vfrom} {vto}, Succ (Assign vto vfrom) Skip.

Inductive SuccClosure : forall {sia sib},
  Control sia -> Control sib -> Prop :=
| SuccClosure_Refl : forall {si} {c : Control si},
  SuccClosure c c
| SuccClosure_Step : forall
    {sia sib sic}
    {c1 : Control sia} {c2 : Control sib} {c3 : Control sic},
    Succ c1 c2 ->
    SuccClosure c2 c3 ->
    SuccClosure c1 c3.

Definition PointsToStatus := (Var * AllocSite) -> Prop.

Definition EmptyStatus : PointsToStatus := fun _ => False.

(* AFPT is an attempt to describe a transition between two
   controls without relying on any state information.
   
   One may think of it as a combination of StepClosure and 
   ConcreteStatePointsTo except state is erased. *)
Inductive AbstractFlowPointsTo : forall {si1 si2}, PointsToStatus -> Control si1 -> Control si2 -> PointsToStatus -> Prop :=
| AFPT_Reflect : forall {si} {c : Control si} {pts : PointsToStatus}, 
    AbstractFlowPointsTo pts c c pts
| AFPT_Trans : forall
    {si1 si2 si3} {pts1 pts2 pts3}
    {c1 : Control si1} {c2 : Control si2} {c3 : Control si3},
    AbstractFlowPointsTo pts1 c1 c2 pts2 ->
    AbstractFlowPointsTo pts2 c2 c3 pts3 ->
    AbstractFlowPointsTo pts1 c1 c3 pts3
| AFPT_Skip : forall
    {pts : PointsToStatus}
    {si1 si2}
    {c1 : Control si1} {c2 : Control si2},
    Succ c1 c2 ->
    Head c1 Skip ->
    AbstractFlowPointsTo pts c1 c2 pts
| AFPT_Alloc : forall
    {si1 si2}
    {c1 : Control si1} {c2 : Control si2}
    {site site1} {v v1}
    {pts1 pts2 : PointsToStatus},
    Succ c1 c2 ->
    Head c1 (Alloc site v) ->
    pts2 (v, site) ->
    (v <> v1 -> pts1 (v1, site1) -> pts2 (v1, site1)) ->
    AbstractFlowPointsTo pts1 c1 c2 pts2
| AFPT_Move : forall
    {si1 si2}
    {c1 : Control si1} {c2 : Control si2}
    {site site1} {vfrom vto v1}
    {pts1 pts2 : PointsToStatus},
    Succ c1 c2 ->
    Head c1 (Assign vto vfrom) ->
    pts1 (vfrom, site) ->
    pts2 (vto, site) ->
    (vto <> v1 -> pts1 (v1, site1) -> pts2 (v1, site1)) ->
    AbstractFlowPointsTo pts1 c1 c2 pts2.

Lemma StepStateErasure : forall
    {si1 si2} {c1 : Control si1} {c2 : Control si2}
    {s1 s2},
    Step c1 s1 c2 s2 -> Succ c1 c2.
Proof.
  intros.
  dependent induction H; econstructor; eassumption.
Qed.

Lemma StepClosureStateErasure : forall
    {si1 si2} {c1 : Control si1} {c2 : Control si2}
    {s1 s2},
    StepClosure c1 s1 c2 s2 -> SuccClosure c1 c2.
Proof.
  intros.
  dependent induction H.
  { constructor. }
  apply StepStateErasure in H.
  econstructor; eassumption.
Qed.

Lemma SingletonInjection : forall {A} {x y : A},
  Singleton A x = Singleton A y -> x = y.
Proof.
  intros.
  assert (In _ (Singleton _ x) y) as H0.
  { rewrite H. econstructor. }
  inversion H0.
  reflexivity.
Qed.

Lemma HeadContainsAlloc : forall
  {si} {c : Control si} {vto} {site},
  Head c (Alloc site vto) -> PTAlloc c vto site.
Proof.
  intros.
  dependent induction H.
  - specialize IHHead with vto site.
    apply PTAllocComposition. left.
    apply IHHead; reflexivity.
  - apply SingletonNotEmptyAlt in x0. contradiction.
  - apply SingletonNotEmptyAlt in x0. contradiction.
  - apply SingletonInjection in x0 as x1.
    rewrite x1. rewrite x1 in x.
    apply JMeq_eq in x.
    rewrite x. constructor; reflexivity.
  - apply SingletonNotEmptyAlt in x0.
    contradiction.
Qed.

(* NOTE: At this point, my supervisor intervened and suggests that I prove the soundness of Andersen in LAlloc from a different angle. Since we have been defining Andersen as a sort of step closure, it is known from experience to be very hard to prove. Instead, we will redefine Andersen as a stepping analysis, to avoid the logical overhead of dealing with transitive closure. *)

(* Analysis comes with its own abstract state, which we've actually defined earlier already: PointsToStatus. At least not everything before this is useless. *)

Definition StatusMove
  (pts : PointsToStatus)
  (vfrom : Var) (vto : Var)
   : PointsToStatus :=
    fun p =>
    match p with (v, site) =>
      if Nat.eqb v vto then
        pts (vfrom, site) \/ pts (vto, site)
      else
        pts (v, site)
    end.

Definition StatusAlloc
  (pts : PointsToStatus)
  (asite : AllocSite) (vto : Var)
   : PointsToStatus :=
    fun p =>
    match p with (v, site) =>
      if (andb (Nat.eqb v vto) (Nat.eqb site asite)) then True
      else pts (v, site)
    end.

Definition ConcreteAnalysis (s : State) : PointsToStatus :=
  fun p =>
  exists val,
  State_valuation s (fst p) = Some val /\
    match State_heap s val with
    | Some hObj => HeapObj_site hObj = snd p
    | None => False
    end.

Definition Overapprox (pts1 pts2 : PointsToStatus) : Prop :=
  forall p, pts1 p -> pts2 p.

Inductive AndersenStep : forall {si_a si_b},
  Control si_a -> PointsToStatus -> Control si_b -> PointsToStatus -> Prop :=
| AStep_SeqL : forall
  {si1 si2 si1' : Ensemble AllocSite}
  {pts pts' : PointsToStatus}
  {c1 : Control si1} {c2 : Control si2} {c1' : Control si1'}
  (dis : Disjoint _ si1 si2)
  (dis' : Disjoint _ si1' si2),
  AndersenStep c1 pts c1' pts' ->
  AndersenStep (Seq c1 c2 dis) pts (Seq c1' c2 dis') pts'
| AStep_SeqR : forall
  {si} {c : Control si} {pts : PointsToStatus},
  AndersenStep (SkipLSeq c) pts c pts
| AStep_Assign : forall
  {pts pts'} {vfrom vto},
  pts' = StatusMove pts vfrom vto ->
  AndersenStep (Assign vto vfrom) pts Skip pts'
| AStep_Alloc : forall
  {pts pts'} {vto} {site},
  pts' = StatusAlloc pts site vto ->
  AndersenStep (Alloc site vto) pts Skip pts'.

Ltac inject_existT H :=
  inversion_sigma H;
  match goal with
  | [ H1 : _ = _ |- _ ] =>
      let Hname := fresh H "eq" in
      assert (Hname : H1 = eq_refl) by apply UIP;
      rewrite Hname in *;
      simpl in *
  end.

Ltac inject_all_existT :=
  repeat match goal with
  | H : existT _ _ _ = existT _ _ _ |- _ =>
      inject_existT H; subst
  end.

Lemma AndersenStepErasure : forall
  {si1 si2} {c1 : Control si1} {c2 : Control si2}
  {pts1 pts2},
  AndersenStep c1 pts1 c2 pts2 -> Succ c1 c2.
Proof.
  intros.
  dependent induction H;
  econstructor;
  eassumption.
Qed.

Lemma AndersenStepRestoration : forall
  {si1 si2} {c1 : Control si1} {c2 : Control si2},
  Succ c1 c2 ->
  forall pts1, exists pts2,
  AndersenStep c1 pts1 c2 pts2.
Proof.
  intros.
  dependent induction H.
  - specialize IHSucc with pts1. destruct IHSucc as [pts2].
    exists pts2. constructor. assumption.
  - exists pts1. constructor.
  - exists (StatusAlloc pts1 site vto).
    constructor. reflexivity.
  - exists (StatusMove pts1 vfrom vto).
    constructor. reflexivity.
Qed.
  
Definition AndersenStepHoare {sih}
  (ch : Control sih) (f : PointsToStatus -> PointsToStatus) : Prop :=
  forall
    {si1 si2} {c1 : Control si1} {c2 : Control si2}
    {pts1 pts2 : PointsToStatus},
  Head c1 ch ->
  AndersenStep c1 pts1 c2 pts2 ->
  f pts1 = pts2.

Lemma ToSkipLSeq : forall
  {si} {c : Control si} {dis : Disjoint _ (Empty_set AllocSite) si},
  Seq Skip c dis = SkipLSeq c.
Proof.
  intros.
  unfold SkipLSeq.
  assert (dis = disjointEmptyL (si)) as Hdis.
  { apply proof_irrelevance. }
  rewrite Hdis. reflexivity.
Qed.

Lemma AndersenInvertSeqR : forall
  {si} {c : Control si} {pts : PointsToStatus}
  {dis : Disjoint _ (Empty_set AllocSite) si},
  AndersenStep (Seq Skip c dis) pts c pts.
Proof.
  intros.
  rewrite ToSkipLSeq.
  constructor.
Qed.

Lemma AndersenStepSkip : 
  AndersenStepHoare
    Skip
    (fun pts1 => pts1).
Proof.
  unfold AndersenStepHoare.
  intros.
  dependent induction H0; try reflexivity;
  inversion H; subst; inject_all_existT.
  - apply IHAndersenStep in H4. assumption.
  - apply IHAndersenStep. constructor.
Qed.

Lemma AndersenStepAssign : forall {vfrom vto : Var},
  AndersenStepHoare
    (Assign vto vfrom)
    (fun pts1 => StatusMove pts1 vfrom vto).
Proof.
  unfold AndersenStepHoare.
  intros.
  dependent induction H0;
  inversion H; subst; inject_all_existT; crush.
  - inversion H3.
Qed.

Lemma AndersenStepAlloc : forall {site : AllocSite} {vto : Var},
  AndersenStepHoare
    (Alloc site vto)
    (fun pts1 => StatusAlloc pts1 site vto).
Proof.
  unfold AndersenStepHoare.
  intros.
  dependent induction H0;
  inversion H; subst; inject_all_existT; crush.
  - inversion H3.
Qed.

Lemma AndersenStepHoareRestore : forall
  {si1 sih sis}
  {c1 : Control si1} {ch : Control sih} {cs : Control sis}
  {f : PointsToStatus -> PointsToStatus},
  AndersenStepHoare ch f ->
  Head c1 ch ->
  Succ c1 cs ->
  forall pts, AndersenStep c1 pts cs (f pts).
Proof.
  unfold AndersenStepHoare.
  intros.
  eapply AndersenStepRestoration in H1.
  destruct H1 as [pts2].
  eapply H in H1 as H2.
  - rewrite <- H2 in H1. exact H1.
  - assumption.
Qed.

Lemma AndersenStepIgnoresSucc : forall
  {si1 si1' si2 si2' sih}
  {c1 : Control si1} {c1' : Control si1'}
  {c2 : Control si2} {c2' : Control si2'}
  {ch : Control sih} {pts pts' : PointsToStatus},
  Head c1 ch ->
  Head c2 ch ->
  Succ c1 c1' ->
  Succ c2 c2' ->
  AndersenStep c1 pts c1' pts' ->
  AndersenStep c2 pts c2' pts'.
Proof.
  intros.
  dependent induction H3.
  - inversion H;
    subst; inject_all_existT;
    apply AndersenStepErasure in H3.
    * subst. apply IHAndersenStep in H7; assumption.
    * subst. pose proof (Head_Skip) as HSkip.
      apply IHAndersenStep in HSkip; assumption.
  - inversion H; subst;
    inject_all_existT;
    epose proof (AndersenStepHoareRestore AndersenStepSkip) as HSkip;
    eapply HSkip; try assumption.
    * inversion H6; subst; inject_all_existT. assumption.
  - inversion H; subst;
    inject_all_existT.
    epose proof (AndersenStepHoareRestore AndersenStepAssign) as HAssign;
    eapply HAssign; try assumption.
  - inversion H; subst;
    inject_all_existT.
    epose proof (AndersenStepHoareRestore AndersenStepAlloc) as HAlloc;
    eapply HAlloc; try assumption.
Qed.

Lemma AlwaysHead : forall {si} {c : Control si},
  exists si2 (c2 : Control si2),
  Head c c2.
Proof.
  intros.
  dependent induction c.
  - exists (Empty_set AllocSite). exists Skip.
    constructor.
  - exists (Empty_set AllocSite). exists (Assign v v0). 
    constructor.
  - exists (Singleton _ l). exists (Alloc l vto).
    constructor.
  - destruct IHc1 as [si3 [c3]].
    eexists. eexists. constructor.
    exact H.
Qed.

(* Unfortunately, I have gotten stuck trying to prove the below fact, which has been leading me to nothing but dead ends. We are certain that in our imperative programming system, recursive syntactic definition of a program is not allowed. As such, we will pose this as an axiom.

It would be ideal to try and prove this without requiring defining such an axiom. But this is rather pedantic and not relevant to our domain of interest. *)

Axiom no_recursion :
  forall (si1' si2 : Ensemble AllocSite)
         (c1' : Control si1') (c2 : Control si2)
         (dis : Disjoint _ si1' si2)
         (H5_ : Union _ si1' si2 = si2),
    eq_rect _ (fun s2 => Control s2)
            (Seq c1' c2 dis) si2 H5_ <> c2.

Lemma NoSuccForSkip : forall
  {si1' si2} {c1' : Control si1'} {c2 : Control si2}
  {dis : Disjoint _ si1' si2},
  Succ (SkipLSeq c2) (Seq c1' c2 dis) -> False.
Proof.
  intros.
  inversion H; subst; inject_all_existT.
  - inversion H3.
  - inversion_sigma H5; subst.
    apply no_recursion in H5_0.
    contradiction.
Qed.

Lemma SuccSeqTrim : forall
  {si1 si2 si1'}
  {c1 : Control si1} {c2 : Control si2} {c1' : Control si1'}
  {dis : Disjoint _ si1 si2} {dis' : Disjoint _ si1' si2},
  Succ (Seq c1 c2 dis) (Seq c1' c2 dis') ->
  Succ c1 c1'.
Proof.
  intros.
  inversion H; subst; inject_all_existT.
  - assumption.
  - inversion H; subst; inject_all_existT.
    + exact H6.
    + erewrite ToSkipLSeq in H. eapply NoSuccForSkip in H. 
      contradiction.
Qed.

Lemma AndersenStepPartial : forall
  {si_a si_a' si_b}
  {c1 : Control si_a} {c1' : Control si_a'} {c2 : Control si_b}
  {pts1 pts2 : PointsToStatus}
  {dis : Disjoint _ si_a si_b}
  {dis' : Disjoint _ si_a' si_b},
  AndersenStep (Seq c1 c2 dis) pts1 (Seq c1' c2 dis') pts2 ->
  AndersenStep c1 pts1 c1' pts2.
Proof.
  intros.
  assert (
    exists (si_h : Ensemble AllocSite) (ch : Control si_h),
      (Head c1 ch) /\ (Head (Seq c1 c2 dis) ch)) as Hch.
  2: {
    destruct Hch as [si_h [ch]].
    destruct H0. 
    eapply AndersenStepIgnoresSucc.
    5: { exact H. }
    - exact H1.
    - exact H0.
    - apply AndersenStepErasure in H. assumption.
    - apply AndersenStepErasure in H. apply SuccSeqTrim in H. assumption.
  }
  1: {
    pose proof (@AlwaysHead) as Hhead. specialize 
    Hhead with si_a c1.
    destruct Hhead as [si3 [c3 Hhead]].
    eexists si3. eexists.
    split.
    - exact Hhead.
    - constructor. exact Hhead.
  }
Qed.
  
Theorem AndersenStepSound : forall
  {si_a si_b} {c1 : Control si_a} {c2 : Control si_b} {s1 s2} {pts1 pts2},
  Overapprox (ConcreteAnalysis s1) pts1 ->
  Step c1 s1 c2 s2 ->
  AndersenStep c1 pts1 c2 pts2 ->
  Overapprox (ConcreteAnalysis s2) pts2.
Proof.
  intros.
  dependent induction H0.
  - eapply AndersenStepPartial in H1.
    eapply IHStep; assumption.
  - assert (pts1 = pts2) as Heq. {
      eapply AndersenStepSkip.
      2: { exact H1. }
      constructor. constructor.
    }
    subst. assumption.
  - assert (StatusMove pts1 vfrom vto = pts2) as Heq. {
      eapply AndersenStepAssign.
      2: { exact H1. }
      constructor.
    }
    subst. unfold StatusMove. unfold Overapprox in *. intros.
    destruct p as [v site].
    destruct (v =? vto) eqn:vcase.
    + left. specialize H with (vfrom, site).
      erewrite Nat.eqb_eq in vcase. subst.
      apply H.
      unfold ConcreteAnalysis in *.
      destruct H0 as [val]. exists val.
      destruct H0. split.
      * rewrite <- H0.
        unfold WriteMap. simpl in *. rewrite Nat.eqb_refl. 
        reflexivity.
      * unfold WriteMap in *. simpl in *. assumption.
    + specialize H with (v, site).
      apply H. unfold ConcreteAnalysis in *.
      destruct H0 as [val]. exists val.
      unfold WriteMap in *.
      simpl in *. rewrite Nat.eqb_sym in vcase.
      rewrite vcase in H0. assumption.
  - assert (StatusAlloc pts1 l vto = pts2) as Heq. {
      eapply AndersenStepAlloc.
      2: { exact H3. }
      constructor.
    }
    subst. unfold StatusAlloc. unfold Overapprox in *.
    intros.
    destruct p as [v site].
    unfold ConcreteAnalysis in *.
    unfold WriteMap in *. simpl in *.
    destruct (andb (v =? vto) (site =? l)) eqn:case. { trivial. }
    specialize H with (v, site).
    apply H.
    destruct H1 as [val].
    simpl in *.

    (* In the two contradictions below, we show that v =? vto and site =? l
       cannot have XOR relation. *)
    destruct (vto =? v) eqn:vcase. {
      destruct H1.
      injection H1 as Hav. rewrite <- Nat.eqb_eq in Hav.
      rewrite Hav in H2. simpl in *. rewrite <- Nat.eqb_eq in H2.
      rewrite Nat.eqb_sym in vcase. rewrite Nat.eqb_sym in H2.
      rewrite vcase in case. rewrite H2 in case.
      simpl in case. discriminate.
    }
    destruct (addr =? val) eqn:addrcase. {
      destruct H1.
      rewrite Nat.eqb_eq in addrcase. subst.
      unfold Unallocated in *.
      destruct H0 as [HUn1 HUn2].
      specialize HUn2 with v.
      contradiction.
    }

    exists val. assumption.
Qed.
