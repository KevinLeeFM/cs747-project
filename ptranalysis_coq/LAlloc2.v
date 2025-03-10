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
This is to enforce unique AllocSites when composing statements together.

The Var set is the set of variables that are written to by the control.
They are present to enforce SSA encoding.
*)
Inductive Control : Ensemble AllocSite -> Ensemble Var -> Type :=
| Skip : Control (Empty_set _) (Empty_set _)
| Assign (vto : Var) (vfrom : Var) : Control (Empty_set _) (Singleton _ vto)
| Alloc (l : AllocSite) (vto : Var) : Control (Singleton _ l) (Empty_set _)
| Seq : forall {ss1 ss2} {sv1 sv2},
  Control ss1 sv1 -> Control ss2 sv2 ->
  Disjoint _ ss1 ss2 -> Disjoint _ sv1 sv2 ->
  Control (Union _ ss1 ss2) (Union _ sv1 sv2).

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

Definition SkipLSeq {ss} {sv} (c : Control ss sv)
  : Control
      (Union AllocSite (Empty_set AllocSite) ss)
      (Union AllocSite (Empty_set AllocSite) sv) := 
    Seq Skip c (disjointEmptyL ss) (disjointEmptyL sv).

Inductive Step : forall {ss1 ss2} {sv1 sv2},
  Control ss1 sv1 -> State -> Control ss2 sv2 -> State -> Prop :=
| Step_SeqL : forall
  {ss1 ss2 ss1' : Ensemble AllocSite}
  {sv1 sv2 sv1' : Ensemble Var}
  {s s' : State}
  {c1 : Control ss1 sv1} {c2 : Control ss2 sv2} {c1' : Control ss1' sv1'}
  (diss : Disjoint _ ss1 ss2)
  (diss' : Disjoint _ ss1' ss2)
  (disv : Disjoint _ sv1 sv2)
  (disv' : Disjoint _ sv1' sv2),
  Step c1 s c1' s' -> Step (Seq c1 c2 diss disv) s (Seq c1' c2 diss' disv') s'
| Step_SeqR : forall
  {ss} {sv} {c : Control ss sv} {s : State},
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

Inductive StepClosure : forall {ss1 ss2} {sv1 sv2},
  Control ss1 sv1 -> State -> Control ss2 sv2 -> State -> Prop :=
| StepClosure_Refl : forall {ss} {sv} {c : Control ss sv} {s : State},
  StepClosure c s c s
| StepClosure_Step : forall
  {ssa ssb ssc} {sva svb svc}
  {c1 : Control ssa sva} {c2 : Control ssb svb} {c3 : Control ssc svc}
  {s1 : State} {s2 : State} {s3 : State},
  Step c1 s1 c2 s2 ->
  StepClosure c2 s2 c3 s3 ->
  StepClosure c1 s1 c3 s3.

(* # Concrete pointer analysis *)

Definition PTAnalysis := forall ss sv, Control ss sv -> Var -> AllocSite -> Prop.

Definition Reachable {ss} {sv} (program : Control ss sv) (state : State) : Prop :=
  exists (ss' : Ensemble _) (sv' : Ensemble _) (program' : Control ss' sv'),
  StepClosure program EmptyState program' state.

Definition ConcretePointsTo
  [ss] [sv] (program : Control ss sv) (v : Var) (site : AllocSite) : Prop :=
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
    forall ss sv (program : Control ss sv) (v : Var) (site : AllocSite),
    concrete ss sv program v site -> abstract ss sv program v site.

(* Analysis relations *)

Fixpoint PTAlloc {ss} {sv} (p : Control ss sv) (var : Var) (site : AllocSite) : Prop :=
  match p with
  | Alloc l vto => var = vto /\ site = l
  | Seq fst snd _ _ => PTAlloc fst var site \/ PTAlloc snd var site
  | _ => False
  end.

Fixpoint PTMove {ss} {sv} (p : Control ss sv) (vto vfrom : Var) : Prop :=
  match p with
  | Assign vto' vfrom' => vto = vto' /\ vfrom = vfrom'
  | Seq fst snd _ _ => PTMove fst vto vfrom \/ PTMove snd vto vfrom
  | _ => False
  end.

(* Andersen-style points-to analysis *)

Inductive Andersen : PTAnalysis :=
| Andersen_Alloc : forall {ss} {sv} {var : Var} {site : AllocSite} {p : Control ss sv},
  PTAlloc p var site -> Andersen p var site
| Andersen_Move : forall {ss} {sv} {vto vfrom : Var} {site : AllocSite} {p : Control ss sv},
  PTMove p vto vfrom ->
  Andersen p vfrom site ->
  Andersen p vto site.

Inductive PTMoveClosure : forall {ss} {sv}, Control ss sv -> Var -> Var -> Prop :=
| PTMoveClosure_Refl :
    forall {ss} {sv} (p : Control ss sv) (v : Var), PTMoveClosure p v v
| PTMoveClosure_Trans :
    forall {ss} {sv} (p : Control ss sv) (vto vinter vfrom : Var),
    PTMoveClosure p vinter vfrom ->
    PTMove p vto vinter ->
    PTMoveClosure p vto vfrom.

(* Keep in mind that the alloc can even come AFTER or DURING the series of moves.
  This analysis is flow-insensitive, so it doesn't matter. *)
Lemma AndersenMoveClosureCarriesAlloc : forall {ss} {sv}
  {p : Control ss sv} {vto vfrom : Var} {site : AllocSite},
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

Fixpoint ConcreteMove {ss} {sv} (p : Control ss sv) (s : State) (vto vfrom : Var) : Prop :=
  match p with
  | Assign vto' vfrom' =>
      (* The first exists is a guard that only accepts Assigns which don't
         get 'stuck'. This shouldn't ever happen for Lalloc, but it's
         here to guard against future change in language spec. *)
      (exists s', StepClosure p s Skip s') /\ vto = vto' /\ vfrom = vfrom'
  | Seq fst snd _ _ =>
      ConcreteMove fst s vto vfrom \/ (
        (exists s', StepClosure fst s Skip s') /\
        (forall s', StepClosure fst s Skip s' -> ConcreteMove snd s' vto vfrom)
      )
  | _ => False
  end.

Inductive ConcreteMoveClosure :
  forall {ss} {sv}, Control ss sv -> State -> Var -> Var -> Prop :=
| ConcreteMoveClosure_Refl :
    forall {ss} {sv} {p : Control ss sv} {s : State} {v : Var},
    ConcreteMoveClosure p s v v
| ConcreteMoveClosure_Trans :
    forall {ss} {sv} {p : Control ss sv} {s : State} {vto vinter vfrom : Var},
    ConcreteMoveClosure p s vinter vfrom ->
    ConcreteMove p s vto vinter ->
    ConcreteMoveClosure p s vto vfrom.
  
Lemma ConcreteMoveClosureCarriesAlloc : forall {ss} {sv}
  {p : Control ss sv} {vto vfrom : Var} {site : AllocSite},
  ConcretePointsTo p vfrom site -> (
    
  )

Theorem Andersen_sound : SoundApprox ConcretePointsTo Andersen. Proof.
  unfold SoundApprox.
  intros.
  dependent induction program.
  4: {
    inversion H as [s]. destruct H0 as [site1]. destruct H0 as [H1]. destruct H0 as [H2].
  }
  - apply SkipNobodyPoints in H. contradiction.
