import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint

-- # Syntax and semantics of LAlloc

abbrev Var := Nat
abbrev Addr := Nat
abbrev Val := Addr
abbrev AllocSite := Nat

inductive Control : Set AllocSite → Type where
  | skip : Control ∅
  | assign (vto : Var) (vfrom : Var) : Control ∅
  | alloc (l : AllocSite) (vto : Var) : Control {l}
  | seq {sfst ssnd : Set AllocSite} :
      Disjoint sfst ssnd →
      Control sfst →
      Control ssnd →
      Control (sfst ∪ ssnd)

open Control

structure HeapObj : Type where
  val : Option Val
  id : AllocSite

abbrev Heap := Addr → Option HeapObj
abbrev Stack := Var → Option Val

structure State : Type where
  H : Heap
  σ : Stack

structure StepState (site : Set AllocSite) : Type where
  control : Control site
  state : State

@[simp]
def emptyState : State := ⟨fun _ => none, fun _ => none⟩

def writeMap {β} (map : Var → β) (k : Var) (v : β) : Var → β :=
  fun k' => if k = k' then v else map k'

@[simp]
def unallocated (h : Heap) (addr : Addr) : Prop := h addr = none

-- lemma stepPreservesWF : ∀ {c1 c2 c1' s s'},
--   WellFormed c1 → Step (c1, s) (c1', s') → WellFormed c1'

@[simp]
def skipLSeq {si} (c : Control si) : Control si := by
  have d : Disjoint ∅ si := by simp
  have exa : Control (∅ ∪ si) := seq d skip c
  simp at exa
  exact exa

-- Small-step semantics of Lalloc
inductive Step : ∀ {si1 si2}, StepState si1 → StepState si2 → Prop where
  | seqL : ∀
    {si1 si2 si1'}
    {c1 : Control si1} {c2 : Control si2} {c1' : Control si1'}
    {s s' : State},
      (dis : Disjoint si1 si2) →
      (dis' : Disjoint si1' si2) →
      Step ⟨c1, s⟩ ⟨c1', s'⟩ →
      Step ⟨seq dis c1 c2, s⟩ ⟨seq dis' c1' c2, s'⟩
  | seqR : ∀ {si} {c : Control si} {s : State},
      Step ⟨skipLSeq c, s⟩ ⟨c, s⟩
  | assign : ∀ {vto vfrom : Var} {h : Heap} {σ σ' : Stack},
      σ' = writeMap σ vto (σ vfrom) →
      Step ⟨assign vto vfrom, ⟨h, σ⟩⟩ ⟨skip, ⟨h, σ'⟩⟩
  | alloc : ∀ {l : AllocSite} {addr : Addr} {vto : Var} {h h' : Heap} {σ σ' : Stack},
      unallocated h addr →
      h' = writeMap h addr (some ⟨none, l⟩) →
      σ' = writeMap σ vto addr →
      Step ⟨alloc l vto, ⟨h, σ⟩⟩ ⟨skip, ⟨h', σ'⟩⟩

inductive StepClosure : ∀ {si1 si2}, StepState si1 → StepState si2 → Prop where
  | refl : ∀ {st}, StepClosure st st
  | step : ∀ {st st' st''}, Step st st' → StepClosure st' st'' → StepClosure st st''

-- # Concrete pointer analysis

def reachable {si} (program : Control si) (state : State) : Prop :=
  ∃ (si' : Set AllocSite) (program' : Control si'), StepClosure ⟨program, emptyState⟩ ⟨program', state⟩

def ConcretePointsTo {si} (program : Control si) (v : Var) (site : AllocSite) : Prop :=
  ∃ (S : State) (p : AllocSite),
    reachable program S ∧
    S.σ v = p ∧
    match (S.H p) with
      | none => false
      | some hObj => hObj.id = site

-- # Abstract pointer analysis

abbrev PTAnalysis := ∀ {si}, Control si → Var → AllocSite → Prop

@[simp]
def soundApprox (concrete : PTAnalysis) (abstract : PTAnalysis) : Prop :=
  ∀ {si} {p : Control si} {v : Var} {site : AllocSite},
    concrete p v site -> abstract p v site

infix:51 " ≼ " => soundApprox

-- ## Generally useful relations

def PTAlloc {si} (p : Control si) (var : Var) (site : AllocSite) : Prop :=
  match p with
  | alloc l vto => vto = var ∧ l = site
  | seq _ fst snd => PTAlloc fst var site ∨ PTAlloc snd var site
  | _ => false

def PTMove {si} (p : Control si) (vto vfrom : Var) : Prop :=
  match p with
  | assign vto' vfrom' => vto = vto' ∧ vfrom = vfrom'
  | seq _ fst snd => PTMove fst vto vfrom ∨ PTMove snd vto vfrom
  | _ => false

-- ## Andersen-style points-to analysis

-- This is based on the Andersen-style points-to analysis from Smaragdakis et al.
-- Any rules related to inter-procedure and field sensitivity are omitted for Lalloc
inductive AndersenPointsTo : PTAnalysis where
  | alloc : ∀ {si} {var : Var} {site : AllocSite} {p : Control si},
      PTAlloc p var site → AndersenPointsTo p var site
  | move : ∀ {si} {vto vfrom : Var} {site : AllocSite} {p : Control si},
      PTMove p vto vfrom → AndersenPointsTo p vfrom site → AndersenPointsTo p vto site

theorem andersenSound : ConcretePointsTo ≼ AndersenPointsTo := by
  simp; intro si p v site con
  induction p with
  | skip =>
    have ncon : ¬ (ConcretePointsTo skip v site) := by
      simp [ConcretePointsTo]
      intro s reach
      simp [reachable] at reach
      