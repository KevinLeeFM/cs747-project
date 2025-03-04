import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint

-- # Syntax and semantics of LAlloc

abbrev Var := Nat
abbrev Addr := Nat
abbrev Val := Addr
abbrev AllocSite := Nat

inductive PrimControl : Type where
  | skip : PrimControl
  | assign (vto : Var) (vfrom : Var) : PrimControl
  | alloc (l: AllocSite) (vto : Var) : PrimControl
  | seq (fst : PrimControl) (snd : PrimControl) : PrimControl

open PrimControl

@[simp]
def sitesOf : PrimControl → Set AllocSite
  | skip => ∅
  | assign _ _ => ∅
  | alloc l _ => {l}
  | seq fst snd => sitesOf fst ∪ sitesOf snd

inductive WellFormed : PrimControl → Prop where
  | skipWF : WellFormed skip
  | assignWF {vto vfrom} : WellFormed (assign vto vfrom)
  | allocWF {l vto} : WellFormed (alloc l vto)
  | seqWF {fst snd} :
      WellFormed fst →
      WellFormed snd →
      Disjoint (sitesOf fst) (sitesOf snd) →
      WellFormed (seq fst snd)

open WellFormed

structure WFControl : Type where
  prim : PrimControl
  wf : WellFormed prim

structure HeapObj : Type where
  val : Option Val
  id : AllocSite

abbrev Heap := Addr → Option HeapObj
abbrev Stack := Var → Option Val

structure State : Type where
  H : Heap
  σ : Stack

abbrev StepState := WFControl × State

@[simp]
def emptyState : State := ⟨fun _ => none, fun _ => none⟩

@[simp]
def writeMap {β} (map : Var → β) (k : Var) (v : β) : Var → β :=
  fun k' => if k = k' then v else map k'

@[simp]
def unallocated (h : Heap) (addr : Addr) : Prop := h addr = none

-- lemma stepPreservesWF : ∀ {c1 c2 c1' s s'},
--   WellFormed c1 → Step (c1, s) (c1', s') → WellFormed c1'

-- All leaves are automatically well-formed
@[simp]
def skipWFControl : WFControl := ⟨skip, skipWF⟩
@[simp]
def assignWFControl (vto : Var) (vfrom : Var) : WFControl := ⟨assign vto vfrom, assignWF⟩
@[simp]
def allocWFControl (l : AllocSite) (vto : Var) : WFControl := ⟨alloc l vto, allocWF⟩

-- To construct a well-formed sequence, we need to supply a proof that the sites of the two sub-commands are disjoint
@[simp]
def wfToControl {c} (wf : WellFormed c) : WFControl := ⟨c, wf⟩

lemma skipLSeqWF {c} (wf : WellFormed c) : WellFormed (seq skip c) := by
  apply seqWF
  . exact skipWF
  . exact wf
  . simp

-- Small-step semantics of Lalloc
inductive Step : StepState → StepState → Prop where
  | seqL : ∀ {c1 c2 c1' : WFControl} {s s' : State},
      (wf_c1c2 : WellFormed (seq c1.prim c2.prim)) →
      (wf_c1'c2 : WellFormed (seq c1'.prim c2.prim)) →
      Step (c1, s) (c1', s') →
      Step (wfToControl wf_c1c2, s) (wfToControl wf_c1'c2, s')
  | seqR : ∀ {c : WFControl} {s : State},
      Step (wfToControl (skipLSeqWF c.wf), s) (c, s)
  | assign : ∀ {vto vfrom : Var} {h : Heap} {σ σ' : Stack},
      σ' = writeMap σ vto (σ vfrom) →
      Step (assignWFControl vto vfrom, ⟨h, σ⟩) (skipWFControl, ⟨h, σ'⟩)
  | alloc : ∀ {l : AllocSite} {addr : Addr} {vto : Var} {h h' : Heap} {σ σ' : Stack},
      unallocated h addr →
      h' = writeMap h addr (some ⟨none, l⟩) →
      σ' = writeMap σ vto addr →
      Step (allocWFControl l vto, ⟨h, σ⟩) (skipWFControl, ⟨h', σ'⟩)

inductive StepClosure : StepState → StepState → Prop where
  | refl : ∀ {st}, StepClosure st st
  | step : ∀ {st st' st''}, Step st st' → StepClosure st' st'' → StepClosure st st''

-- # Concrete pointer analysis

@[simp]
def reachable (program : WFControl) (state : State) : Prop :=
  ∃ program', StepClosure (program, emptyState) (program', state)

@[simp]
def concretePointsTo (program : WFControl) (v : Var) (site : AllocSite) : Prop :=
  ∃ (S : State) (p : AllocSite),
    reachable program S →
    S.σ v = p ->
    match (S.H p) with
      | none => false
      | some hObj => hObj.id = site

-- # Abstract pointer analysis

abbrev PTAnalysis := WFControl → Var → AllocSite → Prop

@[simp]
def soundApprox (concrete : PTAnalysis) (abstract : PTAnalysis) : Prop :=
  ∀ {p : WFControl} {v : Var} {site : AllocSite},
    concrete p v site -> abstract p v site

infix:51 " ≼ " => soundApprox

-- ## Andersen-style points-to analysis

def PTAlloc (p : WFControl) (var : Var) (site : AllocSite) : Prop :=
  match p.prim with
  | alloc l vto => vto = var ∧ l = site
  | seq fst snd => PTAlloc (wfToControl fst.wf) var site ∨ PTAlloc (wfToControl snd.wf) var site
  | _ => false

inductive AndersenPointsTo : PTAnalysis where
  | alloc : ∀ {var : Var} {site : AllocSite}
