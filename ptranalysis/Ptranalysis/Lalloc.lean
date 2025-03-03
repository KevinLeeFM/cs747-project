import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint

-- # Syntax and semantics of LAlloc

abbrev Var := Nat
abbrev Addr := Nat
abbrev Val := Addr
abbrev AllocSite := Nat

inductive ControlPrim : Type where
  | skip : ControlPrim
  | assign (vto : Var) (vfrom : Var) : ControlPrim
  | alloc (l: AllocSite) (vto : Var) : ControlPrim
  | seq (fst : ControlPrim) (snd : ControlPrim) : ControlPrim

def sitesOf : ControlPrim -> Set AllocSite
  | ControlPrim.skip => ∅
  | ControlPrim.assign _ _ => ∅
  | ControlPrim.alloc l _ => {l}
  | ControlPrim.seq fst snd => sitesOf fst ∪ sitesOf snd

inductive WellFormed : ControlPrim -> Prop where
  | skipWF : WellFormed ControlPrim.skip
  | assignWF {vto vfrom} : WellFormed (ControlPrim.assign vto vfrom)
  | allocWF {l vto} : WellFormed (ControlPrim.alloc l vto)
  | seqWF {fst snd} : WellFormed fst → WellFormed snd → Disjoint (sitesOf fst) (sitesOf snd) → WellFormed (ControlPrim.seq fst snd)

structure WFControl : Type where
  prim : ControlPrim
  wf : WellFormed prim

abbrev Heap := Addr → Option (Val × AllocSite)
abbrev Stack := (Var → Val)
abbrev State := (Heap × Stack)
