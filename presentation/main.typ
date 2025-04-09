#import "@preview/touying:0.6.1": *
#import "@preview/curryst:0.5.0": rule, prooftree
#import themes.simple: *

#show: simple-theme.with(aspect-ratio: "16-9")

= CS 747: Formal Verification of Overapproximating Pointer Analysis Algorithms

Kevin Lee

#let Var = math.sans("Var")
#let Val = math.sans("Val")
#let Addr = math.sans("Addr")
#let nat = math.sans("nat")
#let AllocSite = $sans("AllocSite")$
#let partm = math.harpoon.rt
#let Control = math.sans("Control")
#let AExp = math.sans("AExp")
#let BExp = math.sans("BExp")
#let State = math.sans("State")
#let Option = math.sans("Option")
#let HeapObj = math.sans("HeapObj")
#let Heap = $H$
#let Valuation = $sigma$


#let concretestep = $attach(-->, br: I_cal(L))$
#let concreteclosure = $attach(-->, tr: *, br: I_cal(L))$
#let state(s, p) = $angle.l #s, #p angle.r$
#let tuple(..enu) = $angle.l #(enu.pos().join(",")) angle.r$
#let inst(name, ..args) = $sans(name) : #(args.pos().join(math.arrow.r))$

#let skip = math.mono("skip")
#let alloc(site, label: "") = $mono("alloc")_label med #site$
#let assign(vto, vfrom) = $vto <- vfrom$
#let then = $\;$

#let Lalloc = $cal(L)_sans("Alloc")$
#let FPt = $sans("FPt")$
#let Prop = $sans("Prop")$
#let PtG = $sans("PtG")$
#let head = $sans("head")$
#let tail = $sans("tail")$

#let rsub(v, sub) = $attach(#v, br: #sub)$

== Motivation

- Pointer analysis is an essential precursory step to many other forms of static analysis.
  - Knowledge of points-to determines whether two variables may be treated as the same (alias analysis).
- E.g. SeaDSA: used by SeaHorn and SMACK

== Formalization of points-to relation

*Concrete State Points-to*

$sans("SPt")(Sigma : State, v : Var, h : AllocSite) :=$
$ exists a : Addr, Sigma_[Valuation] (v) = a -> Sigma_[Heap] (a)_[AllocSite] = h $

*Concrete Points-to*

$sans("Pt")(p : Control, v: Var, h : AllocSite) :=$
$ exists Sigma in Sigma^*(p), sans("SPt")(Sigma, v, h) $

== Formalization of a sound points-to analysis

We restrict work to only _overapproximating_ pointer analyses.

Given a language $cal(L)$, an *abstract pointer analysis* $sans("Pt")_cal(L)^sharp$ is a _sound approximation_ of a *concrete pointer analysis* $sans("Pt")_cal(L)$, i.e.

$ sans("Pt")_cal(L) prec.eq sans("Pt")_cal(L)^sharp $

iff
$forall P in cal(L), forall v : Var, forall h : AllocSite,$
$ sans("Pt")_cal(L)(P, v, h) -> sans("Pt")_cal(L)^sharp (P, v, h) $

== Goal: Start simple, then build up

$cal(L)_sans("Alloc")$
- Consists of $mono("skip")$, $P_1 then P_2$, $alloc(a)$, $assign(a, b)$.
- Builds the foundational proof framework _that is generalizable to_ more complex languages.

$cal(L)_sans("While")$
- Simple Imperative Language with $alloc(a)$, $mono("read") a$, $mono("write") a$.
- More desirable proof result. May get to if there is enough time.

*All will be compared against Anderseen-style pointer analysis.*

== Basic types of #Lalloc

#table(
  columns: (auto, auto),
  inset: 10pt,
  [Variable], $Var := nat$,
  [Memory address], $Addr := nat$,
  [Values], $Val := Addr$,
  [Allocation site label], $AllocSite := nat$,
  [Heap object], $Option Val times AllocSite$,
  [Heap], $Heap := Addr harpoon.rt HeapObj$,
  [Valuation], $Valuation := Var harpoon.rt Val$,
  [State], $State := Heap times Valuation$
)

== Syntax of #Lalloc

```v
Inductive Control : Ensemble AllocSite -> Type :=
| Skip : Control (Empty_set _)
| Assign : Var -> Var -> Control (Empty_set _)
| Alloc (l : AllocSite) (vto : Var) : Control (Singleton _ l)
| Seq : forall s1 s2,
  Control s1 -> Control s2 -> Disjoint _ s1 s2  -> Control (Union _ s1 s2).
```

Note that the syntax is dependent on the set of $AllocSite$ which the program contains.
- Every `Alloc` must be labelled a unique $AllocSite$!

== Semantics of $cal(L)_sans("Alloc")$

$ (tuple(P_1, s) => tuple(P'_1, s)) / (tuple(P_1 then P_2, s) => tuple(P'_1 then P_2, s')) rsub(=>, "SeqR") $

$ () / (tuple(skip then P_1, s) => tuple(P_1, s)) rsub(=>, "SeqL") $

$ (s'_[sigma] = s_[sigma][v_"to" arrow.r.bar s_[sigma](v_"from")]) / (tuple(assign(v_"to", v_"from"), s) => tuple(skip, s')) rsub(=>, "Assign") $

#pagebreak()

$ (sans("Unallocated")(h, "addr") \ s'_[h] = s_[h]["addr" arrow.r.bar "site"] quad s'_[sigma] = s_[sigma] [v arrow.r.bar "addr"]) / (tuple(alloc("v", label: "site"), s) => tuple(skip, s')) rsub(=>, "Alloc") $


== Anderseen-style pointer-analysis of $cal(L)_sans("Alloc")$

The original set of Datalog rules are filtered down to just two simple inference rules.

$ (sans("HasAlloc")(P, v, "site")) / (sans("Ander")(P, v, "site")) sans("Ander")_"Alloc" $

$ (sans("HasMove")(P, v_"to", v_"from") quad sans("Ander")(P, v_"from", "site")) / (sans("Ander")(P, v_"to", "site")) sans("Ander")_"Move" $

== Stepping stones to connect the two forms of analysis

$ sans("Pt") --> thick ??? thick --> sans("CarryAlloc") --> sans("Ander") $

What is proven so far:

$ sans("CarryAlloc")(P, v_"to", "site")  -> sans("Ander")(P, v_"to", "site") $

Where
- $sans("CarryAlloc")(P, v_"to", "site") =$ 
$ exists v_"from", sans("HasMove")^*(P, v_"to", v_"from") and sans("Alloc")(P, v_"from", "site") $
- $sans("HasMove")^*$ is the transitive closure of $sans("HasMove")$.

== Conjecture: $sans("FPt")$ is a stepping stone
1. Perform state erasure on the small-step semantics
2. Extract points-to precondition/postcondition for each $Control$

*Successor:* $succ$
- Small-step semantics with state erased

#align(center,
  table(
    columns: (auto, auto),
    inset: 10pt,
    align: bottom,
    stroke: 0pt,
    $ (P_1 prec P'_1) / (P_1 then P_2 prec P'_1 then P_2) rsub(succ, "SeqR") $,
    $ () / (skip then P_1 prec P_1) rsub(succ, "SeqL") $,
    $ () / (assign(v_"to", v_"from") prec skip) rsub(succ, "Assign") $,
    $ () / (alloc("v", label: "site") prec skip) rsub(succ, "Alloc") $
  )
)

#pagebreak()

*Head:* $sans("head")(p : Control)$
- The set of possible next $Control$ to be run by the small-step on $p$, for any possible state.

Head is used to anticipate the next action to be taken by the program by $FPt$.

Head-successor is a more semantically consistent way to destruct a program than destructing by the program's syntactical sequence.

#pagebreak()

We needed $State$ to reason about points-to relation. When it's erased, we need another method to reason about it.

*Points-to graph*: $PtG := Var times AllocSite -> Prop$
- Abstract $State$ to only information about points-to relations within the state.

#pagebreak()

*Flow points-to:* $FPt (g_1 : PtG, P_1 : Control, P_2 : Control, g_2 : PtG)$

_Note: this is not yet proven to be a sound approximation of $sans("Pt")$. There may be formulation mistakes._

$ () / (FPt(g, P, P, g)) FPt_"Reflect" $
$ (FPt(g_1, P_1, P_2, g_2) quad FPt(g_2, P_2, P_3, g_3)) / (FPt(g_1, P_1, P_3, g_3)) FPt_"Trans" $
$ (P_1 prec P_2 quad head(P_1) = skip) / (FPt(g, P_1, P_2, g)) FPt_"Skip" $
$ (P_1 prec P_2 quad head(P_1) = alloc(v, label: "site") quad tuple(v, "site") in g_2 \ (v eq.not v_1 and tuple(v_1, "site"_1) in g_1) -> tuple(v_1, "site"_1) in g_2) / (FPt(g_1, P_1, P_2, g_2)) FPt_"Alloc" $
$ (P_1 prec P_2 quad head(P_1) = assign(v_"to", v_"from") quad tuple(v_"from", "site") in g_1 \ tuple(v_"to", "site") in g_2 quad (v_"to" eq.not v_1 and tuple(v_1, "site"_1) in g_1) -> tuple(v_1, "site"_1) in g_2) / (FPt(g_1, P_1, P_2, g_2)) FPt_"Move" $

#pagebreak()

Why might this work?
- Generalizes well to more complex languages.
- Eliminates overhead reasoning about irrelevant parts of the state.
- Unlike $sans("Pt")$, defined inductively in Coq and easier to determine possible subprograms using `econstructor`.
- Head-successor is a more semantically consistent way to destruct a program than destructing by the program's syntactical sequence.

= The work to bridge the gap is ongoing.