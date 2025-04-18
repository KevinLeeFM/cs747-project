#import "template.typ": *

#let Lalloc = $cal("L")_sans("Alloc")$
#let Var = math.sans("Var")
#let Val = math.sans("Val")
#let Addr = math.sans("Addr")
#let nat = math.sans("nat")
#let AllocSite = math.sans("AllocSite")
#let partm = math.harpoon.rt
#let Com = math.sans("Com")
#let AExp = math.sans("AExp")
#let BExp = math.sans("BExp")
#let State = math.sans("State")
#let Option = math.sans("Option")
#let HeapObj = math.sans("HeapObj")
#let Heap = $H$
#let Valuation = $sigma$
#let FPt = math.sans("FPt")
#let Prop = math.sans("Prop")
#let PtG = math.sans("PtG")
#let head = math.sans("head")
#let tail = math.sans("tail")
#let Control = math.sans("Control")
#let Set = math.sans("Set")
#let PTStatus = math.sans("PTStatus")

#let None = math.sans("None")
#let Some(exp) = $sans("Some") med exp$
#let True = $sans("True")$

#let concreteinterp = $cal(I)_cal(L)$
#let concretestep = $attach(==>, br: concreteinterp)$
#let concreteclosure = $attach(==>, tr: *, br: concreteinterp)$
#let state(s, p) = $angle.l #s, #p angle.r$
#let tuple(..enu) = $angle.l #(enu.pos().join(",")) angle.r$
#let inst(name, ..args) = $sf(name) : #(args.pos().join(math.arrow.r))$

#let concreteana = $cal(A)_cal(L)$
#let abstractana = $cal(A)^sharp_cal(L)$
#let overapproxby = $subset.eq.sq$

#let skip = math.mono("skip")
#let alloc(site, label: "") = $mono("alloc")_label med #site$
#let assign(vto, vfrom) = $vto <- vfrom$
#let then = $\;$

#let Andersen = math.sans("Andersen")
#let rsub(v, sub) = $attach(#v, br: #sub)$

#show: acmart.with(
  format: "acmsmall",
  title: "CS 747: Formal Verification of Overapproximating Pointer Analysis Algorithms",
  authors: {
  let uwaterloo = (
      institution: "University of Waterloo",
      streetaddress: "P.O. Box 1212",
      city: "Waterloo",
      state: "ON",
      country: "Canada",
      postcode: "43017-6221")
  (
    (
      name: "Kevin Lee",
      email: "k323lee@uwaterloo.ca",
      affiliation: uwaterloo),
  )},
  shortauthors: "Lee",
  abstract: [
    In this report, we will introduce and motivate the need to formally verify overapproximating pointer analysis algorithms and define a formal foundation for performing the verification that is designed to be highly extensible to imperative languages. We then formalize such proof in Coq and show a proof sketch necessary to prove the soundness of the Andersen analysis on $Lalloc$. Finally, we reflect on the formalization work completed, the limitations of our current work, challenges and lessons encountered during the formalization process, and possible future work for the project.
  ],
  ccs: none,
  keywords: none,
)

= Introduction

Pointer analysis is a form of program static analysis that identifies the set of all possible values that a pointer expression can point to. Deriving this information is an essential upstream task to most inter-procedural static analysis, as most interesting facts about variables in a program requires knowledge about a variable's possible values @smaragdakis_pointer_2015. Practical examples are abound---many context-insensitive pointer analyses has been used in formal verfication projects such as #smallcaps("SeaHorn") and #smallcaps("Smack"). It is therefore paramount that such analysis is precise (as in providing information that is powerful enough to derive practical facts), efficient, and sound.

We report efforts to formally verify the soundness aspect of a range of pointer analysis algorithms. To do this, we will build up from simple languages and incrementally introduce additional language features and possibly different form of context sensitivity of heap objects until we reach interesting verification results that is hopefully useful for the author's research pursuit in #smallcaps("SeaDSA") @ranzato_context-sensitive_2017. In the hopes of maximizing reuse of proofs and formalization, we will unify our work under an overarching proof framework generalized for pointer analyses.

= Proof background

== Proof Framework

In order to evaluate on a family of different pointer analysis algorithms on potentially different languages, we need a standardized framework for determining the validity of such algorithm that is independent from the source language of a particular analysis. We provide a sketch of such a framework as follows, described as a Coq implementation.

We first define the type of variables and allocation site labels---respectively $Var$ and $AllocSite$---simply as $nat$. This modelling does not attempt to make use of any inductive principles of natural numbers, but rather only to enable decidable equalities between discrete objects using Coq's `Nat.eqb`. $AllocSite$ is additionally required to be unique for each `alloc` instruction in a given program. As described in @lalloc, this is achieved by making the program type, $Control$, dependent on $Set AllocSite$.

A concrete program state $Sigma$ is a tuple $angle.l H, sigma angle.r$, where $H : Addr partm Val times AllocSite$ is the heap mapping from memory address to the respective value on the heap allocated by $AllocSite$, and $sigma : Var partm Val$ is the valuation mapping from variables to their assigned values. The exact definition of $Val$ differ between languages. A program $cal(P) : Control$ from a source language $cal(L)$ may be executed by a _small-step concrete interpretation_ $concreteinterp : Control -> State -> Control -> State$ of the language. The resultant states may then be used by a _concrete pointer analysis_ $concreteana : State -> PTStatus$ to generate a points-to graph represented as a _points-to status_, $PTStatus := (p times AllocSite) -> Prop$, where $p$ is a sum of all types in $cal(L)$ which may act as a pointer to some $AllocSite$. Points-to status is an abstraction of a concrete state which holds only information about points-to relations at a given point in execution.

An _abstract pointer analysis_ $abstractana : Control -> PTStatus -> Control -> PTStatus$ is a small-step interpreter of $cal(L)$ that provides a points-to status which is an overapproximation of that generated jointly by $concreteinterp$ and $concreteana$, using static information. Such an abstract interpretation cannot use concrete state information, in which case $abstractana$ surrogates with $PTStatus$. We formalize this relation as a _sound overapproximation_ $overapproxby op(:) PTStatus -> PTStatus -> Prop$, defined as

$ P overapproxby P^sharp <==> forall tuple(v, h) op(:) Var times AllocSite, P(tuple(v, h)) -> P^sharp (tuple(v, h)) $

This relationship extends to analyzers, $concreteana' subset.eq.sq abstractana$, for all programs $cal(P)$ within $cal(L)$, defined as

$ concreteana' overapproxby abstractana <==> (tuple(p_1, P_1) =>_concreteana' tuple(p_2, P_2)) and (tuple(p_1, P^sharp_1) =>_abstractana tuple(p_2, P^sharp_2)) -> P_1 overapproxby P_1^sharp -> P_2 overapproxby P_2^sharp $

where $tuple(p_1, P_1) =>_concreteana' tuple(p_2, P_2) <==> (tuple(p_1, Sigma_1) =>_concreteinterp tuple(p_2, Sigma_2) and concreteana(Sigma_1) = P_1 and concreteana(Sigma_2) = P_2)$.

$overapproxby$ encodes the properties of the subset of pointer analyses we are interested in proving. In particular, $overapproxby$ permits $abstractana$ to assert more relationships than what is actually present in $concreteana$, but never to omit any concrete relationships. The extension of $overapproxby$ assures that the overapproximation is preserved under any program execution step, implying its preservation within their step closure.

In the original proposal of the project, we defined $overapproxby$ with a different formulation using reachable states, step closures, and Datalog-based inference rules for abstract analysis. This formalization is modified in light of the fact that closure of small-step semantics introduces a significant amount of logical overhead and lemmas required to bridge the gap between the two disparate representations of concrete execution and abstract analysis, which distracts from our goal of formalizing. Our current formulation represents both concrete execution and analysis as analogous single-step interpretations, which is much easier to perform inductive proofs upon.

It is worth noting that pointer analysis conventionally identify memory objects by the $AllocSite$ from which they are allocated. This will of course confound memory objects allocated on the same line of instruction. In the framework, we are performing this confounding in $cal(A)_cal(L)$ and $cal(A)^sharp_cal(L)$ for the pragmatic purpose of matching memory objects within $G$ and $G^sharp$ together, up to allocation site sensitivity. For versions of pointer analysis involving more sensitivity, we can replace $AllocSite$ with a tuple $Gamma$ containing all heap allocation contexts necessary for that level of sensitivity.

== Specification of $Lalloc$ <lalloc>

$Lalloc$ is one of the most basic language we can come up with to enable the need to peform pointer analysis. This language is the main subject of this report as it comprises all the work performed in the project. It is our goal to make the lemmas for proving $Lalloc$ as generalized as possible and forms the foundational lemmas to eliminate the basic logical overhead of our pointer analysis formulation for future work.

In $Lalloc$, variables can only hold pointers, and pointers are only found in variables. As such, $Val := AllocSite$ and $PTStatus := (Var times AllocSite) -> Prop$. The syntax and semantics of $Lalloc$ are shown in @lalloc-syntax and @lalloc-semantics, respectively.

#figure(
  [```v
  Inductive Control : Ensemble AllocSite -> Type :=
  | Skip : Control (Empty_set _)
  | Assign : Var -> Var -> Control (Empty_set _)
  | Alloc (l : AllocSite) (vto : Var) : Control (Singleton _ l)
  | Seq : forall s1 s2,
    Control s1 -> Control s2 -> Disjoint _ s1 s2  -> Control (Union _ s1 s2).
  ```],
  placement: top,
  caption: [
    The syntax of $Lalloc$ written in Coq.
  ]
) <lalloc-syntax>

#figure(
  align(center)[#table(
    columns: (auto, auto),
    stroke: 0.5pt,
    align: horizon,
    $ (tuple(P_1, s) => tuple(P'_1, s)) / (tuple(P_1 then P_2, s) => tuple(P'_1 then P_2, s')) rsub(=>, "SeqR") $,

    $ () / (tuple(skip then P_1, s) => tuple(P_1, s)) rsub(=>, "SeqL") $,

    $ (s'_[sigma] = s_[sigma][v_"to" arrow.r.bar s_[sigma](v_"from")]) / (tuple(assign(v_"to", v_"from"), s) => tuple(skip, s')) rsub(=>, "Assign") $,

    $ (sans("Unallocated")(sigma, h, "addr") \ s'_[h] = s_[h]["addr" arrow.r.bar "site"] quad s'_[sigma] = s_[sigma] [v arrow.r.bar "addr"]) / (tuple(alloc("v", label: "site"), s) => tuple(skip, s')) rsub(=>, "Alloc") $
  )],
  placement: top,
  caption: [
    The small-step semantics of $Lalloc$ used by the concrete interpretation $cal(I)_Lalloc$. 
  ]
) <lalloc-semantics>

As seen in @lalloc-syntax, the program type $Control$ is dependent on $Set AllocSite$. This is to ensure that every `alloc` within a constructed program must be labelled with a unique $AllocSite$. This is enforced by requiring each construction of `Seq` to be paired with a proof that the constituent $Control$s' set of $AllocSite$ are disjoint. Their sets are then unioned as the set labelling the `Seq`.

Within @lalloc-semantics, $sans("Unallocated")(sigma, h, "addr") := h("addr") = None and forall v op(:) Var, sigma(v) eq.not Some("addr")$. This proposition ensures that an allocation must create a fresh memory address that does not conflict with any allocated memory addresses within the heap or dangling pointers within the valuation. While dangling pointers cannot be created in $Lalloc$, it nevertheless helps with generalization and simplifying our proof to eliminate cases with inconsistent states.

== Specification of $Andersen$ analysis

In anticipation of the schedule for the project, we restrict our formalization to Andersen-style points-to analysis. This style enables each variable assignment $assign(v_"to", v_"from")$ to copy all points-to relations from $v_"from"$ to $v_"to"$, keeping existing relationships. @smaragdakis_pointer_2015 implements an example overapproximating Andersen-style pointer analysis in Datalog. Note that the original Datalog implementation includes many irrelevant inference rules that describes an imperative language with memory read/writes and function calls, which we exclude. This leaves us with only two rules as shown below.

#align(center)[
  #table(
    columns: (auto, auto),
    inset: 10pt,
    stroke: none,
    align: horizon,
    $ (sans("HasAlloc")(P, v, "site")) / (sans("Ander")(P, v, "site")) sans("Ander")_"Alloc" $,

    $ (sans("HasMove")(P, v_"to", v_"from") quad sans("Ander")(P, v_"from", "site")) / (sans("Ander")(P, v_"to", "site")) sans("Ander")_"Move" $
  )
]

These rules are then adapted into a small-step abstract interpreter $cal(A)^sharp_Lalloc$, as shown in @andersen-semantics.

In $rsub(=>, "Assign")$, $p'$ is modified to include all relations from $v_"from"$ in $v_"to"$. In $rsub(=>, "Alloc")$, $p'$ is modified to include a new relation between the new memory address and $v_"to"$. In both cases, all existing relations in $p$ are preserved, so execution of $cal(A)^sharp_Lalloc$ will only introduce more relations into the points-to status.

#figure(
  align(center)[#table(
    columns: (auto, auto),
    stroke: 0.5pt,
    align: horizon,
    $ (tuple(P_1, p) => tuple(P'_1, p')) / (tuple(P_1 then P_2, p) => tuple(P'_1 then P_2, p')) rsub(=>, "SeqR") $,

    $ () / (tuple(skip then P_1, p) => tuple(P_1, p)) rsub(=>, "SeqL") $,
    
    table.cell(
      $ (p' = lambda tuple(v, "site") . cases(p(v_"from", "site") or p(v_"to", "site") sans("if") v = v_"to", p(v, "site") sans("otherwise"))) / (tuple(assign(v_"to", v_"from"), p) => tuple(skip, p')) rsub(=>, "Assign") $,
      colspan: 2
    ),

    table.cell(
      $ (p' = lambda tuple(v, "site"') . cases(True sans("if") v = v_"to" and "site"' = "site", p(v, "site") sans("otherwise"))) / (tuple(alloc("v", label: "site"), s) => tuple(skip, s')) rsub(=>, "Alloc") $,
      colspan: 2
    )
  )],
  placement: top,
  caption: [
    The small-step semantics of $Lalloc$ used by the abstract interpretation $cal(A)^sharp_Lalloc$. 
  ]
) <andersen-semantics>

= Proof sketch

= Discussions

= References

#bibliography(
  "works.bib",
  title: none,
  style: "association-for-computing-machinery"
)