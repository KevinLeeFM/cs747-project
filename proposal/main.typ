#import "template.typ": *

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
    // Probably don't need an abstract?
  ],
  ccs: none,
  keywords: none,
)

#let Var = sf("Var")
#let Val = sf("Val")
#let Addr = sf("Addr")
#let nat = sf("nat")
#let AllocSite = sf("AllocSite")
#let partm = math.harpoon.rt
#let Com = sf("Com")
#let AExp = sf("AExp")
#let BExp = sf("BExp")

#let concretestep = $attach(-->, br: I_cal(L))$
#let concreteclosure = $attach(-->, tr: *, br: I_cal(L))$
#let state(s, p) = $angle.l #s, #p angle.r$
#let tuple(..enu) = $angle.l #(enu.pos().join(",")) angle.r$
#let inst(name, ..args) = $sf(name) : #(args.pos().join(math.arrow.r))$

= Introduction
Pointer analysis is a form of program static analysis that identifies the set of all possible values that a pointer expression can point to. Deriving this information is an essential upstream task to most inter-procedural static analysis, as most interesting facts about variables in a program requires knowing their possible values @smaragdakis_pointer_2015. It is therefore paramount that such analysis is precise (as in providing information that is powerful enough to derive practical facts), efficient, and sound.

In this proposal, we wish to focus on and formally verify the soundness aspect of a range of pointer analysis algorithms. To do this, we will build up from simple languages and incrementally introduce additional language features and possibly different form of context sensitivity of heap objects until we reach interesting verification results that is hopefully useful for the author's research pursuit in SeaDSA. In the hopes of maximizing reuse of proofs and formalization, we will unify our work under an overarching proof framework generalized for pointer analyses.

= Proof Framework

In order to evaluate on a family of different pointer analysis algorithms on potentially different languages, we need a standardized framework for determining the validity of such algorithm that is independent from the source language of a particular analysis. We provide such a framework as follows.

A program state $Sigma$ is a tuple $angle.l H, c, sigma angle.r$, where $H : Addr partm Val times AllocSite$ is a mapping from memory address to the respective value on the heap allocated by $AllocSite$, $c : Addr$ is a bump allocation counter, and $sigma : Var partm Val$ is a mapping from variables to their assigned values. $AllocSite$ is the type of unique labels for each `alloc` instruction in the program. The exact definition of $Val$ may differ between languages, but is usually $Addr + nat$. A program $cal(P)$ from a source language $cal(L)$ may be executed by a _small-step concrete interpretation_ $I_cal(L)$ of the language. We define the set of reachable states of $cal(P)$ as $ Sigma^*(cal(P)) = {Sigma | exists cal(P)' in cal(L), state(bot, cal(P)) concreteclosure state(Sigma, cal(P)')} $

where $bot$ denotes the empty program state, and $concreteclosure$ represents the closure of the small-step concrete interpretation. $Sigma^*(cal(P))$ is in turn used by a _concrete pointer analysis_ $A_cal(L)$, which summarizes all possible heap states as a single _points-to graph_ $G subset.eq Var times AllocSite$, defined as

$ G = {tuple(v, h) | exists Sigma in Sigma^*(cal(P)), exists p, Sigma_[sigma] (v) = p -> Sigma_[H] (p)_[AllocSite] = h } $

where $T_[*]$ projects $*$ from some tuple $T$. This effectively gives us pointing relations from any variable at any point of running $cal(P)$, which serves as the baseline for our abstract pointer analysis. Note that if we are also interested in tracking points-to relations between memory objects, we can expand $G$ to be $G subset.eq (Var + AllocSite) times AllocSite$ and define its generation accordingly.

An _abstract pointer analysis_ $cal(A)^sharp_cal(L)$ provides a points-to graph $G^sharp$ that is a sound approximation of $G$, using static information. We formalize a _sound approximation_ $prec.eq$ as

$ G prec.eq G^sharp <==> forall tuple(v, h) : Var times AllocSite, tuple(v, h) in G -> tuple(v, h) in G^sharp $

This relationship extends to analyzers, $cal(A_cal(L)) prec.eq cal(A)_cal(L)^sharp$, for all programs $cal(P)$ within $cal(L)$. $prec.eq$ encodes the properties of the subset of pointer analyses we are interested in proving. In particular, $prec.eq$ enforces analyses to be _overapproximating_, which permits $G^sharp$ to assert more relationships than what is actually present in $G$, but never to omit any concrete relationships. 

It is worth noting that pointer analysis conventionally identify memory objects by the allocation site from which they are allocated. This will of course confound memory objects allocated on the same line of instruction. In the framework, we are performing this confounding in $cal(A)_cal(L)$ and $cal(A)^sharp_cal(L)$ for the pragmatic purpose of matching memory objects within $G$ and $G^sharp$ together, up to allocation site sensitivity. For versions of pointer analysis involving more sensitivity, we can replace $AllocSite$ with a tuple $Gamma$ containing all heap allocation contexts necessary for that level of sensitivity.

= Outline of Tasks

This project will mainly comprise of analyzing example algorithms adapted from #cite(<smaragdakis_pointer_2015>, form: "prose"), which provides a plethora of different styles and sensitivities of pointer analyses. Because these algorithms are written in Datalog, they can naturally translate to inductive inference rules for $A^sharp_cal(L)$. Not every Datalog rule and language feature within these algorithm are relevant to all of our languages, so some rules may be cut out or rewritten to better fit the available language constructs.

To ensure that the formulation of the framework may be applied in practice, we will begin with verifying an analysis algorithm bespoke for a toy language, $cal(L)_sf("Alloc")$, which only consist of $inst("Assign", Var, Var, Com)$, $inst("Alloc", Var, Com)$, $inst("Seq", Com, Com, Com)$ and $inst("Skip", Com)$. This will hopefully generate basic lemmas for eliminating some of the logical overhead introduced by our construction of $G$, $G^sharp$, or $prec.eq$, as well as to produce more profound small-step semantics lemmas and its relation to the heap.

Once $cal(L)_sf("Alloc")$ is established, we can extend it to $cal(L)_sf("Load")$, which introduces arithmetic expressions, $inst("Store", Var, Val, Com)$, and $inst("Load", Var, Var, Com)$ (noting that we cannot treat loads as arithmetic expressions, due to the possibility of having both $Addr$ or $nat$ be stored).

Using the facts generated from $cal(L)_sf("Load")$, we can then attempt to extend the language to a Turing-complete $cal(L)_sf("While")$, introducing boolean expressions, $inst("If", BExp, Com, Com, Com)$, and $inst("While", BExp, Com, Com)$. It may be also worth pursing flow-sensitivity within this language to improve the precision of the pointer analysis under investigation.

To keep the project realistic given the time frame, we may attempt to only verify analysis results for the point-to relationship of variables, and omit points-to relationships between memory objects. However, if time permit, we can extend either $cal(L)_sf("Load")$ or $cal(L)_sf("While")$ to also include such analysis results. Other ideas for extended work include introducing fields to memory object, functions, and call stack sensitivity.

= References

#bibliography(
  "works.bib",
  title: none,
  style: "association-for-computing-machinery"
)