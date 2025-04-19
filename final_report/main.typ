#import "@preview/lemmify:0.1.8": *

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
#let head = $sans("head")$
#let StatusMove = math.sans("StatusMove")
#let StatusAlloc = math.sans("StatusAlloc")

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

#let Andersen = math.sans("Ander")
#let rsub(v, sub) = $attach(#v, br: #sub)$

#let AnderRel = math.sans("AnderRel")

#let (
  theorem, lemma, corollary,
  remark, proposition, example,
  proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")

#show: thm-rules

#show thm-selector("thm-group", subgroup: "proof"): it => pad(it, bottom: 1em)

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

Artifacts for this project, including the source for the Coq implementation and written material such as this report, are available online at #link("https://github.com/KevinLeeFM/cs747-project", [`https://github.com/KevinLeeFM/cs747-project`]).

= Proof background

== Proof Framework

In order to evaluate on a family of different pointer analysis algorithms on potentially different languages, we need a standardized framework for determining the validity of such algorithm that is independent from the source language of a particular analysis. We provide a sketch of such a framework as follows, described as a Coq implementation.

We first define the type of variables and allocation site labels---respectively $Var$ and $AllocSite$---simply as $nat$. This modelling does not attempt to make use of any inductive principles of natural numbers, but rather only to enable decidable equalities between discrete objects using Coq's `Nat.eqb`. $AllocSite$ is additionally required to be unique for each `alloc` instruction in a given program. As described in @lalloc, this is achieved by making the program type, $Control$, dependent on $Set AllocSite$.

A concrete program state $Sigma$ is a tuple $angle.l H, sigma angle.r$, where $H : Addr partm Val times AllocSite$ is the heap mapping from memory address to the respective value on the heap allocated by $AllocSite$, and $sigma : Var partm Val$ is the valuation mapping from variables to their assigned values. The exact definition of $Val$ differ between languages. A program $cal(P) : Control$ from a source language $cal(L)$ may be executed by a _small-step concrete interpretation_ $concreteinterp : Control -> State -> Control -> State$ of the language. The resultant states may then be used by a _concrete pointer analysis_ $concreteana : State -> PTStatus$ to generate a points-to graph represented as a _points-to status_, $PTStatus := (p times AllocSite) -> Prop$, where $p$ is a sum of all types in $cal(L)$ which may act as a pointer to some $AllocSite$. Points-to status is an abstraction of a concrete state which holds only information about points-to relations at a given point in execution.

An _abstract pointer analysis_ $abstractana : Control -> PTStatus -> Control -> PTStatus$ is a small-step interpreter of $cal(L)$ that provides a points-to status which is an overapproximation of that generated jointly by $concreteinterp$ and $concreteana$, using static information. Such an abstract interpretation cannot use concrete state information, in which case $abstractana$ surrogates with $PTStatus$. We formalize this relation as a _sound overapproximation_ $overapproxby op(:) PTStatus -> PTStatus -> Prop$, defined as

$ P overapproxby P^sharp <==> forall tuple(v, h) op(:) Var times AllocSite, P(tuple(v, h)) -> P^sharp (tuple(v, h)) $

This relationship extends to analyzers, $concreteana' subset.eq.sq abstractana$, for all programs $cal(P)$ within $cal(L)$, defined as

$ concreteana' overapproxby abstractana <==> (tuple(P_1, p_1) =>_concreteana' tuple(P_2, p_2)) and (tuple(P_1, p^sharp_1) =>_abstractana tuple(P_2, p^sharp_2)) -> p_1 overapproxby p_1^sharp -> p_2 overapproxby p_2^sharp $

where $tuple(P_1, p_1) =>_concreteana' tuple(P_2, p_2) <==> (tuple(P_1, Sigma_1) =>_concreteinterp tuple(P_2, Sigma_2) and concreteana(Sigma_1) = p_1 and concreteana(Sigma_2) = p_2)$.

$overapproxby$ encodes the properties of the subset of pointer analyses we are interested in proving. In particular, $overapproxby$ permits $abstractana$ to assert more relationships than what is actually present in $concreteana$, but never to omit any concrete relationships. The extension of $overapproxby$ assures that the overapproximation is preserved under any program execution step, implying its preservation within their step closures.

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
    The syntax of $Lalloc$ as defined inductively in Coq.
  ]
) <lalloc-syntax>

#figure(
  align(center)[#table(
    columns: (auto, auto),
    stroke: 0.5pt,
    align: horizon,
    $ (tuple(P_1, Sigma) => tuple(P'_1, Sigma)) / (tuple(P_1 then P_2, Sigma) => tuple(P'_1 then P_2, Sigma')) rsub(=>, "SeqR") $,

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

== Specification of $Andersen$ analysis <proof-spec>

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

In $rsub(=>, "Assign")$, $p'$ is modified to include all relations from $v_"from"$ in $v_"to"$. In $rsub(=>, "Alloc")$, $p'$ is modified to include a new relation between the new memory address and $v_"to"$. In both cases, all existing relations in $p$ are preserved, so execution of programs using $cal(A)^sharp_Lalloc$ will monotonically increase the amount of asserted relations, in likeness to the original Datalog rules @smaragdakis_pointer_2015.

#figure(
  align(center)[#table(
    columns: (auto, auto),
    stroke: 0.5pt,
    align: horizon,
    $ (tuple(P_1, p) => tuple(P'_1, p')) / (tuple(P_1 then P_2, p) => tuple(P'_1 then P_2, p')) rsub(=>, "SeqR") $,

    $ () / (tuple(skip then P_1, p) => tuple(P_1, p)) rsub(=>, "SeqL") $,
    
    table.cell(
      [
        $ (p' = StatusMove(p, v_"from", v_"to")) / (tuple(assign(v_"to", v_"from"), p) => tuple(skip, p')) rsub(=>, "Assign") $
        where $StatusMove(p, v_"from", v_"to") = lambda tuple(v, "site"). cases(p(v_"from", "site") or p(v_"to", "site") sans("if") v = v_"to", p(v, "site") sans("otherwise"))$
      ],
      colspan: 2
    ),

    table.cell(
      [
        $ (p' = StatusAlloc(p, "site", v_"to")) / (tuple(alloc(v_"to", label: "site"), p) => tuple(skip, p')) rsub(=>, "Alloc") $
        where $ StatusAlloc(p, "site", v_"to") = lambda tuple(v, "site"') . cases(True sans("if") v = v_"to" and "site"' = "site", p(v, "site"') sans("otherwise"))$
      ],
      colspan: 2
    )
  )],
  placement: top,
  caption: [
    The small-step semantics of $Lalloc$ used by the abstract interpretation $cal(A)^sharp_Lalloc$. Additionally, $StatusMove$ and $StatusAlloc$ are defined, which are reused later.
  ]
) <andersen-semantics>

= Proof sketch

In this section, we provide highlights of the proof implemented in Coq for the soundness of $Andersen$ analysis on $Lalloc$, specifically that $concreteana' overapproxby abstractana$ for all programs $cal(P)$ within $Lalloc$.

One of the first observations to make is that the steps taken by every rule in both $concreteana'$ and $abstractana$ only takes the foremost command in the program into account to determine the semantics of the step, as opposed to the whole expression. The full expression is also arbitrarily divided into a binary expression tree by `Seq`, which introduces a lot of unnecessary complexity. To help eliminate this logical overhead, we use the notion of _head_ and _successor_.

The _head_ of a program $p$, denoted $head(p : Control)$, is the set of possible next $Control$ to be run by the small-step of either $concreteana'$ or $abstractana$ on $p$, for any possible state. In the case of $Lalloc$, there is no state-dependent control flow, so the head of a program is unambiguously the first command in the program. The _successor_ $s$ of a program $p$, denoted $p prec s$, is simply the small-step semantics of either $concreteana'$ or $abstractana$ with state erased. While the successor step is deterministic in $Lalloc$, with state-dependent control flow the steps can become non-deterministic. Successor steps are defined as follows.

#align(center,
  table(
    columns: (auto, auto),
    align: bottom,
    stroke: 0pt,
    $ (P_1 prec P'_1) / (P_1 then P_2 prec P'_1 then P_2) rsub(succ, "SeqR") $,
    $ () / (skip then P_1 prec P_1) rsub(succ, "SeqL") $,
    $ () / (assign(v_"to", v_"from") prec skip) rsub(succ, "Assign") $,
    $ () / (alloc("v", label: "site") prec skip) rsub(succ, "Alloc") $
  )
)

#lemma(name: "State erasure")[
  For any $tuple(P_1, Sigma_1) => tuple(P_2, Sigma_2)$, $P_1 prec P_2$. Likewise for $cal(A)^sharp_Lalloc$ with $p_1$ and $p_2$.
] <state-erasure>
#proof[
  Induction on the rules deriving $tuple(P_1, Sigma_1) => tuple(P_2, Sigma_2)$.
]

#lemma(name: "Step restoration")[
  For any $P_1 prec P_2$, and for all $p_1 : PTStatus$, there exists a $p_2 : PTStatus$ such that $tuple(P_1, p_1) => tuple(P_2, p_2)$.
] <step-restoration>
#proof[
  Induction on the rules deriving $P_1 prec P_2$.
]

Step restoration is necessary to convert reasoning about successors back into stepping representation necessary to connect $concreteana'$ to $abstractana$. The problem is that the semantics of the step is still missing. So far, we can only reason that a step will yield _some_ $p_2$, but no information on $p_2$'s relation to $p_1$. This relation can be restored by observing $h = head(P_1)$ and associating each $h$ with a relation $f$, defined formally as $ AnderRel(h : Control, f : PTStatus -> PTStatus) : Prop := \ forall (P_1, P_2, p_1, p_2), head(P_1, h) -> tuple(P_1, p_1) => tuple(P_2, p_2) -> f(p_1) = p_2 $

The relation for each possible head in $Lalloc$ immediately follows the stepping rules of $cal(A)^sharp_Lalloc$.

#lemma(name: "Andersen stepping relations")[
  The following relations are true.
  #align(center,
    table(
      columns: (auto, auto),
      stroke: none,
      align: horizon,
      $ AnderRel(skip, lambda p.p) $,
      $ AnderRel(assign(v_"to", v_"from"), lambda p . StatusMove(p, v_"to", v_"from")) $,
      table.cell(
      $ AnderRel(alloc(v_"to", label: "site"), lambda p . StatusAlloc(p, "site", v_"to")) $,
      colspan: 2
    )
    )
  )
] <andersen-step-relation>
#proof[For all relations, perform induction on the rules deriving $tuple(P_1, p_1) => tuple(P_2, p_2)$. The `inversion_sigma` tactic is employed to eliminate dependent sum type.]

With these relations, Andersen's stepping semantics is fully restored.

#lemma(name: "Andersen stepping restoration")[
  Given that $head(P) = h$, $P prec P'$, and $AnderRel(h, f)$, then for any $p : PTStatus$, $tuple(P, p) => tuple(P, f(p))$
] <andersen-step-restoration>
#proof[Omitted for brevity.]

One unfortunate axiom that we have to pose in order to complete the proof is the assertion that no recursive definition of $Control$ is allowed, namely $P_1 then P_2 eq.not P_2$. This axiom presented itself using `eq_rect` to avoid the heterogeneity of the equality, and is mandated from the fact that $Control$ is dependent on $Set AllocSite$, which upon induction tend to generate false statements protected from trivial elimination by `eq_rect`. While this may be provable using foundational properties of equality, this is not the focus of our formalization and axiomatization is the most pragmatic solution.

An inductive case in the main theorem is challenging, but can be solved by an adaptation of the fact that only the head determines the semantics of a step.

#lemma(name: "Andersen step partial")[
  If $tuple(P_1 then P_2, p_1) => tuple(P'_1 then P_2, p_2)$, then $tuple(P_1, p_1) => tuple(P'_1, p_2)$.
] <andersen-step-partial>
#proof[We need to first assert that $exists h, head(P_1, h) and head(P_1 then P_2, h)$. This, along with @state-erasure, @step-restoration, and @andersen-step-relation, contribute to the proof.]

With these pieces in place, we can prove the soundness of $Andersen$ under $Lalloc$.

#theorem(name: "Soundness of Andersen")[
  As described in @proof-spec.
]
#proof[
  Induction on the concrete step $tuple(P_1, Sigma_1) => tuple(P_2, Sigma_2)$. The $rsub(=>, "SeqR")$ case requires @andersen-step-partial. The $rsub(=>, "SeqL")$, $rsub(=>, "Assign")$, and $rsub(=>, "Alloc")$ inductive cases requires the $skip$, $mono("assign")$, and $mono("alloc")$ case of @andersen-step-relation, respectively.
]

= Discussions

While we have proven the soundness of $Andersen$ in $Lalloc$, this merely serves as a foundation for formalization of more practical languages. In the original proposal, we aspire to extend $Lalloc$ to $cal(L)_sf("Load")$, which introduces arithmetic expressions, $inst("Store", Var, Val, Com)$, and $inst("Load", Var, Var, Com)$ (noting that we cannot treat loads as arithmetic expressions, due to the possibility of having both $Addr$ or $nat$ be stored). Using the facts generated from $cal(L)_sf("Load")$, we also aspire to extend the language to a Turing-complete $cal(L)_sf("While")$, introducing boolean expressions, $inst("If", BExp, Com, Com, Com)$, and $inst("While", BExp, Com, Com)$. It may be also worth pursing flow-sensitivity within this language to improve the precision of the pointer analysis under investigation.

Unfortunately, due to the limited time frame of this project, as well as unanticipated issues encountered while formalizing $Lalloc$, we cannot get to formalizing these languages. We are still eager to look into them as future work upon this project. Ensuring that every alloc in the program has a unique label turned out to be an especially unexpected challenge that resulted in difficult dependent type proof obligations and many detours into proving basic set theory lemmas in order to appeal to the type system. Our proofs had to make extensive use of proof irrelevance to eliminate type disagreements simply due to the fact that two `Seq`'s disjointness were proven in different ways, but identical otherwise. An important lesson here is to avoid the use of dependent types if possible, as they can quickly slow down the proving process with pedantic false assumptions which cannot be automatically discharged. In our case, this is rather unavoidable---this nevertheless provided an excellent learning experience of dealing with heterogeneous equalities in Coq.

There is also the uncertainty around whether the definition of head and successor extends well to Turing-complete languages, where control flow will cause their definitions to become non-deterministic. This is also subject to future work on this project.

= References

#bibliography(
  "works.bib",
  title: none,
  style: "association-for-computing-machinery"
)