#import "template.typ": *

#show: acmart.with(
  format: "acmsmall",
  title: "CS 747: Formal Verification of Unification-based Pointer Analysis Algorithms",
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
#let partm = $harpoon.rt$

#let concretestep = $attach(-->, br: I_cal(L))$
#let concreteclosure = $attach(-->, tr: *, br: I_cal(L))$
#let state(s, p) = $angle.l #s, #p angle.r$
#let tuple(..enu) = $angle.l #(enu.pos().join(",")) angle.r$

= Introduction
Pointer analysis or alias analysis is an essential step in static analysis, allowing

= Proof Framework

In order to evaluate on a class of different pointer analysis algorithms on potentially different languages, we need a standardized framework for determining the validity of such algorithm that is independent from the source language of a particular analysis. We provide such a framework as follows.

A program state $Sigma$ is a tuple $angle.l h, c, sigma angle.r$, where $h : Addr partm Val$ is a mapping from memory address to the respective value on the heap, $c : Addr$ is a bump allocation counter, and $sigma : Var partm Val$ is a mapping from variables to their assigned values. The exact definition of $Val$ may differ between languages, but is usually $Addr + nat$. A program $cal(P)$ from a source language $cal(L)$ may be executed by a _small-step concrete interpretation_ $I_cal(L)$ of the language. We define the set of reachable states of $cal(P)$ as $ Sigma^*(cal(P)) = {Sigma | exists cal(P)' in cal(L), state(bot, cal(P)) concreteclosure state(Sigma, cal(P)')} $

where $bot$ denotes the empty program state, and $concreteclosure$ represents the closure of the small-step concrete interpretation. $Sigma^*(cal(P))$ is in turn used by a _concrete pointer analysis_ $A_cal(L)$, which summarizes all possible heap states as a single _points-to graph_ $G$, defined as

$ G = {angle.l v, p angle.r | exists Sigma in Sigma^*(cal(P)), Sigma_sigma (v) = p} $

// This is too hard. Probably won't do. Commented out for reference.
// $ cal(G)_p = {angle.l p_1, p_2 angle.r | exists Sigma in Sigma^*(cal(P)), Sigma_h (p_1) = p_2} $

where $Sigma_sigma$ projects $sigma$ from $Sigma$. This effectively gives us pointing relations from any variable at any point of running $cal(P)$, which serves as the baseline for our abstract pointer analysis. It is worth noting that we do not analyze points-to relationships between memory objects, even though we can store pointers within $Sigma_h$.

An _abstract pointer analysis_ $cal(A)^sharp_cal(L)$ provides a points-to graph $G^sharp$ that is a sound approximation of $G$, using only static information that is available without interpretation. We formalize a sound approximation $prec.eq$ as

$ G prec.eq G^sharp <==> forall v_1 v_2 : Var, "alias"(G, v_1, v_2) -> "alias"(G^sharp, v_1, v_2) $

where $"alias"(G, v_1, v_2) = exists p, tuple(v_1, p) in G and tuple(v_2, p) in G$. This relationship extends to analyzers, $cal(A_cal(L)) prec.eq cal(A)_cal(L)^sharp$, for all programs $cal(P)$ within $cal(L)$. $prec.eq$ encodes the properties of the subset of pointer analyses we are interested in proving. In particular, $prec.eq$ enforces analyses to be _overapproximating_, which permits $G^sharp$ to assert more relationships than what is actually present in $G$, but never to omit any concrete relationships. $prec.eq$ also enables analyses to be _unification-based_, which gives $A^sharp_cal(L)$ the freedom to merge multiple memory objects pointed to by the same pointer holders into the same equivalence class.

The reason why we restrict ourselves to the domain of unification-based analyses and omit points-to relationships between memory objects is due to issues with identifying memory objects. While we can easily correspond variable names between $G$ and $G^sharp$ (due to them being available as static program information), we cannot easily correspond their memory objects. In order to account for loops and repeated function calls, $I_cal(L)$ identify memory objects by $Addr$ rather than by their allocation sites. These identities are generated during interpretation by the bump allocator and are not available to $G^sharp$. With unification-based results, we can correspond elements on the graph simply through aliasing equivalence class and


= Outline of Tasks

== Contingency Plan

= References