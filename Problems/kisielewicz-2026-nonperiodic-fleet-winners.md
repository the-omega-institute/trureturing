---
slug: kisielewicz-2026-nonperiodic-fleet-winners
bibkey: kisielewicz2026cubetilings
doi: 10.48550/arXiv.2611.09844
url: https://arxiv.org/html/2611.09844v1#Thmproblem4.p3.1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Lattices/Klartag/Construction/Tiling
---

# Nonperiodic fleets and changes of strict winner

## Problem

The last paragraph of Kisielewicz, Problem 4, asks:

> For two fixed nonperiodic fleets and a fixed base point, choose both shifts
> independently and uniformly from \(E_d\) for every window size. Can the
> strict winner change infinitely often while the sequence of outcomes fails
> to become eventually periodic?

In dimension three at base zero, a fleet is a set of origins in ℤ³ that
covers each lattice point exactly once by translates of \(\{0,1\}^3\).
Nonperiodicity means its translation stabilizer is trivial. For positive
integer side \(a\), retain origins \(t\) with
\(\varepsilon_i\le t_i<\varepsilon_i+a\) for all \(i\). Summing the signed
comparisons over the 64 equally likely ordered shift pairs gives the margin.
The outcome \(O(a)\) is the sign of the margin.

## Motivation

Counting lattice cubes in a finite window connects a global tiling to
an observable that can change with the side length. The question asks how
much of the eventual winner behavior for periodic origin sets survives
for a fixed pair with trivial translation stabilizers.

## Gap

The companion arXiv:2611.12239v1 treats local counters and lattice profiles.
The checked periodic second-moment and finite tiling-code results concern
other regimes. The literature scope and exact formulation are in the
[preregistration](https://github.com/the-omega-institute/trureturing/issues/33707).

## Route

The two marked negative slabs force a trivial stabilizer without affecting
any score. Phase-zero counts on positive slabs give opposite margins at
consecutive selected sizes. Their factorial factors make both sizes
congruent modulo any prescribed period sufficiently far along the sequence.

## Falsifier

A lattice point with zero or multiple covering origins, a nonzero
translation preserving either origin set, or a literal score comparison
with the wrong sign at a selected side would refute the corresponding
property of this pair.

## Evidence

The Lean declaration `KisielewiczFleetWinners.exists_nonperiodic_fleets`
uses the same two origin sets for the cover and stabilizer properties,
the two strict signs, and the counterexample to each eventual period.

## Triage

There are two fixed fleets for which both strict signs occur at sides at
least \(\max(1,B)\) for every cutoff \(B\). For every positive period \(P\)
and cutoff \(B\) there is a side \(c\ge\max(1,B)\) with
\(O(c+P)\ne O(c)\).

## ASSUMED-UNVERIFIED

Publication priority and coverage of unindexed work are unverified.
