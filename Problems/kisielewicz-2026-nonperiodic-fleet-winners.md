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
The outcome \(\operatorname{outcome}(F,G,a)\) is the sign of the margin.

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

- **Proved — unique cover and trivial stabilizers.** At height \(z=-2\),
  the exceptional row at \(y=0\) has odd \(x\)-origins, while all other
  even rows have even \(x\)-origins. This is the only slab with both
  \(x\)-parities, so a stabilizing translation preserves its height.
  Comparing an ordinary row with its ordinary image forces an even
  \(x\)-shift. The exceptional row must then map to itself, forcing
  the \(y\)-shift to be zero. At \(z=-4\), the odd \(y\)-origins of
  the exceptional column at \(x=0\) force the \(x\)-shift to be zero.
  Each row or column still tiles by intervals of length two. Every
  scored origin has \(z\ge0\), so neither marker changes any score.
- **Proved — strict reversals and failure of eventual periodicity.**
  Set \(t_k=8^{k+1}(k+1)!\) and \(a_k=8t_k+3\). Prescribing
  phase-zero slab counts \(2t_k\) and \(3t_k\), and swapping the
  assignments at each step, gives literal margins alternating between
  \(+4\) and \(-4\). For any proposed period \(P>0\) and cutoff,
  choose consecutive selected sizes beyond the cutoff with \(k+1\ge P\).
  Both are \(3\) modulo \(P\) because \(P\) divides both factorials.
  Eventual \(P\)-periodicity would force equal outcomes along the
  progression joining those sizes, contradicting their opposite signs.
- **Scope.** This settles the final nonperiodic part of Problem 4 for one
  fixed pair in dimension three at base zero, with independent uniform
  shifts. The construction permits both strict wins arbitrarily late in
  the same comparison, and the period counterexamples concern the
  outcome defined at every positive integral side. The proof gives no
  classification of other fleets, base points, or dimensions.

## ASSUMED-UNVERIFIED

Publication priority and coverage of unindexed work are unverified.
