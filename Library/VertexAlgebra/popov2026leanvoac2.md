---
bibkey: popov2026leanvoac2
authors: Fedor K. Popov
year: 2026
title: Lean_VOA, Classification/COne/LatticeC2.lean
doi: null
url: https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Classification/COne/LatticeC2.lean
claim: The pinned source proves C2-cofiniteness for a positive-definite even lattice VOA by sector ideals, unbounded oscillator reduction, and finite charge support.
strata_touched:
  - D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/popov2026leanvoac2 -->

# Positive-definite lattice C2 cofiniteness

## Verified locator

<https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Classification/COne/LatticeC2.lean>

The pinned Lean_VOA source is Fedor K. Popov's
`VOA/Classification/COne/LatticeC2.lean` at commit
`013a799ca834a8a6b3afa8129e3e522025b3f45c`. Its theorem
`VOA.Classification.COne.latticeVOAGen_c2Cofinite` proves finite-dimensionality
of the lattice VOA quotient by the C2 span. The port retains the sector-ideal
argument, Newton reduction of arbitrary oscillator powers, and the finite
charge-support argument while replacing the upstream carrier and fields with
the repository's literal `Carrier` and `ActualC2.C2`.

The classical C2 filtration and quotient context is Dong, Li, and Mason,
*Vertex Lie algebras, vertex Poisson algebras and vertex algebras*,
arXiv:math/0102127v1, DOI `10.1090/conm/297/05093`, especially pp. 24–26,
(5.22)–(5.26), Lemma 5.18, and Proposition 5.19. Those pages provide the
classical finite-generation mechanism; the Lean proof terms come from the
pinned Popov source and the local actual-field suppliers.

The source is released under Apache-2.0. The repository root carries the
same license terms; the upstream tree has no additional NOTICE or COPYING
file. This note records source ownership and adaptation, not a claim of
independent mathematical novelty.

## Scope

The theorem allows rank zero, every original charge fiber, every oscillator
degree, and arbitrary positive-definite integral Gram matrices with even
diagonal. It uses the closed charge box
`|B(e_i,delta)| <= G_ii`; charges outside that box have the whole sector ideal.
No determinant-unit or unimodularity premise is used. The result is an
algebraic C2-cofiniteness theorem; analytic CFT, anomaly, fusion, string
theory, and AdS/CFT remain separate mathematical obligations.

Under SPEC A17.2, retire this local proof port when the mathlib revision
pinned by this repository supplies an equivalent lattice C2-cofiniteness
theorem and an existing verified actual-field/carrier equivalence makes the
exact local statement a compiled direct application. At that point replace
the port with direct supplier usage. This condition is presently unmet;
retirement depends on the repository pin and compiled exact bridge, not on
upstream acceptance by mathlib.

Four-slot registration for `positive_definite_c2_cofinite` remains
unfinished: no faithful enrolled readout or compiled evidence for
whole-family variation, sensitivity, observational dependence, and source
selection/realization was produced.
[#28628](https://github.com/the-omega-institute/trureturing/issues/28628)
tracks these missing obligations; #25088 concerns a different theorem.
The linked-issue route under CLAUDE §3.9 permits mathematical delivery with
this audit unfinished; it does not establish `declared_validated` status.
