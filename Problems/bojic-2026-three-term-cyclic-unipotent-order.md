---
slug: bojic-2026-three-term-cyclic-unipotent-order
bibkey: bojic2026semisimple
doi: null
url: https://arxiv.org/abs/2611.33216v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm.piecewise_trinomial_interface
---

# Bojic's three-distinct-offset cyclic unipotent order

## Problem

Section 11 of Ana Bojic, Semisimple–Unipotent Decomposition and the Exact Order of a Linear Cellular Automaton over F2, asks which features of the Rule 150 local valuation extend to other three-term rules on a cyclic graph. The target here is the full three-distinct-offset cyclic branch over F2.

Let n = 2^m q > 0 with q odd, let a, b, and c be distinct representatives below n, and put G = X^a + X^b + X^c. For each monic irreducible f dividing X^q − 1 with f not dividing G, take the class of G in the local quotient by f^(2^m). Its semisimple factor is required to be the odd-order unit in the local decomposition.

## Motivation

The local Rule 150 proof identifies the valuation of the unipotent factor minus one from the first positive Taylor degree at the residue root. For a general trinomial, divide all offsets by their largest common power of two s. If one or three normalized offsets are odd, the normalized degree is one. If exactly two are odd, order the odd pair as A < D, let d be the largest power of two dividing D − A, and let b0 be the largest power of two dividing the even offset, with the constant offset treated separately. The normalized first surviving degree is determined by whether the residue root separates the odd pair, whether d and b0 agree, and whether the two constant coefficients cancel. The original trinomial's first positive Taylor degree is s times the normalized degree.

## Gap

The paper leaves the extension of the local valuation argument to other three-term cyclic rules open in Section 11. The formal target covers every eligible factor of X^q − 1, every thickness exponent, and every distinct triple in the cyclic window. The full cycle of length 2^m q can be even. The statement includes the zero offset and the cancellation branch.

## Route

Taylor expansion in the residue field is represented by the polynomial jet at the residue root. The first positive coefficient gives an exact divisibility criterion for the jet difference. Frobenius squaring transports the first positive degree through the common dyadic factor. In the two-odd branch, the shifted pair and the shifted even term have dyadic factors whose constant coefficients either survive at the smaller degree or cancel at the common degree, where the next coefficient is nonzero. The local quotient then transfers this valuation to the unipotent factor after cancelling the odd-order semisimple unit.

## Falsifier

A tuple satisfying the stated cyclic hypotheses for which the first positive jet degree differs from preregisteredDegree, or for which the local quotient valuation or least power-of-two order differs from the displayed conclusions, would refute the theorem. The factor must divide X^q − 1, the trinomial must be a local unit, and the three offsets must be pairwise distinct.

## Evidence

The named Lean declaration is
D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm.piecewise_trinomial_interface.

It proves existence and uniqueness of the semisimple factor, the equivalence
n ≤ min(preregisteredDegree, 2^m) iff n ≤ 2^m and f^n divides v
for every local decomposition, and the least power-of-two order condition
2^m ≤ preregisteredDegree · p.

The implementation imports the frozen Rule 150 module and uses its Local and IsSemisimplePart definitions. The source paper is recorded by the existing Library note bojic2026semisimple.

Content admission uses the coefficient-cancellation witness. When the leading terms cancel at equal dyadic depth d, the shifted even summand has zero coefficient at the next degree and the odd prefix leaves a nonzero coefficient. The proof of `firstPositive_scaled_trinomial` transports this degree through Frobenius scaling, and the local valuation and order proofs consume that first-positive degree. [Preregistered scope](https://github.com/the-omega-institute/trureturing/issues/35045)

The §3.9 audit for `BojicThreeTerm.piecewise_trinomial_interface` is incomplete. It needs a source-bound bridge to the actual degree function and variation and dependence on valid cyclic inputs. The public `BojicRule150` helpers `project_eq_zero`, `project_X_pow`, `local_pow_eq_of_reduce_eq`, `reduce_eq_of_isSemisimplePart`, and `semisimple_order_eq_residue_order` each need a typed source binding with variation, sensitivity, and dependence evidence. [#35075](https://github.com/the-omega-institute/trureturing/issues/35075)

## Triage

theorem. The declaration settles the three-distinct-offset cyclic branch of the Section 11 direction. Its hypotheses retain the full cyclic range, pairwise distinctness, the primary factor condition, and local invertibility. The branch for other finite graphs remains open.

## ASSUMED-UNVERIFIED

The versioned paper establishes the historical Section 11 wording. Worldwide priority and the status of independent solutions are outside the verification recorded here. Canonical status depends on the compiled source, Scribe projection, registration evidence, and later freeze checks.
