---
bibkey: ho2026nivat
authors: Boon Suan Ho (software)
year: 2026
title: "boonsuan/nivat, pinned Lean sources"
doi: null
url: https://github.com/boonsuan/nivat/tree/4e3614024227acd273c3e8ab41df92c2709e5ab0
claim: "The pinned ProductDifferences source proves a nonempty product of nonzero-direction differences annihilating the original nonzero finite-range integer or rational configuration; FiniteState proves a finite bilateral deterministic-state period bounded by the number of occurring states."
strata_touched:
  - D5/S1/Dynamics/Symbolic/KhetanAnnihilator
  - D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence
license: MIT
triage: anchor
---

# Pinned product-difference and finite-state suppliers

Revision `4e3614024227acd273c3e8ab41df92c2709e5ab0` supplies
`Nivat.Algebra.exists_integer_product_differences` and
`Nivat.Algebra.exists_product_differences_of_annihilator` in
`Nivat/Algebra/ProductDifferences.lean`, and
`Nivat.TwoFactors.periodic_of_deterministic_successor_bounded` in
`Nivat/TwoFactors/FiniteState.lean`.

The first supplier's import closure used here is `Core/Basic`, `Algebra/Action`,
`Algebra/RationalScaling`, and `Algebra/ProductDifferences`. The coefficient
ring action uses positive lattice shifts. Thus exact-cover convolution uses
a mask with negative tile exponents. Directions in the supplied list are
nonzero; the statement permits parallel and repeated directions.

The product-difference statement is the version of the Kari--Szabados
annihilator theorem described in Proposition 3.3 and Appendix A of the
pinned repository's `paper/nivat.tex`; it cites Theorem 11 and Corollary 12
of Kari and Szabados, *An Algebraic Geometric Approach to Nivat's Conjecture*,
https://arxiv.org/abs/1605.05929. The finite-state argument is Lemma 5.2 of
the pinned manuscript. This note attributes the reused software and does
not validate other claims of that manuscript.

The reused portions retain the full MIT notice, including
`Copyright (c) 2026 Boon Suan Ho`, in their owning Lean source. Namespace and
module aggregation adapt the sources to D5; the supplier conclusions are
preserved. The recurrence consumer proves one common factorial period for
all integer lines, using the global alphabet to bound every line's states.
