---
bibkey: mathlib2026strongconcavity
authors: The mathlib Community; Yaël Dillies; Chenyi Li; Ziyu Wang
year: 2026
title: Strong concavity, supremum approximation and completeness
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Convex/Strong.lean
claim: The pinned sources supply strong concavity, approximating sequences for a finite supremum, convergence in a complete subset, and upper semicontinuity; their midpoint Cauchy composition gives attainment without a compactness premise.
strata_touched: []
license: Citation only; the cited mathlib sources are Apache-2.0.
triage: anchor
---

# Attainment from strong concavity on a complete convex domain

The inspected Mathlib revision is
`db584cd6d46c92f209a44c0f1c829460d327499d` (Lean 4.33.0).
`Analysis/Convex/Strong.lean` defines `StrongConcaveOn s m f` with
quadratic modulus `m*r^2/2`, including convexity of the domain. Its source
credits Yaël Dillies, Chenyi Li and Ziyu Wang. The midpoint reward is
therefore `m*norm(x-y)^2/8`.

`Topology/Order/IsLUB.lean` supplies `exists_seq_tendsto_sSup` for a
nonempty bounded-above real image. `Topology/UniformSpace/Cauchy.lean`
supplies `cauchySeq_tendsto_of_isComplete` for a sequence in an actual
complete subset. `Topology/Semicontinuity/Defs.lean` supplies the
neighborhood definition of upper semicontinuity. These existing results
are reused directly.

The project result
`D5.S3.Analytic.Convexity.StrongConcavityAttainment.exists_unique_maximizer`
proves the intervening Cauchy estimate and constructs a unique maximizer
with a midpoint quadratic deficit bound. The domain may be infinite
dimensional and noncompact; a finite upper bound for the objective is an
explicit premise. This is a standard convex-analysis argument, and no
mathematical novelty is claimed.

The motivating quantum entropy application needs its own genuine
trace-norm state carrier and proofs of entropy strong concavity,
boundedness and upper semicontinuity. This reference does not assert the
original common-reference or common-Hamiltonian theorem is complete.
