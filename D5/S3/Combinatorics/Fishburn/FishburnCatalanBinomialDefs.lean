/- GID: D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs
   mirror-E: none(waiver:fixed-fishburn-catalan-binomial-statement-definition)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Catalan.Basic]
   utility: none
   digest: Egge's Conjecture 10.13 on two Fishburn classes counted by a binomial-Catalan sum. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnCatalanBinomialDefs

open D5.S3.Combinatorics

/-! Fixed public statement: Egge, *Pattern-Avoiding Fishburn Permutations and Ascent
    Sequences*, arXiv:2208.01484v1, §10, Conjecture 10.13.  `F_n(B)` is
    `FishburnDefs.avoiders`; `catalan` is Mathlib's Catalan sequence. -/

/-- The binomial transform `∑_{k=1}^{n} C(n-1,k-1) Cat(n-k)`. -/
def binomialCatalan (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (n - 1).choose (k - 1) * catalan (n - k)

/-- Conjecture 10.13: for `n ≥ 1`,
    `|F_n(2413, 2431)| = |F_n(2431, 3241)| = ∑_{k=1}^{n} C(n-1,k-1) Cat(n-k)`. -/
def claim1013 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (FishburnDefs.avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]).ncard = binomialCatalan n ∧
    (FishburnDefs.avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]]).ncard = binomialCatalan n

end D5.S3.Combinatorics.Fishburn.FishburnCatalanBinomialDefs
