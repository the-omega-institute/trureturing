/- GID: D5/S1/Deficit/Displacement/PrimeRadicalPositivity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves nonnegativity of Real.log (primeRadical n) for every natural n. -/

import Mathlib
import D5.S1.Deficit.AlmostAdditivity

/- Provenance: Native proof over pinned mathlib. -/

/-!
Search receipt (pinned sources, inspected 2026-08-18):

* Mathlib: `Mathlib/RingTheory/Radical/NatInt.lean:51` identifies `Nat.radical`
  with the product over `Nat.primeFactors`, and `:54` proves its unconditional positivity;
  `Mathlib/Data/Nat/Factorization/Basic.lean:350` gives `Nat.prod_primeFactors_dvd`;
  `Mathlib/Data/Nat/PrimeFin.lean:35,65,71-79` gives the definition, factor positivity,
  and the empty-product cases (`n = 0` or `n = 1`);
  `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:55` gives
  `Finset.one_le_prod`; and `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:212`
  gives `Real.log_nonneg`. Pinned mathlib does not state the logarithmic
  nonnegativity of the repository's `primeRadical`, so that statement is the only
  declaration published here; the natural-number lower bound it needs is a one-step
  consequence of `Nat.radical_pos` and is therefore proved inline rather than exposed.
* Lean core: a targeted search under the pinned `src/lean` found no declarations for
  `primeFactors`, natural-number radicals, `one_le_prod`, or `log_nonneg`; the sole
  inspected textual `radical` candidate, `Lean/Meta/Sym.lean:90`, is prose about
  radically different proof terms and is unrelated.
* Repository: `D5/S1/Deficit/AlmostAdditivity.lean:18` defines `primeRadical`;
  `:114` states `lambdaMinus_almost_additive`, which bounds by `Real.log (primeRadical _)`
  but does not expose its nonnegativity.
  `D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.lean:65,112` proves a
  private logarithmic sum identity and a private nonnegativity theorem, while its
  public results at `:86` and `:124` state a radical window and an absolute
  `lambdaMinus` bound; the latter consumes the private nonnegativity theorem at `:127`.
  `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.lean:57-62` independently proves
  the same private nonnegativity theorem by a different route and inlines the product
  lower bound; its public radical results at `:27,43` are invariance statements, not
  either bound.
  The inspected repository declarations therefore do not already expose the target
  statement, and it is not a one-step corollary of those frozen public results.
  Because the two proofs above are `private` inside frozen modules, importers cannot
  reach them, so publishing the statement in this new file is the conservative
  extension available.

This list of inspected candidates is not claimed to be exhaustive.
-/

open D5.S1.Deficit.AlmostAdditivity

namespace D5.S1.Deficit.Displacement.PrimeRadicalPositivity

/-- The logarithm of the prime radical is nonnegative, including for `n = 0` and `n = 1`,
whose prime-factor finsets are empty and whose radical is therefore `1`. -/
theorem log_primeRadical_nonneg (n : ℕ) : 0 ≤ Real.log (primeRadical n) := by
  apply Real.log_nonneg
  have hone : 1 ≤ primeRadical n := by
    rw [primeRadical, ← Nat.radical_eq_prod_primeFactors]
    exact Nat.radical_pos n
  exact_mod_cast hone

end D5.S1.Deficit.Displacement.PrimeRadicalPositivity

#print axioms D5.S1.Deficit.Displacement.PrimeRadicalPositivity.log_primeRadical_nonneg
