/- GID: D5/S3/Zeros/GRH/Lib/General/NumberTheory/ClassNumberBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/NumberTheory/ClassNumberBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.NumberTheory.ClassNumberBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/NumberTheory/ClassNumberBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.ProcyclicImage
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Crude bound for the class number by degree and discriminant. -/

open NumberField Ideal Module Set Real Nat

/-- The class number of a number field F of degree n over ℚ is at most (2ⁿ |disc F|)^{n+1}. -/
lemma classNumber_le F [Field F] [NumberField F] :
    classNumber F ≤ (2 ^ finrank ℚ F * (discr F).natAbs) ^ (finrank ℚ F + 1) := by
  have {B} (n : Ioc 0 B) := (span {(n : 𝓞 F)}).absNorm_ne_zero_iff.1 (by aesop)
  grw [classNumber, ← card_eq_fintype_card, (card_le_card_of_surjective (fun x ↦ .mk0
    ⟨span {↑x.1, x.2.out}, by simp; grind⟩) fun C ↦ ?_).trans_eq (@card_sigma _ _ _ this),
    Finset.sum_le_sum fun n _ ↦ (absNorm_span_natCast n.1).trans_le (by grw [n.2.2])]
  simpa [RingOfIntegers.rank] using pow_succ'.ge
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  have := absNorm_pos_of_nonZeroDivisors I
  cases IsDedekindDomain.exists_sup_span_eq I.1.span_singleton_absNorm_le (by aesop)
  use ⟨⟨_, this, ?_⟩, ‹𝓞 F›⟩
  simp_all [← comap_map_quotientMk, span_insert]
  rify
  grw [hI, factorial_le_pow, ← two_le_pi, sqrt_le_self_iff.2 (mod_cast by grind)]; ring
  bound [InfinitePlace.card_add_two_mul_card_eq_rank F]
