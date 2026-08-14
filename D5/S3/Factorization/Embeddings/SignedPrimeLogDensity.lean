/- GID: D5/S3/Factorization/Embeddings/SignedPrimeLogDensity
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/SignedPrimeLogDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical rational logarithmic length is dense in the real line. -/

import D5.S3.Factorization.PositiveRationalGroup

namespace D5.S3.Factorization.Embeddings.SignedPrimeLogDensity

open D5.S3.Factorization.PositiveRationalGroup

/-- The canonical logarithmic lengths of signed prime ledgers are dense in the real line. -/
theorem rational_log_length_dense : DenseRange rationalLogLength := by
  apply dense_of_exists_between
  intro x y hxy
  apply Set.exists_range_iff.2
  obtain ⟨q, hxq, hqy⟩ :
      ∃ q : Rat, Real.exp x < (q : Real) ∧ (q : Real) < Real.exp y :=
    exists_rat_btwn (Real.exp_lt_exp.mpr hxy)
  have hqpos : 0 < q := by
    exact_mod_cast (Real.exp_pos x).trans hxq
  let qnn : NNRat := ⟨q, hqpos.le⟩
  have hqnn : qnn ≠ 0 := by
    intro hzero
    have hcast := congrArg (fun r : NNRat => (r : Rat)) hzero
    exact hqpos.ne' (by simpa [qnn] using hcast)
  let positiveQ : PositiveRational := Units.mk0 qnn hqnn
  let a : SignedPrimeLedger :=
    primeExponentEquivPositiveRational.symm (Additive.ofMul positiveQ)
  refine ⟨a, ?_, ?_⟩
  · rw [rationalLogLength, primeExponentEquivPositiveRational.apply_symm_apply]
    change x < Real.log (q : Real)
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hqpos)).mpr hxq
  · rw [rationalLogLength, primeExponentEquivPositiveRational.apply_symm_apply]
    change Real.log (q : Real) < y
    exact (Real.log_lt_iff_lt_exp (by exact_mod_cast hqpos)).mpr hqy

example {x y : Real} (hxy : x < y) :
    ∃ a : SignedPrimeLedger, x < rationalLogLength a ∧ rationalLogLength a < y := by
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := rational_log_length_dense.exists_between hxy
  exact ⟨a, ha⟩

end D5.S3.Factorization.Embeddings.SignedPrimeLogDensity
