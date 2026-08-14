/- GID: D5/S3/Factorization/Embeddings/SignedPrimeLogEmbedding
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/SignedPrimeLogEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical rational logarithmic length faithfully embeds signed prime ledgers. -/

import D5.S3.Factorization.PositiveRationalGroup

namespace D5.S3.Factorization.Embeddings.SignedPrimeLogEmbedding

open D5.S3.Factorization.PositiveRationalGroup

/-- The canonical logarithmic length retains every signed prime exponent. -/
theorem rational_log_length_injective :
    Function.Injective rationalLogLength := by
  intro a b hlog
  have ha :
      0 < (((((primeExponentEquivPositiveRational a).toMul : NNRat) : Rat) : Real)) := by
    exact_mod_cast
      (pos_iff_ne_zero.mpr (primeExponentEquivPositiveRational a).toMul.ne_zero)
  have hb :
      0 < (((((primeExponentEquivPositiveRational b).toMul : NNRat) : Rat) : Real)) := by
    exact_mod_cast
      (pos_iff_ne_zero.mpr (primeExponentEquivPositiveRational b).toMul.ne_zero)
  have hvalue :
      (((((primeExponentEquivPositiveRational a).toMul : NNRat) : Rat) : Real)) =
        (((((primeExponentEquivPositiveRational b).toMul : NNRat) : Rat) : Real)) :=
    Real.log_injOn_pos ha hb (by simpa [rationalLogLength] using hlog)
  apply primeExponentEquivPositiveRational.injective
  apply Additive.toMul.injective
  apply Units.ext
  exact_mod_cast hvalue

example {a b : SignedPrimeLedger} (h : rationalLogLength a = rationalLogLength b) :
    a = b :=
  rational_log_length_injective h

end D5.S3.Factorization.Embeddings.SignedPrimeLogEmbedding
