/- GID: D5/S3/Factorization/Embeddings/FractionalIdealPrimeValuationFaithfulness
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/FractionalIdealPrimeValuationFaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All prime-ideal valuations faithfully recover a nonzero fractional ideal. -/

import Mathlib.RingTheory.DedekindDomain.Factorization

/- Library-search audit trail (2026-08-25):
   * Current-tree name and body-shape searches found no D5 declaration using
     `FractionalIdeal.count` or its reconstruction theorem, hence no exact
     frozen theorem is available for a receipt-only bind.
   * Pinned Mathlib supplies the exact source primitives: `HeightOneSpectrum R`
     for nonzero prime ideals and `FractionalIdeal.count K v I` for their
     integer exponents.
   * The exact reconstruction theorem
     `FractionalIdeal.finprod_heightOneSpectrum_factorization'` is applied
     directly below. Mathlib has no packaged injectivity implication with the
     leased statement's nonzero fractional-ideal carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace D5.S3.Factorization.Embeddings.FractionalIdealPrimeValuationFaithfulness

/-- Equal valuations at every nonzero prime ideal force equality of nonzero
fractional ideals over a Dedekind domain. -/
theorem prime_valuation_observers_faithful
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDedekindDomain R]
    (I J : {L : FractionalIdeal R⁰ K // L ≠ 0})
    (sameValuation : forall v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v I.1 = FractionalIdeal.count K v J.1) :
    I = J := by
  apply Subtype.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.2,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.2]
  apply finprod_congr
  intro v
  rw [sameValuation v]

#print axioms prime_valuation_observers_faithful

end D5.S3.Factorization.Embeddings.FractionalIdealPrimeValuationFaithfulness
