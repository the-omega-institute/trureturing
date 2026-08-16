/- GID: D5/S3/Factorization/Cyclotomic/GeometricSpectrumFactorization
   generality: G
   mirror-B: D5/B/S3/Factorization/Cyclotomic/GeometricSpectrumFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite geometric sum factors over the nontrivial cyclotomic divisors. -/

import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace D5.S3.Factorization.Cyclotomic.GeometricSpectrumFactorization

/-- For positive `n`, the geometric-sum polynomial is the product of the cyclotomic
polynomials indexed by the divisors of `n` other than one. -/
theorem geometric_sum_eq_cyclotomic_product
    (R : Type*) [CommRing R] {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, (Polynomial.X : Polynomial R) ^ i =
      ∏ d ∈ n.divisors.erase 1, Polynomial.cyclotomic d R :=
  (Polynomial.prod_cyclotomic_eq_geom_sum hn R).symm

#print axioms geometric_sum_eq_cyclotomic_product

end D5.S3.Factorization.Cyclotomic.GeometricSpectrumFactorization
