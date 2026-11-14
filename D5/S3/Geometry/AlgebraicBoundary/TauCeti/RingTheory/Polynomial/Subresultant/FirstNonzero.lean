/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/FirstNonzero
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/FirstNonzero
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/Polynomial/Subresultant/FirstNonzero.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.Polynomial.Subresultant.Bezout
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.Polynomial.Subresultant.GCD

/-!
# The first nonzero subresultant polynomial

Subresultant polynomials vanish below the degree of any common divisor. At the degree of a
monic common divisor, the subresultant is that divisor multiplied by its principal coefficient.
Over a field, the first nonzero subresultant polynomial therefore recovers the monic gcd, with
its scalar fixed by the determinant convention. This identifies the terminal polynomial in
comparisons of subresultants with Euclidean remainder sequences.

The polynomial identification requires a strict index: when the gcd degree equals the smaller
input degree, the terminal principal coefficient is scalar data, not a subresultant polynomial.
Formal degree bounds are retained throughout; the nonvanishing assertion uses an actual left
degree and a right degree bound, as in the principal-coefficient gcd criterion.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4, Proposition 4.25 and Corollary 4.26 (subresultants and the gcd).
-/

public section

namespace TauCeti

open Polynomial

section Domain

variable {R : Type*} [CommRing R]

/-- At the degree of a monic common divisor, a strict-index subresultant polynomial is exactly
that divisor scaled by the principal subresultant coefficient. The scalar is allowed to vanish.
No field hypothesis or actual-degree equality is required. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_of_monic_commonDivisor
    {p q g : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hg : g.Monic) (hgp : g ∣ p) (hgq : g ∣ q) (hj : g.natDegree < min m n) :
    subresultant p q m n g.natDegree = C (psc p q m n g.natDegree) * g := by
  let s := subresultant p q m n g.natDegree
  have hs : s = C s.leadingCoeff * g :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hg
      (dvd_subresultant hm hn hgp hgq)
      (natDegree_le_of_degree_le (degree_subresultant_le p q m n g.natDegree))
  have hcoeff := congrArg (fun r : R[X] => r.coeff g.natDegree) hs
  have hlc : s.leadingCoeff = psc p q m n g.natDegree := by
    simpa only [s, coeff_subresultant, hj, le_refl, and_self, ↓reduceIte,
      subresultantCoeff_self, coeff_C_mul, coeff_natDegree, hg.leadingCoeff, mul_one]
      using hcoeff.symm
  exact hs.trans (by rw [hlc])

end Domain

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- At the gcd degree, a strict-index subresultant is the monic normalization of the Euclidean
gcd scaled by its principal coefficient. This formula also permits oversized formal bounds,
where that coefficient can vanish. -/
theorem _root_.Polynomial.subresultant_natDegree_gcd {p q : K[X]} {m n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hj : (EuclideanDomain.gcd p q).natDegree < min m n) :
    subresultant p q m n (EuclideanDomain.gcd p q).natDegree =
      C (psc p q m n (EuclideanDomain.gcd p q).natDegree) *
        normalize (EuclideanDomain.gcd p q) := by
  by_cases hg : EuclideanDomain.gcd p q = 0
  · have hs := dvd_subresultant (j := (EuclideanDomain.gcd p q).natDegree) hm hn
      (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q)
    rw [hg, zero_dvd_iff] at hs
    simpa only [hg, normalize_zero, mul_zero] using hs
  simpa only [natDegree_normalize] using
    subresultant_eq_C_mul_of_monic_commonDivisor hm hn (monic_normalize hg)
      (normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left p q))
      (normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right p q))
      (by simpa only [natDegree_normalize] using hj)

end Field

end TauCeti
