/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Spectral degree under Laurent coefficient extraction. -/
-- Adapted from uniform-horizontal-radical-degree/work_target.
module

public import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformHorizontalRadicalChart

/-! Extracting and shifting Laurent coefficients preserves spectral support. -/

public section

set_option autoImplicit false

namespace UniformMPSHorizontalSpectral

open MvPolynomial

noncomputable section

variable {σ R : Type*} [CommRing R]

/-- Outer exponents index powers of `U`, and inner exponents index powers of `k`. -/
abbrev ChartLaurent (R : Type*) [Semiring R] := LaurentPolynomial (LaurentPolynomial R)

def chartLaurentC : R →+* ChartLaurent R :=
  LaurentPolynomial.C.comp LaurentPolynomial.C

def chartU : (ChartLaurent R)ˣ := (LaurentPolynomial.isUnit_T 1).unit

def chartK : (ChartLaurent R)ˣ :=
  Units.map (LaurentPolynomial.C : LaurentPolynomial R →+* ChartLaurent R).toMonoidHom
    (LaurentPolynomial.isUnit_T (R := R) 1).unit

/-- The coefficient of `U^u k^k`, with the spectral monomials left in place. -/
def laurentSpectralCoeff (p : MvPolynomial σ (ChartLaurent R)) (u k : ℤ) : MvPolynomial σ R :=
  ∑ m ∈ p.support, monomial m (((p.coeff m).coeff u).coeff k)

@[simp] theorem coeff_laurentSpectralCoeff
    (p : MvPolynomial σ (ChartLaurent R)) (u k : ℤ) (m : σ →₀ ℕ) :
    (laurentSpectralCoeff p u k).coeff m = (((p.coeff m).coeff u).coeff k) := by
  classical
  unfold laurentSpectralCoeff
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split
  · rfl
  · simp [notMem_support_iff.mp ‹m ∉ p.support›]

theorem laurentSpectralCoeff_support_subset
    (p : MvPolynomial σ (ChartLaurent R)) (u k : ℤ) :
    (laurentSpectralCoeff p u k).support ⊆ p.support := by
  intro m hm
  simp only [mem_support_iff, coeff_laurentSpectralCoeff] at hm ⊢
  exact fun h => hm (by simp [h])

theorem laurentSpectralCoeff_totalDegree_le
    (p : MvPolynomial σ (ChartLaurent R)) (u k : ℤ) :
    (laurentSpectralCoeff p u k).totalDegree ≤ p.totalDegree := by
  unfold totalDegree
  exact Finset.sup_le fun _ hm => le_totalDegree (laurentSpectralCoeff_support_subset p u k hm)

/-- Spectral-independent specialization can only remove spectral monomials. -/
theorem specializedLaurent_support_subset {S : Type*} [CommRing S]
    (f : R →+* S) (u k : Sˣ) (p : MvPolynomial σ (ChartLaurent R)) :
    (map (LaurentPolynomial.eval₂ (LaurentPolynomial.eval₂ f k) u) p).support ⊆ p.support :=
  support_map_subset _ _

/-- Multiplying by a Laurent monomial in the Laurent coefficient ring shifts exponents. -/
def shiftChartLaurent (p : MvPolynomial σ (ChartLaurent R)) (u k : ℤ) :
    MvPolynomial σ (ChartLaurent R) :=
  C (LaurentPolynomial.T (R := LaurentPolynomial R) u *
    LaurentPolynomial.C (LaurentPolynomial.T (R := R) k)) * p

theorem laurentSpectralCoeff_shift (p : MvPolynomial σ (ChartLaurent R))
    (u k i j : ℤ) :
    laurentSpectralCoeff (shiftChartLaurent p u k) i j =
      laurentSpectralCoeff p (i - u) (j - k) := by
  ext m
  simp only [coeff_laurentSpectralCoeff, shiftChartLaurent, coeff_C_mul, mul_assoc]
  change (((AddMonoidAlgebra.single u 1 *
    (AddMonoidAlgebra.single 0 (LaurentPolynomial.T k) * p.coeff m)).coeff i).coeff j) = _
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_zero, zero_add]
  change (AddMonoidAlgebra.single k 1 * (p.coeff m).coeff (-u + i)).coeff j = _
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, sub_eq_neg_add]

/-- Both clearing by `U^6` and dividing by `k^2` preserve the same support bound. -/
theorem shiftedLaurent_support_subset (p : MvPolynomial σ (ChartLaurent R)) (u k i j : ℤ) :
    (laurentSpectralCoeff (shiftChartLaurent p u k) i j).support ⊆ p.support := by
  rw [laurentSpectralCoeff_shift]
  exact laurentSpectralCoeff_support_subset p _ _

theorem shiftedLaurent_totalDegree_le (p : MvPolynomial σ (ChartLaurent R)) (u k i j : ℤ) :
    (laurentSpectralCoeff (shiftChartLaurent p u k) i j).totalDegree ≤ p.totalDegree := by
  rw [laurentSpectralCoeff_shift]
  exact laurentSpectralCoeff_totalDegree_le p _ _

/-- Specialize only `k`, leaving a Laurent polynomial in `U`. -/
def specializeChartK (k : Rˣ) : ChartLaurent R →+* LaurentPolynomial R :=
  AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.eval₂ (RingHom.id R) k)

/-- Specialize only `U`, leaving a Laurent polynomial in `k`. -/
def specializeChartU (u : Rˣ) : ChartLaurent R →+* LaurentPolynomial R :=
  LaurentPolynomial.eval₂ (RingHom.id (LaurentPolynomial R))
    (Units.map (LaurentPolynomial.C : R →+* LaurentPolynomial R).toMonoidHom u)

/-- Read the coefficient of the remaining Laurent variable while retaining spectral variables. -/
def spectralCoeffAfterSpecialization (f : ChartLaurent R →+* LaurentPolynomial R)
    (p : MvPolynomial σ (ChartLaurent R)) (n : ℤ) : MvPolynomial σ R :=
  ∑ m ∈ p.support, monomial m ((f (p.coeff m)).coeff n)

theorem spectralCoeffAfterSpecialization_support_subset
    (f : ChartLaurent R →+* LaurentPolynomial R)
    (p : MvPolynomial σ (ChartLaurent R)) (n : ℤ) :
    (spectralCoeffAfterSpecialization f p n).support ⊆ p.support := by
  classical
  intro m hm
  by_contra houtside
  rw [mem_support_iff, spectralCoeffAfterSpecialization] at hm
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', houtside, ↓reduceIte] at hm
  exact hm rfl

theorem spectralCoeffAfterSpecialization_totalDegree_le
    (f : ChartLaurent R →+* LaurentPolynomial R)
    (p : MvPolynomial σ (ChartLaurent R)) (n : ℤ) :
    (spectralCoeffAfterSpecialization f p n).totalDegree ≤ p.totalDegree := by
  unfold totalDegree
  exact Finset.sup_le fun _ hm =>
    le_totalDegree (spectralCoeffAfterSpecialization_support_subset f p n hm)

theorem shiftChartLaurent_totalDegree_le (p : MvPolynomial σ (ChartLaurent R)) (u k : ℤ) :
    (shiftChartLaurent p u k).totalDegree ≤ p.totalDegree := by
  unfold shiftChartLaurent
  simpa only [totalDegree_C, zero_add] using totalDegree_mul (C _) p

end

end UniformMPSHorizontalSpectral
