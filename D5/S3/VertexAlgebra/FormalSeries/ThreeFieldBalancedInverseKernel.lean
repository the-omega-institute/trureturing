/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedInverseKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedInverseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Diagonal and coupled binomial kernels of the balanced native inverse. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedNativeInverse
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerInverseKernel
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedLaurentFiber
import Batteries.Tactic.OpenPrivate

/-! Carnahan's signed-binomial series is substituted only in native series.
The coupled factor is the accepted inner inverse after first-coordinate rescaling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldBalancedInverseKernel
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldBalancedNativeInverse ThreeFieldInnerNativeInverse ThreeFieldInnerInverseKernel
open ThreeFieldFinalCone
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℂ R]
open private factor_inverse binomial_coeff coeff_mul_box from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalInverseCoefficients

private def diagonal (z : ℤ) : MvPowerSeries (Fin 3) R :=
  PowerSeries.subst (MvPowerSeries.X 0 * MvPowerSeries.X 1)
    (PowerSeries.binomialSeries R z)

omit [Algebra ℂ R] in
private theorem diagonal_legal : PowerSeries.HasSubst
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  simp

omit [Algebra ℂ R] in
private theorem diagonal_pow_coeff (q r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t)
      ((MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) ^ q) =
    if r = q ∧ s = q ∧ t = 0 then 1 else 0 := by
  have power : (MvPowerSeries.X 0 * MvPowerSeries.X 1 :
      MvPowerSeries (Fin 3) R) ^ q = MvPowerSeries.monomial (index3 q q 0) 1 := by
    simp [mul_pow, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, index3]
  rw [power, MvPowerSeries.coeff_monomial]
  have eq : index3 r s t = index3 q q 0 ↔ r = q ∧ s = q ∧ t = 0 := by
    constructor
    · intro h
      exact ⟨by simpa [index3] using congrArg (fun d => d 0) h,
        by simpa [index3] using congrArg (fun d => d 1) h,
        by simpa [index3] using congrArg (fun d => d 2) h⟩
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  simp only [eq]

private theorem diagonal_coeff (z : ℤ) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (diagonal (R := R) z) =
    if s = r ∧ t = 0 then integerBinomial z r • (1 : R) else 0 := by
  classical
  rw [diagonal, PowerSeries.coeff_subst diagonal_legal, finsum_eq_single _ r]
  · rw [diagonal_pow_coeff, binomial_coeff]
    by_cases h : s = r ∧ t = 0 <;> simp [h]
  · intro q hq
    rw [diagonal_pow_coeff, ite_eq_right (by tauto), smul_zero]

private def flipS : MvPowerSeries (Fin 3) R →+* MvPowerSeries (Fin 3) R :=
  MvPowerSeries.rescale ![-1, 1, 1]

private theorem flipS_coeff (F : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (flipS F) =
      ((-1 : ℂ) ^ r) • MvPowerSeries.coeff (index3 r s t) F := by
  rw [flipS, MvPowerSeries.coeff_rescale]
  have prod : (index3 r s t).prod (fun i n => (![-1, 1, 1] : Fin 3 → R) i ^ n) =
      (-1 : R) ^ r := by
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _)]
    · simp [Fin.prod_univ_succ, index3]
    · intro i hi
      simp
  rw [prod]
  simp [Algebra.smul_def]

omit [Algebra ℂ R] in
private theorem flipS_X (i : Fin 3) :
    flipS (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) =
      (if i = 0 then -MvPowerSeries.X i else MvPowerSeries.X i) := by
  ext d
  rw [flipS, MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_X]
  by_cases hd : d = Finsupp.single i 1
  · subst d
    fin_cases i <;> simp [MvPowerSeries.coeff_X]
  · fin_cases i <;> simp_all [MvPowerSeries.coeff_X]

private def coupled (k : ℕ) : MvPowerSeries (Fin 3) R :=
  flipS (↑((innerUnit R k 0)⁻¹) : MvPowerSeries (Fin 3) R)

private theorem coupled_coeff (k r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (coupled (R := R) k) =
    if t = 0 ∧ r ≤ s then
      ((-1 : ℂ) ^ (s - r) * integerBinomial (-(k : ℤ)) r *
        integerBinomial (-((2 * k + r : ℕ) : ℤ)) (s - r)) • (1 : R)
    else 0 := by
  classical
  rw [coupled, flipS_coeff, inner_inverse_coeff, Finset.sum_eq_single 0]
  · simp only [Nat.cast_zero, neg_zero, Nat.sub_zero, integerBinomial,
      Ring.choose_zero_right, Int.cast_one, one_smul]
    by_cases h : t = 0 ∧ r ≤ s
    · rw [ite_eq_left h.1, ite_eq_left h.2, ite_eq_left h, smul_smul]
      congr 1
      have sign : (-1 : ℂ) ^ r * (-1 : ℂ) ^ s = (-1 : ℂ) ^ (s - r) := by
        rw [show s = r + (s - r) by omega, pow_add]
        calc
          _ = ((-1 : ℂ) * (-1)) ^ r * (-1 : ℂ) ^ (s - r) := by
            rw [mul_pow]
            ring
          _ = _ := by simp
      simpa only [mul_assoc] using congrArg
        (fun c : ℂ => c * (Ring.choose (-(k : ℤ)) r : ℤ) *
          (Ring.choose (-((2 * k + r : ℕ) : ℤ)) (s - r) : ℤ)) sign
    · rw [ite_eq_right h]
      by_cases ht : t = 0
      · have hrs : ¬ r ≤ s := fun hrs => h ⟨ht, hrs⟩
        rw [ite_eq_left ht, ite_eq_right hrs, smul_zero]
      · rw [ite_eq_right ht, smul_zero]
  · intro l hl hne
    have zero : integerBinomial 0 l = 0 := by
      simp [integerBinomial, Ring.choose_zero_ite, hne]
    simp [zero]
  · simp

private theorem balanced_inverse_kernels (k A : ℕ) :
    (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) =
      diagonal (-(A : ℤ)) * coupled k := by
  have unit_eq : balancedUnitSeries R k A =
      (1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ A *
        flipS (innerUnitSeries R k 0) := by
    simp only [innerUnitSeries, balancedUnitSeries, pow_zero, mul_one,
      map_mul, map_pow, map_sub, map_one, flipS_X]
    simp only [show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true]
    ring
  have cancelCoupled : flipS (innerUnitSeries R k 0) * coupled k = 1 := by
    rw [coupled, ← map_mul]
    have hc : innerUnitSeries R k 0 *
        (↑((innerUnit R k 0)⁻¹) : MvPowerSeries (Fin 3) R) = 1 :=
      (innerUnit R k 0).val_inv
    rw [hc, map_one]
  have cancel : balancedUnitSeries R k A * (diagonal (-(A : ℤ)) * coupled k) = 1 := by
    rw [unit_eq]
    calc
      _ = ((1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ A * diagonal (-(A : ℤ))) *
          (flipS (innerUnitSeries R k 0) * coupled k) := by ring
      _ = 1 := by rw [diagonal, factor_inverse _ diagonal_legal, cancelCoupled, one_mul]
  calc
    _ = (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) *
        (balancedUnitSeries R k A * (diagonal (-(A : ℤ)) * coupled k)) := by
      rw [cancel, mul_one]
    _ = _ := by
      rw [← mul_assoc, show (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) *
        balancedUnitSeries R k A = 1 from (balancedUnit R k A).inv_val, one_mul]

private theorem diagonal_mul_coeff (z : ℤ) (G : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (diagonal z * G) =
    ∑ l ∈ Finset.range (r + 1), if l ≤ s then integerBinomial z l •
      MvPowerSeries.coeff (index3 (r - l) (s - l) t) G else 0 := by
  classical
  rw [coeff_mul_box]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hls : l ≤ s
  · rw [ite_eq_left hls, Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single 0]
      · simp [diagonal_coeff]
      · intro w hw hne
        simp [diagonal_coeff, hne]
      · simp
    · intro v hv hne
      apply Finset.sum_eq_zero
      intro w hw
      simp [diagonal_coeff, hne]
    · simp only [Finset.mem_range, not_lt]
      omega
  · rw [ite_eq_right hls]
    apply Finset.sum_eq_zero
    intro v hv
    have hne : v ≠ l := by have := Finset.mem_range.mp hv; omega
    apply Finset.sum_eq_zero
    intro w hw
    simp [diagonal_coeff, hne]

/-- Full native inverse coefficients, including the forbidden cumulative degrees. -/
theorem balanced_inverse_coeff (k A r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t)
      (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) =
    ∑ l ∈ Finset.range (r + 1), if t = 0 then
      (if r ≤ s then
        (integerBinomial (-(k : ℤ)) (r - l) * integerBinomial (-(A : ℤ)) l *
          (-1 : ℂ) ^ (s - r) *
          integerBinomial (-((2 * k + (r - l) : ℕ) : ℤ)) (s - r)) • (1 : R)
      else 0) else 0 := by
  rw [balanced_inverse_kernels, diagonal_mul_coeff]
  apply Finset.sum_congr rfl
  intro l hl
  have hlr : l ≤ r := by simpa using Finset.mem_range.mp hl
  by_cases hls : l ≤ s
  · rw [ite_eq_left hls, coupled_coeff]
    by_cases ht : t = 0 <;> by_cases hrs : r ≤ s
    · rw [ite_eq_left ⟨ht, by omega⟩, ite_eq_left ht, ite_eq_left hrs, smul_smul]
      rw [show s - l - (r - l) = s - r by omega]
      congr 1
      ring
    · rw [ite_eq_right (by omega), ite_eq_left ht, ite_eq_right hrs, smul_zero]
    · rw [ite_eq_right (by tauto), ite_eq_right ht, smul_zero]
    · rw [ite_eq_right (by tauto), ite_eq_right ht, smul_zero]
  · rw [ite_eq_right hls]
    have hrs : ¬ r ≤ s := by omega
    by_cases ht : t = 0 <;> simp [ht, hrs]

end
end D5.S3.VertexAlgebra.ThreeFieldBalancedInverseKernel
