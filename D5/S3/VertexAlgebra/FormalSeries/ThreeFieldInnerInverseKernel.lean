/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerInverseKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerInverseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The coupled integer-binomial kernel of the inner native inverse. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerNativeInverse
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerLaurentFiber
import Batteries.Tactic.OpenPrivate

/-! The coefficient identity combines the two x-z inverse factors before
expanding z/x. The signed-binomial suppliers are Carnahan's Mathlib results. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldInnerInverseKernel
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldInnerNativeInverse ThreeFieldFinalCone
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

open private xKernel yKernel middleKernel x_coeff y_coeff middle_coeff
  inverse_as_kernels coeff_mul_box middle_mul_coeff x_mul_coeff from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalInverseCoefficients

private theorem binomial_convolution (u v : ℤ) (n : ℕ) :
    (∑ q ∈ Finset.range (n + 1), integerBinomial u q * integerBinomial v (n - q)) =
      integerBinomial (u + v) n := by
  have h := congrArg (PowerSeries.coeff n)
    (PowerSeries.binomialSeries_add (A := ℂ) u v)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [PowerSeries.binomialSeries_coeff, integerBinomial, zsmul_eq_mul,
    Int.cast_smul_eq_zsmul, mul_one] using h.symm

private theorem choose_factor (u : ℤ) (q r : ℕ) (hr : r ≤ q) :
    integerBinomial u q * (q.choose r : ℂ) =
      integerBinomial u r * integerBinomial (u - r) (q - r) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (Ring.choose_smul_choose u hr)
  simpa [integerBinomial, nsmul_eq_mul, mul_comm] using h

private theorem coupled_convolution (k r s : ℕ) :
    (∑ q ∈ Finset.range (s + 1),
      (integerBinomial (-(k : ℤ)) q * (q.choose r : ℂ)) *
        integerBinomial (-(k : ℤ)) (s - q)) =
    if r ≤ s then integerBinomial (-(k : ℤ)) r *
      integerBinomial (-((2 * k + r : ℕ) : ℤ)) (s - r) else 0 := by
  classical
  by_cases hrs : r ≤ s
  · rw [ite_eq_left hrs]
    calc
      _ = ∑ q ∈ Finset.range (s - r + 1),
          integerBinomial (-(k : ℤ)) r *
            (integerBinomial (-(k : ℤ) - r) q *
              integerBinomial (-(k : ℤ)) (s - r - q)) := by
        symm
        apply Finset.sum_bij_ne_zero (fun q _ _ => q + r)
        · intro q hq hne
          simp only [Finset.mem_range] at hq ⊢
          omega
        · intro q hq hne q' hq' hne' heq
          omega
        · intro q hq hne
          have hrq : r ≤ q := by
            by_contra h
            simp [Nat.choose_eq_zero_of_lt (show q < r by omega)] at hne
          refine ⟨q - r, Finset.mem_range.mpr (by simp only [Finset.mem_range] at hq; omega),
            ?_, by omega⟩
          rw [choose_factor _ _ _ hrq] at hne
          simpa [show s - r - (q - r) = s - q by omega, mul_assoc] using hne
        · intro q hq hne
          rw [choose_factor _ _ _ (by omega)]
          simp only [Nat.add_sub_cancel]
          rw [show s - (q + r) = s - r - q by omega]
          ring
      _ = integerBinomial (-(k : ℤ)) r *
          integerBinomial (-(k : ℤ) - r + -(k : ℤ)) (s - r) := by
        rw [← Finset.mul_sum, binomial_convolution]
      _ = _ := by
        congr 2
        push_cast
        ring
  · rw [ite_eq_right hrs]
    apply Finset.sum_eq_zero
    intro q hq
    have hqr : q < r := by
      have := Finset.mem_range.mp hq
      omega
    simp [Nat.choose_eq_zero_of_lt hqr]

variable {R : Type*} [CommRing R] [Algebra ℂ R]

private theorem coupled_coeff (k r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t)
      (middleKernel (R := R) (-(k : ℤ)) * yKernel (-(k : ℤ))) =
    if t = 0 then
      (if r ≤ s then integerBinomial (-(k : ℤ)) r *
        integerBinomial (-((2 * k + r : ℕ) : ℤ)) (s - r) else 0) • (1 : R)
    else 0 := by
  classical
  rw [middle_mul_coeff]
  by_cases ht : t = 0
  · rw [ite_eq_left ht]
    have reduce (q : ℕ) :
        (∑ h ∈ Finset.range (r + 1),
          (integerBinomial (-(k : ℤ)) q * (q.choose h : ℂ)) •
            MvPowerSeries.coeff (index3 (r - h) (s - q) t) (yKernel (-(k : ℤ)))) =
        ((integerBinomial (-(k : ℤ)) q * (q.choose r : ℂ)) *
          integerBinomial (-(k : ℤ)) (s - q)) • (1 : R) := by
      rw [Finset.sum_eq_single r]
      · simp [y_coeff, ht, smul_smul]
      · intro h hh hne
        have hhr : h < r := by have := Finset.mem_range.mp hh; omega
        rw [y_coeff, ite_eq_right (by omega), smul_zero]
      · simp
    simp_rw [reduce]
    rw [← Finset.sum_smul, coupled_convolution]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro q hq
    apply Finset.sum_eq_zero
    intro h hh
    by_cases hrh : r - h = 0 <;> simp [y_coeff, hrh, ht]

private def flip : MvPowerSeries (Fin 3) R →+* MvPowerSeries (Fin 3) R :=
  MvPowerSeries.rescale ![1, -1, 1]

private theorem flip_coeff (F : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (flip F) =
      ((-1 : ℂ) ^ s) • MvPowerSeries.coeff (index3 r s t) F := by
  rw [flip, MvPowerSeries.coeff_rescale]
  have prod : (index3 r s t).prod (fun i n => (![1, -1, 1] : Fin 3 → R) i ^ n) =
      (-1 : R) ^ s := by
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _)]
    · simp [Fin.prod_univ_succ, index3]
    · intro i hi
      simp
  rw [prod]
  simp [Algebra.smul_def]

omit [Algebra ℂ R] in
private theorem flip_X (i : Fin 3) :
    flip (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) =
      (if i = 1 then -MvPowerSeries.X i else MvPowerSeries.X i) := by
  ext d
  rw [flip, MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_X]
  by_cases hd : d = Finsupp.single i 1
  · subst d
    fin_cases i <;> simp [MvPowerSeries.coeff_X]
  · fin_cases i <;> simp_all [MvPowerSeries.coeff_X]

private theorem inner_inverse_kernels (k H : ℕ) :
    (↑((innerUnit R k H)⁻¹) : MvPowerSeries (Fin 3) R) =
      xKernel (-(H : ℤ)) *
        flip (middleKernel (-(k : ℤ)) * yKernel (-(k : ℤ))) := by
  let a : Fin 3 → ℕ := ![k, k, 0]
  have unit_eq : flip (chartUnitSeries R H a) = innerUnitSeries R k H := by
    simp only [chartUnitSeries, innerUnitSeries, map_mul, map_pow, map_add, map_one, flip_X]
    dsimp [a]
    ring
  have hx : flip (xKernel (R := R) (-(H : ℤ))) = xKernel (-(H : ℤ)) := by
    ext d
    have idx : d = index3 (d 0) (d 1) (d 2) := by
      ext i
      fin_cases i <;> simp [index3]
    rw [idx, flip_coeff, x_coeff]
    by_cases hs : d 1 = 0 <;> by_cases ht : d 2 = 0 <;> simp [hs, ht]
  let K : MvPowerSeries (Fin 3) R :=
    flip (↑((chartUnit R H a)⁻¹) : MvPowerSeries (Fin 3) R)
  have cancel : innerUnitSeries R k H * K = 1 := by
    rw [← unit_eq, ← map_mul]
    have hc : chartUnitSeries R H a *
        (↑((chartUnit R H a)⁻¹) : MvPowerSeries (Fin 3) R) = 1 :=
      (chartUnit R H a).val_inv
    rw [hc, map_one]
  have eq : (↑((innerUnit R k H)⁻¹) : MvPowerSeries (Fin 3) R) = K := by
    calc
      _ = (↑((innerUnit R k H)⁻¹) : MvPowerSeries (Fin 3) R) *
          (innerUnitSeries R k H * K) := by rw [cancel, mul_one]
      _ = K := by
        have hc : (↑((innerUnit R k H)⁻¹) : MvPowerSeries (Fin 3) R) *
            innerUnitSeries R k H = 1 := (innerUnit R k H).inv_val
        rw [← mul_assoc, hc, one_mul]
  rw [eq]
  dsimp only [K]
  rw [inverse_as_kernels, map_mul, map_mul, hx]
  simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, mul_assoc]

theorem inner_inverse_coeff (k H r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t)
      (↑((innerUnit R k H)⁻¹) : MvPowerSeries (Fin 3) R) =
    ∑ l ∈ Finset.range (r + 1), integerBinomial (-(H : ℤ)) l •
      (if t = 0 then
        (if r - l ≤ s then
          (((-1 : ℂ) ^ s) * integerBinomial (-(k : ℤ)) (r - l) *
            integerBinomial (-((2 * k + (r - l) : ℕ) : ℤ)) (s - (r - l))) • (1 : R)
          else 0)
        else 0) := by
  rw [inner_inverse_kernels, x_mul_coeff]
  apply Finset.sum_congr rfl
  intro l hl
  rw [flip_coeff, coupled_coeff]
  by_cases ht : t = 0 <;> by_cases hs : r - l ≤ s <;>
    simp [ht, hs, smul_smul, mul_assoc]

end
end D5.S3.VertexAlgebra.ThreeFieldInnerInverseKernel
