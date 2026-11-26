/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Noncommutative operator Cauchy-Schwarz rigidity and clock-area bounds. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Noncommutative Clock-Area Bounds and Shear-Focusing Rigidity

Motivated by the null-cone gravitational clock and corner-area bound in
Chandrasekaran (arXiv:2611.34924v1, Eqs. 3.28, 4.26–4.27, 5.21a–d), this module proves:

1. An exact noncommutative weighted operator Cauchy–Schwarz identity on an arbitrary complex
   Hilbert space `H` for any finite family of (not necessarily commuting) self-adjoint bounded
   operators `A i`, together with exact uniformity rigidity for the zero-deficit case.
2. A fully noncommutative Hilbert-space lower bound for the shear-delayed clock quadratic form
   `Q(η) = (1 - ε) ∑ w i Re ⟪A i η, E i (A i η)⟫` whenever `E i ≥ 1` and `∑ w i ‖A i η‖² = A ‖η‖²`,
   yielding the sharp corner-area upper bound `A ≤ M ℓ² / (1 - ε)²` without classical Wigner
   approximations or commutativity assumptions on the density operators `A i`.
3. The exact two-channel classical deficit decomposition separating corner-density inhomogeneity
   from nonnegative shear-focusing delay, characterizing equality uniquely by zero shear and
   uniform corner density.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace ComplexConjugate

namespace D5.S3.Quantum.Analysis.NullConeGravity.NullConeClockAreaBound

section OperatorCauchySchwarz

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

/-- Exact noncommutative weighted operator Cauchy–Schwarz identity: for any finite family of
(not necessarily commuting) bounded linear operators `A i` on a complex Hilbert space `H` and
real weights `w i`, the weighted variance defect equals half the double sum of pairwise squared
norm differences. -/
theorem operator_weighted_cauchy_schwarz_identity (s : Finset ι) (w : ι → ℝ)
    (A : ι → H →L[ℂ] H) (η : H) :
    (∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖A i η‖ ^ 2) -
      ‖(∑ i ∈ s, (w i : ℂ) • A i) η‖ ^ 2 =
    (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖(A i - A j) η‖ ^ 2 := by
  have hsum_apply :
      (∑ i ∈ s, (w i : ℂ) • A i) η = ∑ i ∈ s, (w i : ℂ) • (A i η) := by
    simp
  have hnorm_sum :
      ‖∑ i ∈ s, (w i : ℂ) • (A i η)‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * (⟪A i η, A j η⟫_ℂ).re := by
    have hre :
        (‖∑ i ∈ s, (w i : ℂ) • (A i η)‖ ^ 2 : ℝ) =
          (⟪∑ i ∈ s, (w i : ℂ) • (A i η), ∑ j ∈ s, (w j : ℂ) • (A j η)⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K]
      change (‖∑ i ∈ s, (w i : ℂ) • (A i η)‖ ^ 2 : ℝ) =
        (((‖∑ i ∈ s, (w i : ℂ) • (A i η)‖ : ℂ) ^ 2)).re
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hre, sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hmul :
        (w i : ℂ) * ((w j : ℂ) * ⟪A i η, A j η⟫_ℂ) =
          ((w i * w j : ℝ) : ℂ) * ⟪A i η, A j η⟫_ℂ := by
      push_cast
      ring
    rw [hmul, Complex.re_ofReal_mul]
  have hdiff_norm : ∀ i j : ι,
      ‖(A i - A j) η‖ ^ 2 =
        ‖A i η‖ ^ 2 - 2 * (⟪A i η, A j η⟫_ℂ).re + ‖A j η‖ ^ 2 := by
    intro i j
    change ‖A i η - A j η‖ ^ 2 = _
    rw [@norm_sub_sq ℂ H _ _ _ (A i η) (A j η)]
    rfl
  rw [hsum_apply, hnorm_sum]
  simp_rw [hdiff_norm]
  have hrhs :
      ∑ i ∈ s, ∑ j ∈ s,
        w i * w j * (‖A i η‖ ^ 2 - 2 * (⟪A i η, A j η⟫_ℂ).re + ‖A j η‖ ^ 2) =
      (∑ i ∈ s, w i * ‖A i η‖ ^ 2) * (∑ j ∈ s, w j)
        - 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * (⟪A i η, A j η⟫_ℂ).re)
        + (∑ i ∈ s, w i) * (∑ j ∈ s, w j * ‖A j η‖ ^ 2) := by
    have hexpand : ∀ i ∈ s,
        ∑ j ∈ s, w i * w j * (‖A i η‖ ^ 2 - 2 * (⟪A i η, A j η⟫_ℂ).re + ‖A j η‖ ^ 2) =
          (w i * ‖A i η‖ ^ 2) * (∑ j ∈ s, w j)
            - 2 * (∑ j ∈ s, w i * w j * (⟪A i η, A j η⟫_ℂ).re)
            + w i * (∑ j ∈ s, w j * ‖A j η‖ ^ 2) := by
      intro i _
      have h1 :
          ∑ j ∈ s, w i * w j * (‖A i η‖ ^ 2 - 2 * (⟪A i η, A j η⟫_ℂ).re + ‖A j η‖ ^ 2) =
            ∑ j ∈ s, ((w i * ‖A i η‖ ^ 2) * w j - 2 * (w i * w j * (⟪A i η, A j η⟫_ℂ).re) +
              w i * (w j * ‖A j η‖ ^ 2)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hrhs]
  ring

/-- Nonnegative operator Cauchy–Schwarz inequality for arbitrary noncommuting operators. -/
theorem operator_weighted_cauchy_schwarz_le (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (A : ι → H →L[ℂ] H) (η : H) :
    ‖(∑ i ∈ s, (w i : ℂ) • A i) η‖ ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖A i η‖ ^ 2) := by
  have hid := operator_weighted_cauchy_schwarz_identity s w A η
  have hnonneg :
      0 ≤ (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖(A i - A j) η‖ ^ 2 := by
    apply mul_nonneg (by norm_num)
    refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    exact mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)
  linarith

/-- Exact uniformity rigidity: for strictly positive weights, the noncommutative operator
Cauchy–Schwarz inequality attains equality on `η` if and only if all operators `A i` act
identically on `η`. -/
theorem operator_weighted_cauchy_schwarz_eq_iff (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (A : ι → H →L[ℂ] H) (η : H) :
    ‖(∑ i ∈ s, (w i : ℂ) • A i) η‖ ^ 2 =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * ‖A i η‖ ^ 2) ↔
    ∀ i ∈ s, ∀ j ∈ s, A i η = A j η := by
  have hid := operator_weighted_cauchy_schwarz_identity s w A η
  constructor
  · intro heq i hi j hj
    have hsum0 :
        ∑ a ∈ s, ∑ b ∈ s, w a * w b * ‖(A a - A b) η‖ ^ 2 = 0 := by
      linarith
    have houter : ∀ a ∈ s, 0 ≤ ∑ b ∈ s, w a * w b * ‖(A a - A b) η‖ ^ 2 := fun a ha =>
      Finset.sum_nonneg fun b hb =>
        mul_nonneg (mul_nonneg (hw a ha).le (hw b hb).le) (sq_nonneg _)
    have hi0 : ∑ b ∈ s, w i * w b * ‖(A i - A b) η‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg houter).mp hsum0 i hi
    have hinner : ∀ b ∈ s, 0 ≤ w i * w b * ‖(A i - A b) η‖ ^ 2 := fun b hb =>
      mul_nonneg (mul_nonneg (hw i hi).le (hw b hb).le) (sq_nonneg _)
    have hij0 : w i * w j * ‖(A i - A j) η‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hinner).mp hi0 j hj
    have hpos : 0 < w i * w j := mul_pos (hw i hi) (hw j hj)
    have hnorm0 : ‖(A i - A j) η‖ ^ 2 = 0 := (mul_eq_zero.mp hij0).resolve_left hpos.ne'
    have hsub0 : (A i - A j) η = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm0)
    exact sub_eq_zero.mp hsub0
  · intro hunif
    have hzero : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖(A i - A j) η‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
      have hsub : (A i - A j) η = 0 := sub_eq_zero.mpr (hunif i hi j hj)
      rw [hsub, norm_zero]
      ring
    linarith

/-- Noncommutative operator lower bound for the shear-delayed null-cone clock quadratic form:
for arbitrary (not necessarily commuting) density operators `A i` with fixed total area
`∑ w i ‖A i η‖² = area * ‖η‖²`, positive self-adjoint square root `B` of
`a = ∑ w i A i` (`B² = a`), and focusing operators `E i ≥ 1` (`‖v‖² ≤ Re ⟪v, E i v⟫`),
the clock quadratic form obeys `Q(η) ≥ (1 - ε) √(area / M) ‖B η‖²`. -/
theorem operator_shear_clock_lower_bound (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hM : 0 < ∑ i ∈ s, w i)
    (ε area : ℝ) (hε : ε < 1) (harea : 0 ≤ area)
    (A E : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hB_sa : IsSelfAdjoint B)
    (hB_sq : B * B = ∑ i ∈ s, (w i : ℂ) • A i)
    (hE : ∀ i ∈ s, ∀ v : H, ‖v‖ ^ 2 ≤ (⟪v, E i v⟫_ℂ).re)
    (η : H) (hA_area : ∑ i ∈ s, w i * ‖A i η‖ ^ 2 = area * ‖η‖ ^ 2) :
    (1 - ε) * Real.sqrt (area / (∑ i ∈ s, w i)) * ‖B η‖ ^ 2 ≤
      (1 - ε) * ∑ i ∈ s, w i * (⟪A i η, E i (A i η)⟫_ℂ).re := by
  set M : ℝ := ∑ i ∈ s, w i
  set aOp : H →L[ℂ] H := ∑ i ∈ s, (w i : ℂ) • A i
  have h1mε : 0 < 1 - ε := sub_pos.mpr hε
  -- Step 1: Focusing monotonicity E i ≥ 1 gives Q(η) ≥ (1 - ε) * area * ‖η‖².
  have hstep1 :
      (1 - ε) * (area * ‖η‖ ^ 2) ≤
        (1 - ε) * ∑ i ∈ s, w i * (⟪A i η, E i (A i η)⟫_ℂ).re := by
    apply mul_le_mul_of_nonneg_left _ h1mε.le
    rw [← hA_area]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hE i hi (A i η)) (hw i hi)
  -- Step 2: Noncommutative operator Cauchy–Schwarz gives ‖aOp η‖ ≤ √(M * area) * ‖η‖.
  have ha_sq : ‖aOp η‖ ^ 2 ≤ (Real.sqrt (M * area) * ‖η‖) ^ 2 := by
    have hcs := operator_weighted_cauchy_schwarz_le s w hw A η
    rw [hA_area] at hcs
    have hMa : 0 ≤ M * area := mul_nonneg hM.le harea
    calc
      ‖aOp η‖ ^ 2 ≤ M * (area * ‖η‖ ^ 2) := hcs
      _ = (M * area) * ‖η‖ ^ 2 := by ring
      _ = (Real.sqrt (M * area)) ^ 2 * ‖η‖ ^ 2 := by rw [Real.sq_sqrt hMa]
      _ = (Real.sqrt (M * area) * ‖η‖) ^ 2 := by ring
  have ha_norm : ‖aOp η‖ ≤ Real.sqrt (M * area) * ‖η‖ := by
    have h1 : 0 ≤ ‖aOp η‖ := norm_nonneg _
    have h2 : 0 ≤ Real.sqrt (M * area) * ‖η‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    nlinarith
  -- Step 3: ‖B η‖² = Re ⟪η, B² η⟫ = Re ⟪η, aOp η⟫ ≤ ‖η‖ ‖aOp η‖ ≤ √(M * area) ‖η‖².
  have hB_norm_sq : ‖B η‖ ^ 2 ≤ Real.sqrt (M * area) * ‖η‖ ^ 2 := by
    have hB_adj : ContinuousLinearMap.adjoint B = B :=
      (ContinuousLinearMap.star_eq_adjoint B).symm.trans hB_sa
    have hinner : ⟪B η, B η⟫_ℂ = ⟪η, aOp η⟫_ℂ := by
      calc
        ⟪B η, B η⟫_ℂ = ⟪η, ContinuousLinearMap.adjoint B (B η)⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right B η (B η)).symm
        _ = ⟪η, B (B η)⟫_ℂ := by rw [hB_adj]
        _ = ⟪η, (B * B) η⟫_ℂ := rfl
        _ = ⟪η, aOp η⟫_ℂ := by rw [hB_sq]
    have hre : ‖B η‖ ^ 2 = (⟪η, aOp η⟫_ℂ).re := by
      have hself : (‖B η‖ ^ 2 : ℝ) = (⟪B η, B η⟫_ℂ).re := by
        rw [inner_self_eq_norm_sq_to_K]
        change (‖B η‖ ^ 2 : ℝ) = (((‖B η‖ : ℂ) ^ 2)).re
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hself, hinner]
    calc
      ‖B η‖ ^ 2 = (⟪η, aOp η⟫_ℂ).re := hre
      _ ≤ ‖⟪η, aOp η⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖η‖ * ‖aOp η‖ := norm_inner_le_norm η (aOp η)
      _ ≤ ‖η‖ * (Real.sqrt (M * area) * ‖η‖) := mul_le_mul_of_nonneg_left ha_norm (norm_nonneg _)
      _ = Real.sqrt (M * area) * ‖η‖ ^ 2 := by ring
  -- Step 4: Multiply by √(area / M) and use √(area / M) * √(M * area) = area.
  have hstep2 :
      Real.sqrt (area / M) * ‖B η‖ ^ 2 ≤ area * ‖η‖ ^ 2 := by
    have hprod : Real.sqrt (area / M) * Real.sqrt (M * area) = area := by
      rw [← Real.sqrt_mul (div_nonneg harea hM.le)]
      have hsimp : area / M * (M * area) = area ^ 2 := by
        field_simp [hM.ne']
      rw [hsimp, Real.sqrt_sq harea]
    calc
      Real.sqrt (area / M) * ‖B η‖ ^ 2
          ≤ Real.sqrt (area / M) * (Real.sqrt (M * area) * ‖η‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hB_norm_sq (Real.sqrt_nonneg _)
      _ = (Real.sqrt (area / M) * Real.sqrt (M * area)) * ‖η‖ ^ 2 := by ring
      _ = area * ‖η‖ ^ 2 := by rw [hprod]
  calc
    (1 - ε) * Real.sqrt (area / M) * ‖B η‖ ^ 2
        = (1 - ε) * (Real.sqrt (area / M) * ‖B η‖ ^ 2) := by ring
    _ ≤ (1 - ε) * (area * ‖η‖ ^ 2) := mul_le_mul_of_nonneg_left hstep2 h1mε.le
    _ ≤ (1 - ε) * ∑ i ∈ s, w i * (⟪A i η, E i (A i η)⟫_ℂ).re := hstep1

/-- Sharp corner-area ceiling from a bounded noncommutative gravitational clock reading:
under the hypotheses of `operator_shear_clock_lower_bound`, any nonzero vector `B η ≠ 0`
with clock reading at most `ℓ` satisfies `area ≤ M * ℓ² / (1 - ε)²`. -/
theorem operator_clock_area_upper_bound (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hM : 0 < ∑ i ∈ s, w i)
    (ε area ℓ : ℝ) (hε : ε < 1) (harea : 0 ≤ area) (_hℓ : 0 ≤ ℓ)
    (A E : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hB_sa : IsSelfAdjoint B)
    (hB_sq : B * B = ∑ i ∈ s, (w i : ℂ) • A i)
    (hE : ∀ i ∈ s, ∀ v : H, ‖v‖ ^ 2 ≤ (⟪v, E i v⟫_ℂ).re)
    (η : H) (hBη : B η ≠ 0)
    (hA_area : ∑ i ∈ s, w i * ‖A i η‖ ^ 2 = area * ‖η‖ ^ 2)
    (hclock : (1 - ε) * ∑ i ∈ s, w i * (⟪A i η, E i (A i η)⟫_ℂ).re ≤ ℓ * ‖B η‖ ^ 2) :
    area ≤ (∑ i ∈ s, w i) * ℓ ^ 2 / (1 - ε) ^ 2 := by
  set M : ℝ := ∑ i ∈ s, w i
  have h1mε : 0 < 1 - ε := sub_pos.mpr hε
  have hlow :=
    operator_shear_clock_lower_bound s w hw hM ε area hε harea A E B hB_sa hB_sq hE η hA_area
  have hnorm_pos : 0 < ‖B η‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hBη)
  have hsqrt_le : (1 - ε) * Real.sqrt (area / M) ≤ ℓ := by
    have hcomb : (1 - ε) * Real.sqrt (area / M) * ‖B η‖ ^ 2 ≤ ℓ * ‖B η‖ ^ 2 := hlow.trans hclock
    exact le_of_mul_le_mul_right hcomb hnorm_pos
  have hdiv : Real.sqrt (area / M) ≤ ℓ / (1 - ε) := (le_div_iff₀' h1mε).mpr hsqrt_le
  have hsq : area / M ≤ (ℓ / (1 - ε)) ^ 2 := by
    have h1 := mul_self_le_mul_self (Real.sqrt_nonneg _) hdiv
    rw [Real.mul_self_sqrt (div_nonneg harea hM.le)] at h1
    simpa [pow_two] using h1
  have hfin : area ≤ (ℓ / (1 - ε)) ^ 2 * M := (div_le_iff₀ hM).mp hsq
  calc
    area ≤ (ℓ / (1 - ε)) ^ 2 * M := hfin
    _ = M * ℓ ^ 2 / (1 - ε) ^ 2 := by
      rw [div_pow]
      ring

end OperatorCauchySchwarz

section ClassicalDeficitRigidity

variable {ι : Type*}

/-- Area-weighted gravitational clock reading with corner facet weights `w`, positive corner
densities `ρ`, radial cutoff `ε`, and per-generator shear delay `δ`. -/
def shearDelayedClock (s : Finset ι) (w ρ δ : ι → ℝ) (ε : ℝ) : ℝ :=
  (∑ i ∈ s, w i * ρ i * ((1 - ε) * ρ i + δ i)) / (∑ i ∈ s, w i * ρ i)

/-- Exact two-channel deficit decomposition and uniform-cap rigidity for the shear-delayed clock:
the excess of `shearDelayedClock` over the round shear-free floor `(1 - ε) √(A / M)` splits into
two nonnegative terms (corner-density inhomogeneity plus shear-focusing delay), and vanishes if
and only if every shear delay vanishes and the corner density is uniform across `s`. -/
theorem shear_clock_deficit_and_rigidity (s : Finset ι) (hs : s.Nonempty)
    (w ρ δ : ι → ℝ) (ε : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hρ : ∀ i ∈ s, 0 < ρ i) (hδ : ∀ i ∈ s, 0 ≤ δ i)
    (hε : ε < 1) :
    let M := ∑ i ∈ s, w i
    let a := ∑ i ∈ s, w i * ρ i
    let area := ∑ i ∈ s, w i * ρ i ^ 2
    shearDelayedClock s w ρ δ ε - (1 - ε) * Real.sqrt (area / M) =
      (1 - ε) * (area / a - Real.sqrt (area / M)) + (∑ i ∈ s, w i * ρ i * δ i) / a ∧
    0 ≤ (1 - ε) * (area / a - Real.sqrt (area / M)) ∧
    0 ≤ (∑ i ∈ s, w i * ρ i * δ i) / a ∧
    (shearDelayedClock s w ρ δ ε = (1 - ε) * Real.sqrt (area / M) ↔
      (∀ i ∈ s, δ i = 0) ∧ (∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j)) := by
  intro M a area
  have h1mε : 0 < 1 - ε := sub_pos.mpr hε
  have hM : 0 < M := Finset.sum_pos hw hs
  have ha : 0 < a := Finset.sum_pos (fun i hi => mul_pos (hw i hi) (hρ i hi)) hs
  have harea : 0 < area :=
    Finset.sum_pos (fun i hi => mul_pos (hw i hi) (sq_pos_of_pos (hρ i hi))) hs
  -- Exact weighted Lagrange identity: M * area - a² = (1/2) ∑∑ w i w j (ρ i - ρ j)².
  have hlag :
      M * area - a ^ 2 = (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 := by
    have hrhs :
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 =
          (∑ i ∈ s, w i * ρ i ^ 2) * (∑ j ∈ s, w j)
            - 2 * (∑ i ∈ s, w i * ρ i) * (∑ j ∈ s, w j * ρ j)
            + (∑ i ∈ s, w i) * (∑ j ∈ s, w j * ρ j ^ 2) := by
      have hexp : ∀ i ∈ s,
          ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 =
            (w i * ρ i ^ 2) * (∑ j ∈ s, w j)
              - 2 * (w i * ρ i) * (∑ j ∈ s, w j * ρ j)
              + w i * (∑ j ∈ s, w j * ρ j ^ 2) := by
        intro i _
        have h1 :
            ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 =
              ∑ j ∈ s, ((w i * ρ i ^ 2) * w j - (2 * (w i * ρ i)) * (w j * ρ j) +
                w i * (w j * ρ j ^ 2)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      have h2 : ∑ i ∈ s, 2 * (w i * ρ i) = 2 * ∑ i ∈ s, w i * ρ i := by
        rw [← Finset.mul_sum]
      rw [h2]
    rw [hrhs]
    dsimp [M, a, area]
    ring
  have hcs_sq : a ^ 2 ≤ M * area := by
    have hnn : 0 ≤ (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 := by
      apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
        mul_nonneg (mul_nonneg (hw i hi).le (hw j hj).le) (sq_nonneg _)
    linarith
  have hcs_div : Real.sqrt (area / M) ≤ area / a := by
    have ha_le : a ≤ Real.sqrt (M * area) := by
      have h := Real.le_sqrt_of_sq_le hcs_sq
      simpa [pow_two] using h
    have hprod : Real.sqrt (area / M) * a ≤ area := by
      calc
        Real.sqrt (area / M) * a ≤ Real.sqrt (area / M) * Real.sqrt (M * area) :=
          mul_le_mul_of_nonneg_left ha_le (Real.sqrt_nonneg _)
        _ = Real.sqrt (area / M * (M * area)) :=
          (Real.sqrt_mul (div_nonneg harea.le hM.le) (M * area)).symm
        _ = Real.sqrt (area ^ 2) := by
          congr 1
          field_simp [hM.ne']
        _ = area := Real.sqrt_sq harea.le
    exact (le_div_iff₀ ha).mpr hprod
  have hdecomp :
      shearDelayedClock s w ρ δ ε - (1 - ε) * Real.sqrt (area / M) =
        (1 - ε) * (area / a - Real.sqrt (area / M)) + (∑ i ∈ s, w i * ρ i * δ i) / a := by
    unfold shearDelayedClock
    have hnum :
        ∑ i ∈ s, w i * ρ i * ((1 - ε) * ρ i + δ i) =
          (1 - ε) * area + ∑ i ∈ s, w i * ρ i * δ i := by
      have h1 :
          ∑ i ∈ s, w i * ρ i * ((1 - ε) * ρ i + δ i) =
            ∑ i ∈ s, ((1 - ε) * (w i * ρ i ^ 2) + w i * ρ i * δ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    change (∑ i ∈ s, w i * ρ i * ((1 - ε) * ρ i + δ i)) / a - (1 - ε) * Real.sqrt (area / M) = _
    rw [hnum]
    field_simp [ha.ne']
    ring
  have hterm1 : 0 ≤ (1 - ε) * (area / a - Real.sqrt (area / M)) :=
    mul_nonneg h1mε.le (sub_nonneg.mpr hcs_div)
  have hterm2 : 0 ≤ (∑ i ∈ s, w i * ρ i * δ i) / a := by
    apply div_nonneg _ ha.le
    exact Finset.sum_nonneg fun i hi => mul_nonneg (mul_nonneg (hw i hi).le (hρ i hi).le) (hδ i hi)
  refine ⟨hdecomp, hterm1, hterm2, ?_⟩
  constructor
  · intro heq
    have hsum0 :
        (1 - ε) * (area / a - Real.sqrt (area / M)) + (∑ i ∈ s, w i * ρ i * δ i) / a = 0 := by
      linarith
    have ht1 : (1 - ε) * (area / a - Real.sqrt (area / M)) = 0 := by linarith
    have ht2 : (∑ i ∈ s, w i * ρ i * δ i) / a = 0 := by linarith
    have hδ0 : ∀ i ∈ s, δ i = 0 := by
      have hnum0 : ∑ i ∈ s, w i * ρ i * δ i = 0 := (div_eq_zero_iff.mp ht2).resolve_right ha.ne'
      have hnn : ∀ i ∈ s, 0 ≤ w i * ρ i * δ i := fun i hi =>
        mul_nonneg (mul_nonneg (hw i hi).le (hρ i hi).le) (hδ i hi)
      intro i hi
      have hitem := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnum0 i hi
      exact (mul_eq_zero.mp hitem).resolve_left (mul_pos (hw i hi) (hρ i hi)).ne'
    have hρ_unif : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j := by
      have hrat : area / a = Real.sqrt (area / M) :=
        sub_eq_zero.mp ((mul_eq_zero.mp ht1).resolve_left h1mε.ne')
      have hsq_eq : (area / a) ^ 2 = area / M := by
        rw [hrat, Real.sq_sqrt (div_nonneg harea.le hM.le)]
      have ha2_eq : M * area = a ^ 2 := by
        have h1 : area ^ 2 * M = area * a ^ 2 := by
          rw [div_pow] at hsq_eq
          have h2 := (div_eq_div_iff (sq_pos_of_pos ha).ne' hM.ne').mp hsq_eq
          linarith
        have h2 : area * (M * area - a ^ 2) = 0 := by linarith
        linarith [(mul_eq_zero.mp h2).resolve_left harea.ne']
      have hsum_sq0 : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 = 0 := by linarith
      have houter : ∀ i ∈ s, 0 ≤ ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 := fun i hi =>
        Finset.sum_nonneg fun j hj =>
          mul_nonneg (mul_nonneg (hw i hi).le (hw j hj).le) (sq_nonneg _)
      intro i hi j hj
      have hi0 := (Finset.sum_eq_zero_iff_of_nonneg houter).mp hsum_sq0 i hi
      have hinner : ∀ j ∈ s, 0 ≤ w i * w j * (ρ i - ρ j) ^ 2 := fun j hj =>
        mul_nonneg (mul_nonneg (hw i hi).le (hw j hj).le) (sq_nonneg _)
      have hij0 := (Finset.sum_eq_zero_iff_of_nonneg hinner).mp hi0 j hj
      have hdiff0 : (ρ i - ρ j) ^ 2 = 0 :=
        (mul_eq_zero.mp hij0).resolve_left (mul_pos (hw i hi) (hw j hj)).ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hdiff0)
    exact ⟨hδ0, hρ_unif⟩
  · rintro ⟨hδ0, hρ_unif⟩
    have ht2 : (∑ i ∈ s, w i * ρ i * δ i) / a = 0 := by
      have hnum0 : ∑ i ∈ s, w i * ρ i * δ i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hδ0 i hi]; ring
      rw [hnum0, zero_div]
    have ha2_eq : M * area = a ^ 2 := by
      have hzero : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (ρ i - ρ j) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
        rw [hρ_unif i hi j hj]
        ring
      linarith
    have hrat : area / a = Real.sqrt (area / M) := by
      have hsq : (area / a) ^ 2 = area / M := by
        rw [div_pow]
        apply (div_eq_div_iff (sq_pos_of_pos ha).ne' hM.ne').mpr
        nlinarith [ha2_eq]
      rw [← hsq, Real.sqrt_sq (div_nonneg harea.le ha.le)]
    have ht1 : (1 - ε) * (area / a - Real.sqrt (area / M)) = 0 := by
      rw [hrat, sub_self, mul_zero]
    linarith

end ClassicalDeficitRigidity

#print axioms operator_weighted_cauchy_schwarz_identity
#print axioms operator_weighted_cauchy_schwarz_eq_iff
#print axioms operator_shear_clock_lower_bound
#print axioms operator_clock_area_upper_bound
#print axioms shear_clock_deficit_and_rigidity

end D5.S3.Quantum.Analysis.NullConeGravity.NullConeClockAreaBound
