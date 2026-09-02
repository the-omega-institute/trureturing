/- GID: D5/S3/Observer/Hankel/GoldenTwoShadowBound
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/GoldenTwoShadowBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Six golden-ratio Gram criteria are equivalent, and their spectral threshold is sharp. -/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Data.List.TFAE
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * D5 body-shape searches found Gram positivity and singular-value results,
     but no theorem packaging these six golden-ratio criteria or defining the
     Hankel Gram operator used here.
   * Pinned Mathlib supplies the continuous-linear-map adjoint norm identity,
     positive C-star order and functional calculus, inverse antitonicity, the
     golden-ratio identities, and `List.TFAE`. No packaged whole theorem was
     found.
   * The installed non-Mathlib Lean packages contain no matching golden Hankel,
     Gram, operator, or inverse bound. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.GoldenTwoShadowBound

open Ring
open scoped CStarAlgebra

private theorem golden_two_shadow_equivalences
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (H : V →L[ℂ] W) (hContraction : ‖H‖ ≤ 1) :
    let D : V →L[ℂ] V := H.adjoint ∘L H
    List.TFAE [
      D ^ 2 ≤ 1 - D,
      D + D ^ 2 ≤ 1,
      ‖D‖ ≤ Real.goldenRatio⁻¹,
      ‖H‖ ≤ Real.sqrt Real.goldenRatio⁻¹,
      ∃ complement : (V →L[ℂ] V)ˣ,
        (complement : V →L[ℂ] V) = 1 - D ∧
          (↑complement⁻¹ : V →L[ℂ] V) ≤
            algebraMap ℝ (V →L[ℂ] V) (Real.goldenRatio ^ 2),
      ∃ complement : (V →L[ℂ] V)ˣ,
        (complement : V →L[ℂ] V) = 1 - D ∧
          D * (↑complement⁻¹ : V →L[ℂ] V) ≤
            algebraMap ℝ (V →L[ℂ] V) Real.goldenRatio] := by
  let D : V →L[ℂ] V := H.adjoint ∘L H
  change List.TFAE [
    D ^ 2 ≤ 1 - D,
    D + D ^ 2 ≤ 1,
    ‖D‖ ≤ Real.goldenRatio⁻¹,
    ‖H‖ ≤ Real.sqrt Real.goldenRatio⁻¹,
    ∃ complement : (V →L[ℂ] V)ˣ,
      (complement : V →L[ℂ] V) = 1 - D ∧
        (↑complement⁻¹ : V →L[ℂ] V) ≤
          algebraMap ℝ (V →L[ℂ] V) (Real.goldenRatio ^ 2),
    ∃ complement : (V →L[ℂ] V)ˣ,
      (complement : V →L[ℂ] V) = 1 - D ∧
        D * (↑complement⁻¹ : V →L[ℂ] V) ≤
          algebraMap ℝ (V →L[ℂ] V) Real.goldenRatio]
  have hD : 0 ≤ D := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    exact ContinuousLinearMap.isPositive_adjoint_comp_self H
  have hDNormOne : ‖D‖ ≤ 1 := by
    rw [show D = H.adjoint ∘L H from rfl,
      ContinuousLinearMap.norm_adjoint_comp_self]
    nlinarith [norm_nonneg H]
  have hDOne : D ≤ 1 := by
    have hOrder :=
      (CStarAlgebra.norm_le_iff_le_algebraMap D zero_le_one hD).mp hDNormOne
    simpa only [map_one] using hOrder
  tfae_have 1 ↔ 2 := by
    simpa only [add_comm] using
      (le_sub_iff_add_le : D ^ 2 ≤ 1 - D ↔ D ^ 2 + D ≤ 1)
  tfae_have 2 ↔ 3 := by
    have hrPos : 0 < Real.goldenRatio⁻¹ :=
      inv_pos.mpr Real.goldenRatio_pos
    have hrEq : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
      rw [Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    have hrSplit :
        Real.goldenRatio⁻¹ + Real.goldenRatio⁻¹ ^ 2 = 1 := by
      rw [hrEq]
      nlinarith [Real.goldenRatio_sq]
    have hSelf : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg hD
    have hPolyCfc :
        cfc (fun y : ℝ => y + y ^ 2) D = D + D ^ 2 := by
      change cfc (fun y : ℝ => id y + (id y) ^ 2) D = D + D ^ 2
      rw [cfc_add D id (fun y : ℝ => (id y) ^ 2), cfc_id ℝ D,
        cfc_pow id 2 D, cfc_id ℝ D]
    have hOneCfc : cfc (fun _ : ℝ => 1) D = 1 := by
      rw [cfc_const (1 : ℝ) D, map_one]
    constructor
    · intro hPoly
      rw [CStarAlgebra.norm_le_iff_le_algebraMap D hrPos.le hD]
      apply le_algebraMap_of_spectrum_le (ha := hSelf)
      intro x hx
      have hxNonnegative : 0 ≤ x := spectrum_nonneg_of_nonneg hD hx
      have hxPoly : x + x ^ 2 ≤ 1 := by
        apply (cfc_le_iff (fun y : ℝ => y + y ^ 2) (fun _ => 1) D).mp
        · rwa [hPolyCfc, hOneCfc]
        · exact hx
      nlinarith [hrSplit]
    · intro hNorm
      rw [← hPolyCfc, ← hOneCfc]
      apply (cfc_le_iff (fun y : ℝ => y + y ^ 2) (fun _ => 1) D).mpr
      intro x hx
      have hxNonnegative : 0 ≤ x := spectrum_nonneg_of_nonneg hD hx
      have hOperatorBound :
          D ≤ algebraMap ℝ (V →L[ℂ] V) Real.goldenRatio⁻¹ :=
        (CStarAlgebra.norm_le_iff_le_algebraMap D hrPos.le hD).mp hNorm
      have hxBound : x ≤ Real.goldenRatio⁻¹ :=
        (le_algebraMap_iff_spectrum_le hSelf).mp hOperatorBound x hx
      nlinarith [hrSplit]
  tfae_have 3 ↔ 4 := by
    have hrNonnegative : 0 ≤ Real.goldenRatio⁻¹ :=
      inv_nonneg.mpr Real.goldenRatio_pos.le
    have hSquareRoot :
        (Real.sqrt Real.goldenRatio⁻¹) ^ 2 = Real.goldenRatio⁻¹ :=
      Real.sq_sqrt hrNonnegative
    rw [show D = H.adjoint ∘L H from rfl,
      ContinuousLinearMap.norm_adjoint_comp_self]
    constructor <;> intro h
    · nlinarith [norm_nonneg H, Real.sqrt_nonneg Real.goldenRatio⁻¹]
    · nlinarith [norm_nonneg H, Real.sqrt_nonneg Real.goldenRatio⁻¹]
  tfae_have 3 ↔ 5 := by
    let A := V →L[ℂ] V
    let r : ℝ := Real.goldenRatio⁻¹
    have hrPos : 0 < r := inv_pos.mpr Real.goldenRatio_pos
    have hrEq : r = Real.goldenRatio - 1 := by
      dsimp only [r]
      rw [Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    have hrSplit : r + r ^ 2 = 1 := by
      rw [hrEq]
      nlinarith [Real.goldenRatio_sq]
    have hrSquareNe : r ^ 2 ≠ 0 := pow_ne_zero 2 hrPos.ne'
    let lowerUnit : Aˣ :=
      Units.map (algebraMap ℝ A) (Units.mk0 (r ^ 2) hrSquareNe)
    have lowerVal : (lowerUnit : A) = algebraMap ℝ A (r ^ 2) := rfl
    have lowerInvVal :
        (↑lowerUnit⁻¹ : A) =
          algebraMap ℝ A (Real.goldenRatio ^ 2) := by
      change algebraMap ℝ A ((r ^ 2)⁻¹) =
        algebraMap ℝ A (Real.goldenRatio ^ 2)
      change algebraMap ℝ A (((Real.goldenRatio⁻¹) ^ 2)⁻¹) =
        algebraMap ℝ A (Real.goldenRatio ^ 2)
      rw [inv_pow, inv_inv]
    have lowerNonnegative : 0 ≤ (lowerUnit : A) := by
      rw [lowerVal]
      exact algebraMap_nonneg A (sq_nonneg r)
    have lowerStrict : IsStrictlyPositive (lowerUnit : A) :=
      ⟨lowerNonnegative, lowerUnit.isUnit⟩
    constructor
    · intro hNorm
      have hOperator : D ≤ algebraMap ℝ A r :=
        (CStarAlgebra.norm_le_iff_le_algebraMap D hrPos.le hD).mp hNorm
      have hLower : (lowerUnit : A) ≤ 1 - D := by
        rw [lowerVal]
        calc
          algebraMap ℝ A (r ^ 2) = 1 - algebraMap ℝ A r := by
            rw [← map_one (algebraMap ℝ A), ← map_sub]
            congr 1
            linarith
          _ ≤ 1 - D := sub_le_sub_left hOperator 1
      have complementStrict : IsStrictlyPositive (1 - D) :=
        lowerStrict.of_le hLower
      let complement : Aˣ := complementStrict.isUnit.unit
      refine ⟨complement, complementStrict.isUnit.unit_spec, ?_⟩
      rw [← lowerInvVal]
      have hInv := CStarAlgebra.inv_le_inv
        (a := lowerUnit) (b := complement) lowerNonnegative
      apply hInv
      simpa only [complement, complementStrict.isUnit.unit_spec] using hLower
    · rintro ⟨complement, hComplement, hInverse⟩
      have complementNonnegative : 0 ≤ (complement : A) := by
        rw [hComplement]
        exact sub_nonneg.mpr hDOne
      have hInverse' :
          (↑complement⁻¹ : A) ≤ (↑lowerUnit⁻¹ : A) := by
        rwa [lowerInvVal]
      have hLower : (lowerUnit : A) ≤ (complement : A) :=
        (CStarAlgebra.inv_le_inv_iff
          complementNonnegative lowerNonnegative).mp hInverse'
      have hOperator : D ≤ algebraMap ℝ A r := by
        rw [hComplement, lowerVal] at hLower
        have hMapSplit :
            algebraMap ℝ A (r ^ 2) = 1 - algebraMap ℝ A r := by
          rw [← map_one (algebraMap ℝ A), ← map_sub]
          congr 1
          linarith
        rw [hMapSplit] at hLower
        exact (sub_le_sub_iff_left (1 : A)).mp hLower
      exact (CStarAlgebra.norm_le_iff_le_algebraMap D hrPos.le hD).mpr
        hOperator
  tfae_have 5 ↔ 6 := by
    let A := V →L[ℂ] V
    constructor
    · rintro ⟨complement, hComplement, hInverse⟩
      refine ⟨complement, hComplement, ?_⟩
      have hProduct :
          D * (↑complement⁻¹ : A) = (↑complement⁻¹ : A) - 1 := by
        have hDEq : D = 1 - (complement : A) := by
          rw [hComplement]
          abel
        rw [hDEq, sub_mul, one_mul]
        simp
      rw [hProduct, sub_le_iff_le_add]
      rw [← map_one (algebraMap ℝ A), ← map_add, ← Real.goldenRatio_sq]
      exact hInverse
    · rintro ⟨complement, hComplement, hProductBound⟩
      refine ⟨complement, hComplement, ?_⟩
      have hProduct :
          D * (↑complement⁻¹ : A) = (↑complement⁻¹ : A) - 1 := by
        have hDEq : D = 1 - (complement : A) := by
          rw [hComplement]
          abel
        rw [hDEq, sub_mul, one_mul]
        simp
      rw [hProduct, sub_le_iff_le_add] at hProductBound
      calc
        (↑complement⁻¹ : A) ≤
            algebraMap ℝ A Real.goldenRatio + 1 := hProductBound
        _ = algebraMap ℝ A (Real.goldenRatio ^ 2) := by
          rw [Real.goldenRatio_sq, map_add, map_one]
  tfae_finish

/-- For every contractive continuous linear map, construct its positive Gram
operator `D = H†H`. The two polynomial order bounds, the norm bounds for `D`
and `H`, and the two inverse order bounds are equivalent at the golden
threshold. Moreover, on nontrivial source and target spaces, every larger
spectral threshold admits a contractive rank-one Gram operator for which the
positive two-shadow inequality fails. -/
theorem golden_two_shadow_bound
    (V W : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] :
    (∀ H : V →L[ℂ] W, ‖H‖ ≤ 1 →
      let D : V →L[ℂ] V := H.adjoint ∘L H
      List.TFAE [
        D ^ 2 ≤ 1 - D,
        D + D ^ 2 ≤ 1,
        ‖D‖ ≤ Real.goldenRatio⁻¹,
        ‖H‖ ≤ Real.sqrt Real.goldenRatio⁻¹,
        ∃ complement : (V →L[ℂ] V)ˣ,
          (complement : V →L[ℂ] V) = 1 - D ∧
            (↑complement⁻¹ : V →L[ℂ] V) ≤
              algebraMap ℝ (V →L[ℂ] V) (Real.goldenRatio ^ 2),
        ∃ complement : (V →L[ℂ] V)ˣ,
          (complement : V →L[ℂ] V) = 1 - D ∧
            D * (↑complement⁻¹ : V →L[ℂ] V) ≤
              algebraMap ℝ (V →L[ℂ] V) Real.goldenRatio]) ∧
      (Nontrivial V → Nontrivial W →
        ∀ t : ℝ, Real.goldenRatio⁻¹ < t →
          ∃ H : V →L[ℂ] W,
            ‖H‖ ≤ 1 ∧
              ‖H.adjoint ∘L H‖ ≤ t ∧
                ¬ ((H.adjoint ∘L H) ^ 2 ≤
                  1 - (H.adjoint ∘L H))) := by
  refine ⟨fun H hH => golden_two_shadow_equivalences H hH, ?_⟩
  intro hV hW t ht
  let _ : Nontrivial V := hV
  let _ : Nontrivial W := hW
  let r : ℝ := min t 1
  have hPhiLtOne : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hrGt : Real.goldenRatio⁻¹ < r := by
    exact lt_min ht hPhiLtOne
  have hrNonnegative : 0 ≤ r := by
    exact (inv_pos.mpr Real.goldenRatio_pos).le.trans hrGt.le
  have hrLeOne : r ≤ 1 := min_le_right t 1
  have hrLeT : r ≤ t := min_le_left t 1
  let s : ℝ := Real.sqrt r
  have hsNonnegative : 0 ≤ s := Real.sqrt_nonneg r
  have hsSquare : s ^ 2 = r := Real.sq_sqrt hrNonnegative
  obtain ⟨v, hv⟩ := exists_norm_eq V (c := 1) (by norm_num)
  obtain ⟨w, hw⟩ := exists_norm_eq W (c := 1) (by norm_num)
  let H : V →L[ℂ] W := s • InnerProductSpace.rankOne ℂ w v
  have hHNorm : ‖H‖ = s := by
    change ‖s • InnerProductSpace.rankOne ℂ w v‖ = s
    rw [norm_smul, InnerProductSpace.norm_rankOne, hv, hw]
    simp [Real.norm_eq_abs, abs_of_nonneg hsNonnegative]
  have hHContraction : ‖H‖ ≤ 1 := by
    rw [hHNorm]
    nlinarith
  have hDNorm : ‖H.adjoint ∘L H‖ = r := by
    calc
      ‖H.adjoint ∘L H‖ = ‖H‖ * ‖H‖ :=
        ContinuousLinearMap.norm_adjoint_comp_self H
      _ = s * s := by rw [hHNorm]
      _ = r := by simpa [pow_two] using hsSquare
  refine ⟨H, hHContraction, hDNorm.le.trans hrLeT, ?_⟩
  intro hTwoShadow
  have hGoldenBound : ‖H.adjoint ∘L H‖ ≤ Real.goldenRatio⁻¹ :=
    ((golden_two_shadow_equivalences H hHContraction).out 0 2).mp
      hTwoShadow
  rw [hDNorm] at hGoldenBound
  exact (not_lt_of_ge hGoldenBound) hrGt

end D5.S3.Observer.Hankel.GoldenTwoShadowBound
