/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickThreshold
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Exact weighted positive-overlap optimality from orthogonal residuals. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
import D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Tactic

/-! Weighted trace optimization and the canonical threshold residuals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickInterior
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem hermitian_optimal_iff (A B Y : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hY : Y.IsHermitian)
    (hYA : Y ≤ A) (hYB : Y ≤ B) :
    (∀ X : Matrix n n ℂ, X.IsHermitian → X ≤ A → X ≤ B →
      X.trace.re ≤ Y.trace.re) ↔ (A - Y) * (B - Y) = 0 := by
  let hH := hA.sub hB
  let R := RHLinalg.hermPosPart hH
  let Q := RHLinalg.hermNegPart hH
  have hRQ : R - Q = A - B := RHLinalg.hermPosPart_sub_hermNegPart hH
  obtain ⟨hX, hXA, hXB, hmax⟩ := hermitian_overlap_unique A B hA hB
  constructor
  · intro h
    have hy : Y = A - R := (hmax Y hY hYA hYB).2
      (le_antisymm (hmax Y hY hYA hYB).1 (h _ hX hXA hXB))
    have hr : A - Y = R := by rw [hy]; abel
    have hq : B - Y = Q := by
      calc
        _ = (A - Y) - (A - B) := by abel
        _ = R - (R - Q) := by rw [hr, ← hRQ]
        _ = Q := by abel
    rw [hr, hq]
    exact RHLinalg.hermPosPart_mul_hermNegPart hH
  · intro hz
    have hp : (posPart (A - B) : Matrix n n ℂ) = A - Y :=
      (CFC.posPart_negPart_unique
        (show A - B = (A - Y) - (B - Y) by abel) hz
        (sub_nonneg.mpr hYA) (sub_nonneg.mpr hYB)).1
    have hb : (posPart (A - B) : Matrix n n ℂ) = R := by
      rw [CFC.posPart_def, cfcₙ_eq_cfc, hH.cfc_eq]
      rfl
    have hy : A - R = Y := by rw [← hb, hp]; abel
    intro X hh h1 h2
    have hx := (hmax X hh h1 h2).1
    change X.trace.re ≤ (A - R).trace.re at hx
    simpa only [hy] using hx

/-- A strictly positive overlap point is optimal under a strictly positive
trace weight exactly when its two upper-bound residuals are orthogonal in
that weight. The optimization ranges over actual PSD matrices. -/
theorem weighted_overlap_optimal_iff (A B W Y : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hW : W.PosDef) (hY : Y.PosDef) (hYA : Y ≤ A) (hYB : Y ≤ B) :
    (∀ X : Matrix n n ℂ, 0 ≤ X → X ≤ A → X ≤ B →
      (W * X).trace.re ≤ (W * Y).trace.re) ↔
      (A - Y) * W * (B - Y) = 0 := by
  rw [positive_interior_relaxation A B W Y hY hYA hYB]
  obtain ⟨u₀, hu₀, hWu⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hW.isStrictlyPositive
  obtain ⟨u, rfl⟩ := hu₀
  let G : Matrix n n ℂ → Matrix n n ℂ := fun X => (u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ)
  let F : Matrix n n ℂ → Matrix n n ℂ := fun X => (↑(u⁻¹) : Matrix n n ℂ) * X * star (↑(u⁻¹) : Matrix n n ℂ)
  have hFG (X : Matrix n n ℂ) : F (G X) = X := by
    simp only [F, G, Matrix.mul_assoc, ← Matrix.mul_assoc (↑(u⁻¹) : Matrix n n ℂ) (↑u : Matrix n n ℂ),
      Units.inv_mul, Matrix.one_mul, ← star_mul, Units.inv_mul, star_one, Matrix.mul_one]
  have hGF (X : Matrix n n ℂ) : G (F X) = X := by
    simp only [F, G, Matrix.mul_assoc, ← Matrix.mul_assoc (↑u : Matrix n n ℂ) (↑(u⁻¹) : Matrix n n ℂ),
      Units.mul_inv, Matrix.one_mul, ← star_mul, Units.mul_inv, star_one, Matrix.mul_one]
  have hGherm (X : Matrix n n ℂ) (hX : X.IsHermitian) : (G X).IsHermitian := by
    change ((u : Matrix n n ℂ) * X * (u : Matrix n n ℂ)ᴴ).IsHermitian
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hX
  have hFherm (X : Matrix n n ℂ) (hX : X.IsHermitian) : (F X).IsHermitian := by
    change ((↑(u⁻¹) : Matrix n n ℂ) * X * (↑(u⁻¹) : Matrix n n ℂ)ᴴ).IsHermitian
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hX
  have hGmono {X Z : Matrix n n ℂ} (h : X ≤ Z) : G X ≤ G Z := by
    apply Matrix.le_iff.mpr
    simpa only [G, Matrix.mul_sub, Matrix.sub_mul, Matrix.star_eq_conjTranspose] using
      (Matrix.le_iff.mp h).mul_mul_conjTranspose_same (u : Matrix n n ℂ)
  have hFmono {X Z : Matrix n n ℂ} (h : X ≤ Z) : F X ≤ F Z := by
    apply Matrix.le_iff.mpr
    simpa only [F, Matrix.mul_sub, Matrix.sub_mul, Matrix.star_eq_conjTranspose] using
      (Matrix.le_iff.mp h).mul_mul_conjTranspose_same (↑(u⁻¹) : Matrix n n ℂ)
  have htrace (X : Matrix n n ℂ) : (G X).trace.re = (W * X).trace.re := by
    dsimp only [G]
    rw [Matrix.trace_mul_cycle, ← hWu]
  have hres : (G A - G Y) * (G B - G Y) = G ((A - Y) * W * (B - Y)) := by
    have hsub (X Z : Matrix n n ℂ) : G X - G Z = G (X - Z) := by
      simp only [G, Matrix.mul_sub, Matrix.sub_mul]
    rw [hsub, hsub]
    simp only [G, hWu, Matrix.mul_assoc]
  have hzero : (G A - G Y) * (G B - G Y) = 0 ↔ (A - Y) * W * (B - Y) = 0 := by
    rw [hres]
    constructor
    · intro h
      have he := congrArg F h
      simpa only [hFG, F, Matrix.mul_zero, Matrix.zero_mul] using he
    · intro h
      simp only [h, G, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hzero, ← hermitian_optimal_iff (G A) (G B) (G Y)
    (hGherm A hA) (hGherm B hB) (hGherm Y hY.isHermitian) (hGmono hYA) (hGmono hYB)]
  constructor
  · intro h X hX hXA hXB
    have ha : F X ≤ A := by simpa only [hFG] using hFmono hXA
    have hb : F X ≤ B := by simpa only [hFG] using hFmono hXB
    have he := h (F X) (hFherm X hX) ha hb
    rw [← htrace, hGF, ← htrace] at he
    exact he
  · intro h X hX hXA hXB
    have he := h (G X) (hGherm X hX) (hGmono hXA) (hGmono hXB)
    simpa only [htrace] using he

/-- Scalar functional-calculus minimum of the two commuting upper bounds. -/
def canonicalOverlap (D : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => min x (t * (1 - x))) D

theorem canonical_residuals (D : Matrix n n ℂ) (hD : D.IsHermitian) (t : ℝ) :
    D - canonicalOverlap D t = thresholdPositive D t ∧
      t • (1 - D) - canonicalOverlap D t = thresholdNegative D t := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ D) :=
    D.finite_real_spectrum.continuousOn f
  have hB : cfc (fun x : ℝ => t * (1 - x)) D = t • (1 - D) := by
    rw [cfc_const_mul t (fun x : ℝ => 1 - x) D (hc _),
      cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) D (hc _) (hc _),
      cfc_const 1 D hD.isSelfAdjoint, cfc_id' ℝ D hD.isSelfAdjoint]
    simp
  constructor
  · calc
      _ = cfc (fun x : ℝ => x) D - cfc (fun x : ℝ => min x (t * (1 - x))) D := by
        rw [cfc_id' ℝ D hD.isSelfAdjoint]
        rfl
      _ = cfc (fun x : ℝ => x - min x (t * (1 - x))) D :=
        (cfc_sub _ _ D (hc _) (hc _)).symm
      _ = thresholdPositive D t := by
        apply cfc_congr
        intro x _
        dsimp only
        rcases le_total x (t * (1 - x)) with h | h
        · rw [min_eq_left h, sub_self, max_eq_right (sub_nonpos.mpr h)]
        · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  · calc
      _ = cfc (fun x : ℝ => t * (1 - x)) D - cfc (fun x : ℝ => min x (t * (1 - x))) D := by
        rw [hB]
        rfl
      _ = cfc (fun x : ℝ => t * (1 - x) - min x (t * (1 - x))) D :=
        (cfc_sub _ _ D (hc _) (hc _)).symm
      _ = thresholdNegative D t := by
        apply cfc_congr
        intro x _
        dsimp only
        rcases le_total x (t * (1 - x)) with h | h
        · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
        · rw [min_eq_right h, sub_self, max_eq_right (sub_nonpos.mpr h)]

private theorem canonical_posDef (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (hd : ∀ i, 0 < hD.eigenvalues i ∧ hD.eigenvalues i < 1)
    (t : ℝ) (ht : 0 < t) : (canonicalOverlap D t).PosDef := by
  apply Matrix.IsStrictlyPositive.posDef
  apply (cfc_isStrictlyPositive_iff _ D (D.finite_real_spectrum.continuousOn _) hD.isSelfAdjoint).2
  intro x hx
  rw [hD.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact lt_min (hd i).1 (mul_pos ht (sub_pos.mpr (hd i).2))

/-- The exact single-threshold optimum criterion for a strict common corner.
The conclusion compares the canonical point with every actual PSD feasible
matrix; the orthogonality condition is derived, rather than assumed. -/
theorem canonical_optimal_iff (D W : Matrix n n ℂ)
    (hD : D.IsHermitian) (hW : W.PosDef)
    (hd : ∀ i, 0 < hD.eigenvalues i ∧ hD.eigenvalues i < 1)
    (t : ℝ) (ht : 0 < t) :
    (∀ X : Matrix n n ℂ, 0 ≤ X → X ≤ D → X ≤ t • (1 - D) →
      (W * X).trace.re ≤ (W * canonicalOverlap D t).trace.re) ↔
      thresholdPositive D t * W * thresholdNegative D t = 0 := by
  obtain ⟨hrA, hrB⟩ := canonical_residuals D hD t
  have hYA : canonicalOverlap D t ≤ D := by
    rw [← sub_nonneg, hrA]
    exact cfc_nonneg fun _ _ => le_max_right _ _
  have hYB : canonicalOverlap D t ≤ t • (1 - D) := by
    rw [← sub_nonneg, hrB]
    exact cfc_nonneg fun _ _ => le_max_right _ _
  have hB : (t • (1 - D)).IsHermitian :=
    (Matrix.isHermitian_one.sub hD).smul (IsSelfAdjoint.all t)
  simpa only [hrA, hrB] using weighted_overlap_optimal_iff D (t • (1 - D)) W
    (canonicalOverlap D t) hD hB hW (canonical_posDef D hD hd t ht) hYA hYB

/-- On the strict common corner, the canonical overlap solves every positive
threshold optimization exactly when the weight commutes with the contraction.
This includes the empty carrier and repeated eigenvalues. -/
theorem canonical_all_thresholds_iff_commute (D W : Matrix n n ℂ)
    (hD : D.IsHermitian) (hW : W.PosDef)
    (hd : ∀ i, 0 < hD.eigenvalues i ∧ hD.eigenvalues i < 1) :
    (∀ t : ℝ, 0 < t →
      ∀ X : Matrix n n ℂ, 0 ≤ X → X ≤ D → X ≤ t • (1 - D) →
        (W * X).trace.re ≤ (W * canonicalOverlap D t).trace.re) ↔ W * D = D * W := by
  have hcuts := all_thresholds_iff_commute D W hD hW.isHermitian
    (fun i j _ => ⟨hd i, hd j⟩)
  rw [← hcuts]
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro ht
  exact canonical_optimal_iff D W hD hW hd t ht

end D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold
