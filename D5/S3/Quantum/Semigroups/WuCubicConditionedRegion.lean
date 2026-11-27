import D5.S3.Quantum.Semigroups.WuCubicConditioningComparison
import D5.S3.Quantum.Semigroups.WuCubicConditioningRotation
import D5.S3.Quantum.Semigroups.WuCubicOneModeEquality
import D5.S3.Quantum.Semigroups.WuCubicTransverseCentered

/-! The literal Wu cubic deficit on the region of positive embedded spectrum
with minimum at least two thirds of the maximum. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set
open scoped ComplexOrder Kronecker MatrixOrder Pointwise

namespace D5.S3.Quantum.Semigroups.WuCubicConditionedRegion

open WuCubicOperatorBridge (Mat G GInv)
open WuCubicOperatorNormalization (operatorDeficit operatorDeficit_scalar)
open WuCubicConditioningRotation (ModeRotation rotate exists_conditioning_rotation)
open WuCubicHotInnerPartialTrace (lift reduce)
open WuCubicConditioningSegment (conditioning_segment_bounds)
open WuCubicConditioningComparison (operatorDeficit_conditioning_lt)
open WuCubicOneModeEquality (operatorDeficit_lift_nonneg operatorDeficit_lift_eq_zero_iff)
open WuCubicConditionedHessian (embeddedGenerator)
open WuCubicTransverseCentered (operatorDeficit_centered_pos_normalized)
open WuCubicThermalBasis (Index degree coefficient basis_repr)
open WuCubicAngularCertificate (physicalFrame)
open private rotate_sandwich rotate_inverse from
  D5.S3.Quantum.Semigroups.WuCubicConditioningRotation
open private conditioning_path_posDef reduce_posDef from
  D5.S3.Quantum.Semigroups.WuCubicConditioningComparison
open private G_mul_GInv GInv_mul_G weighted_spectral_energy_scale spectral_entropy_scale from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private G_adjoint recover_input exists_ordered_frame deficit_eq_weighted from
  D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization

private theorem embedded_spectrum_rotate {U : Mat} (hU : ModeRotation U) (r : ℝ) (X : Mat) :
    spectrum ℝ (G r * rotate U X * G r) = spectrum ℝ (G r * X * G r) := by
  let V : unitary Mat := ⟨U, Unitary.mem_iff.mpr ⟨hU.columns, hU.rows⟩⟩
  rw [rotate_sandwich hU]
  exact Unitary.spectrum_star_right_conjugate (R := ℝ) (U := V)

private theorem input_posDef {r : ℝ} (hr : 1 ≤ r) {X : Mat}
    (hX : (G r * X * G r).PosDef) : X.PosDef := by
  have hG : IsUnit (G r) := ⟨⟨G r, GInv r, G_mul_GInv hr, GInv_mul_G hr⟩, rfl⟩
  exact hG.posDef_star_left_conjugate_iff.mp
    (by simpa only [Matrix.star_eq_conjTranspose, G_adjoint] using hX)

private theorem operatorDeficit_smul {r : ℝ} (hr : 1 ≤ r) (c : ℝ) (X : Mat)
    (hX : (G r * X * G r).PosSemidef) :
    operatorDeficit r (c • X) = c ^ 3 * operatorDeficit r X := by
  obtain ⟨U, v, _, _, _, hv⟩ := exists_ordered_frame hX
  have hd : diagonal (fun i => ((c * v i : ℝ) : ℂ)) =
      c • diagonal (fun i => (v i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    exact Complex.ofReal_mul c (v i)
  have hc : G r * (c • X) * G r = physicalFrame U *
      diagonal (fun i => ((c * v i : ℝ) : ℂ)) * (physicalFrame U)ᴴ := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, hv, hd]
  rw [deficit_eq_weighted hr _ U _ hc, deficit_eq_weighted hr X U _ hv,
    weighted_spectral_energy_scale, spectral_entropy_scale]
  ring

section Curvature

variable {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
  (hcenter : ∀ (M W : Mat) (hM : M.PosDef), W.IsHermitian → W ≠ 0 →
    (5 / 9 : ℝ) • (1 : Mat) ≤ M → M ≤ 1 → 3 ≤ M.trace.re →
    (∃ i, hM.isHermitian.eigenvalues i = 1) →
    (∀ k : Index, degree k < 2 → coefficient r (GInv r * W * GInv r) k = 0) →
    let F := fun t : ℝ => operatorDeficit r (GInv r * (M + t • W) * GInv r)
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → 2 * F 0 < F t + F (-t))

include hr hrhi hcenter

private theorem centered_on_conditioning_path {L : ℝ} (Y : Mat) (hY : Y.IsHermitian)
    (hL : 0 < L) (hM : (G r * Y * G r).IsHermitian)
    (hlow : ∀ i, 2 / 3 * L ≤ hM.eigenvalues i)
    (hup : ∀ i, hM.eigenvalues i ≤ L) (hmax : ∃ i, hM.eigenvalues i = L)
    (hdegree : ∀ k : Index, degree k < 2 → coefficient r (Y - lift (reduce r Y)) k = 0)
    (hres : Y - lift (reduce r Y) ≠ 0) :
    let f := fun s : ℝ => operatorDeficit r (lift (reduce r Y) + s • (Y - lift (reduce r Y)))
    ∀ s ∈ Ioo (0 : ℝ) 1, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      2 * f s < f (s + t) + f (s - t) := by
  intro f s hs
  let Y₀ := lift (reduce r Y)
  let H := Y - Y₀
  let P := fun u : ℝ => Y₀ + u • H
  have hpos (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : (G r * P u * G r).PosDef :=
    conditioning_path_posDef hr hrhi Y hL hM hlow hup hmax u hu
  have hP₀ : (P 0).PosDef := input_posDef hr (hpos 0 ⟨le_rfl, zero_le_one⟩)
  have hH : H.IsHermitian := hY.sub (by simpa only [P, zero_smul, add_zero] using hP₀.isHermitian)
  have hP (u : ℝ) : G r * P u * G r =
      (1 - u) • (G r * Y₀ * G r) + u • (G r * Y * G r) := by
    simp only [P, H, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul]
    module
  obtain ⟨A, hA, hMs, hMsmax, hMseig, hMstr⟩ :=
    conditioning_segment_bounds hr hrhi Y hL hs.1.le hs.2.le hM hlow hup hmax
  have hMs' : (G r * P s * G r).PosDef := by
    rw [hP]
    exact hMs
  let M := A⁻¹ • (G r * P s * G r)
  let W := A⁻¹ • (G r * H * G r)
  have hAinv : 0 < A⁻¹ := inv_pos.mpr hA
  have hAp : A⁻¹ * A = 1 := inv_mul_cancel₀ hA.ne'
  have hMn : M.PosDef := hMs'.smul hAinv
  have hW : W.IsHermitian := by
    have hGH : (G r * H * G r).IsHermitian := by
      simp only [Matrix.IsHermitian, G_adjoint, Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    exact hGH.smul (star_trivial _)
  have hGH : GInv r * W * GInv r = A⁻¹ • H := by
    simp only [W, Matrix.mul_smul, Matrix.smul_mul, recover_input hr]
  have hWne : W ≠ 0 := by
    intro h
    apply hres
    have hz : A⁻¹ • H = 0 := by simpa only [h, Matrix.mul_zero, Matrix.zero_mul] using hGH.symm
    exact (smul_eq_zero.mp hz).resolve_left hAinv.ne'
  have hWdegree (k : Index) (hk : degree k < 2) :
      coefficient r (GInv r * W * GInv r) k = 0 := by
    have hz : coefficient r H k = 0 := hdegree k hk
    rw [hGH]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), ← basis_repr (zero_le_one.trans hr),
      map_smul, Finsupp.smul_apply]
    simp only [basis_repr (zero_le_one.trans hr), hz, smul_zero]
  have hbounds : (5 / 9 : ℝ) • (1 : Mat) ≤ M ∧ M ≤ 1 := by
    rw [show M = A⁻¹ • ((1 - s) • (G r * Y₀ * G r) + s • (G r * Y * G r)) from
      congrArg (A⁻¹ • ·) (hP s)]
    have hlo := (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hMs.isHermitian _).mp
      (fun i => (hMseig i).1)
    have hhi := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hMs.isHermitian _).mp
      (fun i => (hMseig i).2)
    have hcoef : A⁻¹ * (5 / 9 * A) = 5 / 9 := by
      rw [mul_left_comm, hAp, mul_one]
    exact ⟨by simpa only [smul_smul, hcoef] using
      smul_le_smul_of_nonneg_left hlo hAinv.le, by
      simpa only [smul_smul, hAp, one_smul] using
        smul_le_smul_of_nonneg_left hhi hAinv.le⟩
  have htrace : 3 ≤ M.trace.re := by
    have ht := mul_le_mul_of_nonneg_left hMstr hAinv.le
    rw [mul_left_comm, hAp, mul_one] at ht
    simpa only [M, hP, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul] using ht
  have hmaxn : ∃ i, hMn.isHermitian.eigenvalues i = 1 := by
    change (1 : ℝ) ∈ Set.range hMn.isHermitian.eigenvalues
    rw [← hMn.isHermitian.spectrum_real_eq_range_eigenvalues]
    have ha : A ∈ spectrum ℝ (G r * P s * G r) := by
      rw [hP, hMs.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact hMsmax
    change (1 : ℝ) ∈ spectrum ℝ (A⁻¹ • (G r * P s * G r))
    rw [spectrum.smul_eq_smul _ _ ⟨A, ha⟩]
    exact ⟨A, ha, by simpa only [smul_eq_mul] using hAp⟩
  obtain ⟨δ, hδ, hlocal⟩ := hcenter M W hMn hW hWne hbounds.1 hbounds.2 htrace hmaxn hWdegree
  have hscale (t : ℝ) (ht : s + t ∈ Icc (0 : ℝ) 1) :
      operatorDeficit r (GInv r * (M + t • W) * GInv r) = A⁻¹ ^ 3 * f (s + t) := by
    have heq : GInv r * (M + t • W) * GInv r = A⁻¹ • P (s + t) := by
      simp only [M, W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        recover_input hr, P]
      module
    rw [heq, operatorDeficit_smul hr _ _ (hpos _ ht).posSemidef]
  refine ⟨min δ (min s (1 - s)), lt_min hδ (lt_min hs.1 (sub_pos.mpr hs.2)), ?_⟩
  intro t ht hsmall
  have htδ := hsmall.trans_le (min_le_left _ _)
  have hts := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht₁ := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hplus : s + t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith⟩
  have hminus : s + -t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hs.2]⟩
  have h := hlocal t ht htδ
  change 2 * operatorDeficit r (GInv r * (M + (0 : ℝ) • W) * GInv r) <
    operatorDeficit r (GInv r * (M + t • W) * GInv r) +
      operatorDeficit r (GInv r * (M + (-t) • W) * GInv r) at h
  rw [hscale 0 (by simpa only [add_zero] using Ioo_subset_Icc_self hs),
    hscale t hplus, hscale (-t) hminus, add_zero, ← sub_eq_add_neg,
    ← mul_add, mul_left_comm 2] at h
  exact lt_of_mul_lt_mul_left h (pow_nonneg hAinv.le 3)

/-- Local strict centered curvature on normalized transverse directions implies
nonnegativity and positive-scalar rigidity for the original complex observable. -/
private theorem operatorDeficit_conditionedRegion_of_centered {L : ℝ} {X : Mat}
    (hX : X.PosSemidef) (hL : 0 < L)
    (hmax : IsGreatest (spectrum ℝ (G r * X * G r)) L)
    (hlow : ∀ a ∈ spectrum ℝ (G r * X * G r), 2 / 3 * L ≤ a) :
    0 ≤ operatorDeficit r X ∧
      (operatorDeficit r X = 0 ↔ ∃ a : ℝ, 0 < a ∧ X = (a : ℂ) • (1 : Mat)) := by
  obtain ⟨U, _, hU, _, _, hdegree⟩ := exists_conditioning_rotation hr hX.isHermitian
  let Y := rotate U X
  have hY : Y.PosSemidef := hX.mul_mul_conjTranspose_same U
  have hM : (G r * Y * G r).IsHermitian := by
    have hP := hY.conjTranspose_mul_mul_same (G r)
    rw [G_adjoint] at hP
    exact hP.isHermitian
  have hspec : Set.range hM.eigenvalues = spectrum ℝ (G r * X * G r) :=
    hM.spectrum_real_eq_range_eigenvalues.symm.trans (embedded_spectrum_rotate hU r X)
  have heig (i : WuCubicOperatorBridge.Occupation) :
      hM.eigenvalues i ∈ spectrum ℝ (G r * X * G r) :=
    hspec ▸ Set.mem_range_self i
  have hylo (i : WuCubicOperatorBridge.Occupation) : 2 / 3 * L ≤ hM.eigenvalues i :=
    hlow _ (heig i)
  have hyhi (i : WuCubicOperatorBridge.Occupation) : hM.eigenvalues i ≤ L :=
    hmax.2 (heig i)
  have hymax : ∃ i, hM.eigenvalues i = L := by
    change L ∈ Set.range hM.eigenvalues
    rw [hspec]
    exact hmax.1
  have hYpos : Y.PosDef := input_posDef hr <| hM.posDef_iff_eigenvalues_pos.mpr
    (fun i => lt_of_lt_of_le (by positivity) (hylo i))
  have hred := reduce_posDef hr hYpos
  have hnonneg := operatorDeficit_lift_nonneg hr hred
  have hcompare (hres : Y - lift (reduce r Y) ≠ 0) :
      operatorDeficit r (lift (reduce r Y)) < operatorDeficit r Y :=
    operatorDeficit_conditioning_lt hr hrhi Y hL hM hylo hyhi hymax
      (centered_on_conditioning_path hr hrhi hcenter Y hY.isHermitian hL hM hylo hyhi hymax hdegree)
      hres
  have hdef : operatorDeficit r X = operatorDeficit r Y := (hU.deficit_eq r X).symm
  have hnores : operatorDeficit r X = 0 → Y = lift (reduce r Y) := by
    intro hz
    by_contra hne
    have hlt := hcompare (sub_ne_zero.mpr hne)
    rw [← hdef, hz] at hlt
    exact (not_lt_of_ge hnonneg) hlt
  refine ⟨?_, ?_⟩
  · rw [hdef]
    by_cases h : Y - lift (reduce r Y) = 0
    · simpa only [← sub_eq_zero.mp h] using hnonneg
    · exact hnonneg.trans (hcompare h).le
  · constructor
    · intro hz
      have hy := hnores hz
      have hz₀ : operatorDeficit r (lift (reduce r Y)) = 0 := by rw [← hy, ← hdef, hz]
      obtain ⟨a, ha, hscalar⟩ := (operatorDeficit_lift_eq_zero_iff hr hred).mp hz₀
      have hy_scalar : Y = (a : ℂ) • (1 : Mat) := by
        calc
          Y = lift (reduce r Y) := hy
          _ = (a : ℂ) • (1 : Mat) := by
            rw [hscalar, lift, Matrix.kronecker_smul, Matrix.one_kronecker_one]
      refine ⟨a, ha, ?_⟩
      calc
        X = rotate Uᴴ Y := (rotate_inverse hU.columns X).symm
        _ = (a : ℂ) • (1 : Mat) := by simp [hy_scalar, rotate, hU.columns]
    · rintro ⟨a, _, rfl⟩
      exact operatorDeficit_scalar hr a

end Curvature

/-- In the positive, two-thirds spectral region, the mixed-generator estimate
gives the literal Wu cubic inequality and characterizes positive-scalar equality. -/
theorem operatorDeficit_conditionedRegion_of_mixed {r L : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
    (hmixed : ∀ (M W : Mat), M.PosDef → W.IsHermitian →
      (5 / 9 : ℝ) • (1 : Mat) ≤ M → M ≤ 1 →
      (∀ k : Index, degree k < 2 → coefficient r (GInv r * W * GInv r) k = 0) →
      (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
        ((M * W + W * M) * embeddedGenerator r W).trace.re)
    {X : Mat} (hX : X.PosSemidef) (hL : 0 < L)
    (hmax : IsGreatest (spectrum ℝ (G r * X * G r)) L)
    (hlow : ∀ a ∈ spectrum ℝ (G r * X * G r), 2 / 3 * L ≤ a) :
    0 ≤ operatorDeficit r X ∧
      (operatorDeficit r X = 0 ↔ ∃ a : ℝ, 0 < a ∧ X = (a : ℂ) • (1 : Mat)) := by
  refine operatorDeficit_conditionedRegion_of_centered hr hrhi ?_ hX hL hmax hlow
  intro M W hM hW hWne hlo hhi htrace htop hdegree
  exact operatorDeficit_centered_pos_normalized hr hrhi M W hM hW hWne hlo hhi htrace htop
    (hmixed M W hM hW hlo hhi hdegree)

run_cmd do
  for axiomName in ← Lean.collectAxioms ``operatorDeficit_conditionedRegion_of_mixed do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unexpected axiom for operatorDeficit_conditionedRegion_of_mixed: {axiomName}"

end D5.S3.Quantum.Semigroups.WuCubicConditionedRegion
