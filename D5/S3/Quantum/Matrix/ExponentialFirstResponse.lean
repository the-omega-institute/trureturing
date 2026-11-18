/- GID: D5/S3/Quantum/Matrix/ExponentialFirstResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/ExponentialFirstResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matrix exponential derivative from the original measurable first response. -/

import D5.S3.Quantum.Analysis.MeasurableFirstResponse
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # The derivative of the matrix exponential from measurable evolution -/

noncomputable section


open scoped Matrix.Norms.L2Operator Topology
open MeasureTheory Set Filter Asymptotics NormedSpace
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
open D5.S3.Quantum.Analysis.MeasurableFirstResponse

namespace D5.S3.Quantum.Matrix.ExponentialFirstResponse

private abbrev Mat (n : Type*) := Matrix n n ℂ

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : NormedAlgebra ℚ (Mat n) := .restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℚ (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  .restrictScalars ℚ ℂ _

private noncomputable abbrev operatorEquiv :=
  (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv

private noncomputable def identityContraction : Contraction (EuclideanSpace ℂ n) where
  operator _ := 1
  zero := rfl
  add _ _ := by ext x; rfl
  norm_le _ := ContinuousLinearMap.norm_id_le
  continuous _ := continuous_const

private theorem constantEvolution (A : Mat n) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    measurableEvolution identityContraction (fun _ => operatorEquiv A) t r =
      operatorEquiv (exp ((t - r) • A)) := by
  let S : Contraction (EuclideanSpace ℂ n) := identityContraction
  let C := operatorEquiv A
  let B : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun _ => C
  let g : ℝ → ℝ := fun _ => ‖C‖
  have hB : ∀ x, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Icc 0 t)) :=
    fun _ => aestronglyMeasurable_const
  have hg : IntegrableOn g (Icc 0 t) := integrableOn_const (by simp)
  have hd := native_data S B (hr.trans hrt) hB g hg
    (fun _ _ => norm_nonneg C) (fun _ _ => le_rfl)
  have hop (u : ℝ) : S.action u = 1 := rfl
  have hmap : operatorEquiv (exp ((t - r) • A)) = exp ((t - r) • C) := by
    rw [NormedSpace.map_exp (operatorEquiv (n := n))
      ((operatorEquiv (n := n)).toLinearEquiv.toContinuousLinearEquiv.continuous)]
    congr 1
    exact ((operatorEquiv (n := n)).toLinearEquiv.toLinearMap.restrictScalars ℝ).map_smul _ _
  change measurableEvolution S B t r = _
  rw [hmap]
  apply ContinuousLinearMap.ext
  intro x
  let F : ℝ → EuclideanSpace ℂ n := fun s => measurableEvolution S B s r x
  let X : ℝ → EuclideanSpace ℂ n := fun s => exp ((s - r) • C) x
  have hF : ContinuousOn F (Icc r t) :=
    (hd.1 x).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hs => ⟨hr, hs.1, hs.2⟩)
  have hX : Continuous X := by
    dsimp [X]
    fun_prop
  have hX' (s : ℝ) : HasDerivAt X (C (X s)) s := by
    have hs : HasDerivAt (fun y : ℝ => y - r) 1 s := (hasDerivAt_id s).sub_const r
    have he : HasDerivAt (fun y : ℝ => exp ((y - r) • C))
        (C * exp ((s - r) • C)) s := by
      simpa only [Function.comp_def, one_smul] using
        (hasDerivAt_exp_smul_const' C (s - r)).scomp s hs
    simpa [X, Function.comp_def] using
      ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ n) x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s he
  have hm (u : ℝ) (hu : u ∈ Icc r t) :
      F u = x + ∫ s in r..u, C (F s) := by
    simpa [F, B, hop] using hd.2.2 u r ⟨hr, hu.1, hu.2⟩ x
  have hx (u : ℝ) : X u = x + ∫ s in r..u, C (X s) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hX' s)
      ((C.continuous.comp hX).intervalIntegrable r u)]
    have hstart : X r = x := by simp [X]
    rw [hstart]
    abel
  have hy : ∀ u ∈ Icc r t, F u - X u = causal S B r (fun s => F s - X s) u := by
    intro u hu
    have hiF : IntervalIntegrable (fun s => C (F s)) volume r u :=
      (C.continuous.comp_continuousOn (hF.mono (Icc_subset_Icc le_rfl hu.2))).intervalIntegrable_of_Icc hu.1
    have hiX : IntervalIntegrable (fun s => C (X s)) volume r u :=
      (C.continuous.comp hX).intervalIntegrable _ _
    rw [hm u hu, hx u, add_sub_add_left_eq_sub]
    simpa [causal, hop, B] using (intervalIntegral.integral_sub hiF hiX).symm
  exact sub_eq_zero.mp (continuous_residual_eq_zero S B hrt
    (fun _ => aestronglyMeasurable_const) g (integrableOn_const (by simp))
    (fun _ _ => norm_nonneg C) (fun _ _ => le_rfl)
    (hF.sub hX.continuousOn) hy t ⟨hrt, le_rfl⟩)

/-- The Bochner derivative operator, with the perturbation between the exponential factors. -/
noncomputable def derivative (A : Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  ∫ u : ℝ in 0..1, ContinuousLinearMap.mulLeftRight ℂ (Mat n)
    (exp ((1 - u) • A)) (exp (u • A))

private theorem derivativeIntegrable (A : Mat n) :
    IntervalIntegrable (fun u : ℝ => ContinuousLinearMap.mulLeftRight ℂ (Mat n)
      (exp ((1 - u) • A)) (exp (u • A))) volume 0 1 := by
  apply Continuous.intervalIntegrable
  apply (ContinuousLinearMap.mulLeftRight ℂ (Mat n)).continuous.comp
    (NormedSpace.exp_continuous.comp (continuous_const.sub continuous_id |>.smul continuous_const)) |>.clm_apply
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

/-- Evaluation of the continuous linear derivative commutes with the Bochner integral. -/
theorem derivative_apply (A J : Matrix n n ℂ) :
    derivative A J = ∫ u : ℝ in 0..1, exp ((1 - u) • A) * J * exp (u • A) := by
  unfold derivative
  rw [ContinuousLinearMap.intervalIntegral_apply (derivativeIntegrable A)]
  simp only [ContinuousLinearMap.mulLeftRight_apply]

private theorem response_eq (A J : Mat n) (x : EuclideanSpace ℂ n) :
    response identityContraction (fun _ => operatorEquiv A)
      (fun _ => operatorEquiv J) 1 0 x = operatorEquiv (derivative A J) x := by
  let U := (operatorEquiv (n := n)).toLinearEquiv.toContinuousLinearEquiv
  let L := (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ n) x).comp U.toContinuousLinearMap
  have hi : IntervalIntegrable (fun u : ℝ => exp ((1 - u) • A) * J * exp (u • A)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [derivative_apply]
  change _ = L _
  rw [← L.intervalIntegral_comp_comm hi, response]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  dsimp only
  rw [constantEvolution A hu.1 hu.2, constantEvolution A le_rfl hu.1]
  simp [L, U, map_mul]

private theorem remainder (A J : Mat n) :
    ‖exp (A + J) - exp A - derivative A J‖ ≤
      (1 / 2 : ℝ) * Real.exp (‖A‖ + ‖J‖) * ‖J‖ ^ 2 := by
  let C := operatorEquiv (n := n)
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  obtain ⟨_, _, hb, hc⟩ := (uniform_signed_response identityContraction
    (fun _ => C A) (fun _ => C J) zero_le_one (fun _ => aestronglyMeasurable_const)
    (fun _ => aestronglyMeasurable_const) (fun _ => ‖C A‖) (fun _ => ‖C J‖)
    (integrableOn_const (by simp)) (integrableOn_const (by simp))
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)).1 0 1 le_rfl zero_le_one le_rfl x
  have hsum : (fun _ : ℝ => C A) + (fun _ => C J) = fun _ => operatorEquiv (A + J) := by
    ext s : 1
    exact (map_add C A J).symm
  have h := hb.trans hc
  rw [hsum, constantEvolution (A + J) le_rfl zero_le_one,
    constantEvolution A le_rfl zero_le_one, response_eq] at h
  simpa [C, Matrix.l2_opNorm_toEuclideanCLM, map_sub] using h

/-- The full complex Fréchet derivative of the noncommutative matrix exponential. -/
theorem hasFDerivAt_exp (A : Matrix n n ℂ) :
    HasFDerivAt NormedSpace.exp (derivative A) A := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  let c : ℝ := (1 / 2 : ℝ) * Real.exp (‖A‖ + 1)
  refine IsBigO.trans_isLittleO (g := fun J : Mat n => ‖J‖ ^ 2) ?_
    (isLittleO_norm_pow_id (by decide : 1 < 2))
  refine IsBigO.of_bound c ?_
  filter_upwards [(continuous_norm.continuousAt : ContinuousAt (fun J : Mat n => ‖J‖) 0)
    (eventually_le_nhds (show ‖(0 : Mat n)‖ < (1 : ℝ) by simp))] with J hJ
  rw [Real.norm_of_nonneg (by positivity)]
  apply (remainder A J).trans
  dsimp [c]
  gcongr
  exact hJ

#print axioms hasFDerivAt_exp

end D5.S3.Quantum.Matrix.ExponentialFirstResponse
