import D5.S3.Quantum.Semigroups.WuCubicConditioningSegment
import D5.S3.Quantum.Semigroups.WuCubicCenteredComparison
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Physical Gibbs conditioning for the Wu v1 (3.54) cubic deficit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicConditioningComparison

open WuCubicOperatorBridge (Mat Occupation D G GInv generator)
open WuCubicOperatorNormalization (operatorDeficit)
open WuCubicHotInnerPartialTrace (Local lift reduce rightGenerator hasDerivAt_operatorDeficit)
open WuCubicConditioningSegment (conditioning_segment_bounds_of_ratio)
open WuCubicCenteredComparison (endpoint_lt_of_centered_pos)
open WuRepeatedMiddleCubic (alpha)
open private cubeVariation generator_affine gibbs_entry_pos reduce_apply reduce_lift from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
open private gibbsOccupation from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private GInv_mul_G G_mul_GInv from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private G_adjoint from D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization

private theorem reduce_posDef {r : ℝ} (hr : 1 ≤ r) {X : Mat} (hX : X.PosDef) :
    (reduce r X).PosDef := by
  have hblock (i : Fin 2) :
      (gibbsOccupation r i • X.submatrix (fun j => (i, j)) (fun j => (i, j))).PosDef :=
    (hX.submatrix (fun _ _ h => congrArg Prod.snd h)).smul (gibbs_entry_pos hr i)
  have heq : reduce r X = ∑ i : Fin 2,
      gibbsOccupation r i • X.submatrix (fun j => (i, j)) (fun j => (i, j)) := by
    ext j k
    simp [reduce_apply, Matrix.sum_apply, RCLike.real_smul_eq_coe_mul]
  rw [heq, Fin.sum_univ_two]
  exact (hblock 0).add (hblock 1)

/-- The actual Gibbs-weighted residual gives zero first variation at the
conditioned observable. -/
theorem hasDerivAt_conditioning_deficit {r : ℝ} (hr : 1 ≤ r) {X : Mat} (hX : X.PosDef) :
    HasDerivAt (fun s : ℝ => operatorDeficit r
      (lift (reduce r X) + s • (X - lift (reduce r X)))) 0 0 := by
  let P := reduce r X
  let H := X - lift P
  have hP := reduce_posDef hr hX
  have hLift : (lift P).IsHermitian := by
    rw [lift, Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      hP.isHermitian.eq]
  have hH : H.IsHermitian := hX.isHermitian.sub hLift
  have hred : reduce r H = 0 := by
    have hsub : reduce r (X - lift P) = reduce r X - reduce r (lift P) := by
      ext j k
      simp [reduce_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
    dsimp only [H]
    rw [hsub, reduce_lift hr]
    exact sub_self P
  have hgen : rightGenerator r 0 = 0 := by simp [rightGenerator]
  simpa only [hred, hgen, cubeVariation, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    Matrix.trace_zero, Complex.zero_re, mul_zero, sub_zero] using
    hasDerivAt_operatorDeficit hr P hP H hH

/-- The physical deficit is continuous on an affine segment of positive-definite
embedded observables. -/
theorem continuousOn_operatorDeficit_affine (r : ℝ) (Y H : Mat)
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, (G r * (Y + s • H) * G r).PosDef) :
    ContinuousOn (fun s : ℝ => operatorDeficit r (Y + s • H)) (Icc 0 1) := by
  let X : ℝ → Mat := fun s => Y + s • H
  let M : ℝ → Mat := fun s => G r * X s * G r
  let N : ℝ → Mat := fun s => G r * generator r (X s) * G r
  let T : Mat →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap Occupation ℝ ℂ).toContinuousLinearMap
  have hX : Continuous X := by dsimp [X]; fun_prop
  have hM : Continuous M := (continuous_const.mul hX).mul continuous_const
  have hN : Continuous N := by
    simp only [N, X, generator_affine]
    fun_prop
  have hcube (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (M s ^ 3).PosDef := by
    have h := hpos s hs
    exact (h.posSemidef.pow 3).posDef_iff_isUnit.mpr (h.isUnit.pow 3)
  have hlog : ContinuousOn (fun s => CFC.log (M s ^ 3)) (Icc (0 : ℝ) 1) :=
    CFC.continuousOn_log.comp (hM.pow 3).continuousOn
      (fun s hs => ⟨(hcube s hs).isHermitian, (hcube s hs).isUnit⟩)
  have hE := T.continuous.comp ((hM.pow 2).mul hN)
  have hS : ContinuousOn
      (fun s => T (M s ^ 3 * (CFC.log (M s ^ 3) - cfc Real.log (D r)))) (Icc 0 1) :=
    T.continuous.comp_continuousOn
      ((hM.pow 3).continuousOn.mul (hlog.sub continuousOn_const))
  have hmass := Real.continuous_mul_log.comp (T.continuous.comp (hM.pow 3))
  exact (continuous_const.mul hE).continuousOn.sub
    (continuousOn_const.mul (hS.sub hmass.continuousOn))

section Spectral

variable {r L ratio : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) (X : Mat) (hL : 0 < L)
  (hRatio : 0 < ratio)
  (hM : (G r * X * G r).IsHermitian)
  (hlow : ∀ i, ratio * L ≤ hM.eigenvalues i)
  (hup : ∀ i, hM.eigenvalues i ≤ L)
  (hmax : ∃ i, hM.eigenvalues i = L)

include hr hhi hL hRatio hM hlow hup hmax

private theorem conditioning_path_posDef (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (G r * (lift (reduce r X) + s • (X - lift (reduce r X))) * G r).PosDef := by
  obtain ⟨_, _, hpos, _⟩ :=
    conditioning_segment_bounds_of_ratio hr hhi X hL hRatio hs.1 hs.2 hM hlow hup hmax
  have heq : G r * (lift (reduce r X) + s • (X - lift (reduce r X))) * G r =
      (1 - s) • (G r * lift (reduce r X) * G r) + s • (G r * X * G r) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul]
    module
  rwa [heq]

/-- Under the physical segment's spectral hypotheses, the deficit is stationary
at the Gibbs-conditioned endpoint and continuous on the full closed segment. -/
theorem conditioning_segment_stationary_continuous_of_ratio :
    let f := fun s : ℝ => operatorDeficit r (lift (reduce r X) + s • (X - lift (reduce r X)))
    HasDerivAt f 0 0 ∧ ContinuousOn f (Icc 0 1) := by
  dsimp only
  have hpos := conditioning_path_posDef hr hhi X hL hRatio hM hlow hup hmax
  have hend := hpos 1 ⟨zero_le_one, le_rfl⟩
  rw [one_smul, add_sub_cancel] at hend
  have hG : IsUnit (G r) :=
    ⟨⟨G r, GInv r, G_mul_GInv hr, GInv_mul_G hr⟩, rfl⟩
  have hX : X.PosDef := hG.posDef_star_left_conjugate_iff.mp (by
    simpa only [Matrix.star_eq_conjTranspose, G_adjoint] using hend)
  exact ⟨hasDerivAt_conditioning_deficit hr hX, continuousOn_operatorDeficit_affine r _ _ hpos⟩

/-- Interior strict centered positivity gives a strict comparison whenever
the physical observable has a nonzero Gibbs-weighted residual. -/
theorem operatorDeficit_conditioning_lt_of_ratio
    (hcenter : X - lift (reduce r X) ≠ 0 →
      let f := fun s : ℝ => operatorDeficit r (lift (reduce r X) + s • (X - lift (reduce r X)))
      ∀ s ∈ Ioo (0 : ℝ) 1, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
        2 * f s < f (s + t) + f (s - t))
    (hres : X - lift (reduce r X) ≠ 0) :
    operatorDeficit r (lift (reduce r X)) < operatorDeficit r X := by
  obtain ⟨hderiv, hcont⟩ :=
    conditioning_segment_stationary_continuous_of_ratio hr hhi X hL hRatio hM hlow hup hmax
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel] using
    endpoint_lt_of_centered_pos hcont (hcenter hres) hderiv

end Spectral

section TwoThirds

variable {r L : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) (X : Mat) (hL : 0 < L)
  (hM : (G r * X * G r).IsHermitian)
  (hlow : ∀ i, 2 / 3 * L ≤ hM.eigenvalues i)
  (hup : ∀ i, hM.eigenvalues i ≤ L)
  (hmax : ∃ i, hM.eigenvalues i = L)

include hr hhi hL hM hlow hup hmax

/-- Stationarity and continuity on the two-thirds spectral region. -/
theorem conditioning_segment_stationary_continuous :
    let f := fun s : ℝ => operatorDeficit r (lift (reduce r X) + s • (X - lift (reduce r X)))
    HasDerivAt f 0 0 ∧ ContinuousOn f (Icc 0 1) :=
  conditioning_segment_stationary_continuous_of_ratio hr hhi X hL (ratio := 2 / 3)
    (by norm_num) hM hlow hup hmax

/-- Strict conditioning comparison on the two-thirds spectral region. -/
theorem operatorDeficit_conditioning_lt
    (hcenter : X - lift (reduce r X) ≠ 0 →
      let f := fun s : ℝ => operatorDeficit r (lift (reduce r X) + s • (X - lift (reduce r X)))
      ∀ s ∈ Ioo (0 : ℝ) 1, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
        2 * f s < f (s + t) + f (s - t))
    (hres : X - lift (reduce r X) ≠ 0) :
    operatorDeficit r (lift (reduce r X)) < operatorDeficit r X :=
  operatorDeficit_conditioning_lt_of_ratio hr hhi X hL (ratio := 2 / 3)
    (by norm_num) hM hlow hup hmax hcenter hres

end TwoThirds

run_cmd do
  for theoremName in #[``hasDerivAt_conditioning_deficit, ``continuousOn_operatorDeficit_affine,
      ``conditioning_segment_stationary_continuous_of_ratio, ``operatorDeficit_conditioning_lt_of_ratio,
      ``conditioning_segment_stationary_continuous, ``operatorDeficit_conditioning_lt] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom for {theoremName}: {axiomName}"

end D5.S3.Quantum.Semigroups.WuCubicConditioningComparison
