/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal two-variable frequency and displacement differential equations. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows

/-! The original ordinary bilinear symmetry supplies the second frequency action. -/

noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
open OriginalGaussianExternalResolvent OriginalGaussianExternalFrequency
open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalFrequencyRows
open OriginalGaussianExternalDisplacement OriginalGaussianExternalGenerators
open OriginalGaussianExternalEvolution OriginalGaussianAllIndexResolvent
open OriginalGaussianWeightedResolvent
open OriginalGaussianBilinearTranspose OriginalGaussianDifferentiation

lemma literal_symmetry (square out out' : Bool) (p q : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    (if square then externalT out p out' q z else externalJ out p out' q z) =
      (if square then externalT out' q out p z else externalJ out' q out p z) := by
  let X := externalVector out p z
  let Y := externalVector out' q z
  have hp : sourceBilinearFunctional X (OriginalGaussianResolvent.resolvent z Y) =
      sourceBilinearFunctional Y (OriginalGaussianResolvent.resolvent z X) :=
    (resolvent_bilinear_transpose hz X Y).trans (sourceBilinearFunctional_comm _ _)
  have hm : sourceBilinearFunctional X (oppositeResolvent z Y) =
      sourceBilinearFunctional Y (oppositeResolvent z X) :=
    (opposite_bilinear_transpose hz X Y).trans (sourceBilinearFunctional_comm _ _)
  have hX := external_contractions_explicit out p out' q hz
  have hY := external_contractions_explicit out' q out p hz
  cases square
  · simp only [Bool.false_eq_true, ite_false]
    rw [← hX.2.2.1, ← hY.2.2.1]
    change sourceBilinearFunctional X (oddResolvent z Y) =
      sourceBilinearFunctional Y (oddResolvent z X)
    rw [odd_eq_half_difference hz]
    simp only [smul_apply, sub_apply, map_smul, map_sub, smul_eq_mul, hp, hm]
  · simp only [ite_true]
    rw [← hX.2.2.2.1, ← hY.2.2.2.1]
    change sourceBilinearFunctional X (squareResolvent z Y) =
      sourceBilinearFunctional Y (squareResolvent z X)
    rw [square_half hz]
    simp only [smul_apply, add_apply, map_smul, map_add, smul_eq_mul, hp, hm]

private lemma kernel_symmetry (square out out' : Bool) (u v : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    kernelMode square out out' u v z = kernelMode square out' out v u z := by
  unfold kernelMode
  calc
    _ = ∑' pq : ℕ × ℕ, (if square then externalT out' pq.2 out pq.1 z
        else externalJ out' pq.2 out pq.1 z) * v ^ pq.2 * u ^ pq.1 := by
      apply tsum_congr
      intro pq
      rw [literal_symmetry square out out' pq.1 pq.2 hz]
      ring
    _ = _ := (Equiv.prodComm ℕ ℕ).tsum_eq
      (fun pq : ℕ × ℕ => (if square then externalT out' pq.1 out pq.2 z
        else externalJ out' pq.1 out pq.2 z) * v ^ pq.1 * u ^ pq.2)

/-- The scaled first frequency operator on the actual generator, before its zero-row correction. -/
def firstModeDerivative (square out out' : Bool) (u v z : ℂ) : ℂ :=
  u * (1 - u) * deriv (fun w => kernelMode square out out' w v z) u +
    (if out then (1 - 3 * u) / 2 else -(u + 1) / 2) *
      kernelMode square out out' u v z

/-- The scaled second frequency operator on the actual generator, before its zero-row correction. -/
def secondModeDerivative (square out out' : Bool) (u v z : ℂ) : ℂ :=
  v * (1 - v) * deriv (fun w => kernelMode square out out' u w z) v +
    (if out' then (1 - 3 * v) / 2 else -(v + 1) / 2) *
      kernelMode square out out' u v z

private lemma swapped_derivative_eq (square out out' : Bool) (u v : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) : firstModeDerivative square out' out v u z =
      secondModeDerivative square out out' u v z := by
  have hf : (fun w => kernelMode square out' out w u z) =
      (fun w => kernelMode square out out' u w z) := by
    funext w
    exact kernel_symmetry square out' out w u hz
  simp only [firstModeDerivative, secondModeDerivative, hf,
    kernel_symmetry square out' out v u hz]

private lemma first_frequency (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    HasSum (fun pq : ℕ × ℕ => modeScale out u *
      modeFrequency out pq.1 (fun e k =>
        if square then externalT e k out' pq.2 z else externalJ e k out' pq.2 z) *
          u ^ pq.1 * v ^ pq.2)
      (firstModeDerivative square out out' u v z - modeB out *
        (∑' q : ℕ, (if square then externalT false 0 out' q z
          else externalJ false 0 out' q z) * v ^ q)) := by
  have h := external_frequency_generated square out out' hu hv
  convert h using 1
  cases out <;> simp only [firstModeDerivative, modeB, Bool.false_eq_true,
    ite_false, ite_true] <;> ring

/-- Literal transpose symmetry transports the frequency sum to the second external variable. -/
theorem second_frequency (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    HasSum (fun pq : ℕ × ℕ => modeScale out' v *
      modeFrequency out' pq.2 (fun e k =>
        if square then externalT out pq.1 e k z else externalJ out pq.1 e k z) *
          u ^ pq.1 * v ^ pq.2)
      (secondModeDerivative square out out' u v z - modeB out' *
        (∑' p : ℕ, (if square then externalT false 0 out p z
          else externalJ false 0 out p z) * u ^ p)) := by
  have h := first_frequency square out' out hv hu
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg u]
  rw [swapped_derivative_eq square out out' u v hz] at h
  have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h
  apply hs.congr_fun
  intro pq
  simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap,
    Prod.snd_swap, modeFrequency]
  rw [literal_symmetry square out out' pq.1 pq.2 hz,
    literal_symmetry square out (predecessor out' pq.2).1 pq.1
      (predecessor out' pq.2).2 hz]
  ring

set_option maxHeartbeats 800000 in
-- The actual mode sums are matched before their zero-row corrections are eliminated.
/-- The original J/T displacement equations act on both partial derivatives of the literal kernels. -/
theorem displacement_with_boundary (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lam := shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    let B := fun (sq e : Bool) (w : ℂ) => ∑' k : ℕ,
      (if sq then externalT false 0 e k z else externalJ false 0 e k z) * w ^ k
    let U := fun e w => sourceMode e w x * modeA e w x -
      modeB e * OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
    let V := fun e w => sourceMode e w x * modeH e w x lam +
      modeB e * OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
    (modeScale out' v * (firstModeDerivative false out out' u v z - modeB out * B false out' v) +
      modeScale out u * (secondModeDerivative false out out' u v z - modeB out' * B false out u) =
        (1 - x) * (U out u * V out' v + V out u * U out' v) / 2) ∧
    (modeScale out' v * (firstModeDerivative true out out' u v z - modeB out * B true out' v) -
      modeScale out u * (secondModeDerivative true out out' u v z - modeB out' * B true out u) =
        (1 - x) * (U out u * V out' v - V out u * U out' v) / 2) := by
  dsimp only
  have hu' : ‖u‖ + ‖(Real.sqrt r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hu
  have hv' : ‖v‖ + ‖(Real.sqrt r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hv
  have hrs : r ≤ Real.sqrt r := Real.le_sqrt_self_iff.mpr hr1.le
  have hur : ‖u‖ + r < 1 := by linarith
  have hvr : ‖v‖ + r < 1 := by linarith
  have hsource := external_displacement_generated out out' hr hr1 hur hvr
  constructor
  · have hh := ((first_frequency false out out' hu' hv').mul_left (modeScale out' v)).add
      ((second_frequency false out out' hu' hv').mul_left (modeScale out u))
    have hs := hh.congr_fun (g := fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
        (modeFrequency out pq.1 (fun e k => externalJ e k out' pq.2 (Real.sqrt r : ℂ)) +
          modeFrequency out' pq.2 (fun e k => externalJ out pq.1 e k (Real.sqrt r : ℂ))) *
            u ^ pq.1 * v ^ pq.2) (fun pq => by
      simp only [Bool.false_eq_true, ite_false]
      ring)
    exact hs.unique hsource.1
  · have hh := ((first_frequency true out out' hu' hv').mul_left (modeScale out' v)).sub
      ((second_frequency true out out' hu' hv').mul_left (modeScale out u))
    have hs := hh.congr_fun (g := fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
        (modeFrequency out pq.1 (fun e k => externalT e k out' pq.2 (Real.sqrt r : ℂ)) -
          modeFrequency out' pq.2 (fun e k => externalT out pq.1 e k (Real.sqrt r : ℂ))) *
            u ^ pq.1 * v ^ pq.2) (fun pq => by
      simp only [ite_true]
      ring)
    exact hs.unique hsource.2

private lemma cancel_boundary (c t A M N a b h k d e L R : ℂ)
    (ht : c * A = t) (hA : c * A ^ 2 = 1)
    (hL : L = c * ((M * a - d * A) * (N * k + e * A) +
      (M * h + d * A) * (N * b - e * A)) / 2 +
        d * (t / 2 * (N * (k - b)) + e) + e * (t / 2 * (M * (h - a)) + d))
    (hR : R = c * ((M * a - d * A) * (N * k + e * A) -
      (M * h + d * A) * (N * b - e * A)) / 2 +
        d * (t / 2 * (N * (k + b))) - e * (t / 2 * (M * (h + a)))) :
    L = c * M * N * (a * k + h * b) / 2 + d * e ∧
      R = c * M * N * (a * k - h * b) / 2 := by
  constructor
  · linear_combination hL - (d * e) * hA - (d * N * (k - b) / 2 + e * M * (h - a) / 2) * ht
  · linear_combination hR + (e * M * (h + a) / 2 - d * N * (k + b) / 2) * ht

set_option maxHeartbeats 800000 in
-- The literal zero-row values cancel the source scalar corrections.
/-- EJ and ETd hold for the full original kernels with the evaluated source amplitudes. -/
theorem displacement_differential (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lam := shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    (modeScale out' v * firstModeDerivative false out out' u v z +
      modeScale out u * secondModeDerivative false out out' u v z =
        (1 - x) * sourceMode out u x * sourceMode out' v x *
          (modeA out u x * modeH out' v x lam + modeH out u x lam * modeA out' v x) / 2 +
            modeB out * modeB out') ∧
    (modeScale out' v * firstModeDerivative true out out' u v z -
      modeScale out u * secondModeDerivative true out out' u v z =
        (1 - x) * sourceMode out u x * sourceMode out' v x *
          (modeA out u x * modeH out' v x lam - modeH out u x lam * modeA out' v x) / 2) := by
  dsimp only
  let z : ℂ := Real.sqrt r
  let x : ℂ := r
  let lam := shiftedCentralDerivative x 0 / D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
  let B := fun (sq e : Bool) (w : ℂ) => ∑' k : ℕ,
    (if sq then externalT false 0 e k z else externalJ false 0 e k z) * w ^ k
  let U := fun e w => sourceMode e w x * modeA e w x -
    modeB e * OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
  let V := fun e w => sourceMode e w x * modeH e w x lam +
    modeB e * OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
  have hsource := displacement_with_boundary out out' hr hr1 hu hv
  change
    (modeScale out' v * (firstModeDerivative false out out' u v z - modeB out * B false out' v) +
      modeScale out u * (secondModeDerivative false out out' u v z - modeB out' * B false out u) =
        (1 - x) * (U out u * V out' v + V out u * U out' v) / 2) ∧
    (modeScale out' v * (firstModeDerivative true out out' u v z - modeB out * B true out' v) -
      modeScale out u * (secondModeDerivative true out out' u v z - modeB out' * B true out u) =
        (1 - x) * (U out u * V out' v - V out u * U out' v) / 2) at hsource
  have hrs : r ≤ Real.sqrt r := Real.le_sqrt_self_iff.mpr hr1.le
  have hur : ‖u‖ + r < 1 := by linarith
  have hvr : ‖v‖ + r < 1 := by linarith
  have hbJ (e : Bool) (w : ℂ) (hw : ‖w‖ + r < 1) :
      modeScale e w * B false e w = (Real.sqrt (1 - r) : ℂ) / 2 *
        (sourceMode e w x * (modeH e w x lam - modeA e w x)) + modeB e := by
    simpa only [B, Bool.false_eq_true, ite_false, mul_assoc, tsum_mul_left] using
      (external_negative_zero_generated e hr hr1 hw).1.tsum_eq
  have hbT (e : Bool) (w : ℂ) (hw : ‖w‖ + r < 1) :
      modeScale e w * B true e w = (Real.sqrt (1 - r) : ℂ) / 2 *
        (sourceMode e w x * (modeH e w x lam + modeA e w x)) := by
    simpa only [B, ite_true, mul_assoc, tsum_mul_left] using
      (external_negative_zero_generated e hr hr1 hw).2.tsum_eq
  let A := OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
  let t : ℂ := Real.sqrt (1 - r)
  have hn : t * A = 1 := boundary_normalization hr hr1
  have ht : t ^ 2 = 1 - x := by
    dsimp [t, x]
    norm_cast
    exact Real.sq_sqrt (by linarith)
  have hca : (1 - x) * A = t := by
    rw [← ht, pow_two, mul_assoc, hn, mul_one]
  have hca2 : (1 - x) * A ^ 2 = 1 := by
    calc
      _ = (t * A) ^ 2 := by rw [← ht]; ring
      _ = 1 := by rw [hn]; norm_num
  have hJ : modeScale out' v * firstModeDerivative false out out' u v z +
      modeScale out u * secondModeDerivative false out out' u v z =
        (1 - x) * (U out u * V out' v + V out u * U out' v) / 2 +
          modeB out * (modeScale out' v * B false out' v) +
          modeB out' * (modeScale out u * B false out u) := by
    linear_combination hsource.1
  have hT : modeScale out' v * firstModeDerivative true out out' u v z -
      modeScale out u * secondModeDerivative true out out' u v z =
        (1 - x) * (U out u * V out' v - V out u * U out' v) / 2 +
          modeB out * (modeScale out' v * B true out' v) -
          modeB out' * (modeScale out u * B true out u) := by
    linear_combination hsource.2
  rw [hbJ out' v hvr, hbJ out u hur] at hJ
  rw [hbT out' v hvr, hbT out u hur] at hT
  exact cancel_boundary (1 - x) t A (sourceMode out u x) (sourceMode out' v x)
    (modeA out u x) (modeA out' v x) (modeH out u x lam) (modeH out' v x lam)
    (modeB out) (modeB out') _ _ hca hca2 hJ hT

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
