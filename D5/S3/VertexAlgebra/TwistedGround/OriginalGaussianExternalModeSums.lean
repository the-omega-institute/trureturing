/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual signed frequency-moment generators with the input-zero boundary retained. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators

/-! Polynomial mode equations avoid assigning a Laurent quotient at the negative zero mode. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums
open OriginalGaussianSourceEvaluation OriginalGaussianExternalFrequency
open OriginalGaussianExternalDisplacement OriginalGaussianExternalMoments
open OriginalGaussianExternalGenerators

private lemma mode_derivative (out : Bool) {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => (p : ℂ) * sourceAmplitude out p x * u ^ (p - 1))
      (deriv (fun w => sourceMode out w x) u) ∧
    DifferentiableAt ℂ (fun w => sourceMode out w x) u := by
  obtain ⟨R, huR, hR⟩ := exists_between (show ‖u‖ < 1 - ‖x‖ by linarith)
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg u) huR
  have hs := (sourceAmplitude_mode_hasSum out (u := (R : ℂ)) (x := x)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0] using
      (show R + ‖x‖ < 1 by linarith))).summable.norm
  have hd (p : ℕ) : DifferentiableOn ℂ (fun w : ℂ => sourceAmplitude out p x * w ^ p)
      (Metric.ball 0 R) := fun w _ =>
    ((hasDerivAt_pow p w).const_mul _).differentiableAt.differentiableWithinAt
  have hb (p : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      ‖sourceAmplitude out p x * w ^ p‖ ≤ ‖sourceAmplitude out p x * (R : ℂ) ^ p‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w)
      (by simpa only [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp hw).le) p)
      (norm_nonneg _)
  have hu : u ∈ Metric.ball (0 : ℂ) R := by simpa using huR
  have h := Complex.hasSum_deriv_of_summable_norm hs hd Metric.isOpen_ball hb hu
  constructor
  · simpa only [deriv_const_mul_field, deriv_pow_field, sourceMode, mul_left_comm,
      mul_assoc] using h
  · exact (Complex.differentiableOn_tsum_of_summable_norm hs hd Metric.isOpen_ball hb)
      |>.differentiableAt (Metric.isOpen_ball.mem_nhds hu)

private lemma weighted_mode (out : Bool) (a : ℂ) {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => ((p : ℂ) + a) * sourceAmplitude out p x * u ^ p)
      (u * deriv (fun w => sourceMode out w x) u + a * sourceMode out u x) := by
  have hm := (sourceAmplitude_mode_hasSum out hsmall).summable.hasSum
  have hd := (mode_derivative out hsmall).1.mul_left u
  have he (p : ℕ) : u * ((p : ℂ) * sourceAmplitude out p x * u ^ (p - 1)) =
      (p : ℂ) * sourceAmplitude out p x * u ^ p := by
    cases p with
    | zero => simp
    | succ p => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring
  have hh := (hd.congr_fun (fun p => (he p).symm)).add (hm.mul_left a)
  exact hh.congr_fun (fun p => by ring)

/-- Both actual U generators follow from the mode derivative, with the exact p=0 boundary. -/
theorem sourceMoment_generators {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => sourceMoment true p x * u ^ p)
      (u * (1 - u) * deriv (fun w => sourceMode true w x) u +
        (1 - 3 * u) / 2 * sourceMode true u x - sourceAmplitude false 0 x / 2) ∧
    HasSum (fun p : ℕ => u * sourceMoment false p x * u ^ p)
      (u * (1 - u) * deriv (fun w => sourceMode false w x) u -
        (u + 1) / 2 * sourceMode false u x + sourceAmplitude false 0 x / 2) := by
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg u]
  have hplus := weighted_mode true (1 / 2 : ℂ) hsmall
  have hpnext := (weighted_mode true (3 / 2 : ℂ) hsmall).mul_left u
  have hpre : HasSum (fun p : ℕ => ((p : ℂ) + 1 / 2) *
      sourceAmplitude (predecessor true p).1 (predecessor true p).2 x * u ^ p)
      (sourceAmplitude false 0 x / 2 + u *
        (u * deriv (fun w => sourceMode true w x) u + 3 / 2 * sourceMode true u x)) := by
    apply (hasSum_nat_add_iff' 1).mp
    convert hpnext using 1
    · ext p
      simp only [predecessor, ite_true, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        pow_succ]
      ring
    · simp only [Finset.sum_range_one, predecessor, ite_true, Nat.cast_zero,
        zero_add, pow_zero, mul_one]
      ring
  have hm := weighted_mode false (1 / 2 : ℂ) hsmall
  have htail := (hasSum_nat_add_iff' 1).mpr (weighted_mode false (-1 / 2 : ℂ) hsmall)
  have hnnext : HasSum (fun p : ℕ => ((p : ℂ) + 1 / 2) *
      sourceAmplitude false (p + 1) x * u ^ (p + 1))
      (u * deriv (fun w => sourceMode false w x) u - sourceMode false u x / 2 +
        sourceAmplitude false 0 x / 2) := by
    convert htail using 1
    · ext p
      push_cast
      ring
    · simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one]
      ring
  constructor
  · have hh := hplus.sub hpre
    convert hh using 1
    · ext p
      rw [sourceMoment_eq_modeFrequency true p hx]
      simp only [modeFrequency, externalParameter, ite_true]
      ring
    · ring
  · have hh := hnnext.sub (hm.mul_left u)
    convert hh using 1
    · ext p
      rw [sourceMoment_eq_modeFrequency false p hx]
      simp only [modeFrequency, externalParameter, Bool.false_eq_true, ite_false,
        predecessor, pow_succ]
      ring
    · ring

private lemma mode_factors_ne_zero {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    1 - u ≠ 0 ∧ 1 - (1 - x) * u ≠ 0 ∧ 1 - x - u ≠ 0 := by
  have hu : ‖u‖ < 1 := by linarith [norm_nonneg x]
  have hne {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
    intro he
    have hh := congrArg norm (sub_eq_zero.mp he)
    simp only [norm_one] at hh
    linarith
  refine ⟨hne hu, hne ?_, ?_⟩
  · calc
      ‖(1 - x) * u‖ ≤ (1 + ‖x‖) * ‖u‖ := by
        rw [norm_mul]
        gcongr
        simpa only [norm_one] using norm_sub_le (1 : ℂ) x
      _ ≤ ‖u‖ + ‖x‖ := by nlinarith [norm_nonneg x]
      _ < 1 := hsmall
  · have hh : ‖x + u‖ < 1 := lt_of_le_of_lt (norm_add_le x u) (by linarith)
    simpa only [sub_sub] using hne hh

private lemma mode_derivative_explicit (out : Bool) {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1) :
    let a : ℂ := if out then 1 else 1 - x
    let b : ℂ := if out then 1 - x else 1
    deriv (fun w => sourceMode out w x) u =
      sourceMode out u x * (1 / (2 * (1 - u)) + b / (2 * (a - b * u))) := by
  dsimp only
  let a : ℂ := if out then 1 else 1 - x
  let b : ℂ := if out then 1 - x else 1
  change deriv (fun w => sourceMode out w x) u =
    sourceMode out u x * (1 / (2 * (1 - u)) + b / (2 * (a - b * u)))
  have hden {w : ℂ} (hw : ‖w‖ + ‖x‖ < 1) :
      (1 - w) * (a - b * w) ≠ 0 := by
    have hh := mode_factors_ne_zero hw
    cases out <;> simp_all [a, b]
  have hsquare {w : ℂ} (hw : ‖w‖ + ‖x‖ < 1) :
      sourceMode out w x ^ 2 * ((1 - w) * (a - b * w)) = 1 := by
    have hh := sourceMode_square hw
    have he : sourceMode out w x ^ 2 = 1 / ((1 - w) * (a - b * w)) := by
      cases out
      · simpa [a, b] using hh.2
      · simpa [a, b] using hh.1
    rw [he]
    exact div_mul_cancel₀ _ (hden hw)
  have hm := (mode_derivative out hsmall).2.hasDerivAt
  have hd := ((hasDerivAt_const u (1 : ℂ)).sub (hasDerivAt_id u)).mul
    ((hasDerivAt_const u a).sub ((hasDerivAt_id u).const_mul b))
  have he : (fun w => sourceMode out w x ^ 2 * ((1 - w) * (a - b * w)))
      =ᶠ[𝓝 u] (fun _ => 1) := by
    have hn : ∀ᶠ w : ℂ in 𝓝 u, ‖w‖ + ‖x‖ < 1 :=
      (continuous_norm.continuousAt.add continuousAt_const).eventually (gt_mem_nhds hsmall)
    exact hn.mono (fun _ hw => hsquare hw)
  have hz := (((hm.pow 2).mul hd).congr_of_eventuallyEq he.symm).unique
    (hasDerivAt_const u (1 : ℂ))
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq] at hz
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub, mul_one] at hz
  have hM : sourceMode out u x ≠ 0 := by
    intro hzero
    have hh := hsquare hsmall
    norm_num [hzero] at hh
  have hlin : 2 * ((1 - u) * (a - b * u)) *
      deriv (fun w => sourceMode out w x) u +
      sourceMode out u x * (-(a - b * u) - (1 - u) * b) = 0 := by
    apply mul_left_cancel₀ hM
    linear_combination hz
  have h1 := (mode_factors_ne_zero hsmall).1
  have h2 : a - b * u ≠ 0 := (mul_ne_zero_iff.mp (hden hsmall)).2
  have h2' : a - u * b ≠ 0 := by simpa only [mul_comm] using h2
  field_simp [h1, h2, h2']
  linear_combination hlin

/-- The actual signed U mode sums have rational amplitudes, with both zero-mode inputs. -/
theorem sourceMoment_generators_explicit {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => sourceMoment true p x * u ^ p)
      (sourceMode true u x * (1 - 2 * u + (1 - x) * u ^ 2) /
        (2 * (1 - (1 - x) * u)) - sourceAmplitude false 0 x / 2) ∧
    HasSum (fun p : ℕ => u * sourceMoment false p x * u ^ p)
      (sourceMode false u x * (u * (1 - u) / (2 * (1 - x - u)) - 1 / 2) +
        sourceAmplitude false 0 x / 2) := by
  have h := sourceMoment_generators hsmall
  rw [mode_derivative_explicit true hsmall] at h
  rw [mode_derivative_explicit false hsmall] at h
  simp only [ite_true, Bool.false_eq_true, ite_false, one_mul] at h
  have hn := mode_factors_ne_zero hsmall
  have hp : 1 - u + u * x ≠ 0 := by
    convert hn.2.1 using 1 <;> ring
  constructor
  · convert h.1 using 1
    field_simp [hn.1, hn.2.1, hp]
    ring_nf
    field_simp [hp]
    ring
  · convert h.2 using 1
    field_simp [hn.1, hn.2.2]
    ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums
