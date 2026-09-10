/- GID: D5/S3/Arith/GoldenResource/HarmonicGammaTail
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/HarmonicGammaTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A signed harmonic-log tail estimate yields a ten-digit Euler-constant upper bound. -/

/-
proof_shape: content for harmonic_log_tail_lower and its named companion
  eulerMascheroni_upper_128, after inlining the latter's live dependency on the former.
Direct frozen dependencies: none; the proof uses pinned Mathlib analysis.
escape_witness: step_gap_pos establishes positivity uniformly on positive real inputs;
  corrected_seq_strictAnti and corrected_seq_tendsto retain a strict first-step gap above γ.
  Derivative algebra and finite arithmetic alone are not the witness.
admission_basis: escape-witness.
utility: the main result is a general analytic inequality; the numeric corollary is its
  explicitly requested named companion, not an independent computational delivery.
  Consumer → prerequisite: eulerMascheroni_upper_128 → harmonic_log_tail_lower.
  The existing RobinRationalBasis.robinPositiveJudge_sound accepts a coarse gamma bracket;
  it does not explicitly require this precision, and no new import by it is claimed.
Provenance: classical Euler–Maclaurin estimate, literature-attested via the Blueprint's
  L-plane note; no mathematical novelty is claimed.
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.HarmonicGammaTail

open Filter Topology

private noncomputable def stepGap (x : ℝ) : ℝ :=
  Real.log (x + 1) - Real.log x - (1 / 2) * x⁻¹ - (1 / 2) * (x + 1)⁻¹ +
    (1 / 12) * (x⁻¹) ^ 2 - (1 / 12) * ((x + 1)⁻¹) ^ 2

private lemma step_gap_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt stepGap (-1 / (6 * x ^ 3 * (x + 1) ^ 3)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  have hi := (hasDerivAt_id x).inv hx0
  have hj := ((hasDerivAt_id x).add_const 1).inv hx1
  have hl := ((hasDerivAt_id x).add_const 1).log hx1
  have hd := ((((hl.sub (Real.hasDerivAt_log hx0)).sub (hi.const_mul (1 / 2))).sub
    (hj.const_mul (1 / 2))).add ((hi.pow 2).const_mul (1 / 12))).sub
    ((hj.pow 2).const_mul (1 / 12))
  convert! hd using 1
  dsimp
  field_simp
  ring

private lemma step_gap_tendsto_zero : Tendsto stepGap atTop (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hj : Tendsto (fun x : ℝ => (x + 1)⁻¹) atTop (𝓝 0) :=
    hi.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hl := Real.tendsto_log_comp_add_sub_log (1 : ℝ)
  have hsub := (hl.sub (hi.const_mul (1 / 2))).sub (hj.const_mul (1 / 2))
  have hadd := hsub.add ((hi.pow 2).const_mul (1 / 12))
  have hd := hadd.sub ((hj.pow 2).const_mul (1 / 12))
  unfold stepGap
  simpa only [mul_zero, sub_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hd

private lemma step_gap_pos (x : ℝ) (hx : 0 < x) : 0 < stepGap x := by
  have ha : StrictAntiOn stepGap (Set.Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    · intro y hy
      exact (step_gap_hasDerivAt y hy).continuousAt.continuousWithinAt
    · intro y hy
      have hy0 : 0 < y := (interior_subset hy : y ∈ Set.Ioi 0)
      rw [(step_gap_hasDerivAt y hy0).deriv]
      exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hle : 0 ≤ stepGap (x + 1) := by
    apply le_of_tendsto step_gap_tendsto_zero
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    exact ha.antitoneOn (show 0 < x + 1 by linarith) (show 0 < y by linarith) hy
  exact hle.trans_lt (ha hx (show 0 < x + 1 by linarith) (by linarith))

private noncomputable def correctedSeq (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - (1 / 2) * ((n : ℝ) + 1)⁻¹ +
    (1 / 12) * (((n : ℝ) + 1)⁻¹) ^ 2

private lemma corrected_seq_step (n : ℕ) :
    correctedSeq n - correctedSeq (n + 1) = stepGap ((n : ℝ) + 1) := by
  simp only [correctedSeq, stepGap, harmonic_succ, Rat.cast_add, Rat.cast_inv,
    Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  ring

private lemma corrected_seq_strictAnti : StrictAnti correctedSeq := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [← sub_pos, corrected_seq_step]
  exact step_gap_pos _ (by positivity)

private lemma corrected_seq_tendsto :
    Tendsto correctedSeq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hl := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := (hl.sub (hi.const_mul (1 / 2))).add ((hi.pow 2).const_mul (1 / 12))
  unfold correctedSeq
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, mul_zero, sub_zero, add_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht

/-- A uniform signed lower estimate for the harmonic–logarithmic tail after two corrections. -/
theorem harmonic_log_tail_lower (N : ℕ) (hN : 1 ≤ N) :
    1 / (2 * N : ℝ) - 1 / (12 * (N : ℝ) ^ 2) <
      (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_comm 1 n]
  have hstrict : Real.eulerMascheroniConstant < correctedSeq n :=
    (corrected_seq_strictAnti.antitone.le_of_tendsto corrected_seq_tendsto (n + 1)).trans_lt
      (corrected_seq_strictAnti (Nat.lt_succ_self n))
  dsimp [correctedSeq] at hstrict
  push_cast at hstrict ⊢
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] at hstrict ⊢
  linarith only [hstrict]

/-- The uniform tail estimate at 128 gives this rational upper bound for Euler's constant. -/
theorem eulerMascheroni_upper_128 :
    Real.eulerMascheroniConstant < (5772156650 / 10 ^ 10 : ℝ) := by
  have htail := harmonic_log_tail_lower 128 (by norm_num)
  have hlog := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 12
  norm_num [Finset.sum_range_succ] at hlog
  norm_num [harmonic] at htail
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow] at htail
  norm_num at htail ⊢
  linarith only [htail, hlog]
#print axioms harmonic_log_tail_lower
#print axioms eulerMascheroni_upper_128

end D5.S3.Arith.GoldenResource.HarmonicGammaTail
