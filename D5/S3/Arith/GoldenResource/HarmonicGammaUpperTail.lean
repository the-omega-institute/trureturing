/- GID: D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/HarmonicGammaUpperTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A strict fourth-order upper bound completes the corrected harmonic-log tail bracket. -/

/-
proof_shape: content for harmonic_log_tail_upper and its named companion
  harmonic_log_tail_bounds, whose upper component uses the former on a live path.
Direct frozen dependency: D5/S3/Arith/GoldenResource/HarmonicGammaTail,
  statement_id sha256:a40c747352a586ff27baae23a34bc812476e0843d721817a311f21eab3f5562e.
  Its private stepGap, correctedSeq, step identity and limits are reused with open private.
  The companion also uses harmonic_log_tail_lower,
  statement_id sha256:c5dd4b35decb8df3d6bb8483fb3b20d1e6c99516fa109dc118d08fce16329c3f.
escape_witness: upper_gap_neg proves f(x) < w(x) uniformly for x > 0 from the
  derivative sign and limit of f-w. Finite telescoping and a strict first-step
  margin then place the fourth-corrected sequence strictly below gamma.
  Pure derivative algebra and finite arithmetic are not escape witnesses.
admission_basis: escape-witness.
utility: none; all declarations are general analytic definitions or estimates,
  not bounded enumeration, a checker, numerical reduction, or a certified instance.
  Consumer -> prerequisite: harmonic_log_tail_bounds -> harmonic_log_tail_upper.
  RobinRationalBasis accepts coarse gamma witnesses; it does not explicitly demand
  ten-digit precision. This supplies a permitted tighter analytic bound.
Provenance: literature-attested classical Euler-Maclaurin estimate, DLMF 5.11.2
  and its positive-real remainder sign; reuse nist2026asymptotic, no novelty claimed.
-/

import D5.S3.Arith.GoldenResource.HarmonicGammaTail
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.HarmonicGammaUpperTail

open Filter Topology

open private stepGap step_gap_hasDerivAt step_gap_tendsto_zero correctedSeq
  corrected_seq_step corrected_seq_tendsto
  from D5.S3.Arith.GoldenResource.HarmonicGammaTail

private noncomputable def fourthCorrection (x : ℝ) : ℝ := (1 / 120) * (x⁻¹) ^ 4

private noncomputable def upperGap (x : ℝ) : ℝ :=
  stepGap x - (fourthCorrection x - fourthCorrection (x + 1))

private lemma upper_gap_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt upperGap ((5 * x ^ 2 + 5 * x + 1) / (30 * x ^ 5 * (x + 1) ^ 5)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  have hi := (((hasDerivAt_id x).inv hx0).pow 4).const_mul (1 / 120)
  have hj := ((((hasDerivAt_id x).add_const 1).inv hx1).pow 4).const_mul (1 / 120)
  have hd := (step_gap_hasDerivAt x hx).sub (hi.sub hj)
  convert! hd using 1
  dsimp
  field_simp
  ring

private lemma upper_gap_tendsto_zero : Tendsto upperGap atTop (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hj := hi.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have ht := step_gap_tendsto_zero.sub
    (((hi.pow 4).const_mul (1 / 120)).sub ((hj.pow 4).const_mul (1 / 120)))
  unfold upperGap fourthCorrection
  simpa only [Function.comp_def, id_eq, zero_pow (by norm_num : (4 : ℕ) ≠ 0),
    mul_zero, sub_zero] using ht

private lemma upper_gap_neg (x : ℝ) (hx : 0 < x) : upperGap x < 0 := by
  have hm : StrictMonoOn upperGap (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · intro y hy
      exact (upper_gap_hasDerivAt y hy).continuousAt.continuousWithinAt
    · intro y hy
      have hy0 : 0 < y := (interior_subset hy : y ∈ Set.Ioi 0)
      rw [(upper_gap_hasDerivAt y hy0).deriv]
      positivity
  have hle : upperGap (x + 1) ≤ 0 := by
    apply ge_of_tendsto upper_gap_tendsto_zero
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    exact hm.monotoneOn (show 0 < x + 1 by linarith) (show 0 < y by linarith) hy
  exact (hm hx (show 0 < x + 1 by linarith) (by linarith)).trans_le hle

private noncomputable def fourthSeq (n : ℕ) : ℝ :=
  correctedSeq n - fourthCorrection ((n : ℝ) + 1)

private lemma fourth_seq_step_lt (n : ℕ) : fourthSeq n < fourthSeq (n + 1) := by
  have hg := upper_gap_neg ((n : ℝ) + 1) (by positivity)
  rw [upperGap, ← corrected_seq_step] at hg
  simp only [fourthSeq, Nat.cast_add, Nat.cast_one]
  linarith only [hg]

private lemma fourth_seq_telescope (n m : ℕ) : fourthSeq n ≤ fourthSeq (n + m) := by
  have hs : 0 ≤ ∑ k ∈ Finset.range m, (fourthSeq (n + (k + 1)) - fourthSeq (n + k)) := by
    apply Finset.sum_nonneg
    intro k _
    exact sub_nonneg.mpr (by simpa only [Nat.add_assoc] using (fourth_seq_step_lt (n + k)).le)
  rw [Finset.sum_range_sub (fun k => fourthSeq (n + k)) m, Nat.add_zero] at hs
  exact sub_nonneg.mp hs

private lemma fourth_seq_tendsto :
    Tendsto fourthSeq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := corrected_seq_tendsto.sub ((hi.pow 4).const_mul (1 / 120))
  unfold fourthSeq fourthCorrection
  simpa only [zero_pow (by norm_num : (4 : ℕ) ≠ 0),
    mul_zero, sub_zero] using ht

private lemma fourth_seq_lt_gamma (n : ℕ) : fourthSeq n < Real.eulerMascheroniConstant := by
  have hle : fourthSeq (n + 1) ≤ Real.eulerMascheroniConstant := by
    apply ge_of_tendsto (fourth_seq_tendsto.comp (tendsto_add_atTop_nat (n + 1)))
    exact Filter.Eventually.of_forall fun m => by
      simpa only [Function.comp_def, Nat.add_comm] using fourth_seq_telescope (n + 1) m
  exact (fourth_seq_step_lt n).trans_le hle

/-- The corrected harmonic-logarithmic remainder is strictly below its fourth-order term. -/
theorem harmonic_log_tail_upper (N : ℕ) (hN : 1 ≤ N) :
    (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant -
      1 / (2 * N : ℝ) + 1 / (12 * (N : ℝ) ^ 2) < 1 / (120 * (N : ℝ) ^ 4) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_comm 1 n]
  have hstrict := fourth_seq_lt_gamma n
  dsimp [fourthSeq, correctedSeq, fourthCorrection] at hstrict
  push_cast at hstrict ⊢
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] at hstrict ⊢
  linarith only [hstrict]

/-- The two strict bounds on the corrected remainder, for every positive integer. -/
theorem harmonic_log_tail_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 < (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant -
      1 / (2 * N : ℝ) + 1 / (12 * (N : ℝ) ^ 2) ∧
    (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant -
      1 / (2 * N : ℝ) + 1 / (12 * (N : ℝ) ^ 2) < 1 / (120 * (N : ℝ) ^ 4) := by
  constructor
  · have hl := HarmonicGammaTail.harmonic_log_tail_lower N hN
    linarith only [hl]
  · exact harmonic_log_tail_upper N hN

#print axioms harmonic_log_tail_upper
#print axioms harmonic_log_tail_bounds

end D5.S3.Arith.GoldenResource.HarmonicGammaUpperTail
