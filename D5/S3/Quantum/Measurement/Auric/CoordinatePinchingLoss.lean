/- GID: D5/S3/Quantum/Measurement/Auric/CoordinatePinchingLoss
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/CoordinatePinchingLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual AURIC decoding losses at fixed block law form a sharp interval, and equal entropy and coherent success allow distinct recorded optima. -/

import D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Order.IntermediateValue

/-! The attainable decoding loss at fixed block law and a pair with equal entropy and distinct recorded optima. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix
open Matrix JointRecordDecoding
open D5.S3.Entropy.MaxEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Measurement.Auric.CoordinatePinchingEntropy
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open D5.S3.Quantum.Subentropy.GuessingProbability
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree

namespace D5.S3.Quantum.Measurement.Auric.CoordinatePinchingLoss

section LossRange

variable {ι : Type*} [Fintype ι] {k : ℕ}

private theorem amplitude_eq_sum (c : ι → Fin k) (t : ι → ℝ) (b : Fin k) :
    blockAmplitude c t b = ∑ i ∈ fiber c b, t i := by
  simp [blockAmplitude, maskedProfile, fiber, Finset.sum_filter]

private theorem amplitude_bounds (c : ι → Fin k) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (b : Fin k) :
    Real.sqrt (blockWeight c t b) ≤ blockAmplitude c t b ∧
      blockAmplitude c t b ≤ Real.sqrt ((fiber c b).card * blockWeight c t b) := by
  rw [amplitude_eq_sum, blockWeight]
  have hsum : 0 ≤ ∑ i ∈ fiber c b, t i := Finset.sum_nonneg fun i _ => ht i
  constructor
  · exact (Real.sqrt_le_iff).2 ⟨hsum, Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => ht i⟩
  · exact (Real.le_sqrt (by positivity) (by positivity)).2 sq_sum_le_card_mul_sum_sq

def crossBlockLoss (ι : Type*) [Fintype ι] {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  2 * (Fintype.card ι : ℝ)⁻¹ * ∑ b, ∑ d, if b < d then a b * a d else 0

private theorem crossBlockLoss_mono (a b : Fin k → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j) :
    crossBlockLoss ι a ≤ crossBlockLoss ι b := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hij
  · exact mul_le_mul (hab i) (hab j) (ha j) ((ha i).trans (hab i))
  · exact le_rfl

private theorem endpoint_profiles [DecidableEq ι] (c : ι → Fin k) (q : Fin k → ℝ)
    (hq : ∀ b, 0 ≤ q b) (he : ∀ b, fiber c b = ∅ → q b = 0) :
    (∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ blockWeight c t = q ∧
      blockAmplitude c t = fun b => Real.sqrt (q b)) ∧
    (∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ blockWeight c t = q ∧
      blockAmplitude c t = fun b => Real.sqrt ((fiber c b).card * q b)) := by
  classical
  let pivot (b : Fin k) (h : (fiber c b).Nonempty) : ι := h.choose
  let sparse (i : ι) :=
    if h : (fiber c (c i)).Nonempty then
      if i = pivot (c i) h then Real.sqrt (q (c i)) else 0
    else 0
  let flat (i : ι) := Real.sqrt (q (c i) / (fiber c (c i)).card)
  have hc {i : ι} {b : Fin k} (hi : i ∈ fiber c b) : c i = b := by
    simpa [fiber] using hi
  have sparse_sum (b : Fin k) (f : ℝ → ℝ) (hzero : f 0 = 0) :
      ∑ i ∈ fiber c b, f (sparse i) = f (Real.sqrt (q b)) := by
    by_cases h : (fiber c b).Nonempty
    · have hmem : pivot b h ∈ fiber c b := h.choose_spec
      have hval (i : ι) (hi : i ∈ fiber c b) :
          sparse i = if i = pivot b h then Real.sqrt (q b) else 0 := by
        simp only [sparse, hc hi, dite_eq_left h]
      calc
        _ = ∑ i ∈ fiber c b, (if i = pivot b h then f (Real.sqrt (q b)) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hval i hi]
          split_ifs <;> simp [hzero]
        _ = _ := by simp [hmem]
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp h
      simp [hempty, he b hempty, hzero]
  have flat_sum (b : Fin k) (f : ℝ → ℝ) :
      ∑ i ∈ fiber c b, f (flat i) =
        (fiber c b).card * f (Real.sqrt (q b / (fiber c b).card)) := by
    calc
      _ = ∑ _i ∈ fiber c b, f (Real.sqrt (q b / (fiber c b).card)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [flat, hc hi]
      _ = _ := by simp [nsmul_eq_mul]
  constructor
  · refine ⟨sparse, fun i => ?_, ?_, ?_⟩
    · dsimp only [sparse]
      split_ifs <;> positivity
    · funext b
      exact (sparse_sum b (· ^ 2) (by norm_num)).trans (Real.sq_sqrt (hq b))
    · funext b
      rw [amplitude_eq_sum]
      exact sparse_sum b id rfl
  · refine ⟨flat, fun i => Real.sqrt_nonneg _, ?_, ?_⟩
    · funext b
      rw [blockWeight, flat_sum b (· ^ 2), Real.sq_sqrt (div_nonneg (hq b) (by positivity))]
      by_cases h : (fiber c b).Nonempty
      · have hr : ((fiber c b).card : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
        field_simp
      · have hempty := Finset.not_nonempty_iff_eq_empty.mp h
        simp [hempty, he b hempty]
    · funext b
      rw [amplitude_eq_sum]
      change (∑ i ∈ fiber c b, id (flat i)) = _
      rw [flat_sum b id]
      dsimp only [id]
      by_cases h : (fiber c b).Nonempty
      · have hr : ((fiber c b).card : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
        apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
        rw [mul_pow, Real.sq_sqrt (div_nonneg (hq b) (by positivity)),
          Real.sq_sqrt (mul_nonneg (by positivity) (hq b))]
        field_simp
      · simp [Finset.not_nonempty_iff_eq_empty.mp h]

variable [DecidableEq ι] [Nonempty ι]

/-- The score set includes arbitrary AURIC continuations with arbitrary joint
terminal flag and residual POVMs. -/
def recordedScores (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (hnorm : ∑ i, t i ^ 2 = 1) : Set ℝ :=
  {s | ∃ descend : Fin k → Protocol ι,
    s ∈ successProbabilitySet (uniformPrior ι) (flaggedPhaseStates c u t hu hnorm descend)}

def auricLoss (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (hnorm : ∑ i, t i ^ 2 = 1) : ℝ :=
  pGuess (uniformPrior ι) (fun j => pureState (phaseVector u t j)
    (phaseVector_norm u t hu hnorm j)) - sSup (recordedScores c u t hu hnorm)

private theorem auricLoss_eq (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (hnorm : ∑ i, t i ^ 2 = 1) (ht : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    auricLoss c u t hu hnorm = crossBlockLoss ι (blockAmplitude c t) := by
  unfold auricLoss recordedScores
  rw [(isGreatest_flaggedPhase c u t hu hnorm ht horth).csSup_eq,
    ← pGuess_pinchedPhase c u t hu hnorm ht horth]
  exact phase_decoding_loss c u t hu hnorm ht horth

/-- At fixed feasible block probabilities, actual AURIC losses fill the entire sharp
closed interval. A block can have zero probability or no coordinates. -/
theorem auricLoss_attainable_eq_Icc
    (c : ι → Fin k) (u : ι → ι → ℂ)
    (hu : ∀ j i, ‖u j i‖ = 1)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0)
    (q : Fin k → ℝ) (hq : ∀ b, 0 ≤ q b) (hs : ∑ b, q b = 1)
    (he : ∀ b, fiber c b = ∅ → q b = 0) :
    {L : ℝ | ∃ (t : ι → ℝ) (hnorm : ∑ i, t i ^ 2 = 1),
      (∀ i, 0 ≤ t i) ∧ blockWeight c t = q ∧ L = auricLoss c u t hu hnorm} =
    Set.Icc (crossBlockLoss ι fun b => Real.sqrt (q b))
      (crossBlockLoss ι fun b => Real.sqrt ((fiber c b).card * q b)) := by
  have hnormalize (t : ι → ℝ) (hw : blockWeight c t = q) : ∑ i, t i ^ 2 = 1 := by
    rw [← sum_blockWeight c t, hw, hs]
  ext L
  constructor
  · rintro ⟨t, hn, ht, hw, rfl⟩
    rw [auricLoss_eq c u t hu hn ht horth]
    have hb (b : Fin k) := amplitude_bounds c t ht b
    simp only [hw] at hb
    exact ⟨crossBlockLoss_mono _ _ (fun _ => Real.sqrt_nonneg _) (fun b => (hb b).1),
      crossBlockLoss_mono _ _ (fun b => (Real.sqrt_nonneg _).trans (hb b).1)
        (fun b => (hb b).2)⟩
  · intro hL
    obtain ⟨⟨t₀, ht₀, hw₀, ha₀⟩, ⟨t₁, ht₁, hw₁, ha₁⟩⟩ := endpoint_profiles c q hq he
    let path (x : ℝ) (i : ι) := Real.sqrt ((1 - x) * t₀ i ^ 2 + x * t₁ i ^ 2)
    have hpath (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : blockWeight c (path x) = q := by
      funext b
      have hx₀ := hx.1
      have hx₁ := sub_nonneg.mpr hx.2
      simp only [blockWeight, path, Real.sq_sqrt (add_nonneg
        (mul_nonneg hx₁ (sq_nonneg _)) (mul_nonneg hx₀ (sq_nonneg _))),
        Finset.sum_add_distrib, ← Finset.mul_sum]
      change (1 - x) * blockWeight c t₀ b + x * blockWeight c t₁ b = q b
      rw [hw₀, hw₁]
      ring
    have hzero : path 0 = t₀ := by
      funext i
      simp [path, Real.sqrt_sq (ht₀ i)]
    have hone : path 1 = t₁ := by
      funext i
      simp [path, Real.sqrt_sq (ht₁ i)]
    let loss (x : ℝ) := crossBlockLoss ι (blockAmplitude c (path x))
    have hcontinuous : Continuous loss := by
      have hamp (b : Fin k) : Continuous fun x => blockAmplitude c (path x) b := by
        simp only [amplitude_eq_sum]
        exact continuous_finsetSum _ fun i _ => by dsimp [path]; fun_prop
      unfold loss crossBlockLoss
      apply continuous_const.mul
      apply continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun d _ => ?_
      split_ifs
      · exact (hamp b).mul (hamp d)
      · exact continuous_const
    have hL' : L ∈ Set.Icc (loss 0) (loss 1) := by
      simpa [loss, hzero, hone, ha₀, ha₁] using hL
    obtain ⟨x, hx, hxL⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      hcontinuous.continuousOn hL'
    have hn := hnormalize _ (hpath x hx)
    have ht (i : ι) : 0 ≤ path x i := Real.sqrt_nonneg _
    exact ⟨path x, hn, ht, hpath x hx, hxL.symm.trans (auricLoss_eq c u _ hu hn ht horth).symm⟩

omit [DecidableEq ι] [Nonempty ι] in
/-- The sparse endpoint depends on the order-one-half Rényi entropy of the block law. -/
theorem lower_endpoint_renyi (q : Fin k → ℝ) (hq : ∀ b, 0 ≤ q b)
    (hs : ∑ b, q b = 1) :
    crossBlockLoss ι (fun b => Real.sqrt (q b)) =
      (Real.exp (2 * Real.log (∑ b, Real.sqrt (q b))) - 1) / Fintype.card ι := by
  let a (b : Fin k) := Real.sqrt (q b)
  have hsq : ∑ b, a b ^ 2 = 1 := by simpa only [a, Real.sq_sqrt (hq _)] using hs
  have hpos : 0 < ∑ b, a b := by
    have hn : 0 ≤ ∑ b, a b := Finset.sum_nonneg fun b _ => Real.sqrt_nonneg _
    refine lt_of_le_of_ne hn ?_
    intro hz
    have hall : ∀ b, a b = 0 := fun b =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Real.sqrt_nonneg (q j))).mp
        hz.symm b (Finset.mem_univ b)
    simp [hall] at hsq
  have hsplit (b d : Fin k) : a b * a d =
      (if b = d then a b ^ 2 else 0) +
        (if b < d then a b * a d else 0) + (if d < b then a d * a b else 0) := by
    rcases lt_trichotomy b d with h | rfl | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · simp [pow_two]
    · simp [h, h.ne.symm, not_lt_of_ge h.le, mul_comm]
  have hexpand : (∑ b, a b) ^ 2 = 1 + 2 * ∑ b, ∑ d, if b < d then a b * a d else 0 := by
    rw [pow_two, Fintype.sum_mul_sum]
    calc
      _ = ∑ b, ∑ d, ((if b = d then a b ^ 2 else 0) +
          (if b < d then a b * a d else 0) + (if d < b then a d * a b else 0)) := by
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => hsplit b d
      _ = _ := by
        simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq, hsq]
        rw [Finset.sum_comm (f := fun b d => if d < b then a d * a b else 0)]
        ring
  change crossBlockLoss ι a = (Real.exp (2 * Real.log (∑ b, a b)) - 1) / _
  rw [two_mul, Real.exp_add, Real.exp_log hpos, ← pow_two, hexpand]
  unfold crossBlockLoss
  ring

end LossRange

private def blockBit (a : Bool) : Fin 2 := if a then 1 else 0

def twoBitPartition (x : Word 2) : Fin 2 := blockBit (x 0)

private def halves (a : ℝ) (sign : Bool) : ℝ :=
  (a + if sign then Real.sqrt (1 - a ^ 2) else -Real.sqrt (1 - a ^ 2)) / 2

private def profile (a b : ℝ) (x : Word 2) : ℝ :=
  halves (if x 0 then b else a) (x 1)

private theorem halves_nonneg {a : ℝ} (ha : 0 ≤ a) (hl : 1 / 2 ≤ a ^ 2)
    (s : Bool) : 0 ≤ halves a s := by
  have h := Real.sqrt_le_iff.mpr ⟨ha, show 1 - a ^ 2 ≤ a ^ 2 by linarith⟩
  cases s <;> simp [halves] <;> linarith [Real.sqrt_nonneg (1 - a ^ 2)]

private theorem halves_sum (a : ℝ) : halves a false + halves a true = a := by
  simp [halves]
  ring

private theorem halves_sq {a : ℝ} (ha : a ^ 2 ≤ 1) :
    halves a false ^ 2 + halves a true ^ 2 = 1 / 2 := by
  simp only [halves, Bool.false_eq_true, ↓reduceIte]
  nlinarith [Real.sq_sqrt (sub_nonneg.mpr ha)]

private theorem word_sum {R : Type*} [AddCommMonoid R] (f : Bool → Bool → R) :
    (∑ x : Word 2, f (x 0) (x 1)) = (f false false + f false true) +
      (f true false + f true true) := by
  calc
    _ = ∑ x : Bool × Bool, f x.1 x.2 :=
      Fintype.sum_equiv (finTwoArrowEquiv Bool) _ _ (fun _ => rfl)
    _ = _ := by simp only [Fintype.sum_prod_type, sum_bool]

private theorem profile_weight {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) :
    blockWeight twoBitPartition (profile a b) = fun _ => 1 / 2 := by
  funext d
  rw [blockWeight, fiber, Finset.sum_filter]
  unfold twoBitPartition profile
  rw [word_sum (fun x y => if blockBit x = d then halves (if x then b else a) y ^ 2 else 0)]
  fin_cases d
  · simpa [blockBit] using halves_sq ha
  · simpa [blockBit] using halves_sq hb

private theorem profile_amplitude (a b : ℝ) :
    blockAmplitude twoBitPartition (profile a b) 0 = a ∧ blockAmplitude twoBitPartition (profile a b) 1 = b := by
  constructor
  · unfold blockAmplitude maskedProfile twoBitPartition profile
    rw [word_sum (fun x y => if blockBit x = 0 then halves (if x then b else a) y else 0)]
    simp [blockBit, halves_sum]
  · unfold blockAmplitude maskedProfile twoBitPartition profile
    rw [word_sum (fun x y => if blockBit x = 1 then halves (if x then b else a) y else 0)]
    simp [blockBit, halves_sum]

private theorem profile_total (a b : ℝ) :
    (∑ x, profile a b x) = a + b := by
  unfold profile
  rw [word_sum (fun x y => halves (if x then b else a) y)]
  simp [halves_sum]

private theorem profile_norm {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) :
    ∑ x, profile a b x ^ 2 = 1 := by
  rw [← sum_blockWeight twoBitPartition, profile_weight ha hb]
  norm_num [Fin.sum_univ_two]

private theorem example_entropy (t : Word 2 → ℝ) (hn : ∑ i, t i ^ 2 = 1)
    (ht : blockWeight twoBitPartition t = fun _ => 1 / 2) (j : Word 2) :
    vonNeumannEntropy (pinchedPhaseStates twoBitPartition walsh t walsh_norm hn j) = Real.log 2 := by
  have h := phase_pinching_entropy_gain twoBitPartition walsh t walsh_norm hn j
  rw [pure_entropy, sub_zero, ht] at h
  rw [h, shannonEntropy, Fin.sum_univ_two, Real.negMulLog, one_div, Real.log_inv]
  ring

/-- Equal block law, entropy, and coherent optimum coexist with a strict increase in
the actual sharp recorded score. The two block sums change from (7/8, 7/8) to
(15/16, 13/16), corresponding to a displacement of 1/16. -/
theorem equal_entropy_coherent_different_recorded :
    ∃ (t₀ t₁ : Word 2 → ℝ) (hn₀ : ∑ i, t₀ i ^ 2 = 1) (hn₁ : ∑ i, t₁ i ^ 2 = 1),
      (∀ i, 0 ≤ t₀ i) ∧ (∀ i, 0 ≤ t₁ i) ∧
      (∀ b, (fiber twoBitPartition b).card = 2) ∧
      blockWeight twoBitPartition t₀ = (fun _ => 1 / 2) ∧ blockWeight twoBitPartition t₁ = (fun _ => 1 / 2) ∧
      (∀ j, vonNeumannEntropy (pinchedPhaseStates twoBitPartition walsh t₀ walsh_norm hn₀ j) = Real.log 2 ∧
        vonNeumannEntropy (pinchedPhaseStates twoBitPartition walsh t₁ walsh_norm hn₁ j) = Real.log 2) ∧
      IsGreatest (successProbabilitySet (uniformPrior (Word 2)) (fun j =>
        pureState (phaseVector walsh t₀ j) (phaseVector_norm walsh t₀ walsh_norm hn₀ j))) (49 / 64) ∧
      IsGreatest (successProbabilitySet (uniformPrior (Word 2)) (fun j =>
        pureState (phaseVector walsh t₁ j) (phaseVector_norm walsh t₁ walsh_norm hn₁ j))) (49 / 64) ∧
      IsGreatest (recordedScores twoBitPartition walsh t₀ walsh_norm hn₀) (49 / 128) ∧
      IsGreatest (recordedScores twoBitPartition walsh t₁ walsh_norm hn₁) (197 / 512) := by
  let t₀ := profile (7 / 8) (7 / 8)
  let t₁ := profile (15 / 16) (13 / 16)
  have hn₀ : ∑ i, t₀ i ^ 2 = 1 := profile_norm (by norm_num) (by norm_num)
  have hn₁ : ∑ i, t₁ i ^ 2 = 1 := profile_norm (by norm_num) (by norm_num)
  have hp₀ : ∀ i, 0 ≤ t₀ i := fun i => by
    simp only [t₀, profile, ite_self]
    exact halves_nonneg (by norm_num) (by norm_num) _
  have hp₁ : ∀ i, 0 ≤ t₁ i := fun i => by
    dsimp [t₁, profile]
    split_ifs <;> exact halves_nonneg (by norm_num) (by norm_num) _
  have hw₀ : blockWeight twoBitPartition t₀ = fun _ => 1 / 2 := profile_weight (by norm_num) (by norm_num)
  have hw₁ : blockWeight twoBitPartition t₁ = fun _ => 1 / 2 := profile_weight (by norm_num) (by norm_num)
  refine ⟨t₀, t₁, hn₀, hn₁, hp₀, hp₁, ?_, hw₀, hw₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rw [Finset.card_eq_sum_ones, fiber, Finset.sum_filter]
    unfold twoBitPartition
    rw [word_sum (fun x _ => if blockBit x = d then (1 : ℕ) else 0)]
    fin_cases d <;> norm_num [blockBit]
  · exact fun j => ⟨example_entropy t₀ hn₀ hw₀ j, example_entropy t₁ hn₁ hw₁ j⟩
  · convert isGreatest_phase walsh t₀ walsh_norm walsh_orthogonal hp₀ hn₀ using 1
    norm_num [t₀, profile_total, Fintype.card_fun]
  · convert isGreatest_phase walsh t₁ walsh_norm walsh_orthogonal hp₁ hn₁ using 1
    norm_num [t₁, profile_total, Fintype.card_fun]
  · have ho : pinchedOptimum twoBitPartition t₀ = 49 / 128 := by
      obtain ⟨h₀, h₁⟩ := profile_amplitude (7 / 8) (7 / 8)
      norm_num [t₀, pinchedOptimum, Fin.sum_univ_two, Fintype.card_fun, h₀, h₁]
    rw [← ho]
    exact isGreatest_flaggedPhase twoBitPartition walsh t₀ walsh_norm hn₀ hp₀ walsh_orthogonal
  · have ho : pinchedOptimum twoBitPartition t₁ = 197 / 512 := by
      obtain ⟨h₀, h₁⟩ := profile_amplitude (15 / 16) (13 / 16)
      norm_num [t₁, pinchedOptimum, Fin.sum_univ_two, Fintype.card_fun, h₀, h₁]
    rw [← ho]
    exact isGreatest_flaggedPhase twoBitPartition walsh t₁ walsh_norm hn₁ hp₁ walsh_orthogonal

end D5.S3.Quantum.Measurement.Auric.CoordinatePinchingLoss
