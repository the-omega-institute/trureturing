/- GID: D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary
   mirror-E: none(waiver:pure-mathematical-argument)
   anchors: []
   utility: none
   digest: Sharp two-pair physical rank bound, unit-speed attainment, and finite-family nonattainment. -/

import D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
import D5.S3.ConceptDynamics.ObservationTopology.TwoHarmonicRotationObstruction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp Filter Set
open scoped BigOperators Classical Topology Matrix.Norms.L2Operator

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.FiniteRankBoundary

open PairedDelayGeometry TwoRowSpectralNorm FinitePairedKernel
open SixDimensionalSharpGeometry
open D5.S3.ConceptDynamics.ObservationTopology.TwoHarmonicRotationObstruction

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private theorem energy_pos (k : ι → ℕ) (a : ι → ℝ)
    (hinj : ∀ φ ψ, pairedSensor k a φ = pairedSensor k a ψ →
      circleState φ = circleState ψ)
    (φ ψ : ℝ) (hne : circleState φ ≠ circleState ψ) :
    0 < rowEnergy k a (φ - ψ) := by
  rw [← paired_chord_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hne (hinj φ ψ h))))

private theorem rank_values_bddBelow (k : ι → ℕ) (a : ι → ℝ) (θ : ℝ) :
    BddBelow (stableRankValues k a θ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨φ, ψ, _, rfl⟩
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem physical_turn_distinct (d : ℝ) (hd : 0 < d) (hd' : d < 2 * Real.pi) :
    circleState d ≠ circleState 0 := by
  intro he
  have h := circle_chord_norm_sq d 0
  rw [he, sub_self, norm_zero] at h
  simp only [sub_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < d / 2)
    (by linarith : d / 2 < Real.pi)
  nlinarith [sq_pos_of_pos hs]

private theorem rank_le_of_correlation (k : ι → ℕ) (a : ι → ℝ)
    (hinj : ∀ φ ψ, pairedSensor k a φ = pairedSensor k a ψ →
      circleState φ = circleState ψ)
    (φ ψ : ℝ) (hne : circleState φ ≠ circleState ψ)
    (hc : rowEnergy k a (φ - ψ) / 2 ≤
      |rowCorrelation k a (Real.pi / 6) (φ - ψ)|) :
    sensorStableRank k a (Real.pi / 6) ≤ 4 / 3 := by
  have hA := energy_pos k a hinj φ ψ hne
  have hq : (1 / 2 : ℝ) ≤
      |rowCorrelation k a (Real.pi / 6) (φ - ψ)| / rowEnergy k a (φ - ψ) :=
    (le_div_iff₀ hA).mpr (by simpa [div_eq_mul_inv, mul_comm] using hc)
  have h := csInf_le (rank_values_bddBelow k a (Real.pi / 6))
    (show matrixStableRank (delayMatrix k a (Real.pi / 6) φ -
        delayMatrix k a (Real.pi / 6) ψ) ∈ stableRankValues k a (Real.pi / 6)
      from ⟨φ, ψ, hne, rfl⟩)
  apply h.trans
  rw [paired_pointwise_stable_rank k a _ φ ψ hA]
  apply (div_le_iff₀ (by linarith : 0 < 1 +
    |rowCorrelation k a (Real.pi / 6) (φ - ψ)| / rowEnergy k a (φ - ψ))).mpr
  linarith

private theorem isolated_pair_bound (k : ι → ℕ) (a : ι → ℝ)
    (hinj : ∀ φ ψ, pairedSensor k a φ = pairedSensor k a ψ →
      circleState φ = circleState ψ)
    (i j : ι) (hij : i ≠ j) (hall : Finset.univ = {i, j})
    (hj : 1 < k j) (hi : (1 / 2 : ℝ) ≤ |Real.cos ((k i : ℝ) * (Real.pi / 6))|) :
    sensorStableRank k a (Real.pi / 6) ≤ 4 / 3 := by
  let d : ℝ := 2 * Real.pi / (k j : ℝ)
  have hjR : (1 : ℝ) < (k j : ℝ) := by exact_mod_cast hj
  have hj0 : (k j : ℝ) ≠ 0 := by linarith
  have hd : 0 < d := div_pos (by positivity) (by linarith)
  have hd' : d < 2 * Real.pi := by
    apply (div_lt_iff₀ (by linarith : 0 < (k j : ℝ))).mpr
    have hm := mul_pos (show 0 < 2 * Real.pi by positivity) (sub_pos.mpr hjR)
    nlinarith
  have hne := physical_turn_distinct d hd hd'
  have hz : Real.sin ((k j : ℝ) * d / 2) = 0 := by
    have he : (k j : ℝ) * d / 2 = Real.pi := by
      dsimp [d]
      field_simp [hj0]
      <;> ring
    rw [he, Real.sin_pi]
  have he : rowCorrelation k a (Real.pi / 6) d =
      Real.cos ((k i : ℝ) * (Real.pi / 6)) * rowEnergy k a d := by
    simp only [rowCorrelation, rowEnergy, hall, Finset.sum_pair hij, hz, zero_pow,
      mul_zero, add_zero]
    ring
  apply rank_le_of_correlation k a hinj d 0 hne
  simp only [sub_zero]
  have hA : 0 < rowEnergy k a d := by simpa using energy_pos k a hinj d 0 hne
  rw [he, abs_mul, abs_of_pos hA]
  simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hi hA.le

/-- The infimum uses every pair of distinct physical Circle states, with the
actual Frobenius and Euclidean operator norms from `sensorStableRank`. -/
theorem at_most_two_pairs (k : ι → ℕ) (a : ι → ℝ)
    (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i) (hk_inj : Function.Injective k)
    (hinj : ∀ φ ψ, pairedSensor k a φ = pairedSensor k a ψ →
      circleState φ = circleState ψ)
    (hcard : Fintype.card ι ≤ 2) :
    sensorStableRank k a (Real.pi / 6) ≤ 4 / 3 := by
  classical
  have hg := (finite_paired_injective_iff_gcd_one k a hk ha).mp hinj
  have hcos : (1 / 2 : ℝ) ≤ |Real.cos (Real.pi / 6)| := by
    rw [Real.cos_pi_div_six, abs_of_nonneg (by positivity)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  by_cases hsmall : Fintype.card ι ≤ 1
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have hall : Finset.univ = ({i} : Finset ι) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Finset.card_le_one.mp hsmall j (Finset.mem_univ j) i (Finset.mem_univ i)
    have hi : k i = 1 := by simpa [hall] using hg
    have he (d : ℝ) : rowCorrelation k a (Real.pi / 6) d =
        Real.cos (Real.pi / 6) * rowEnergy k a d := by
      simp only [rowCorrelation, rowEnergy, hall, Finset.sum_singleton, hi,
        Nat.cast_one, one_mul]
      ring
    apply rank_le_of_correlation k a hinj (2 * Real.pi / 3) 0 separated_third_turn
    simp only [sub_zero]
    have hA : 0 < rowEnergy k a (2 * Real.pi / 3) := by
      simpa using energy_pos k a hinj _ _ separated_third_turn
    rw [he, abs_mul, abs_of_pos hA]
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hcos hA.le
  · have hc : (Finset.univ : Finset ι).card = 2 := by
      change Fintype.card ι = 2
      omega
    obtain ⟨i, j, hij, hall⟩ := Finset.card_eq_two.mp hc
    have hcop : Nat.Coprime (k i) (k j) := by
      simpa [hall, Finset.gcd_insert, Finset.gcd_singleton, gcd_eq_nat_gcd,
        Nat.coprime_iff_gcd_eq_one] using hg
    by_cases hi : k i = 1
    · have hj : 1 < k j := by
        have hne : k i ≠ k j := fun h => hij (hk_inj h)
        have hp := hk j
        omega
      apply isolated_pair_bound k a hinj i j hij hall hj
      simpa [hi] using hcos
    · by_cases hj : k j = 1
      · apply isolated_pair_bound k a hinj j i hij.symm
          (by simpa [Finset.pair_comm] using hall) (by have hp := hk i; omega)
        simpa [hj] using hcos
      · have hob := coprime_two_frequency_cosine_obstruction (k i) (k j) hcop
        rcases le_max_iff.mp hob with hi' | hj'
        · exact isolated_pair_bound k a hinj i j hij hall (by have hp := hk j; omega) hi'
        · exact isolated_pair_bound k a hinj j i hij.symm
            (by simpa [Finset.pair_comm] using hall) (by have hp := hk i; omega) hj'

private theorem two_three_rank (a : Fin 2 → ℝ) (ha : ∀ i, 0 < a i) :
    (∀ φ ψ, pairedSensor ![2, 3] a φ = pairedSensor ![2, 3] a ψ →
      circleState φ = circleState ψ) ∧
    sensorStableRank ![2, 3] a (Real.pi / 6) = 4 / 3 := by
  have hk : ∀ i : Fin 2, 0 < (![2, 3] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> norm_num
  have hg : Finset.univ.gcd (![2, 3] : Fin 2 → ℕ) = 1 := by decide
  have hi := (finite_paired_injective_iff_gcd_one ![2, 3] a hk ha).mpr hg
  refine ⟨hi, le_antisymm (at_most_two_pairs ![2, 3] a hk ha ?_ hi (by simp)) ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · apply le_csInf (show (stableRankValues ![2, 3] a (Real.pi / 6)).Nonempty from
        ⟨_, 2 * Real.pi / 3, 0, separated_third_turn, rfl⟩)
    rintro r ⟨φ, ψ, hne, rfl⟩
    have hA := energy_pos ![2, 3] a hi φ ψ hne
    have hB : |rowCorrelation ![2, 3] a (Real.pi / 6) (φ - ψ)| ≤
        rowEnergy ![2, 3] a (φ - ψ) / 2 := by
      have hc2 : Real.cos ((2 : ℝ) * (Real.pi / 6)) = 1 / 2 := by
        rw [show (2 : ℝ) * (Real.pi / 6) = Real.pi / 3 by ring, Real.cos_pi_div_three]
      have hc3 : Real.cos ((3 : ℝ) * (Real.pi / 6)) = 0 := by
        rw [show (3 : ℝ) * (Real.pi / 6) = Real.pi / 2 by ring, Real.cos_pi_div_two]
      simp only [rowCorrelation, rowEnergy, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Nat.cast_ofNat, hc2, hc3, mul_zero, zero_mul, add_zero]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg (a 1)) (sq_nonneg (Real.sin (3 * (φ - ψ) / 2)))]
    rw [paired_pointwise_stable_rank ![2, 3] a _ φ ψ hA]
    have hq : |rowCorrelation ![2, 3] a (Real.pi / 6) (φ - ψ)| /
        rowEnergy ![2, 3] a (φ - ψ) ≤ 1 / 2 :=
      (div_le_iff₀ hA).mpr (by simpa [div_eq_mul_inv, mul_comm] using hB)
    apply (le_div_iff₀ (add_pos_of_pos_of_nonneg (by norm_num)
      (div_nonneg (abs_nonneg _) hA.le))).mpr
    linarith

/-- Arbitrary positive amplitudes at frequencies two and three attain the bound.
Dividing both amplitudes by their derivative budget gives unit speed and retains
the same exact rank. -/
theorem two_three_attainment_and_normalization (a : Fin 2 → ℝ) (ha : ∀ i, 0 < a i) :
    (∀ φ ψ, pairedSensor ![2, 3] a φ = pairedSensor ![2, 3] a ψ →
      circleState φ = circleState ψ) ∧
    sensorStableRank ![2, 3] a (Real.pi / 6) = 4 / 3 ∧
    ∃ b : Fin 2 → ℝ, (∀ i, b i = a i / Real.sqrt (4 * a 0 ^ 2 + 9 * a 1 ^ 2)) ∧
      (∀ i, 0 < b i) ∧
      (∀ φ ψ, pairedSensor ![2, 3] b φ = pairedSensor ![2, 3] b ψ →
        circleState φ = circleState ψ) ∧
      sensorStableRank ![2, 3] b (Real.pi / 6) = 4 / 3 ∧
      ∀ φ, ‖deriv (pairedSensor ![2, 3] b) φ‖ = 1 := by
  obtain ⟨hi, hr⟩ := two_three_rank a ha
  let Z : ℝ := 4 * a 0 ^ 2 + 9 * a 1 ^ 2
  have hZ : 0 < Z := by
    dsimp [Z]
    exact add_pos
      (mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_pos (ha 0)))
      (mul_pos (by norm_num : (0 : ℝ) < 9) (sq_pos_of_pos (ha 1)))
  let b : Fin 2 → ℝ := fun i => a i / Real.sqrt Z
  have hb : ∀ i, 0 < b i := fun i => div_pos (ha i) (Real.sqrt_pos.mpr hZ)
  obtain ⟨hib, hrb⟩ := two_three_rank b hb
  refine ⟨hi, hr, b, fun _ => rfl, hb, hib, hrb, ?_⟩
  intro φ
  let k : Fin 2 → ℕ := ![2, 3]
  let v : EuclideanSpace ℝ (Fin 2 × Fin 2) := toLp 2 (fun p => b p.1 *
    if p.2 = 0 then -Real.sin ((k p.1 : ℝ) * φ) * (k p.1 : ℝ)
    else Real.cos ((k p.1 : ℝ) * φ) * (k p.1 : ℝ))
  have hd : HasDerivAt (pairedSensor k b) v φ := by
    let f : ℝ → (Fin 2 × Fin 2 → ℝ) := fun x p => b p.1 *
      if p.2 = 0 then Real.cos ((k p.1 : ℝ) * x) else Real.sin ((k p.1 : ℝ) * x)
    have hp : HasDerivAt f (ofLp v) φ := by
      apply hasDerivAt_pi.mpr
      intro p
      have hlinear : HasDerivAt (fun x : ℝ => (k p.1 : ℝ) * x) (k p.1 : ℝ) φ := by
        simpa using (hasDerivAt_id φ).const_mul (k p.1 : ℝ)
      by_cases hc : p.2 = 0
      · simpa [f, v, hc] using hlinear.cos.const_mul (b p.1)
      · simpa [f, v, hc] using hlinear.sin.const_mul (b p.1)
    exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (f φ)).comp_hasDerivAt φ hp
  change ‖deriv (pairedSensor k b) φ‖ = 1
  rw [hd.deriv]
  have hs : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    have hp (i : Fin 2) : ∑ j : Fin 2, v (i, j) ^ 2 = b i ^ 2 * (k i : ℝ) ^ 2 := by
      simp only [Fin.sum_univ_two, v, PiLp.toLp_apply]
      norm_num
      linear_combination (b i ^ 2 * (k i : ℝ) ^ 2) * Real.sin_sq_add_cos_sq ((k i : ℝ) * φ)
    simp_rw [hp]
    norm_num [Fin.sum_univ_two, k, b, div_pow, Real.sq_sqrt hZ.le]
    field_simp [hZ.ne']
    dsimp [Z]
    ring
  nlinarith [norm_nonneg v]

private theorem cosine_period_average (n : ℕ) (hn : 0 < n) :
    (∫ d : ℝ in 0..(2 * Real.pi), Real.cos ((n : ℝ) * d)) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [intervalIntegral.integral_comp_mul_left _ hnR, integral_cos]
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    have he : (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [he, Real.sin_nat_mul_pi]
  simp [hs]

private theorem zero_correlation_forces_cosines (k : ι → ℕ) (a : ι → ℝ)
    (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i)
    (hB : ∀ d, rowCorrelation k a (Real.pi / 6) d = 0) :
    ∀ i, Real.cos ((k i : ℝ) * (Real.pi / 6)) = 0 := by
  let c : ι → ℝ := fun i => Real.cos ((k i : ℝ) * (Real.pi / 6))
  let w : ι → ℝ := fun i => a i ^ 2
  have hhalf (x : ℝ) : 2 * Real.sin (x / 2) ^ 2 = 1 - Real.cos x := by
    have h := Real.cos_two_mul (x / 2)
    have hs := Real.sin_sq_add_cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    nlinarith
  have hsum (d : ℝ) : (∑ i, w i * c i) = ∑ i, w i * c i * Real.cos ((k i : ℝ) * d) := by
    have h := hB d
    have he : rowCorrelation k a (Real.pi / 6) d =
        2 * ((∑ i, w i * c i) - ∑ i, w i * c i * Real.cos ((k i : ℝ) * d)) := by
      unfold rowCorrelation
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [w, c]
      linear_combination
        (2 * a i ^ 2 * Real.cos ((k i : ℝ) * (Real.pi / 6))) * hhalf ((k i : ℝ) * d)
    rw [he] at h
    linarith
  have havg : ∑ i, w i * c i = 0 := by
    have he := congrArg (fun f : ℝ → ℝ => ∫ d in 0..(2 * Real.pi), f d)
      (funext hsum)
    have hint : ∀ i ∈ (Finset.univ : Finset ι),
        IntervalIntegrable (fun d : ℝ => w i * c i * Real.cos ((k i : ℝ) * d))
          MeasureTheory.volume 0 (2 * Real.pi) := by
      intro i _
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_const, intervalIntegral.integral_finsetSum hint] at he
    have hterm (i : ι) : (∫ d : ℝ in 0..(2 * Real.pi),
        w i * c i * Real.cos ((k i : ℝ) * d)) = 0 := by
      rw [intervalIntegral.integral_const_mul, cosine_period_average (k i) (hk i), mul_zero]
    simp only [hterm, Finset.sum_const_zero, sub_zero, smul_eq_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (by positivity)
  have hs : ∑ i, w i * c i ^ 2 = 0 := by
    have h := hsum (Real.pi / 6)
    rw [havg] at h
    simpa only [c, pow_two, mul_assoc] using h.symm
  intro i
  have hw : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ w j * c j ^ 2 := by
    intro j _
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hi : w i * c i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hw).mp hs i (Finset.mem_univ i)
  have hwpos : 0 < w i := sq_pos_of_pos (ha i)
  have hz : c i ^ 2 = 0 := (mul_eq_zero.mp hi).resolve_left hwpos.ne'
  exact sq_eq_zero_iff.mp hz

/-- No finite positive injective physical paired sensor attains two. The proof
uses a period average and the positive cosine-square sum, then exhibits the
forbidden third-turn physical alias. -/
theorem finite_rank_strict (k : ι → ℕ) (a : ι → ℝ)
    (hk : ∀ i, 0 < k i) (ha : ∀ i, 0 < a i) (_hk_inj : Function.Injective k)
    (hinj : ∀ φ ψ, pairedSensor k a φ = pairedSensor k a ψ →
      circleState φ = circleState ψ) :
    sensorStableRank k a (Real.pi / 6) < 2 := by
  by_contra hnot
  have hR : 2 ≤ sensorStableRank k a (Real.pi / 6) := le_of_not_gt hnot
  have hzero : ∀ φ ψ, circleState φ ≠ circleState ψ →
      rowCorrelation k a (Real.pi / 6) (φ - ψ) = 0 := by
    intro φ ψ hne
    have hA := energy_pos k a hinj φ ψ hne
    have hp := hR.trans (csInf_le (rank_values_bddBelow k a (Real.pi / 6))
      (show matrixStableRank (delayMatrix k a (Real.pi / 6) φ -
          delayMatrix k a (Real.pi / 6) ψ) ∈ stableRankValues k a (Real.pi / 6)
        from ⟨φ, ψ, hne, rfl⟩))
    rw [paired_pointwise_stable_rank k a _ φ ψ hA] at hp
    have hq0 : 0 ≤ |rowCorrelation k a (Real.pi / 6) (φ - ψ)| /
        rowEnergy k a (φ - ψ) := div_nonneg (abs_nonneg _) hA.le
    have hq := (le_div_iff₀ (by linarith : 0 < 1 +
      |rowCorrelation k a (Real.pi / 6) (φ - ψ)| / rowEnergy k a (φ - ψ))).mp hp
    have hz : |rowCorrelation k a (Real.pi / 6) (φ - ψ)| /
        rowEnergy k a (φ - ψ) = 0 := by linarith
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hA.ne')
  have hB : ∀ d, rowCorrelation k a (Real.pi / 6) d = 0 := by
    intro d
    by_cases hd : circleState d ≠ circleState 0
    · simpa using hzero d 0 hd
    · have he : circleState d = circleState 0 := not_ne_iff.mp hd
      have hs := circle_chord_norm_sq d 0
      rw [he, sub_self, norm_zero] at hs
      simp only [sub_zero, zero_pow (by norm_num : 2 ≠ 0)] at hs
      have hz : Real.sin (d / 2) = 0 := by nlinarith [sq_nonneg (Real.sin (d / 2))]
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
      have hkz (i : ι) : Real.sin ((k i : ℝ) * d / 2) = 0 := by
        have heq : (k i : ℝ) * d / 2 = ((k i : ℤ) * n : ℤ) * Real.pi := by
          push_cast
          calc
            (k i : ℝ) * d / 2 = (k i : ℝ) * (d / 2) := by ring
            _ = (k i : ℝ) * ((n : ℝ) * Real.pi) := by rw [hn]
            _ = _ := by ring
        rw [heq, Real.sin_int_mul_pi]
      simp [rowCorrelation, hkz]
  have hc := zero_correlation_forces_cosines k a hk ha hB
  have he : rowEnergy k a (2 * Real.pi / 3) = 0 := by
    have hz (i : ι) : Real.sin ((k i : ℝ) * (2 * Real.pi / 3) / 2) = 0 := by
      rw [show (k i : ℝ) * (2 * Real.pi / 3) / 2 =
        2 * ((k i : ℝ) * (Real.pi / 6)) by ring, Real.sin_two_mul, hc i, mul_zero]
    simp [rowEnergy, hz]
  have hpos : 0 < rowEnergy k a (2 * Real.pi / 3) := by
    simpa using energy_pos k a hinj _ _ separated_third_turn
  linarith

/-- Among the original finite positive distinct-frequency paired families,
three is the least pair count whose injective physical sensors can have rank
arbitrarily close to two. The witness is the actual six-coordinate family. -/
theorem minimum_pair_count :
    IsLeast {n : ℕ | ∀ r : ℝ, r < 2 → ∃ (k : Fin n → ℕ) (a : Fin n → ℝ),
      (∀ i, 0 < k i) ∧ (∀ i, 0 < a i) ∧ Function.Injective k ∧
      (∀ φ ψ, pairedSensor k a φ = pairedSensor k a ψ → circleState φ = circleState ψ) ∧
      r < sensorStableRank k a (Real.pi / 6)} 3 ∧
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 × Fin 2)) = 6 := by
  constructor
  · have hk : ∀ i, 0 < frequencies i := by intro i; fin_cases i <;> norm_num [frequencies]
    have hki : Function.Injective frequencies := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [frequencies]
    have hg : Finset.univ.gcd frequencies = 1 := by decide
    have hlimit : Tendsto actualRank (𝓝[>] (0 : ℝ)) (𝓝 2) := by
      have hs : Tendsto (fun ε : ℝ => Real.sqrt (ε / 2)) (𝓝[>] 0) (𝓝 0) := by
        have hc : ContinuousAt (fun ε : ℝ => Real.sqrt (ε / 2)) 0 := by fun_prop
        simpa using hc.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
      have ht := actual_rank_defect_scaled_limit.mul hs
      simp only [mul_zero] at ht
      have he : Tendsto (fun ε : ℝ => 2 - actualRank ε) (𝓝[>] 0) (𝓝 0) := by
        apply ht.congr'
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr (div_pos hε (by norm_num))).ne'
      have ht' := (tendsto_const_nhds (x := (2 : ℝ))).sub he
      simpa using ht'
    constructor
    · intro r hr
      have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 / 2 ∧ r < actualRank ε := by
        have hu : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 2 :=
          (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
        filter_upwards [self_mem_nhdsWithin, hu, hlimit.eventually_const_lt hr] with ε hε hu hl
        exact ⟨hε, hu.le, hl⟩
      obtain ⟨ε, hε, _, hrε⟩ := hp.exists
      have ha : ∀ i, 0 < amplitudes ε i := by
        intro i
        have hZ := normalization_pos ε hε
        fin_cases i
        · change 0 < Real.sqrt ε / Real.sqrt (normalization ε)
          exact div_pos (Real.sqrt_pos.mpr hε) (Real.sqrt_pos.mpr hZ)
        · change 0 < 1 / Real.sqrt (normalization ε)
          exact div_pos (by norm_num : (0 : ℝ) < 1) (Real.sqrt_pos.mpr hZ)
        · change 0 < Real.sqrt ε / Real.sqrt (normalization ε)
          exact div_pos (Real.sqrt_pos.mpr hε) (Real.sqrt_pos.mpr hZ)
      refine ⟨frequencies, amplitudes ε, hk, ha, hki,
        (finite_paired_injective_iff_gcd_one frequencies (amplitudes ε) hk ha).mpr hg, ?_⟩
      exact hrε
    · intro n hn
      by_contra hnot
      have hn2 : n ≤ 2 := by omega
      obtain ⟨k, a, hk, ha, hki, hinj, hr⟩ := hn (3 / 2) (by norm_num)
      by_cases hn0 : n = 0
      · subst n
        have he : pairedSensor k a (2 * Real.pi / 3) = pairedSensor k a 0 := by
          ext p
          exact Fin.elim0 p.1
        exact separated_third_turn (hinj _ _ he)
      · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
        have hb := at_most_two_pairs k a hk ha hki hinj (by simpa using hn2)
        linarith
  · simp

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.FiniteRankBoundary
