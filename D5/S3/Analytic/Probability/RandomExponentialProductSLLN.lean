/- GID: D5/S3/Analytic/Probability/RandomExponentialProductSLLN
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/RandomExponentialProductSLLN
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bounded iid operator exponentials satisfy the strong law on every Banach space. -/

import D5.S3.Quantum.AURICOmega.ExponentialTail
import D5.S3.Observer.Linear.ExactTaylorObservationRemainder
import Mathlib.Probability.StrongLaw

/-! Products of bounded iid operator exponentials and their deterministic Abel estimate. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace D5.S3.Analytic.Probability.RandomExponentialProductSLLN

/-- The factors are multiplied from left to right in increasing index order. -/
def randomProduct {𝕜 e α : Type} [RCLike 𝕜] [NormedAddCommGroup e]
    [NormedSpace 𝕜 e] (a : ℕ → α → e →L[𝕜] e) (n : ℕ) (t : ℝ) (ω : α) :
    e →L[𝕜] e :=
  (List.ofFn fun i : Fin n => NormedSpace.exp (((t / n : ℝ) : 𝕜) • a i ω)).prod

/-- Almost sure convergence in the strong operator topology, uniformly on compact time intervals. -/
def claim : Prop :=
  ∀ (𝕜 e α : Type) [RCLike 𝕜] [NormedAddCommGroup e] [NormedSpace 𝕜 e]
    [CompleteSpace e] [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ],
    letI := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
    letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
    ∀ (a : ℕ → α → e →L[𝕜] e),
      (∀ i, AEStronglyMeasurable (a i) μ) →
      Pairwise (fun i j => IndepFun (a i) (a j) μ) →
      (∀ i, IdentDistrib (a i) (a 0) μ μ) →
      ∀ (m : ℝ), (∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m) →
      ∀ (x : e) (t : ℝ), 0 ≤ t → ∀ᵐ ω ∂μ,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
          ‖(randomProduct a n s ω -
            NormedSpace.exp (((s : ℝ) : 𝕜) • ∫ z, a 0 z ∂μ)) x‖ < ε

private def eulerProduct {e : Type*} [Ring e] [Module ℝ e]
    (a : ℕ → e) (h : ℝ) (n : ℕ) : e :=
  (List.ofFn fun i : Fin n => 1 + h • a i).prod

private def centeredSum {e : Type*} [AddCommGroup e] (a : ℕ → e) (b : e) (n : ℕ) : e :=
  ∑ i ∈ Finset.range n, (a i - b)

private lemma ordered_norm {e : Type*} [NormedRing e] [NormOneClass e]
    (a : ℕ → e) (l : ℝ) (n : ℕ) (ha : ∀ i < n, ‖a i‖ ≤ l) :
    ‖(List.ofFn fun i : Fin n => a i).prod‖ ≤ l ^ n := by
  refine (List.norm_prod_le _).trans ?_
  have hb := List.prod_map_le_prod_map₀
    (s := List.ofFn fun i : Fin n => a i) (fun z : e => ‖z‖) (fun _ => l)
    (fun z _ => norm_nonneg z) (by
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact ha i i.isLt)
  simpa only [List.map_const', List.prod_replicate, List.length_ofFn] using hb

private lemma euler_succ {e : Type*} [Ring e] [Module ℝ e]
    (a : ℕ → e) (h : ℝ) (n : ℕ) :
    eulerProduct a h (n + 1) = eulerProduct a h n * (1 + h • a n) := by
  change (List.ofFn fun i : Fin (n + 1) => 1 + h • a i).prod = _
  rw [List.ofFn_succ', List.prod_concat]
  rfl

private lemma euler_norm {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] (a : ℕ → e) (m h : ℝ) (n : ℕ)
    (hh : 0 ≤ h) (ha : ∀ i < n, ‖a i‖ ≤ m) :
    ‖eulerProduct a h n‖ ≤ (1 + h * m) ^ n := by
  change ‖(List.ofFn fun i : Fin n => 1 + h • a i).prod‖ ≤ _
  apply ordered_norm (fun i => 1 + h • a i) (1 + h * m) n
  intro i hi
  calc
    _ ≤ ‖(1 : e)‖ + ‖h • a i‖ := norm_add_le _ _
    _ = 1 + h * ‖a i‖ := by
      rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ _ := by gcongr; exact ha i hi

private lemma abel_step {e : Type*} [Ring e] [Algebra ℝ e]
    (a : ℕ → e) (b : e) (h : ℝ) (n : ℕ) :
    eulerProduct a h (n + 1) - (1 + h • b) ^ (n + 1) -
        h • (eulerProduct a h (n + 1) * centeredSum a b (n + 1)) =
      (eulerProduct a h n - (1 + h • b) ^ n -
        h • (eulerProduct a h n * centeredSum a b n)) * (1 + h • b) +
      h ^ 2 • (eulerProduct a h n *
        (centeredSum a b n * b - a n * centeredSum a b (n + 1))) := by
  rw [euler_succ, pow_succ]
  unfold centeredSum
  rw [Finset.sum_range_succ]
  simp only [mul_add, add_mul, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul, mul_one, mul_assoc]
  module

private lemma euler_abel_bound {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] (a : ℕ → e) (b : e) (m h r : ℝ) (n : ℕ)
    (hm : 0 ≤ m) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (ha : ∀ i < n, ‖a i‖ ≤ m) (hb : ‖b‖ ≤ m)
    (hs : ∀ k ≤ n, ‖centeredSum a b k‖ ≤ r) :
    ‖eulerProduct a h n - (1 + h • b) ^ n‖ ≤
      h * Real.exp (h * m * n) * (1 + 2 * h * m * n) * r := by
  let l := 1 + h * m
  have hl : 1 ≤ l := by dsimp [l]; nlinarith
  have hq : ‖1 + h • b‖ ≤ l := by
    calc
      _ ≤ ‖(1 : e)‖ + ‖h • b‖ := norm_add_le _ _
      _ = 1 + h * ‖b‖ := by rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      _ ≤ l := by dsimp [l]; gcongr
  have he : ∀ k ≤ n,
      ‖eulerProduct a h k - (1 + h • b) ^ k - h • (eulerProduct a h k * centeredSum a b k)‖ ≤
        2 * k * h ^ 2 * m * r * l ^ k := by
    intro k hk
    induction k with
    | zero =>
      unfold eulerProduct centeredSum
      rw [List.ofFn_zero, List.prod_nil, Finset.sum_range_zero, pow_zero]
      simp only [sub_self, mul_zero, smul_zero, norm_zero,
        Nat.cast_zero, zero_mul, pow_zero, le_refl]
    | succ k ih =>
      rw [abel_step]
      have hp := euler_norm a m h k hh (fun i hi => ha i (by omega))
      have hterm : ‖centeredSum a b k * b - a k * centeredSum a b (k + 1)‖ ≤ 2 * m * r := by
        calc
          _ ≤ ‖centeredSum a b k * b‖ + ‖a k * centeredSum a b (k + 1)‖ := norm_sub_le _ _
          _ ≤ r * m + m * r := add_le_add
            ((norm_mul_le _ _).trans (mul_le_mul (hs k (by omega)) hb (norm_nonneg _) hr))
            ((norm_mul_le _ _).trans (mul_le_mul (ha k (by omega))
              (hs (k + 1) hk) (norm_nonneg _) hm))
          _ = _ := by ring
      have hpow : l ^ k ≤ l ^ (k + 1) := pow_le_pow_right₀ hl (by omega)
      calc
        _ ≤ ‖(eulerProduct a h k - (1 + h • b) ^ k -
            h • (eulerProduct a h k * centeredSum a b k)) * (1 + h • b)‖ +
            ‖h ^ 2 • (eulerProduct a h k *
              (centeredSum a b k * b - a k * centeredSum a b (k + 1)))‖ := norm_add_le _ _
        _ ≤ (2 * k * h ^ 2 * m * r * l ^ k) * l + h ^ 2 * (l ^ k * (2 * m * r)) := by
          apply add_le_add
          · exact (norm_mul_le _ _).trans
              (mul_le_mul (ih (by omega)) hq (norm_nonneg _) (by positivity))
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
            gcongr
            exact (norm_mul_le _ _).trans (mul_le_mul hp hterm (norm_nonneg _) (by positivity))
        _ ≤ (2 * k * h ^ 2 * m * r * l ^ k) * l + h ^ 2 * (l ^ (k + 1) * (2 * m * r)) := by
          gcongr
        _ = 2 * (k + 1 : ℕ) * h ^ 2 * m * r * l ^ (k + 1) := by
          rw [pow_succ l k, Nat.cast_add, Nat.cast_one]
          ring
  have hp := euler_norm a m h n hh ha
  have hp_exp : l ^ n ≤ Real.exp (h * m * n) := by
    calc
      l ^ n ≤ (Real.exp (h * m)) ^ n := by
        gcongr
        simpa only [l, add_comm] using Real.add_one_le_exp (h * m)
      _ = Real.exp (h * m * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ ‖eulerProduct a h n - (1 + h • b) ^ n - h • (eulerProduct a h n * centeredSum a b n)‖ +
        ‖h • (eulerProduct a h n * centeredSum a b n)‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * n * h ^ 2 * m * r * l ^ n + h * (l ^ n * r) := by
      apply add_le_add (he n le_rfl)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul hp (hs n le_rfl) (norm_nonneg _) (by positivity))
    _ = h * l ^ n * (1 + 2 * h * m * n) * r := by ring
    _ ≤ _ := by gcongr

private lemma ordered_perturbation {e : Type*} [NormedRing e] [NormOneClass e]
    (a b : ℕ → e) (l d : ℝ) (n : ℕ) (hl : 1 ≤ l) (hd : 0 ≤ d)
    (ha : ∀ i < n, ‖a i‖ ≤ l) (hb : ∀ i < n, ‖b i‖ ≤ l)
    (he : ∀ i < n, ‖a i - b i‖ ≤ d) :
    ‖(List.ofFn fun i : Fin n => a i).prod -
      (List.ofFn fun i : Fin n => b i).prod‖ ≤ n * d * l ^ n := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.prod_nil, sub_self, norm_zero,
      Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    rw [List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]
    change ‖(List.ofFn fun i : Fin n => a i).prod * a n -
      (List.ofFn fun i : Fin n => b i).prod * b n‖ ≤ _
    have hp := ordered_norm b l n (fun i hi => hb i (by omega))
    have hi := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
      (fun i hi => he i (by omega))
    have hid : (List.ofFn fun i : Fin n => a i).prod * a n -
        (List.ofFn fun i : Fin n => b i).prod * b n =
      ((List.ofFn fun i : Fin n => a i).prod -
        (List.ofFn fun i : Fin n => b i).prod) * a n +
      (List.ofFn fun i : Fin n => b i).prod * (a n - b n) := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖((List.ofFn fun i : Fin n => a i).prod -
          (List.ofFn fun i : Fin n => b i).prod) * a n‖ +
          ‖(List.ofFn fun i : Fin n => b i).prod * (a n - b n)‖ := norm_add_le _ _
      _ ≤ (n * d * l ^ n) * l + l ^ n * d := add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul hi (ha n (by omega)) (norm_nonneg _) (by positivity)))
        ((norm_mul_le _ _).trans (mul_le_mul hp (he n (by omega)) (norm_nonneg _) (by positivity)))
      _ ≤ (n * d * l ^ n) * l + l ^ (n + 1) * d :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hl (Nat.le_succ n)) hd)
      _ = (n + 1 : ℕ) * d * l ^ (n + 1) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring

private lemma exp_euler_remainder {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] [CompleteSpace e] (z : e) (r : ℝ)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hsmall : r ≤ 1) :
    ‖NormedSpace.exp z - (1 + z)‖ ≤ (3 / 4 : ℝ) * r ^ 2 := by
  have h := D5.S3.Quantum.AURICOmega.ExponentialTail.exp_remainder_le z r 2 hr hz
    (by norm_num only [Nat.cast_ofNat]; linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, zero_add] at h
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat] at h
  refine h.trans ?_
  rw [div_le_iff₀ (show 0 < 1 - r / 3 by linarith)]
  nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) (show 0 ≤ 1 - r by linarith)]

private lemma exponential_euler_bound {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] [CompleteSpace e] (a : ℕ → e) (m t : ℝ) (n : ℕ)
    (hm : 0 ≤ m) (ht : 0 ≤ t) (hn : 0 < n)
    (ha : ∀ i < n, ‖a i‖ ≤ m) (hsmall : t / n * m ≤ 1) :
    ‖(List.ofFn fun i : Fin n => NormedSpace.exp ((t / n) • a i)).prod -
      eulerProduct a (t / n) n‖ ≤
      (3 / 4 : ℝ) * m ^ 2 * t ^ 2 * Real.exp (m * t) / n := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh : 0 ≤ t / n := div_nonneg ht hnpos.le
  have hr : 0 ≤ t / n * m := mul_nonneg hh hm
  have hnorm (i : ℕ) (hi : i < n) : ‖(t / n) • a i‖ ≤ t / n * m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left (ha i hi) hh
  have he := ordered_perturbation
    (fun i => NormedSpace.exp ((t / n) • a i)) (fun i => 1 + (t / n) • a i)
    (Real.exp (t / n * m)) ((3 / 4 : ℝ) * (t / n * m) ^ 2) n
    (Real.one_le_exp hr) (by positivity)
    (fun i hi => by
      simpa only [Finset.sum_range_zero, sub_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul] using
        D5.S3.Observer.Linear.ExactTaylorObservationRemainder.exp_tail_le
          (𝕜 := ℝ) ((t / n) • a i) (t / n * m) 0 hr (hnorm i hi))
    (fun i hi => (norm_add_le _ _).trans (by
      rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      exact (add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left (ha i hi) hh)).trans
        (show 1 + t / n * m ≤ Real.exp (t / n * m) by
          linarith [Real.add_one_le_exp (t / n * m)])))
    (fun i hi => exp_euler_remainder _ _ hr (hnorm i hi) hsmall)
  change ‖(List.ofFn fun i : Fin n => NormedSpace.exp ((t / n) • a i)).prod -
    (List.ofFn fun i : Fin n => 1 + (t / n) • a i).prod‖ ≤ _
  convert he using 1
  rw [← Real.exp_nat_mul]
  have harg : (n : ℝ) * (t / n * m) = m * t := by field_simp (discharger := positivity)
  rw [harg]
  field_simp (discharger := positivity)

private lemma centered_max_sublinear {e : Type*} [NormedAddCommGroup e]
    [NormedSpace ℝ e] (a : ℕ → e) (b : e)
    (hav : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i)
      atTop (𝓝 b)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ k ≤ n, ‖centeredSum a b k‖ ≤ ε * n := by
  have hcenter : ∀ n : ℕ, 0 < n →
      centeredSum a b n = (n : ℝ) • ((n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, a i) - b) := by
    intro n hn
    unfold centeredSum
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt (Nat.cast_pos.mpr hn)),
      one_smul, Nat.cast_smul_eq_nsmul]
  intro ε hε
  have hev : ∀ᶠ k : ℕ in atTop,
      ‖(k : ℝ)⁻¹ • (∑ i ∈ Finset.range k, a i) - b‖ < ε := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hav ε hε)
  obtain ⟨k, hk⟩ := eventually_atTop.mp hev
  let c := ∑ i ∈ Finset.range k, ‖centeredSum a b i‖
  have hlarge : ∀ᶠ n : ℕ in atTop, c / ε ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (c / ε))
  filter_upwards [hlarge] with n hn
  intro j hj
  by_cases hjk : j < k
  · have hfirst : ‖centeredSum a b j‖ ≤ c :=
      Finset.single_le_sum (fun i _ => norm_nonneg (centeredSum a b i))
        (Finset.mem_range.mpr hjk)
    exact hfirst.trans ((div_le_iff₀ hε).mp hn |>.trans_eq (mul_comm _ _))
  · by_cases hjpos : 0 < j
    · rw [hcenter j hjpos, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg j)]
      calc
        _ ≤ (j : ℝ) * ε := mul_le_mul_of_nonneg_left (hk j (by omega)).le (Nat.cast_nonneg j)
        _ ≤ ε * n := by nlinarith [show (j : ℝ) ≤ n from Nat.cast_le.mpr hj]
    · have hjzero : j = 0 := by omega
      subst j
      unfold centeredSum
      rw [Finset.sum_range_zero, norm_zero]
      positivity

private lemma deterministic_uniform {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] [CompleteSpace e] (a : ℕ → e) (b : e) (m : ℝ)
    (hm : 0 ≤ m) (ha : ∀ i, ‖a i‖ ≤ m) (hb : ‖b‖ ≤ m)
    (hav : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i)
      atTop (𝓝 b)) :
    ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖(List.ofFn fun i : Fin n => NormedSpace.exp ((s / n) • a i)).prod -
          NormedSpace.exp (s • b)‖ < ε := by
  intro t ht ε hε
  let c := Real.exp (m * t)
  let d := t * c * (1 + 2 * m * t)
  let f := (3 / 2 : ℝ) * m ^ 2 * t ^ 2 * c
  let δ := ε / (2 * (d + 1))
  have hc : 0 < c := Real.exp_pos _
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (2 * (d + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hδsmall : d * δ < ε / 2 := by nlinarith
  have hmax := centered_max_sublinear a b hav δ hδ
  have hlarge : ∀ᶠ n : ℕ in atTop, t * m ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (t * m))
  have htail : ∀ᶠ n : ℕ in atTop, f / (n : ℝ) < ε / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat f).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hmax, eventually_gt_atTop (0 : ℕ), hlarge, htail] with n hsums hn hnm htail
  intro s hs
  have hs0 := hs.1
  have hst := hs.2
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh : 0 ≤ s / n := div_nonneg hs0 hnpos.le
  have hsmall : s / n * m ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hnpos]
    exact (mul_le_mul_of_nonneg_right hst hm).trans hnm
  let p := (List.ofFn fun i : Fin n => NormedSpace.exp ((s / n) • a i)).prod
  let q := eulerProduct a (s / n) n
  let v := (1 + (s / n) • b) ^ n
  let w := NormedSpace.exp (s • b)
  let k := (3 / 4 : ℝ) * m ^ 2 * t ^ 2 * c / n
  have herr : (3 / 4 : ℝ) * m ^ 2 * s ^ 2 * Real.exp (m * s) / n ≤ k := by
    dsimp [k, c]
    gcongr
  have hpq : ‖p - q‖ ≤ k :=
    (exponential_euler_bound a m s n hm hs0 hn (fun i _ => ha i) hsmall).trans herr
  have hconst := exponential_euler_bound (fun _ => b) m s n hm hs0 hn
    (fun _ _ => hb) hsmall
  change ‖(List.ofFn fun _ : Fin n => NormedSpace.exp ((s / n) • b)).prod -
    (List.ofFn fun _ : Fin n => 1 + (s / n) • b).prod‖ ≤ _ at hconst
  rw [List.ofFn_const, List.prod_replicate, List.ofFn_const, List.prod_replicate] at hconst
  have hcancel : (n : ℝ) * (s / n) = s := by field_simp (discharger := positivity)
  have hexp : NormedSpace.exp ((s / n) • b) ^ n = w := by
    let := NormedAlgebra.restrictScalars ℚ ℝ e
    rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hcancel]
  rw [hexp, norm_sub_rev] at hconst
  have hvw : ‖v - w‖ ≤ k := hconst.trans herr
  have habel := euler_abel_bound a b m (s / n) (δ * n) n hm hh (by positivity)
    (fun i _ => ha i) hb hsums
  have harg : s / n * m * n = m * s := by field_simp (discharger := positivity)
  have hfactor : 1 + 2 * (s / n) * m * n = 1 + 2 * m * s := by field_simp (discharger := positivity)
  have hqv : ‖q - v‖ ≤ d * δ := by
    refine habel.trans ?_
    calc
      _ = δ * s * Real.exp (m * s) * (1 + 2 * m * s) := by
        rw [harg, hfactor]
        field_simp (discharger := positivity)
      _ ≤ δ * t * c * (1 + 2 * m * t) := by dsimp [c]; gcongr
      _ = d * δ := by dsimp [d]; ring
  change ‖p - w‖ < ε
  calc
    _ ≤ ‖p - q‖ + ‖q - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖p - q‖ + (‖q - v‖ + ‖v - w‖) :=
      add_le_add (le_refl _) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ k + (d * δ + k) := add_le_add hpq (add_le_add hqv hvw)
    _ = d * δ + f / n := by dsimp [k, f]; ring
    _ < ε := by linarith

private lemma operator_uniform_to_sot {𝕜 e α : Type} [RCLike 𝕜]
    [NormedAddCommGroup e] [NormedSpace 𝕜 e] [CompleteSpace e]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (a : ℕ → α → e →L[𝕜] e)
    (hsm : ∀ i, AEStronglyMeasurable (a i) μ)
    (hind : letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
      Pairwise (fun i j => IndepFun (a i) (a j) μ))
    (hid : letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
      ∀ i, IdentDistrib (a i) (a 0) μ μ)
    (m : ℝ) (ha : ∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m) :
    letI := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
    ∀ (x : e) (t : ℝ), 0 ≤ t → ∀ᵐ ω ∂μ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖(randomProduct a n s ω -
          NormedSpace.exp (((s : ℝ) : 𝕜) • ∫ z, a 0 z ∂μ)) x‖ < ε := by
  let := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
  let : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
  let : BorelSpace (e →L[𝕜] e) := ⟨rfl⟩
  intro x t ht
  by_cases htriv : Subsingleton e
  · let := htriv
    refine Filter.Eventually.of_forall fun ω ε hε => ?_
    refine Filter.Eventually.of_forall fun n s hs => ?_
    have hz : ∀ y : e, ‖y‖ = 0 := by
      intro y
      rw [Subsingleton.elim y 0, norm_zero]
    rw [hz]
    exact hε
  · let : Nontrivial e := not_subsingleton_iff_nontrivial.mp htriv
    let b : e →L[𝕜] e := ∫ z, a 0 z ∂μ
    have hint : Integrable (a 0) μ := Integrable.of_bound (hsm 0) m (ha 0)
    have hm : 0 ≤ m := by
      obtain ⟨ω, hω⟩ := (ha 0).exists
      exact (norm_nonneg (a 0 ω)).trans hω
    have hb : ‖b‖ ≤ m := by
      simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (ha 0)
    have hstrong := ProbabilityTheory.strong_law_ae a hint hind hid
    have hbounded : ∀ᵐ ω ∂μ, ∀ i, ‖a i ω‖ ≤ m := ae_all_iff.mpr ha
    filter_upwards [hstrong, hbounded] with ω hω hbound
    intro ε hε
    have hη : 0 < ε / (‖x‖ + 1) := by positivity
    have hunif := deterministic_uniform (fun i => a i ω) b m hm hbound hb hω t ht
      (ε / (‖x‖ + 1)) hη
    filter_upwards [hunif] with n hn
    intro s hs
    change ‖((List.ofFn fun i : Fin n => NormedSpace.exp ((s / n) • a i ω)).prod -
      NormedSpace.exp (s • b)) x‖ < ε
    let u := (List.ofFn fun i : Fin n => NormedSpace.exp ((s / n) • a i ω)).prod -
      NormedSpace.exp (s • b)
    calc
      ‖u x‖ ≤ ‖u‖ * ‖x‖ := u.le_opNorm x
      _ ≤ ‖u‖ * (‖x‖ + 1) := by gcongr; linarith
      _ < (ε / (‖x‖ + 1)) * (‖x‖ + 1) :=
        mul_lt_mul_of_pos_right (hn s hs) (by positivity)
      _ = ε := div_mul_cancel₀ _ (by positivity)

theorem result : claim := by
  intro 𝕜 e α _ _ _ _ _ μ _
  let := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
  let : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
  intro a hsm hind hid m ha
  exact operator_uniform_to_sot μ a hsm hind hid m ha

end D5.S3.Analytic.Probability.RandomExponentialProductSLLN
