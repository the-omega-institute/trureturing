/- GID: D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalReadoutUniformLimit
   mirror-E: none(waiver:actual-geometric-readout-uniform-limit)
   anchors: []
   utility: none
   digest: Geometric mechanical readouts approach the slope uniformly as weights flatten. -/

import D5.S1.Words.Mechanical.MechanicalReadoutOrder
import D5.S1.Words.Mechanical.MechanicalDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit

open Set Finset Filter
open scoped BigOperators Topology
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalReadoutOrder

/-- Flattening the geometric weights makes the completed readout uniformly
close to the slope, at every phase. The estimate comes from the bounded
cumulative-floor discrepancy, not from the phase-averaged L1 identity. -/
theorem geometric_readout_uniform_slope_bound
    (r alpha x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : alpha ∈ Ico (0 : ℝ) 1) :
    |geometricReadout r alpha x - alpha| ≤ 1 - r ∧
    (∀ (target : ℝ) (n : ℕ),
        |weightedPrefix (fun j => (1 - r) * r ^ j) alpha x n - target| ≤
          r ^ n + (1 - r) + |alpha - target|) ∧
    (1 - r) * (Int.fract x - 1) ≤ geometricReadout r alpha x - alpha ∧
      geometricReadout r alpha x - alpha ≤ (1 - r) * Int.fract x := by
  let q : ℕ → ℝ := fun j => (1 - r) * r ^ j
  let P : ℕ → ℝ := fun n => weightedPrefix q alpha x n
  let B : ℕ → ℝ := fun k =>
    (⌊x + (k : ℝ) * alpha⌋ : ℝ) - (⌊x⌋ : ℝ) - (k : ℝ) * alpha
  have hB0 : B 0 = 0 := by
    dsimp [B]
    simp only [Nat.cast_zero, zero_mul, add_zero, sub_self]
  have hcount (k : ℕ) :
      (lowerMechanicalWindowTrueCount alpha x 0 k : ℝ) =
        (⌊x + (k : ℝ) * alpha⌋ : ℝ) - (⌊x⌋ : ℝ) := by
    have h := lowerMechanicalWindowTrueCount_eq_floor
      (alpha := alpha) (rho := x) ha.1 ha.2 0 k
    have h' : (lowerMechanicalWindowTrueCount alpha x 0 k : ℤ) =
        ⌊x + (k : ℝ) * alpha⌋ - ⌊x⌋ := by
      simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.zero_add] using h
    exact_mod_cast h'
  have hB (k : ℕ) : -1 ≤ B k ∧ B k ≤ 1 := by
    have hd := lower_mechanical_window_true_discrepancy
      (alpha := alpha) (rho := x) ha.1 ha.2 0 k
    rw [abs_lt] at hd
    have heq : B k = (lowerMechanicalWindowTrueCount alpha x 0 k : ℝ) -
        (k : ℝ) * alpha := by
      dsimp [B]
      rw [hcount]
    rw [heq]
    exact ⟨hd.1.le, hd.2.le⟩
  have hBfract (k : ℕ) : B k = Int.fract x - Int.fract (x + (k : ℝ) * alpha) := by
    unfold B Int.fract
    ring
  have hBfine (k : ℕ) : Int.fract x - 1 ≤ B k ∧ B k ≤ Int.fract x := by
    rw [hBfract]
    exact ⟨sub_le_sub_left (Int.fract_lt_one _).le _,
      sub_le_self _ (Int.fract_nonneg _)⟩
  have hq0 (k : ℕ) : 0 ≤ q k :=
    mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0 k)
  have hdrop (k : ℕ) : q k - q (k + 1) = (1 - r) ^ 2 * r ^ k := by
    dsimp [q]
    rw [pow_succ]
    ring
  have hdrop0 (k : ℕ) : 0 ≤ q k - q (k + 1) := by
    rw [hdrop]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _)
  have hqn (n : ℕ) : (∑ j ∈ range n, q j) = 1 - r ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; dsimp [q]; ring
  have hletter (j : ℕ) :
      (lowerMechanicalLetter alpha x j : ℝ) - alpha = B (j + 1) - B j := by
    dsimp [B, lowerMechanicalLetter]
    push_cast
    ring
  have hparts (n : ℕ) :
      (∑ j ∈ range n, q j * (B (j + 1) - B j)) =
        q n * B n + ∑ j ∈ range n, (q j - q (j + 1)) * B (j + 1) := by
    induction n with
    | zero => simp [hB0]
    | succ n ih =>
        rw [sum_range_succ, ih, sum_range_succ]
        ring
  have hcoeff (n : ℕ) :
      q n + ∑ j ∈ range n, (q j - q (j + 1)) = 1 - r := by
    induction n with
    | zero => simp [q]
    | succ n ih =>
        rw [sum_range_succ]
        linarith
  have herr (n : ℕ) :
      P n - alpha * (1 - r ^ n) =
        q n * B n + ∑ j ∈ range n, (q j - q (j + 1)) * B (j + 1) := by
    calc
      P n - alpha * (1 - r ^ n) =
          ∑ j ∈ range n, q j * ((lowerMechanicalLetter alpha x j : ℝ) - alpha) := by
            dsimp [P, weightedPrefix]
            rw [← hqn n, Finset.mul_sum]
            simp_rw [mul_sub]
            rw [sum_sub_distrib]
            simp_rw [mul_comm alpha]
      _ = ∑ j ∈ range n, q j * (B (j + 1) - B j) := by
        apply sum_congr rfl
        intro j _
        rw [hletter]
      _ = _ := hparts n
  have hfinite (n : ℕ) : |P n - alpha * (1 - r ^ n)| ≤ 1 - r := by
    rw [herr]
    have htop :
        q n * B n + ∑ j ∈ range n, (q j - q (j + 1)) * B (j + 1) ≤
          q n + ∑ j ∈ range n, (q j - q (j + 1)) := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left (hB n).2 (hq0 n)).trans_eq
          (mul_one _)
      · apply sum_le_sum
        intro j _
        exact (mul_le_mul_of_nonneg_left (hB (j + 1)).2 (hdrop0 j)).trans_eq
          (mul_one _)
    have hbottom :
        -(q n + ∑ j ∈ range n, (q j - q (j + 1))) ≤
          q n * B n + ∑ j ∈ range n, (q j - q (j + 1)) * B (j + 1) := by
      rw [neg_add, ← Finset.sum_neg_distrib]
      apply add_le_add
      · have hb : 0 ≤ B n + 1 := by linarith [(hB n).1]
        nlinarith [mul_nonneg (hq0 n) hb]
      · apply sum_le_sum
        intro j _
        have hb : 0 ≤ B (j + 1) + 1 := by linarith [(hB (j + 1)).1]
        nlinarith [mul_nonneg (hdrop0 j) hb]
    rw [hcoeff n] at htop hbottom
    exact abs_le.mpr ⟨hbottom, htop⟩
  have hfiniteFine (n : ℕ) :
      (1 - r) * (Int.fract x - 1) ≤ P n - alpha * (1 - r ^ n) ∧
        P n - alpha * (1 - r ^ n) ≤ (1 - r) * Int.fract x := by
    rw [herr]
    constructor
    · rw [← hcoeff n, add_mul, Finset.sum_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hBfine n).1 (hq0 n))
        (sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hBfine (j + 1)).1 (hdrop0 j))
    · rw [← hcoeff n, add_mul, Finset.sum_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hBfine n).2 (hq0 n))
        (sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hBfine (j + 1)).2 (hdrop0 j))
  have htail (n : ℕ) :
      0 ≤ geometricReadout r alpha x - P n ∧
        geometricReadout r alpha x - P n ≤ r ^ n := by
    exact (geometric_readout_isometric_completion r alpha alpha hr0 hr1 ha ha).2.2.1 x n
  have hp : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hP : Tendsto P atTop (𝓝 (geometricReadout r alpha x)) := by
    apply Metric.tendsto_atTop.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hp).2 eps heps)
    refine ⟨N, ?_⟩
    intro n hn
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (htail n).1]
    exact lt_of_le_of_lt (htail n).2 (hN n hn)
  have he : Tendsto (fun n : ℕ => P n - alpha * (1 - r ^ n)) atTop
      (𝓝 (geometricReadout r alpha x - alpha)) := by
    convert hP.sub (tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)) using 1
    norm_num
  have hne : Tendsto (fun n : ℕ => |P n - alpha * (1 - r ^ n)|) atTop
      (𝓝 |geometricReadout r alpha x - alpha|) :=
    (continuous_abs.tendsto _).comp he
  have huniform : |geometricReadout r alpha x - alpha| ≤ 1 - r :=
    le_of_tendsto hne (Eventually.of_forall hfinite)
  refine ⟨huniform, ?_, ?_, ?_⟩
  · intro target n
    have htailAbs : |P n - geometricReadout r alpha x| ≤ r ^ n := by
      rw [abs_sub_comm, abs_of_nonneg (htail n).1]
      exact (htail n).2
    have htriangle : |P n - target| ≤
        |P n - geometricReadout r alpha x| +
          |geometricReadout r alpha x - alpha| + |alpha - target| := by
      calc
        |P n - target| =
            |(P n - geometricReadout r alpha x) +
              (geometricReadout r alpha x - alpha) + (alpha - target)| := by
                congr 1
                ring
        _ ≤ |(P n - geometricReadout r alpha x) +
                (geometricReadout r alpha x - alpha)| + |alpha - target| := abs_add_le _ _
        _ ≤ _ := add_le_add
          (abs_add_le (P n - geometricReadout r alpha x)
            (geometricReadout r alpha x - alpha)) le_rfl
    change |P n - target| ≤ r ^ n + (1 - r) + |alpha - target|
    linarith
  · exact ge_of_tendsto he (Eventually.of_forall fun n => (hfiniteFine n).1)
  · exact le_of_tendsto he (Eventually.of_forall fun n => (hfiniteFine n).2)

/-- Taking the observation horizon to infinity recovers the completed
readout at fixed ratio; flattening the weights first sends each fixed
prefix to zero, whereas the completed readout tends to the slope. -/
theorem geometric_readout_iterated_limit_order (alpha x : ℝ)
    (ha : alpha ∈ Ico (0 : ℝ) 1) :
    (∀ r : ℝ, r ∈ Ico (0 : ℝ) 1 →
      Tendsto (fun n : ℕ => weightedPrefix (fun j => (1 - r) * r ^ j) alpha x n)
        atTop (𝓝 (geometricReadout r alpha x))) ∧
    Tendsto (fun r : ℝ => geometricReadout r alpha x) (𝓝[<] (1 : ℝ)) (𝓝 alpha) ∧
    (∀ n : ℕ,
      Tendsto (fun r : ℝ => weightedPrefix (fun j => (1 - r) * r ^ j) alpha x n)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))) := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hrange : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
    (nhdsLT_basis 1).mem_of_mem (by norm_num)
  have hto0 : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert tendsto_const_nhds.sub hid using 1 <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have hp : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2
    have htail (n : ℕ) :
        0 ≤ geometricReadout r alpha x -
          weightedPrefix (fun j => (1 - r) * r ^ j) alpha x n ∧
        geometricReadout r alpha x -
          weightedPrefix (fun j => (1 - r) * r ^ j) alpha x n ≤ r ^ n :=
      (geometric_readout_isometric_completion r alpha alpha hr.1 hr.2 ha ha).2.2.1 x n
    apply Metric.tendsto_atTop.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hp).2 eps heps)
    refine ⟨N, ?_⟩
    intro n hn
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (htail n).1]
    exact lt_of_le_of_lt (htail n).2 (hN n hn)
  · apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [hrange, (tendsto_order.mp hto0).2 eps heps] with r hr hsmall
    have hb := (geometric_readout_uniform_slope_bound r alpha x hr.1.le hr.2 ha).1
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hb hsmall
  · intro n
    have hcont : Continuous (fun r : ℝ =>
        weightedPrefix (fun j => (1 - r) * r ^ j) alpha x n) := by
      simp only [weightedPrefix]
      fun_prop
    have hval : weightedPrefix (fun j => (1 - (1 : ℝ)) * (1 : ℝ) ^ j)
        alpha x n = 0 := by simp [weightedPrefix]
    simpa only [hval] using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds

#print axioms geometric_readout_uniform_slope_bound
#print axioms geometric_readout_iterated_limit_order

end D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
