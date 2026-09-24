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
      ∀ (target : ℝ) (n : ℕ),
        |weightedPrefix (fun j => (1 - r) * r ^ j) alpha x n - target| ≤
          r ^ n + (1 - r) + |alpha - target| := by
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
  refine ⟨huniform, ?_⟩
  intro target n
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

#print axioms geometric_readout_uniform_slope_bound

end D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
