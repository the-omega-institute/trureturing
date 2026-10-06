/- GID: D5/S1/Digit/Infinite/SevenCycleOriginalGraph
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleOriginalGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original endpoint parameters for the seven-cycle coordinates. -/

import D5.S1.Digit.Infinite.SevenCycleCollisionFuture

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleOriginalGraph

open D5.S0.Carrier (GoldenInt conj)
open D5.S1.Scale (embedding)
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCollisionData
open private golden_data budget_bounds actual_entry source_windows shifted_source_windows shifted_source_tail
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private entry_algebra entry_bounds from D5.S1.Digit.Infinite.SevenCycleCollisionColors
open private phase_lawful from D5.S1.Digit.Infinite.SevenCycleCollisionFuture
open private actual_phase actual_phase_mod actual_phase_guard actual_guard phase_state periodic_rival
  from D5.S1.Digit.Infinite.SevenCycleCollisionRecords

/-- The original construction uses twenty times a denominator of the budget coefficients. -/
def denominator : ℕ := 20 * 244760

private theorem budget_formula : budget = (99504 - 145874 * t) / 244760 := by
  obtain ⟨ht2, hg, hg2, hglo, _⟩ := golden_data
  have hg0 : 0 < g := by linarith
  have hD : 4 * (1 + g ^ 7) ≠ 0 := by positivity
  have hp : 244760 * g ^ 7 * (g - 1 / 5) =
      4 * (1 + g ^ 7) * (60699 * g - 14329) := by
    linear_combination
      (-57316 + 13532 * g - 3188 * g ^ 2 + 780 * g ^ 3 - 68 * g ^ 4 +
        508 * g ^ 5 + 1964 * g ^ 6) * hg2
  have hd : reduction = (60699 * g - 14329) / 244760 := by
    unfold reduction
    apply (div_eq_iff hD).2
    nlinarith only [hp]
  unfold budget lambda
  rw [hd]
  nlinarith only [ht2, hg]

private theorem golden_ratio_t : Real.goldenRatio = 1 + t := by
  change Real.goldenRatio = 1 + Real.goldenRatio⁻¹
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

private theorem lattice_member (a b : ℤ) (x : ℝ)
    (hx : x = ((a : ℝ) + b * t) / denominator)
    (hs : x ∈ stateInterval false)
    (hc : |((a : ℝ) - b * (1 + t)) / denominator| ≤ 100) :
    x ∈ endpoints denominator 100 := by
  refine ⟨hs, ⟨a - b, b⟩, ?_, ?_⟩
  · rw [hx]
    simp [embedding, golden_ratio_t]
    ring
  · simpa [embedding, conj, golden_ratio_t, sub_eq_add_neg] using hc

private theorem offset_conjugate_bound (l : Label) :
    |embedding (conj (offsetInteger l))| * g ≤ (1 - g) * 100 := by
  obtain ⟨_, _, _, hglo, hghi⟩ := golden_data
  have ht : (1 / 2 : ℝ) < t ∧ t < 5 / 8 := by
    have hg := golden_data.2.1
    constructor <;> linarith only [hglo, hghi, hg]
  have hprod : g * t ≤ g := by
    have h := mul_nonneg (show 0 ≤ g by linarith only [hglo])
      (show 0 ≤ 1 - t by linarith only [ht.2])
    nlinarith only [h]
  cases h0 : l.val 0 <;> cases h1 : l.val 1 <;> cases h2 : l.val 2 <;>
    norm_num [embedding, conj, offsetInteger, h0, h1, h2, golden_ratio_t]
  all_goals try rw [abs_of_nonneg (by linarith only [ht.1])]
  all_goals nlinarith only [hglo, hghi, ht.1, ht.2, hprod]

private theorem original_parameters : endpointParameters budget denominator 100 := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  obtain ⟨hd0, hd, hb0, hb⟩ := budget_bounds
  have ht : (1 / 2 : ℝ) < t ∧ t < 5 / 8 := by constructor <;> linarith
  have htsq : t ^ 2 = 1 - t := by linarith
  have hf := budget_formula
  have hcell (i : Fin 6) :
      -1 ≤ cellLower i ∧ cellLower i ≤ 1 + t ∧
      -1 ≤ cellUpper i ∧ cellUpper i ≤ 1 + t := by
    fin_cases i <;> norm_num [cellLower, cellUpper, cuts, lambda] <;>
      (repeat' apply And.intro) <;> nlinarith
  have hpoint (a b : ℤ) (x : ℝ)
      (hx : x = ((a : ℝ) + b * t) / denominator)
      (hs : x ∈ stateInterval false)
      (hc : |((a : ℝ) - b * (1 + t)) / denominator| ≤ 100) :
      x ∈ endpoints denominator 100 := lattice_member a b x hx hs hc
  refine ⟨by norm_num [denominator], by norm_num, ?_, ?_⟩
  · intro x hx
    rcases hx with (hx | ⟨i, rfl⟩) | ⟨i, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · apply hpoint (-4895200) (0)
        · norm_num [denominator] <;> nlinarith only [ht2, hg]
        · norm_num [stateInterval, abs_of_pos (by linarith : 0 < t)] <;> (try constructor) <;>
            nlinarith only [ht.1, ht.2, ht2, hg]
        · rw [abs_le]
          norm_num [denominator] <;> constructor <;> linarith only [ht.1, ht.2]
      · apply hpoint (4895200) (4895200)
        · norm_num [denominator] <;> nlinarith only [ht2, hg]
        · norm_num [stateInterval, abs_of_pos (by linarith : 0 < t)] <;> (try constructor) <;>
            nlinarith only [ht.1, ht.2, ht2, hg]
        · rw [abs_le]
          norm_num [denominator] <;> constructor <;> linarith only [ht.1, ht.2]
      · apply hpoint (0) (4895200)
        · norm_num [denominator] <;> nlinarith only [ht2, hg]
        · norm_num [stateInterval, abs_of_pos (by linarith : 0 < t)] <;> (try constructor) <;>
            nlinarith only [ht.1, ht.2, ht2, hg]
        · rw [abs_le]
          norm_num [denominator] <;> constructor <;> linarith only [ht.1, ht.2]
      · apply hpoint (-4895200) (4895200)
        · norm_num [denominator] <;> nlinarith only [ht2, hg]
        · norm_num [stateInterval, abs_of_pos (by linarith : 0 < t)] <;> (try constructor) <;>
            nlinarith only [ht.1, ht.2, ht2, hg]
        · rw [abs_le]
          norm_num [denominator] <;> constructor <;> linarith only [ht.1, ht.2]
      · apply hpoint (-4895200) (9790400)
        · norm_num [denominator] <;> nlinarith only [ht2, hg]
        · norm_num [stateInterval, abs_of_pos (by linarith : 0 < t)] <;> (try constructor) <;>
            nlinarith only [ht.1, ht.2, ht2, hg]
        · rw [abs_le]
          norm_num [denominator] <;> constructor <;> linarith only [ht.1, ht.2]
      · apply hpoint (0) (9790400)
        · norm_num [denominator] <;> nlinarith only [ht2, hg]
        · norm_num [stateInterval, abs_of_pos (by linarith : 0 < t)] <;> (try constructor) <;>
            nlinarith only [ht.1, ht.2, ht2, hg]
        · rw [abs_le]
          norm_num [denominator] <;> constructor <;> linarith only [ht.1, ht.2]
    · change max (-1) (cellLower i - budget) ∈ endpoints denominator 100
      have hs : max (-1) (cellLower i - budget) ∈ stateInterval false := by
        simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
        exact ⟨le_max_left _ _, max_le (by linarith [ht.1]) (by linarith [(hcell i).2.1])⟩
      rcases max_cases (-1 : ℝ) (cellLower i - budget) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hs ⊢
        apply hpoint (-4895200) 0
        · norm_num [denominator]
        · exact hs
        · rw [abs_le]
          norm_num [denominator]
      · rw [he] at hs ⊢
        fin_cases i
        · apply hpoint (-6885280) (2917480)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-7374800) (8302200)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-8353840) (14176440)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-4437680) (10260280)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-5416720) (16134520)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-1500560) (12218360)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
    · change min (1 + t) (cellUpper i + budget) ∈ endpoints denominator 100
      have hs : min (1 + t) (cellUpper i + budget) ∈ stateInterval false := by
        simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
        exact ⟨le_min (by linarith [ht.1]) (by linarith [(hcell i).2.2.1]), min_le_left _ _⟩
      rcases min_cases (1 + t) (cellUpper i + budget) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hs ⊢
        apply hpoint 4895200 4895200
        · norm_num [denominator]
          ring
        · exact hs
        · rw [abs_le]
          norm_num [denominator] <;> constructor <;> linarith only [ht.1, ht.2]
      · rw [he] at hs ⊢
        fin_cases i
        · apply hpoint (-3394640) (2467240)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-4373680) (8341480)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-457520) (4425320)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (-1436560) (10299560)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (2479600) (6383400)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
        · apply hpoint (6885280) (1977720)
          · norm_num [cellLower, cellUpper, cuts, denominator, lambda]
            rw [hf]
            nlinarith only [ht2, hg]
          · exact hs
          · rw [abs_le]
            norm_num [denominator]
            constructor <;> linarith only [ht.1, ht.2]
  · exact offset_conjugate_bound

private theorem entry_lattice : firstEntry ∈ endpoints denominator 100 ∧
    rivalEntry ∈ endpoints denominator 100 ∧ feedingEntry ∈ endpoints denominator 100 := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  have ht : (1 / 2 : ℝ) < t ∧ t < 5 / 8 := by constructor <;> linarith
  have hd : reduction = (121398 * t - 75028) / 244760 := by
    have h := budget_formula
    unfold budget lambda at h
    nlinarith only [h, ht2]
  have hs (b : Bool) : (if b then firstEntry else rivalEntry) ∈ stateInterval false := by
    rw [← actual_entry, ← closed_observation_graph_realization.2.1 false]
    exact ⟨_, by simp [stateAddress], rfl⟩
  have hx : firstEntry = (-2061200 + (-295200 : ℝ) * t) / denominator := by
    rw [entry_algebra.1, hd]
    unfold lowerEntry denominator
    rw [hg]
    nlinarith only [ht2]
  have hy : rivalEntry = (128000 + (1057600 : ℝ) * t) / denominator := by
    unfold rivalEntry upperEntry denominator
    rw [hd, hg]
    ring
  have hz : feedingEntry = (-2061200 + (4600000 : ℝ) * t) / denominator := by
    have h : feedingEntry = firstEntry + t := by
      unfold feedingEntry firstEntry
      linarith [entry_algebra.2.1]
    rw [h, hx]
    norm_num [denominator]
    ring
  refine ⟨lattice_member (-2061200) (-295200) _ (by simpa only [Int.cast_neg, Int.cast_ofNat] using hx) (hs true) ?_,
    lattice_member 128000 1057600 _ hy (hs false) ?_,
    lattice_member (-2061200) 4600000 _ (by simpa only [Int.cast_neg, Int.cast_ofNat] using hz) ?_ ?_⟩
  · rw [abs_le]
    norm_num [denominator]
    constructor <;> linarith only [ht.1, ht.2]
  · rw [abs_le]
    norm_num [denominator]
    constructor <;> linarith only [ht.1, ht.2]
  · have h := entry_bounds.2.2.2.2.2
    norm_num [cellLower, cellUpper, cuts, lambda] at h
    simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
    constructor <;> nlinarith only [h.1, h.2, ht.1, ht.2, ht2, hg]
  · rw [abs_le]
    norm_num [denominator]
    constructor <;> linarith only [ht.1, ht.2]

private theorem orbit_lattice (b : Bool) (j : ℕ) :
    kappa (bitShift (source b) (3 * j)) ∈ endpoints denominator 100 := by
  have hg0 : 0 < g := by have := golden_data.2.2.2.1; linarith
  have hp := original_parameters
  have hinv := (closed_observation_graph_realization.2.2.2.2.2.1
    budget denominator 100 hp).2.1
  induction j with
  | zero =>
    change kappa (source b) ∈ _
    rw [actual_entry]
    cases b
    · exact entry_lattice.2.1
    · exact entry_lattice.1
  | succ j ih =>
    have hs : kappa (bitShift (source b) (3 * (j + 1))) ∈ stateInterval false := by
      rw [← closed_observation_graph_realization.2.1 false]
      exact ⟨_, by simp [stateAddress], rfl⟩
    have he : inverseBranch (window (source b) j)
        (kappa (bitShift (source b) (3 * j))) =
        kappa (bitShift (source b) (3 * (j + 1))) := by
      have h := (closed_observation_graph_realization.2.2.1
        (bitShift (source b) (3 * j))).1
      simp only [shifted_source_windows, Nat.add_zero, shifted_source_tail] at h
      unfold inverseBranch
      apply (div_eq_iff hg0.ne').2
      unfold branch at h
      linarith
    rw [← he]
    exact hinv _ _ ih (by rwa [he])

/-- All original endpoint singletons are retained, with their incoming guards. -/
noncomputable def orbitVertex (b : Bool) (j : ℕ) : Vertex denominator 100 :=
  ⟨(phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩,
      kappa (bitShift (source b) (3 * j)), kappa (bitShift (source b) (3 * j))),
    orbit_lattice b j, orbit_lattice b j,
    by rw [actual_phase_mod]; exact phase_state b j,
    by rw [actual_phase_mod]; exact phase_state b j,
    le_rfl, Or.inl rfl⟩

private theorem orbit_edge (b : Bool) (j : ℕ) :
    edge (orbitVertex b j) (window (source b) j) (orbitVertex b (j + 1)) := by
  have hl := phase_lawful b j
  have hrec := (closed_observation_graph_realization.2.2.1
    (bitShift (source b) (3 * j))).1
  simp only [shifted_source_windows, Nat.add_zero, shifted_source_tail] at hrec
  have hg0 : 0 < g := by have := golden_data.2.2.2.1; linarith
  have he : inverseBranch (window (source b) j)
      (kappa (bitShift (source b) (3 * j))) =
      kappa (bitShift (source b) (3 * (j + 1))) := by
    unfold inverseBranch
    apply (div_eq_iff hg0.ne').2
    unfold branch at hrec
    linarith
  change lawful _ _ _ ∧
    Set.Icc (kappa (bitShift (source b) (3 * j)))
      (kappa (bitShift (source b) (3 * j))) ⊆ _ ∧
    Set.Icc (kappa (bitShift (source b) (3 * (j + 1))))
      (kappa (bitShift (source b) (3 * (j + 1)))) ⊆ _
  simp only [Set.Icc_self, Set.singleton_subset_iff]
  refine ⟨hl, ⟨kappa (bitShift (source b) (3 * (j + 1))), ?_, hrec.symm⟩, ?_⟩
  · rw [actual_phase_mod]
    exact phase_state b (j + 1)
  · exact ⟨_, ⟨le_rfl, le_rfl⟩, he⟩

private theorem orbit_period (b : Bool) (j : ℕ) : orbitVertex b (j + 7) = orbitVertex b j := by
  apply Subtype.ext
  simp [orbitVertex, actual_phase_mod, Nat.add_mod]

private theorem rival_qualified :
    D5.S1.Digit.Infinite.SevenCycleSeparationRefutation.singletonRival denominator 100 (source false) := by
  refine ⟨7, by decide, periodic_rival, orbitVertex false, ?_, orbit_edge false, orbit_period false⟩
  intro j
  exact ⟨(actual_guard false j).symm, Set.Icc_self _⟩

end D5.S1.Digit.Infinite.SevenCycleOriginalGraph


