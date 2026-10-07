/- GID: D5/S1/Digit/Infinite/SevenCycleCoherenceRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCoherenceRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite future separation asserted as a necessary condition for actual SCC coherence. -/

import D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
import D5.S1.Digit.Infinite.WindowCylinderPartition
import D5.S1.Words.ReturnWords.CoherentReturnPathTemplates

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleOriginalGraph

open D5.S0.Carrier (GoldenInt conj)
open D5.S1.Scale (embedding)
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open private source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private golden_data budget_bounds actual_entry source_windows shifted_source_windows shifted_source_tail
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private entry_algebra entry_bounds
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private phase_lawful
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private actual_phase actual_phase_mod actual_phase_guard actual_guard phase_state periodic_rival
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation

/-- The original construction uses twenty times a denominator of the budget coefficients. -/
private def denominator : ℕ := 20 * 244760

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
  have hzero : kappa (bitShift (source b) 0) ∈ endpoints denominator 100 := by
    change kappa (source b) ∈ _
    rw [actual_entry]
    cases b
    · exact entry_lattice.2.1
    · exact entry_lattice.1
  have hstep (i : ℕ)
      (hi : kappa (bitShift (source b) (3 * i)) ∈ endpoints denominator 100) :
      kappa (bitShift (source b) (3 * (i + 1))) ∈ endpoints denominator 100 := by
    have hs : kappa (bitShift (source b) (3 * (i + 1))) ∈ stateInterval false := by
      rw [← closed_observation_graph_realization.2.1 false]
      exact ⟨_, by simp [stateAddress], rfl⟩
    have he : inverseBranch (window (source b) i)
        (kappa (bitShift (source b) (3 * i))) =
        kappa (bitShift (source b) (3 * (i + 1))) := by
      have h := (closed_observation_graph_realization.2.2.1
        (bitShift (source b) (3 * i))).1
      simp only [shifted_source_windows, Nat.add_zero, shifted_source_tail] at h
      unfold inverseBranch
      apply (div_eq_iff hg0.ne').2
      unfold branch at h
      linarith
    rw [← he]
    exact hinv _ _ hi (by rwa [he])
  have h1 := hstep 0 hzero
  have h2 := hstep 1 h1
  have h3 := hstep 2 h2
  have h4 := hstep 3 h3
  have h5 := hstep 4 h4
  have h6 := hstep 5 h5
  have hm : kappa (bitShift (source b) (3 * j)) =
      kappa (bitShift (source b) (3 * (j % 7))) := by
    simp only [actual_phase_mod, Nat.mod_mod]
  rw [hm]
  have hr : j % 7 < 7 := Nat.mod_lt _ (by decide)
  rcases (show j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨
      j % 7 = 4 ∨ j % 7 = 5 ∨ j % 7 = 6 by omega) with h | h | h | h | h | h | h
  · simpa only [h, Nat.mul_zero] using hzero
  · simpa only [h] using h1
  · simpa only [h] using h2
  · simpa only [h] using h3
  · simpa only [h] using h4
  · simpa only [h] using h5
  · simpa only [h] using h6

/-- All original endpoint singletons are retained, with their incoming guards. -/
private noncomputable def orbitVertex (b : Bool) (j : ℕ) : Vertex denominator 100 :=
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

namespace D5.S1.Digit.Infinite.SevenCycleSourceFibres

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.SignedSeriesRange (signedValue signed_series_range v)
open private source
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
private theorem seam_tail (w : List Block) :
    ∃ N : ℕ, ∀ n, N ≤ n → (prependWord w v).val n ≠ (prependWord w v).val (n + 1) := by
  refine ⟨len w, ?_⟩
  intro n hn
  rw [D5.S1.Digit.Infinite.WindowCylinderPartition.prepend_digits,
    D5.S1.Digit.Infinite.WindowCylinderPartition.prepend_digits,
    if_neg (by omega), if_neg (by omega)]
  intro h
  have h' := Bool.eq_iff_iff.mp h
  simp only [v, decide_eq_true_eq] at h'
  omega

private theorem source_not_seam (b : Bool) (j : ℕ) :
    signedValue (bitShift (source b) (3 * j)) ∉ Set.range seam := by
  have hno (w : List Block) : bitShift (source b) (3 * j) ≠ prependWord w v := by
    intro h
    obtain ⟨N, hN⟩ := seam_tail w
    have he := hN (21 * (N + 3 * j + 1) + 5 - 3 * j) (by omega)
    rw [← h] at he
    simp only [bitShift, source] at he
    have h0 : (21 * (N + 3 * j + 1) + 5 - 3 * j + 3 * j) % 21 = 5 := by omega
    have h1 : (21 * (N + 3 * j + 1) + 5 - 3 * j + 1 + 3 * j) % 21 = 6 := by omega
    simp [h0, h1] at he
  rintro ⟨w, hw⟩
  have h := ((signed_series_fibres.1 w).2 (bitShift (source b) (3 * j))).mp hw.symm
  rcases h with h | h
  · simp only [leftStream] at h
    exact hno _ h
  · simp only [rightStream] at h
    exact hno _ h

private theorem source_fibre (b : Bool) (j : ℕ) (x : LegalDigits)
    (hx : kappa x = kappa (bitShift (source b) (3 * j))) :
    x = bitShift (source b) (3 * j) := by
  have hs : signedValue x = signedValue (bitShift (source b) (3 * j)) := by
    rw [closed_observation_graph_realization.1, closed_observation_graph_realization.1] at hx
    have ht : t ≠ 0 := ne_of_gt (inv_pos.mpr Real.goldenRatio_pos)
    exact neg_injective ((div_left_inj' (pow_ne_zero 2 ht)).mp hx)
  have hm : signedValue (bitShift (source b) (3 * j)) ∈
      Set.Icc D5.S1.Digit.Infinite.SignedSeriesRange.a
        D5.S1.Digit.Infinite.SignedSeriesRange.b := by
    rw [← signed_series_range.1]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy, hu⟩ := signed_series_fibres.2.2 _ hm (source_not_seam b j)
  exact (hu x hs).trans (hu _ rfl).symm

end D5.S1.Digit.Infinite.SevenCycleSourceFibres

namespace D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation (singletonRival separates)
open D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
open Quiver

/-- The full product of the original graphs, retaining every jointly permitted color
and every original all-containment edge, including parallel source-label pairs. -/
@[instance_reducible] noncomputable def pairedGraph (b : ℝ) (q : ℕ) (R : ℝ) :
    Quiver (Vertex q R × Vertex q R) where
  Hom a z := {lm : Label × Label // edge a.1 lm.1 z.1 ∧ edge a.2 lm.2 z.2 ∧
    ∃ c : Fin 6, permits b a.1 c ∧ permits b a.2 c}

/-- Reachability after an initial equal-label history and its first unequal-label edge. -/
def divergenceReachable (b : ℝ) (q : ℕ) (R : ℝ) (r : Vertex q R × Vertex q R) : Prop :=
  letI := pairedGraph b q R
  ∃ a u v : Vertex q R × Vertex q R,
    a.1.val.1 = false ∧ a.2.val.1 = false ∧
    ∃ stem : Path a u, (∀ lm ∈ output (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val) stem, lm.1 = lm.2) ∧
    ∃ e : u ⟶ v, e.val.1 ≠ e.val.2 ∧ Nonempty (Path v r)

/-- An actual rival belongs to a cyclic, divergence-reachable SCC whose two source
projections and ordered source-pair returns all satisfy the original synchronization law. -/
def actualCoherentRival (b : ℝ) (q : ℕ) (R : ℝ) (eta : LegalDigits) : Prop :=
  letI := pairedGraph b q R
  ∃ r : Vertex q R × Vertex q R,
    r.2.val.1 = actualGuard false eta 1 ∧
    piece r.2 = {kappa (bitShift eta 3)} ∧ divergenceReachable b q R r ∧
    Cyclic (StronglyConnectedComponent.mk r) ∧
    Coherent (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val.1) (StronglyConnectedComponent.mk r) ∧
    Coherent (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val.2) (StronglyConnectedComponent.mk r) ∧
    Coherent (fun {a z : Vertex q R × Vertex q R} (e : a ⟶ z) => e.val) (StronglyConnectedComponent.mk r)

/-- The claimed necessity of unconditional finite future separation for actual return coherence. -/
def claim : Prop :=
  ∀ (b : ℝ) (q : ℕ) (R : ℝ), 0 < b → b < lambda → endpointParameters b q R →
    ∀ eta : LegalDigits, singletonRival q R eta → actualCoherentRival b q R eta →
      separates b eta

end D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation

namespace D5.S1.Digit.Infinite.SevenCyclePairedGraph

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation
open D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
open Quiver
open private source phaseGuard phaseColor firstLabel rivalLabel lowerEntry upperEntry
  firstEntry rivalEntry feedingEntry phase budget_bounds actual_entry
  budget golden_data shifted_source_windows shifted_source_tail source_windows
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private actual_phase_mod actual_phase_guard actual_guard phase_state
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private entry_bounds uniform_colors
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private feeding_scalar phase_lawful
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open D5.S1.Digit.Infinite.SevenCycleOriginalGraph (denominator orbitVertex orbit_edge orbit_period entry_lattice original_parameters)
open private periodic_targets
  from D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open D5.S1.Digit.Infinite.SevenCycleSourceFibres (source_fibre)

local notation "PV" => (Vertex denominator 100 × Vertex denominator 100)

private theorem orbit_edge_unique (b : Bool) (j : ℕ) (l : Label)
    (u : Vertex denominator 100) (he : edge (orbitVertex b j) l u) :
    l = window (source b) j ∧ u = orbitVertex b (j + 1) := by
  have hlow : u.val.2.1 ∈ piece u := ⟨le_rfl, u.property.2.2.2.2.1⟩
  have hhigh : u.val.2.2 ∈ piece u := ⟨u.property.2.2.2.2.1, le_rfl⟩
  have hinv (z : ℝ) (hz : z ∈ piece u) :
      z = inverseBranch l (kappa (bitShift (source b) (3 * j))) := by
    obtain ⟨x, hx, rfl⟩ := he.2.2 hz
    have hx' : x = kappa (bitShift (source b) (3 * j)) := by
      simpa only [piece, orbitVertex, Set.Icc_self, Set.mem_singleton_iff] using hx
    rw [hx']
  obtain ⟨y, hy, hky⟩ := (closed_observation_graph_realization.2.1 u.val.1).symm ▸
    u.property.2.2.1
  obtain ⟨x, hx, _⟩ := closed_observation_graph_realization.2.2.2.1
    (orbitVertex b j).val.1 l u.val.1 y he.1 hy
  have hg : g ≠ 0 := by have h := golden_data.2.2.2.1; linarith
  have hscalar : kappa x = kappa (bitShift (source b) (3 * j)) := by
    rw [(closed_observation_graph_realization.2.2.1 x).1, hx.2.1, hx.2.2, hky,
      hinv _ hlow]
    unfold branch inverseBranch
    field_simp [hg]
    <;> ring
  have hxe := source_fibre b j x hscalar
  have hl : l = window (source b) j := by
    rw [hxe, shifted_source_windows, Nat.add_zero] at hx
    exact hx.2.1.symm
  have hnext : inverseBranch l (kappa (bitShift (source b) (3 * j))) =
      kappa (bitShift (source b) (3 * (j + 1))) := by
    have hrec := (closed_observation_graph_realization.2.2.1
      (bitShift (source b) (3 * j))).1
    simp only [shifted_source_windows, Nat.add_zero, shifted_source_tail] at hrec
    rw [hl]
    unfold inverseBranch
    apply (div_eq_iff hg).2
    unfold branch at hrec
    linarith
  refine ⟨hl, Subtype.ext ?_⟩
  have hs := (phase_lawful b j).2
  have hu := he.1.2
  rw [hl] at hu
  have ha := (hinv _ hlow).trans hnext
  have hb := (hinv _ hhigh).trans hnext
  exact Prod.ext (hu.trans hs.symm) (Prod.ext ha hb)

private noncomputable def orbitPair (j : ℕ) :
    PV := (orbitVertex true j, orbitVertex false j)

private noncomputable local instance : Quiver (PV) :=
  pairedGraph budget denominator 100

private theorem orbit_common_color (j : ℕ) :
    permits budget (orbitVertex true j) (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) ∧
    permits budget (orbitVertex false j) (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
  obtain ⟨p, hp, epsilon, heps, he⟩ := periodic_targets
  have point_color (b : Bool) :
      kappa (bitShift (source b) (3 * j)) ∈
        observation budget (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
    have hc := hp b ⟨j % 7, Nat.mod_lt _ (by decide)⟩
    have hd := (abs_le.mp (he b ⟨j % 7, Nat.mod_lt _ (by decide)⟩))
    rw [← actual_phase_mod] at hd
    have hs : kappa (bitShift (source b) (3 * j)) ∈ stateInterval false := by
      rw [← closed_observation_graph_realization.2.1 false]
      exact ⟨_, by simp [stateAddress], rfl⟩
    exact ⟨max_le hs.1 (by linarith [hc.1]), le_min hs.2 (by linarith [hc.2])⟩
  have h (b : Bool) :
      permits budget (orbitVertex b j) (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
    intro x hx
    have hx' : x = kappa (bitShift (source b) (3 * j)) := by
      simpa only [piece, orbitVertex, Set.Icc_self, Set.mem_singleton_iff] using hx
    rw [hx']
    exact point_color b
  exact ⟨h true, h false⟩

private noncomputable def orbit_arrow (j : ℕ) : orbitPair j ⟶ orbitPair (j + 1) :=
  ⟨(window (source true) j, window (source false) j),
    orbit_edge true j, orbit_edge false j,
    ⟨_, (orbit_common_color j).1, (orbit_common_color j).2⟩⟩

private theorem pair_arrow_unique (j : ℕ) (z : PV)
    (e : orbitPair j ⟶ z) :
    e.val = (window (source true) j, window (source false) j) ∧ z = orbitPair (j + 1) := by
  have h1 := orbit_edge_unique true j e.val.1 z.1 e.property.1
  have h2 := orbit_edge_unique false j e.val.2 z.2 e.property.2.1
  exact ⟨Prod.ext h1.1 h2.1, Prod.ext h1.2 h2.2⟩

private theorem arrow_from_orbit (a z : PV)
    (j : ℕ) (ha : a = orbitPair j) (e : a ⟶ z) :
    e.val = (window (source true) j, window (source false) j) ∧ z = orbitPair (j + 1) := by
  subst a
  exact pair_arrow_unique j z e

private theorem path_forced {α : Type} (f : Label × Label → α) (j : ℕ) {z : PV}
    (H : Path (orbitPair j) z) :
    z = orbitPair (j + H.length) ∧
    output (fun {a z : PV} (e : a ⟶ z) => f e.val) H = (List.range H.length).map
      (fun i => f (window (source true) (j + i), window (source false) (j + i))) := by
  induction H with
  | nil => simp [output]
  | @cons a z H e ih =>
    have he := arrow_from_orbit a z (j + H.length) ih.1 e
    refine ⟨?_, ?_⟩
    · simpa only [Path.length_cons, Nat.add_assoc] using he.2
    · simp only [output, Path.weight_cons, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      change output (fun {a z : PV} (e : a ⟶ z) => f e.val) H ++ [f e.val] = _
      rw [ih.2, he.1, Path.length_cons, List.range_succ, List.map_append]
      rfl

private noncomputable def orbit_segment (j : ℕ) :
    (n : ℕ) → Path (orbitPair j) (orbitPair (j + n))
  | 0 => by simpa using (Path.nil : Path (orbitPair j) (orbitPair j))
  | n + 1 => by
      simpa only [Nat.add_assoc] using (orbit_segment j n).cons (orbit_arrow (j + n))

private theorem pair_period (j : ℕ) : orbitPair (j + 7) = orbitPair j :=
  Prod.ext (orbit_period true j) (orbit_period false j)

private noncomputable def orbit_return (j : ℕ) : Path (orbitPair j) (orbitPair j) :=
  Eq.rec (motive := fun z _ => Path (orbitPair j) z) (orbit_segment j 7) (pair_period j)

private theorem return_length (j : ℕ) : (orbit_return j).length = 7 := by
  have cast_length (a b c : PV)
      (h : b = c) (H : Path a b) : (Eq.rec (motive := fun z _ => Path a z) H h).length = H.length := by
    subst c
    rfl
  exact (cast_length _ _ _ (pair_period j) (orbit_segment j 7)).trans
    (by simp [orbit_segment, Path.length])

private noncomputable def feedingVertex : Vertex denominator 100 :=
  ⟨(false, feedingEntry, feedingEntry), entry_lattice.2.2, entry_lattice.2.2,
    entry_lattice.2.2.1, entry_lattice.2.2.1, le_rfl, Or.inl rfl⟩

private noncomputable def feedingPair : PV :=
  (feedingVertex, orbitVertex false 0)

private noncomputable def feeding_arrow : feedingPair ⟶ orbitPair 1 := by
  have hg : g ≠ 0 := by have h := golden_data.2.2.2.1; linarith
  have hscalar : feedingEntry = branch nullLabel
      (kappa (bitShift (source true) (3 * 1))) := by
    rw [actual_phase_mod]
    simpa only [Nat.mod_eq_of_lt (by decide : 1 < 7), ↓reduceIte] using (show feedingEntry = branch nullLabel (phase firstEntry ⟨1, by decide⟩) from feeding_scalar.symm)
  have hleft : edge feedingVertex nullLabel (orbitVertex true 1) := by
    have hs := phase_state true 1
    rw [← actual_phase_mod] at hs
    have hinv : inverseBranch nullLabel feedingEntry =
        kappa (bitShift (source true) (3 * 1)) := by
      rw [hscalar]
      simp [inverseBranch, branch, hg]
    change lawful false nullLabel false ∧
      Set.Icc feedingEntry feedingEntry ⊆ _ ∧
      Set.Icc (kappa (bitShift (source true) (3 * 1)))
        (kappa (bitShift (source true) (3 * 1))) ⊆ _
    simp only [Set.Icc_self, Set.singleton_subset_iff]
    refine ⟨by simp [lawful, outgoing, nullLabel], ⟨_, ?_, hscalar.symm⟩,
      ⟨feedingEntry, ⟨le_rfl, le_rfl⟩, hinv⟩⟩
    simpa [orbitVertex, phaseGuard] using hs
  have hcolor : permits budget feedingVertex 2 ∧ permits budget (orbitVertex false 0) 2 := by
    have hb : 0 < budget := budget_bounds.2.2.1
    have hf := entry_bounds.2.2.2.2.2
    have hr := entry_bounds.2.2.2.2.1
    constructor
    · intro x hx
      have he : x = feedingEntry := by simpa [piece, feedingVertex] using hx
      subst x
      exact ⟨max_le entry_lattice.2.2.1.1 (by linarith [hf.1]),
        le_min entry_lattice.2.2.1.2 (by linarith [hf.2])⟩
    · intro x hx
      have he : x = rivalEntry := by
        have hx' : x = kappa (source false) := by
          simpa [piece, orbitVertex, bitShift] using hx
        exact hx'.trans (actual_entry false)
      subst x
      exact ⟨max_le entry_lattice.2.1.1.1 (by linarith [hr.1]),
        le_min entry_lattice.2.1.1.2 (by linarith [hr.2])⟩
  refine ⟨(nullLabel, nullLabel), hleft, ?_, 2, hcolor.1, hcolor.2⟩
  simpa [source_windows, rivalLabel, feedingPair, orbitPair]
    using orbit_edge false 0

private theorem no_null_window (j : ℕ) : window (source true) j ≠ nullLabel := by
  rw [source_windows]
  simp only [↓reduceIte]
  have hr : j % 7 < 7 := Nat.mod_lt _ (by decide)
  rcases (show j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨
      j % 7 = 4 ∨ j % 7 = 5 ∨ j % 7 = 6 by omega) with h | h | h | h | h | h | h
  all_goals
    simp only [h, firstLabel]
    intro he
  all_goals
    have hc := congrArg (fun l : Label => (l.val 0, l.val 1, l.val 2)) he
    norm_num [threeLabel, twoLabel, fiveLabel, nullLabel] at hc

private theorem no_return_to_head : ¬ Nonempty (Path (orbitPair 1) feedingPair) := by
  rintro ⟨H⟩
  have he := arrow_from_orbit feedingPair (orbitPair 1) (1 + H.length)
    (path_forced id 1 H).1 feeding_arrow
  apply no_null_window (1 + H.length)
  simpa only [feeding_arrow] using (congrArg Prod.fst he.1).symm

private theorem component_orbit (a : Component (StronglyConnectedComponent.mk (orbitPair 1))) :
    ∃ j : ℕ, a.val = orbitPair j := by
  obtain ⟨⟨H⟩, _⟩ := StronglyConnectedComponent.mk_eq_mk.mp a.property.symm
  by_cases hh : a.val = feedingPair
  · exact False.elim (no_return_to_head ⟨hh ▸ H⟩)
  · exact ⟨1 + H.length, (path_forced id 1 H).1⟩

private theorem inclusion_length
    (S : StronglyConnectedComponent (PV))
    {a z : Component S} (H : Path a z) :
    ((componentInclusion S).mapPath H).length = H.length := by
  exact component_inclusion_length S H

private theorem inclusion_output
    (S : StronglyConnectedComponent (PV))
    {α : Type} (f : Label × Label → α) {a z : Component S} (H : Path a z) :
    output (fun {a z : PV} (e : a ⟶ z) => f e.val)
      ((componentInclusion S).mapPath H) =
    output (componentLabel
      (fun {a z : PV} (e : a ⟶ z) => f e.val) S) H := by
  exact component_inclusion_output (fun {a z : PV} (e : a ⟶ z) => f e.val) S H

private theorem original_component_coherent :
    Coherent (fun {a z : PV} (e : a ⟶ z) => e.val.1) (StronglyConnectedComponent.mk (orbitPair 1)) ∧
    Coherent (fun {a z : PV} (e : a ⟶ z) => e.val.2) (StronglyConnectedComponent.mk (orbitPair 1)) ∧
    Coherent (fun {a z : PV} (e : a ⟶ z) => e.val) (StronglyConnectedComponent.mk (orbitPair 1)) := by
  classical
  have hfinite := (closed_observation_graph_realization.2.2.2.2.2.1
    budget denominator 100 original_parameters).2.2.1
  letI : Finite (Vertex denominator 100) := Set.finite_univ_iff.mp hfinite
  have hcy : Cyclic (StronglyConnectedComponent.mk (orbitPair 1)) := by
    let q : Component (StronglyConnectedComponent.mk (orbitPair 1)) := ⟨orbitPair 1, rfl⟩
    obtain ⟨J, hJ⟩ := liftComponentPath _ (orbit_return 1) rfl rfl
    refine ⟨q, J, ?_⟩
    have hl := congrArg Path.length hJ
    rw [inclusion_length, return_length] at hl
    omega
  have hprefix {α : Type} (f : Label × Label → α) :
      PeriodicPrefixes (fun {a z : PV} (e : a ⟶ z) => f e.val) (StronglyConnectedComponent.mk (orbitPair 1)) := by
    intro a
    obtain ⟨j, hj⟩ := component_orbit a
    rcases a with ⟨a, ha⟩
    change a = orbitPair j at hj
    subst a
    refine ⟨(fun i => f (window (source true) (j + i), window (source false) (j + i))),
      7, by decide, ?_, ?_⟩
    · intro n
      simp [source_windows, Nat.add_mod, Nat.add_assoc]
    · intro z H i hi
      let K := (componentInclusion _).mapPath H
      have hK := inclusion_output _ f H
      have hlen : K.length = H.length := inclusion_length _ H
      have hout : output (fun {a z : PV} (e : a ⟶ z) => f e.val) K =
          (List.range H.length).map
            (fun n => f (window (source true) (j + n), window (source false) (j + n))) := by
        simpa only [hlen] using (path_forced f j K).2
      rw [← hK, hout]
      simp [hi]
  have hcoherent {α : Type} (f : Label × Label → α) :
      Coherent (fun {a z : PV} (e : a ⟶ z) => f e.val) (StronglyConnectedComponent.mk (orbitPair 1)) :=
    (coherent_component_phases _ _ hcy).1.mpr
      ((coherent_component_phases _ _ hcy).2.1.mpr (hprefix f))
  exact ⟨hcoherent Prod.fst, hcoherent Prod.snd, hcoherent id⟩

private theorem actual_coherent_rival :
    actualCoherentRival budget denominator 100 (source false) := by
  classical
  have hfinite := (closed_observation_graph_realization.2.2.2.2.2.1
    budget denominator 100 original_parameters).2.2.1
  letI : Finite (Vertex denominator 100) := Set.finite_univ_iff.mp hfinite
  have hcy : Cyclic (StronglyConnectedComponent.mk (orbitPair 1)) := by
    let q : Component (StronglyConnectedComponent.mk (orbitPair 1)) := ⟨orbitPair 1, rfl⟩
    obtain ⟨J, hJ⟩ := liftComponentPath _ (orbit_return 1) rfl rfl
    refine ⟨q, J, ?_⟩
    have hl := congrArg Path.length hJ
    rw [inclusion_length, return_length] at hl
    omega
  refine ⟨orbitPair 1, ?_, Set.Icc_self _, ?_, hcy,
    original_component_coherent.1, original_component_coherent.2.1,
    original_component_coherent.2.2⟩
  · exact (actual_guard false 1).symm
  · refine ⟨orbitPair 0, orbitPair 0, orbitPair 1, rfl, rfl, Path.nil, ?_,
      orbit_arrow 0, ?_, ⟨Path.nil⟩⟩
    · simp [output]
    · intro he
      have hh := congrArg (fun l : Label => l.val 1) he
      simp [orbit_arrow, source_windows,
        firstLabel,
        rivalLabel, threeLabel, nullLabel] at hh

end D5.S1.Digit.Infinite.SevenCyclePairedGraph
