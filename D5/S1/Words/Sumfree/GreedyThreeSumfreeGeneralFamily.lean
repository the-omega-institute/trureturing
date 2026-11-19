/- GID: D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily
   generality: G
   mirror-B: D5/B/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Theorem 19 gives the full seeded greedy range and exact characteristic periodicity. -/

import D5.S1.Words.Sumfree.GreedyThreeSumfreeTwoParameter

set_option maxRecDepth 100000

/-! The full Theorem 19 family, with exact characteristic period and onset. -/

namespace D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily

open D5.S1.Words.Sumfree.GreedyThreeSumfreeTwoParameter
open D5.S1.Words.Sumfree.GreedyThreeSumfreeTwoParameter.Reuse

private def Printed (f g d z : Nat) : Prop :=
  z = f ∨ z = g ∨ z = (f + 2 * g + d - 1) - 1 ∨ z = (f + 2 * g + d - 1) ∨
    (g + d ≤ z ∧ g + d - 2 ≤ z % ((3 * f + 5 * g + 2 * d - 3)) ∧ z % ((3 * f + 5 * g + 2 * d - 3)) ≤ (f + 2 * g + d - 1) - 2)

/-- The candidate set, with the initial interval and every positive-index translate. -/
def A (f g d : Nat) : Set Nat :=
  {f, g} ∪ Set.Icc (g + d) ((f + 2 * g + d - 1)) ∪
    ⋃ t ∈ Set.Ici 1, (fun r => t * ((3 * f + 5 * g + 2 * d - 3)) + r) '' Set.Icc (g + d - 2) ((f + 2 * g + d - 1) - 2)

private def BlockCandidate (f g d z : Nat) : Prop :=
  z = f ∨ z = g ∨ (g + d ≤ z ∧ z ≤ (f + 2 * g + d - 1)) ∨
    ∃ t, 1 ≤ t ∧ t * ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2) ≤ z ∧ z ≤ t * ((3 * f + 5 * g + 2 * d - 3)) + ((f + 2 * g + d - 1) - 2)

private theorem printed_initial {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (hz : z < (3 * f + 5 * g + 2 * d - 3)) :
    Printed f g d z ↔ z = f ∨ z = g ∨ (g + d ≤ z ∧ z ≤ (f + 2 * g + d - 1)) := by
  unfold Printed
  rw [Nat.mod_eq_of_lt hz]
  omega

private theorem initial_mem {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (hz : g + d ≤ z ∧ z ≤ (f + 2 * g + d - 1)) : Printed f g d z := by
  rw [printed_initial hf hg hd (by omega)]
  exact Or.inr (Or.inr hz)

private theorem block_mem {f g d t z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ht : 1 ≤ t) (hz : t * ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2) ≤ z ∧
      z ≤ t * ((3 * f + 5 * g + 2 * d - 3)) + ((f + 2 * g + d - 1) - 2)) : Printed f g d z := by
  have hM : (3 * f + 5 * g + 2 * d - 3) ≤ t * ((3 * f + 5 * g + 2 * d - 3)) := Nat.le_mul_of_pos_left _ ht
  have heq : z = t * ((3 * f + 5 * g + 2 * d - 3)) + (z - t * ((3 * f + 5 * g + 2 * d - 3))) := by omega
  have hr : z - t * ((3 * f + 5 * g + 2 * d - 3)) < (3 * f + 5 * g + 2 * d - 3) := by omega
  have hm : z % ((3 * f + 5 * g + 2 * d - 3)) = z - t * ((3 * f + 5 * g + 2 * d - 3)) := by
    conv_lhs => rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  unfold Printed
  rw [hm]
  omega

private theorem block_candidate_eq_printed {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d) :
    BlockCandidate f g d z ↔ Printed f g d z := by
  constructor
  · rintro (rfl | rfl | hi | ⟨t, ht, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact initial_mem hf hg hd hi
    · exact block_mem hf hg hd ht hz
  · intro hz
    by_cases hlt : z < (3 * f + 5 * g + 2 * d - 3)
    · rcases (printed_initial hf hg hd hlt).mp hz with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have hdiv : 1 ≤ z / ((3 * f + 5 * g + 2 * d - 3)) := (Nat.one_le_div_iff (by omega)).mpr (by omega)
      have hmod := Nat.mod_add_div z ((3 * f + 5 * g + 2 * d - 3))
      have hbounds : g + d - 2 ≤ z % ((3 * f + 5 * g + 2 * d - 3)) ∧ z % ((3 * f + 5 * g + 2 * d - 3)) ≤ (f + 2 * g + d - 1) - 2 := by
        unfold Printed at hz
        omega
      exact Or.inr (Or.inr (Or.inr ⟨z / ((3 * f + 5 * g + 2 * d - 3)), hdiv, by
        rw [Nat.mul_comm]
        omega⟩))

private theorem candidate_eq_printed {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d) :
    A f g d z ↔ Printed f g d z := by
  change z ∈ A f g d ↔ Printed f g d z
  rw [← block_candidate_eq_printed hf hg hd]
  simp only [A, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_Icc, Set.mem_iUnion, Set.mem_Ici, Set.mem_image, BlockCandidate]
  constructor
  · rintro ((h | h) | ⟨t, ht, r, hr, rfl⟩)
    · exact h.elim Or.inl (Or.inr ∘ Or.inl)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨t, ht, by omega⟩))
  · rintro (h | h | h | ⟨t, ht, hz⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨t, ht, z - t * ((3 * f + 5 * g + 2 * d - 3)), by omega, by omega⟩

private theorem mem_candidate_eq_printed {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d) :
    z ∈ A f g d ↔ Printed f g d z := candidate_eq_printed hf hg hd

private theorem initial_gap_covered_printed {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2)
    (hz : (f + 2 * g + d - 1) < z ∧ z < ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) :
    RestrictedThreeSum (Printed f g d) z := by
  by_cases h1 : z ≤ 2 * f + 3 * g + d - 1
  · refine ⟨f, g, z - f - g, by omega, by omega, Or.inl rfl,
      Or.inr (Or.inl rfl), initial_mem hf hg hd (by omega), by omega⟩
  by_cases h2 : z ≤ 3 * f + 4 * g + 2 * d - 3
  · obtain ⟨x, y, hx, hxy, hy, he⟩ := sum_two_distinct_interval
      (L := g + d) (U := (f + 2 * g + d - 1)) (z := z - f) (by omega) (by omega)
    exact ⟨f, x, y, by omega, hxy, Or.inl rfl,
      initial_mem hf hg hd (by omega), initial_mem hf hg hd (by omega), by omega⟩
  by_cases h3 : z ≤ 2 * f + 5 * g + 2 * d - 3
  · obtain ⟨x, y, hx, hxy, hy, he⟩ := sum_two_distinct_interval
      (L := g + d) (U := (f + 2 * g + d - 1)) (z := z - g) (by omega) (by omega)
    exact ⟨g, x, y, by omega, hxy, Or.inr (Or.inl rfl),
      initial_mem hf hg hd (by omega), initial_mem hf hg hd (by omega), by omega⟩
  · obtain ⟨x, y, w, hx, hxy, hyw, hw, he⟩ := sum_three_distinct_interval
      (L := g + d) (U := (f + 2 * g + d - 1)) (z := z) (by omega) (by omega)
    exact ⟨x, y, w, hxy, hyw, initial_mem hf hg hd (by omega),
      initial_mem hf hg hd (by omega), initial_mem hf hg hd (by omega), he⟩

private theorem periodic_gap_covered_printed {f g d t z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g)
    (ht : 1 ≤ t)
    (hz : t * ((3 * f + 5 * g + 2 * d - 3)) + ((f + 2 * g + d - 1) - 2) < z ∧
      z < t * ((3 * f + 5 * g + 2 * d - 3)) + ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) :
    RestrictedThreeSum (Printed f g d) z := by
  have htM : (3 * f + 5 * g + 2 * d - 3) ≤ t * ((3 * f + 5 * g + 2 * d - 3)) := Nat.le_mul_of_pos_left _ ht
  by_cases h1 : z ≤ t * ((3 * f + 5 * g + 2 * d - 3)) + 2 * f + 3 * g + d - 3
  · refine ⟨f, g, z - f - g, by omega, by omega, Or.inl rfl,
      Or.inr (Or.inl rfl), block_mem hf hg hd ht (by omega), by omega⟩
  by_cases h2 : z ≤ t * ((3 * f + 5 * g + 2 * d - 3)) + 3 * f + 4 * g + 2 * d - 4
  · obtain ⟨x, y, hx, hx', hy, hy', he⟩ := sum_two_intervals
      (L := g + d) (U := (f + 2 * g + d - 1))
      (V := t * ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) (W := t * ((3 * f + 5 * g + 2 * d - 3)) + ((f + 2 * g + d - 1) - 2))
      (z := z - f) (by omega) (by omega) (by omega)
    exact ⟨f, x, y, by omega, by omega, Or.inl rfl,
      initial_mem hf hg hd ⟨hx,hx'⟩, block_mem hf hg hd ht ⟨hy,hy'⟩, by omega⟩
  by_cases h3 : z ≤ t * ((3 * f + 5 * g + 2 * d - 3)) + 2 * f + 5 * g + 2 * d - 4
  · obtain ⟨x, y, hx, hx', hy, hy', he⟩ := sum_two_intervals
      (L := g + d) (U := (f + 2 * g + d - 1))
      (V := t * ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) (W := t * ((3 * f + 5 * g + 2 * d - 3)) + ((f + 2 * g + d - 1) - 2))
      (z := z - g) (by omega) (by omega) (by omega)
    exact ⟨g, x, y, by omega, by omega, Or.inr (Or.inl rfl),
      initial_mem hf hg hd ⟨hx,hx'⟩, block_mem hf hg hd ht ⟨hy,hy'⟩, by omega⟩
  · obtain ⟨p, w, hp, hp', hw, hw', he⟩ := sum_two_intervals
      (L := 2 * (g + d) + 1) (U := 2 * ((f + 2 * g + d - 1)) - 1)
      (V := t * ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) (W := t * ((3 * f + 5 * g + 2 * d - 3)) + ((f + 2 * g + d - 1) - 2))
      (z := z) (by omega) (by omega) (by omega)
    obtain ⟨x, y, hx, hxy, hy, hp⟩ := sum_two_distinct_interval
      (L := g + d) (U := (f + 2 * g + d - 1)) (z := p) (by omega) ⟨hp,hp'⟩
    exact ⟨x, y, w, hxy, by omega, initial_mem hf hg hd (by omega),
      initial_mem hf hg hd (by omega), block_mem hf hg hd ht ⟨hw,hw'⟩, by omega⟩

/-- Four distinct-entry sum families cover the complete gap after the initial interval. -/
private theorem initial_gap_covered {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2)
    (hz : (f + 2 * g + d - 1) < z ∧ z < ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) :
    RestrictedThreeSum (A f g d) z := by
  simpa only [RestrictedThreeSum, candidate_eq_printed hf hg hd] using
    (initial_gap_covered_printed hf hg hd ha hex hz)

/-- Four sum families cover every gap following a positive-index periodic interval. -/
private theorem periodic_gap_covered {f g d t z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g)
    (ht : 1 ≤ t)
    (hz : t * ((3 * f + 5 * g + 2 * d - 3)) + ((f + 2 * g + d - 1) - 2) < z ∧
      z < t * ((3 * f + 5 * g + 2 * d - 3)) + ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) :
    RestrictedThreeSum (A f g d) z := by
  simpa only [RestrictedThreeSum, candidate_eq_printed hf hg hd] using
    (periodic_gap_covered_printed hf hg hd ha ht hz)

private theorem complement_covered {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2)
    (hz : g + d < z) (hn : ¬ Printed f g d z) :
    RestrictedThreeSum (Printed f g d) z := by
  by_cases h0 : z < ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)
  · have hc : RestrictedThreeSum (A f g d) z := initial_gap_covered hf hg hd ha hex ⟨by
      by_contra h
      exact hn (initial_mem hf hg hd (by omega)), h0⟩
    simpa only [RestrictedThreeSum, candidate_eq_printed hf hg hd] using hc
  · let t := (z - (g + d - 2)) / ((3 * f + 5 * g + 2 * d - 3))
    have ht : 1 ≤ t := (Nat.one_le_div_iff (by omega)).mpr (by omega)
    have he := Nat.mod_add_div (z - (g + d - 2)) ((3 * f + 5 * g + 2 * d - 3))
    have hr := Nat.mod_lt (z - (g + d - 2)) (show 0 < (3 * f + 5 * g + 2 * d - 3) by omega)
    have hlo : t * ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2) ≤ z := by
      dsimp [t]
      rw [Nat.mul_comm]
      omega
    have hhi : z < t * ((3 * f + 5 * g + 2 * d - 3)) + ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2) := by
      dsimp [t]
      rw [Nat.mul_comm]
      omega
    have hc : RestrictedThreeSum (A f g d) z := periodic_gap_covered hf hg hd ha ht ⟨by
      by_contra h
      exact hn (block_mem hf hg hd ht ⟨hlo, by omega⟩), hhi⟩
    simpa only [RestrictedThreeSum, candidate_eq_printed hf hg hd] using hc

private theorem printed_shape {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (hz : Printed f g d z) :
    z = f ∨ z = g ∨ (g + d ≤ z ∧ g + d - 2 ≤ z % ((3 * f + 5 * g + 2 * d - 3)) ∧
      z % ((3 * f + 5 * g + 2 * d - 3)) ≤ (f + 2 * g + d - 1) ∧
      (z % ((3 * f + 5 * g + 2 * d - 3)) ≤ (f + 2 * g + d - 1) - 2 ∨ z = z % ((3 * f + 5 * g + 2 * d - 3)))) := by
  rcases hz with h | h | rfl | rfl | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [Nat.mod_eq_of_lt (show (f + 2 * g + d - 1) - 1 < (3 * f + 5 * g + 2 * d - 3) by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show (f + 2 * g + d - 1) < (3 * f + 5 * g + 2 * d - 3) by omega)]
    omega
  · omega

private theorem residue_gap {f g d s : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (hs : (f + 2 * g + d - 1) - 2 < s ∧ s < ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2)) :
    s % ((3 * f + 5 * g + 2 * d - 3)) < g + d - 2 ∨ (f + 2 * g + d - 1) - 2 < s % ((3 * f + 5 * g + 2 * d - 3)) := by
  by_cases h : s < (3 * f + 5 * g + 2 * d - 3)
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : s = ((3 * f + 5 * g + 2 * d - 3)) + (s - ((3 * f + 5 * g + 2 * d - 3))) := by omega
    have hr : s - ((3 * f + 5 * g + 2 * d - 3)) < (3 * f + 5 * g + 2 * d - 3) := by omega
    conv_lhs => rw [he]
    simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hr]
    omega

-- The ordered residue cases require a larger arithmetic budget.
set_option maxHeartbeats 2000000 in
private theorem three_sum_excluded {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (hz : RestrictedThreeSum (Printed f g d) z) :
    g + d < z ∧ ¬ Printed f g d z := by
  obtain ⟨x, y, w, hxy, hyw, hx, hy, hw, rfl⟩ := hz
  have sx := printed_shape hf hg hd hx
  have sy := printed_shape hf hg hd hy
  have sw := printed_shape hf hg hd hw
  have hlo : (f + 2 * g + d - 1) < x + y + w := by omega
  have h1 : f % ((3 * f + 5 * g + 2 * d - 3)) = f := Nat.mod_eq_of_lt (by omega)
  have hgmod : g % ((3 * f + 5 * g + 2 * d - 3)) = g := Nat.mod_eq_of_lt (by omega)
  have hb : (f + 2 * g + d - 1) - 2 < x % ((3 * f + 5 * g + 2 * d - 3)) + y % ((3 * f + 5 * g + 2 * d - 3)) + w % ((3 * f + 5 * g + 2 * d - 3)) ∧
      x % ((3 * f + 5 * g + 2 * d - 3)) + y % ((3 * f + 5 * g + 2 * d - 3)) + w % ((3 * f + 5 * g + 2 * d - 3)) < ((3 * f + 5 * g + 2 * d - 3)) + (g + d - 2) := by
    rcases sx with rfl | rfl | sx <;>
      rcases sy with rfl | rfl | sy <;>
      rcases sw with rfl | rfl | sw
    all_goals simp only [h1, hgmod] at *
    all_goals omega
  have hm := residue_gap hf hg hd hb
  have he : (x + y + w) % ((3 * f + 5 * g + 2 * d - 3)) =
      (x % ((3 * f + 5 * g + 2 * d - 3)) + y % ((3 * f + 5 * g + 2 * d - 3)) + w % ((3 * f + 5 * g + 2 * d - 3))) % ((3 * f + 5 * g + 2 * d - 3)) := by
    simp [Nat.add_mod]
  constructor
  · omega
  · unfold Printed
    rw [he]
    omega

private theorem restricted_three_sum_eq_complement_printed {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) :
    RestrictedThreeSum (Printed f g d) z ↔ g + d < z ∧ ¬ Printed f g d z :=
  ⟨three_sum_excluded hf hg hd, fun ⟨hz, hn⟩ => complement_covered hf hg hd ha hex hz hn⟩

/-- The restricted triple-sum set is exactly the complement above the third seed. -/
theorem restricted_three_sum_eq_complement {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) :
    RestrictedThreeSum (A f g d) z ↔ g + d < z ∧ z ∉ A f g d := by
  simpa only [RestrictedThreeSum, candidate_eq_printed hf hg hd, mem_candidate_eq_printed hf hg hd] using
    (restricted_three_sum_eq_complement_printed (z := z) hf hg hd ha hex)


/-- Reversed literal greedy prefixes, using the existing distinct-entry test. -/
def greedyPrefix (f g d : Nat) : Nat → List Nat :=
  Nat.rec [g + d, g, f] (fun _ s => Nat.find (next_exists s) :: s)

/-- The range of the literal least-next-entry sequence. -/
def S (f g d z : Nat) : Prop := ∃ n, z ∈ greedyPrefix f g d n

private theorem greedy_prefix_invariant {f g d : Nat}
    (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) (n : Nat) :
    g + d + n ≤ (greedyPrefix f g d n).headD 0 ∧
      ∀ z, z ∈ greedyPrefix f g d n ↔
        z ≤ (greedyPrefix f g d n).headD 0 ∧ Printed f g d z := by
  induction n with
  | zero =>
    constructor
    · simp [greedyPrefix]
    · intro z
      change z ∈ [g + d, g, f] ↔ z ≤ g + d ∧ Printed f g d z
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      by_cases hz : z ≤ g + d
      · rw [printed_initial hf hg hd (by omega)]
        omega
      · constructor <;> intro h <;> omega
  | succ n ih =>
    let s := greedyPrefix f g d n
    let u := Nat.find (next_exists s)
    change g + d + n ≤ s.headD 0 ∧ ∀ z, z ∈ s ↔ z ≤ s.headD 0 ∧ Printed f g d z at ih
    have hu : s.headD 0 < u ∧ forbidden s u = false := Nat.find_spec (next_exists s)
    have hmin {v : Nat} (hv : s.headD 0 < v) (hvu : v < u) : Forbidden s v := by
      have hn := Nat.find_min (next_exists s) hvu
      have hb : forbidden s v = true := by
        cases hb : forbidden s v <;> simp_all
      exact (forbidden_correct s v).mp hb
    have hgap {v : Nat} (hv : s.headD 0 < v) (hvu : v < u) : ¬ Printed f g d v := by
      obtain ⟨x,hx,y,hy,w,hw,hxy,hyw,he⟩ := hmin hv hvu
      exact (three_sum_excluded hf hg hd
        ⟨x,y,w,hxy,hyw,((ih.2 x).mp hx).2,((ih.2 y).mp hy).2,
          ((ih.2 w).mp hw).2,he⟩).2
    have huA : Printed f g d u := by
      by_contra hn
      obtain ⟨x,y,w,hxy,hyw,hx,hy,hw,he⟩ := complement_covered hf hg hd ha hex (by omega) hn
      have hxpos : 0 < x := by
        have := printed_shape hf hg hd hx
        omega
      have hbound {v : Nat} (hv : v < u) (hvA : Printed f g d v) : v ∈ s := by
        apply (ih.2 v).mpr
        exact ⟨by by_contra h; exact hgap (by omega) hv hvA, hvA⟩
      have hb := (forbidden_correct s u).mpr
        ⟨x,hbound (by omega) hx,y,hbound (by omega) hy,w,hbound (by omega) hw,hxy,hyw,he⟩
      rw [hu.2] at hb
      contradiction
    change g + d + (n + 1) ≤ u ∧ ∀ z, z ∈ u :: s ↔ z ≤ u ∧ Printed f g d z
    constructor
    · omega
    · intro z
      rw [List.mem_cons]
      constructor
      · rintro (rfl | hz)
        · exact ⟨le_rfl, huA⟩
        · have hz' := (ih.2 z).mp hz
          exact ⟨by omega, hz'.2⟩
      · rintro ⟨hle,hz⟩
        by_cases heq : z = u
        · exact Or.inl heq
        · exact Or.inr ((ih.2 z).mpr
            ⟨by by_contra h; exact hgap (by omega) (by omega) hz, hz⟩)

/-- Theorem 19's interval formula is the range of the actual greedy rule. -/
theorem s_eq_A {f g d : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) :
    S f g d = A f g d := by
  funext z
  apply propext
  rw [candidate_eq_printed hf hg hd]
  constructor
  · rintro ⟨n,hn⟩
    exact ((greedy_prefix_invariant hf hg hd ha hex n).2 z).mp hn |>.2
  · intro hz
    have hi := greedy_prefix_invariant hf hg hd ha hex z
    exact ⟨z,(hi.2 z).mpr ⟨by omega,hz⟩⟩

/-- A characteristic period q from the integer position N. -/
def PeriodFrom (P : Nat → Prop) (q N : Nat) : Prop :=
  ∀ n, N ≤ n → (P (n + q) ↔ P n)

private theorem cyclic_interval_shift {M L U q : Nat}
    (hL : 0 < L) (hLU : L ≤ U) (hUM : U + 1 < M)
    (hs : ∀ r, r < M →
      (L ≤ (r + q) % M ∧ (r + q) % M ≤ U ↔ L ≤ r ∧ r ≤ U)) : M ∣ q := by
  have h1 := (hs L (by omega)).mpr ⟨le_rfl,hLU⟩
  have h0 : ¬ (L ≤ (L - 1 + q) % M ∧ (L - 1 + q) % M ≤ U) := by
    intro h
    have := (hs (L - 1) (by omega)).mp h
    omega
  let k := q % M
  have hk : k < M := Nat.mod_lt _ (by omega)
  have e1 : (L + q) % M = (L + k) % M := by simp [k,Nat.add_mod]
  have e0 : (L - 1 + q) % M = (L - 1 + k) % M := by simp [k,Nat.add_mod]
  rw [e1] at h1
  rw [e0] at h0
  have hk0 : k = 0 := by
    by_cases hc : L + k < M
    · rw [Nat.mod_eq_of_lt hc] at h1
      rw [Nat.mod_eq_of_lt (show L - 1 + k < M by omega)] at h0
      omega
    · have r1 : (L + k) % M = L + k - M := by
        have he : L + k = M + (L + k - M) := by omega
        conv_lhs => rw [he]
        simp [Nat.add_mod,Nat.mod_eq_of_lt (show L + k - M < M by omega)]
      rw [r1] at h1
      by_cases hc0 : L - 1 + k < M
      · rw [Nat.mod_eq_of_lt hc0] at h0
        omega
      · have r0 : (L - 1 + k) % M = L - 1 + k - M := by
          have he : L - 1 + k = M + (L - 1 + k - M) := by omega
          conv_lhs => rw [he]
          simp [Nat.add_mod,Nat.mod_eq_of_lt (show L - 1 + k - M < M by omega)]
        rw [r0] at h0
        omega
  exact Nat.dvd_of_mod_eq_zero hk0

private theorem printed_tail {f g d n : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (hn : f + 2 * g + d - 1 < n) :
    Printed f g d n ↔
      g + d - 2 ≤ n % (3 * f + 5 * g + 2 * d - 3) ∧ n % (3 * f + 5 * g + 2 * d - 3) ≤ f + 2 * g + d - 1 - 2 := by
  unfold Printed
  omega

private theorem periods_divisible {f g d q N : Nat}
    (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (hp : PeriodFrom (Printed f g d) q N) : (3 * f + 5 * g + 2 * d - 3) ∣ q := by
  let M := 3 * f + 5 * g + 2 * d - 3
  have hM : 0 < M := by dsimp [M]; omega
  have hUM : f + 2 * g + d - 1 - 2 + 1 < M := by dsimp [M]; omega
  apply cyclic_interval_shift (M := M) (L := g + d - 2) (U := f + 2 * g + d - 1 - 2)
    (by omega) (by omega) hUM
  intro r hr
  let k := N + (f + 2 * g + d - 1) + M + 1
  have hmul : k ≤ k * M := Nat.le_mul_of_pos_right _ hM
  have hkN : N + (f + 2 * g + d - 1) + 1 ≤ k := by dsimp [k]; omega
  have hn : f + 2 * g + d - 1 < k * M + r := by omega
  have hnq : f + 2 * g + d - 1 < k * M + r + q := by omega
  have hN : N ≤ k * M + r := by omega
  have h := hp (k * M + r) hN
  rw [printed_tail hf hg hd hnq,printed_tail hf hg hd hn] at h
  have e : (k * M + r) % M = r := by simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
  have eq : (k * M + r + q) % M = (r + q) % M := by simp [Nat.add_mod]
  change (g + d - 2 ≤ (k * M + r + q) % M ∧ (k * M + r + q) % M ≤ f + 2 * g + d - 1 - 2 ↔
    g + d - 2 ≤ (k * M + r) % M ∧ (k * M + r) % M ≤ f + 2 * g + d - 1 - 2) at h
  rwa [eq,e] at h

private theorem onset_obstruction {f g d q : Nat}
    (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d) (hq : 0 < q)
    (hdiv : (3 * f + 5 * g + 2 * d - 3) ∣ q) :
    Printed f g d (f + 2 * g + d - 1) ∧ ¬ Printed f g d (f + 2 * g + d - 1 + q) := by
  have hmem : Printed f g d (f + 2 * g + d - 1) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨hmem, ?_⟩
  rw [printed_tail hf hg hd (by omega)]
  have hm : (f + 2 * g + d - 1 + q) % (3 * f + 5 * g + 2 * d - 3) = f + 2 * g + d - 1 := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero,
      Nat.mod_eq_of_lt (show f + 2 * g + d - 1 < 3 * f + 5 * g + 2 * d - 3 by omega),
      Nat.mod_eq_of_lt (show f + 2 * g + d - 1 < 3 * f + 5 * g + 2 * d - 3 by omega)]
  rw [hm]
  omega

/-- Exact positive eventual characteristic periods and their earliest integer onset.
N counts positive integer positions before periodicity, not sequence entries. -/
theorem characteristic_periods {f g d : Nat}
    (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d)
    (ha : d + 1 ≤ f + g) (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) (q N : Nat) (hq : 0 < q) :
    PeriodFrom (S f g d) q (N + 1) ↔
      (3 * f + 5 * g + 2 * d - 3) ∣ q ∧ f + 2 * g + d - 1 ≤ N := by
  have hs := s_eq_A hf hg hd ha hex
  have he : S f g d = Printed f g d := by
    funext z
    apply propext
    rw [hs]
    exact candidate_eq_printed hf hg hd
  rw [he]
  constructor
  · intro hp
    have hdiv := periods_divisible hf hg hd hp
    refine ⟨hdiv, ?_⟩
    have hb := onset_obstruction hf hg hd hq hdiv
    by_contra hn
    exact hb.2 ((hp (f + 2 * g + d - 1) (by omega)).mpr hb.1)
  · rintro ⟨hdiv,hN⟩ n hn
    rw [printed_tail hf hg hd (by omega),printed_tail hf hg hd (by omega)]
    have hmod : (n + q) % (3 * f + 5 * g + 2 * d - 3) = n % (3 * f + 5 * g + 2 * d - 3) := by
      simp [Nat.add_mod,Nat.mod_eq_zero_of_dvd hdiv]
    rw [hmod]

#print axioms restricted_three_sum_eq_complement
#print axioms s_eq_A
#print axioms characteristic_periods

end D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
