/- GID: D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter
   generality: G
   mirror-B: D5/B/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Greedy three-sumfree membership has a universal two-parameter periodic formula. -/

import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Lattice

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace D5.S1.Words.Sumfree.GreedyThreeSumfreeTwoParameter

private def Printed (g d z : Nat) : Prop :=
  z = 1 ∨ z = g ∨ z = 2*g+d-1 ∨ z = 2*g+d ∨
    (g+d ≤ z ∧ g+d-2 ≤ z % (5*g+2*d) ∧ z % (5*g+2*d) ≤ 2*g+d-2)

private instance printedDecidable (g d z : Nat) : Decidable (Printed g d z) := inferInstanceAs (Decidable (_ ∨ _))

def RestrictedThreeSum (A : Nat → Prop) (z : Nat) : Prop :=
  ∃ x y w, x < y ∧ y < w ∧ A x ∧ A y ∧ A w ∧ x+y+w = z

/-- The candidate set, with the initial interval and every positive-index translate. -/
def A (g d : Nat) : Set Nat :=
  {1, g} ∪ Set.Icc (g+d) (2*g+d) ∪
    ⋃ t ∈ Set.Ici 1, (fun r => t*(5*g+2*d)+r) '' Set.Icc (g+d-2) (2*g+d-2)

private def BlockCandidate (g d z : Nat) : Prop :=
  z = 1 ∨ z = g ∨ (g+d ≤ z ∧ z ≤ 2*g+d) ∨
    ∃ t, 1 ≤ t ∧ t*(5*g+2*d)+(g+d-2) ≤ z ∧ z ≤ t*(5*g+2*d)+(2*g+d-2)

private theorem printed_initial {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : z < 5*g+2*d) :
    Printed g d z ↔ z = 1 ∨ z = g ∨ (g+d ≤ z ∧ z ≤ 2*g+d) := by
  unfold Printed
  rw [Nat.mod_eq_of_lt hz]
  omega

private theorem initial_mem {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : g+d ≤ z ∧ z ≤ 2*g+d) : Printed g d z := by
  rw [printed_initial hd hg (by omega)]
  exact Or.inr (Or.inr hz)

private theorem block_mem {g d t z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (ht : 1 ≤ t) (hz : t*(5*g+2*d)+(g+d-2) ≤ z ∧
      z ≤ t*(5*g+2*d)+(2*g+d-2)) : Printed g d z := by
  have hM : 5*g+2*d ≤ t*(5*g+2*d) := Nat.le_mul_of_pos_left _ ht
  have heq : z = t*(5*g+2*d) + (z-t*(5*g+2*d)) := by omega
  have hr : z-t*(5*g+2*d) < 5*g+2*d := by omega
  have hm : z % (5*g+2*d) = z-t*(5*g+2*d) := by
    conv_lhs => rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  unfold Printed
  rw [hm]
  omega

private theorem block_candidate_eq_printed {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    BlockCandidate g d z ↔ Printed g d z := by
  constructor
  · rintro (rfl | rfl | hi | ⟨t, ht, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact initial_mem hd hg hi
    · exact block_mem hd hg ht hz
  · intro hz
    by_cases hlt : z < 5*g+2*d
    · rcases (printed_initial hd hg hlt).mp hz with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have hdiv : 1 ≤ z / (5*g+2*d) := (Nat.one_le_div_iff (by omega)).mpr (by omega)
      have hmod := Nat.mod_add_div z (5*g+2*d)
      have hbounds : g+d-2 ≤ z % (5*g+2*d) ∧ z % (5*g+2*d) ≤ 2*g+d-2 := by
        unfold Printed at hz
        omega
      exact Or.inr (Or.inr (Or.inr ⟨z / (5*g+2*d), hdiv, by
        rw [Nat.mul_comm]
        omega⟩))

private theorem candidate_eq_printed {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    A g d z ↔ Printed g d z := by
  change z ∈ A g d ↔ Printed g d z
  rw [← block_candidate_eq_printed hd hg]
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
    · exact Or.inr ⟨t, ht, z-t*(5*g+2*d), by omega, by omega⟩

private theorem mem_candidate_eq_printed {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    z ∈ A g d ↔ Printed g d z := candidate_eq_printed hd hg

private theorem sum_two_intervals {L U V W z : Nat} (hLU : L ≤ U) (hVW : V ≤ W)
    (hz : L+V ≤ z ∧ z ≤ U+W) :
    ∃ x y, L ≤ x ∧ x ≤ U ∧ V ≤ y ∧ y ≤ W ∧ x+y = z := by
  have hz' : z ∈ Set.Icc (L+V) (U+W) := hz
  rw [← Set.Icc_add_Icc hLU hVW] at hz'
  obtain ⟨x, hx, y, hy, hxy⟩ := hz'
  exact ⟨x, y, hx.1, hx.2, hy.1, hy.2, hxy⟩

private theorem sum_two_distinct_interval {L U z : Nat} (_hLU : L < U)
    (hz : 2*L+1 ≤ z ∧ z ≤ 2*U-1) :
    ∃ x y, L ≤ x ∧ x < y ∧ y ≤ U ∧ x+y = z := by
  by_cases h : z ≤ L+U
  · exact ⟨L, z-L, by omega⟩
  · exact ⟨z-U, U, by omega⟩

private theorem sum_three_distinct_interval {L U z : Nat} (hLU : L+2 ≤ U)
    (hz : 3*L+3 ≤ z ∧ z ≤ 3*U-3) :
    ∃ x y w, L ≤ x ∧ x < y ∧ y < w ∧ w ≤ U ∧ x+y+w = z := by
  by_cases h : z ≤ L+2*U-1
  · obtain ⟨y, w, hy, hyw, hw, he⟩ := sum_two_distinct_interval
      (L := L+1) (U := U) (z := z-L) (by omega) (by omega)
    exact ⟨L, y, w, by omega⟩
  · obtain ⟨x, y, hx, hxy, hy, he⟩ := sum_two_distinct_interval
      (L := L) (U := U-1) (z := z-U) (by omega) (by omega)
    exact ⟨x, y, U, by omega⟩

private theorem initial_gap_covered_printed {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : 2*g+d < z ∧ z < (5*g+2*d)+(g+d-2)) :
    RestrictedThreeSum (Printed g d) z := by
  by_cases h1 : z ≤ 3*g+d+1
  · refine ⟨1, g, z-1-g, by omega, by omega, Or.inl rfl,
      Or.inr (Or.inl rfl), initial_mem hd hg (by omega), by omega⟩
  by_cases h2 : z ≤ 4*g+2*d
  · obtain ⟨x, y, hx, hxy, hy, he⟩ := sum_two_distinct_interval
      (L := g+d) (U := 2*g+d) (z := z-1) (by omega) (by omega)
    exact ⟨1, x, y, by omega, hxy, Or.inl rfl,
      initial_mem hd hg (by omega), initial_mem hd hg (by omega), by omega⟩
  by_cases h3 : z ≤ 5*g+2*d-1
  · obtain ⟨x, y, hx, hxy, hy, he⟩ := sum_two_distinct_interval
      (L := g+d) (U := 2*g+d) (z := z-g) (by omega) (by omega)
    exact ⟨g, x, y, by omega, hxy, Or.inr (Or.inl rfl),
      initial_mem hd hg (by omega), initial_mem hd hg (by omega), by omega⟩
  · obtain ⟨x, y, w, hx, hxy, hyw, hw, he⟩ := sum_three_distinct_interval
      (L := g+d) (U := 2*g+d) (z := z) (by omega) (by omega)
    exact ⟨x, y, w, hxy, hyw, initial_mem hd hg (by omega),
      initial_mem hd hg (by omega), initial_mem hd hg (by omega), he⟩

private theorem periodic_gap_covered_printed {g d t z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (ht : 1 ≤ t)
    (hz : t*(5*g+2*d)+(2*g+d-2) < z ∧
      z < t*(5*g+2*d)+(5*g+2*d)+(g+d-2)) :
    RestrictedThreeSum (Printed g d) z := by
  have htM : 5*g+2*d ≤ t*(5*g+2*d) := Nat.le_mul_of_pos_left _ ht
  by_cases h1 : z ≤ t*(5*g+2*d)+3*g+d-1
  · refine ⟨1, g, z-1-g, by omega, by omega, Or.inl rfl,
      Or.inr (Or.inl rfl), block_mem hd hg ht (by omega), by omega⟩
  by_cases h2 : z ≤ t*(5*g+2*d)+4*g+2*d-1
  · obtain ⟨x, y, hx, hx', hy, hy', he⟩ := sum_two_intervals
      (L := g+d) (U := 2*g+d)
      (V := t*(5*g+2*d)+(g+d-2)) (W := t*(5*g+2*d)+(2*g+d-2))
      (z := z-1) (by omega) (by omega) (by omega)
    exact ⟨1, x, y, by omega, by omega, Or.inl rfl,
      initial_mem hd hg ⟨hx,hx'⟩, block_mem hd hg ht ⟨hy,hy'⟩, by omega⟩
  by_cases h3 : z ≤ t*(5*g+2*d)+5*g+2*d-2
  · obtain ⟨x, y, hx, hx', hy, hy', he⟩ := sum_two_intervals
      (L := g+d) (U := 2*g+d)
      (V := t*(5*g+2*d)+(g+d-2)) (W := t*(5*g+2*d)+(2*g+d-2))
      (z := z-g) (by omega) (by omega) (by omega)
    exact ⟨g, x, y, by omega, by omega, Or.inr (Or.inl rfl),
      initial_mem hd hg ⟨hx,hx'⟩, block_mem hd hg ht ⟨hy,hy'⟩, by omega⟩
  · obtain ⟨p, w, hp, hp', hw, hw', he⟩ := sum_two_intervals
      (L := 2*(g+d)+1) (U := 2*(2*g+d)-1)
      (V := t*(5*g+2*d)+(g+d-2)) (W := t*(5*g+2*d)+(2*g+d-2))
      (z := z) (by omega) (by omega) (by omega)
    obtain ⟨x, y, hx, hxy, hy, hp⟩ := sum_two_distinct_interval
      (L := g+d) (U := 2*g+d) (z := p) (by omega) ⟨hp,hp'⟩
    exact ⟨x, y, w, hxy, by omega, initial_mem hd hg (by omega),
      initial_mem hd hg (by omega), block_mem hd hg ht ⟨hw,hw'⟩, by omega⟩

/-- Four distinct-entry sum families cover the complete gap after the initial interval. -/
theorem initial_gap_covered {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : 2*g+d < z ∧ z < (5*g+2*d)+(g+d-2)) :
    RestrictedThreeSum (A g d) z := by
  simpa only [RestrictedThreeSum, candidate_eq_printed hd hg] using
    (initial_gap_covered_printed hd hg hz)

/-- Four sum families cover every gap following a positive-index periodic interval. -/
theorem periodic_gap_covered {g d t z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (ht : 1 ≤ t)
    (hz : t*(5*g+2*d)+(2*g+d-2) < z ∧
      z < t*(5*g+2*d)+(5*g+2*d)+(g+d-2)) :
    RestrictedThreeSum (A g d) z := by
  simpa only [RestrictedThreeSum, candidate_eq_printed hd hg] using
    (periodic_gap_covered_printed hd hg ht hz)

private theorem complement_covered {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : g+d < z) (hn : ¬ Printed g d z) :
    RestrictedThreeSum (Printed g d) z := by
  by_cases h0 : z < (5*g+2*d)+(g+d-2)
  · have hc : RestrictedThreeSum (A g d) z := initial_gap_covered hd hg ⟨by
      by_contra h
      exact hn (initial_mem hd hg (by omega)), h0⟩
    simpa only [RestrictedThreeSum, candidate_eq_printed hd hg] using hc
  · let t := (z-(g+d-2)) / (5*g+2*d)
    have ht : 1 ≤ t := (Nat.one_le_div_iff (by omega)).mpr (by omega)
    have he := Nat.mod_add_div (z-(g+d-2)) (5*g+2*d)
    have hr := Nat.mod_lt (z-(g+d-2)) (show 0 < 5*g+2*d by omega)
    have hlo : t*(5*g+2*d)+(g+d-2) ≤ z := by
      dsimp [t]
      rw [Nat.mul_comm]
      omega
    have hhi : z < t*(5*g+2*d)+(5*g+2*d)+(g+d-2) := by
      dsimp [t]
      rw [Nat.mul_comm]
      omega
    have hc : RestrictedThreeSum (A g d) z := periodic_gap_covered hd hg ht ⟨by
      by_contra h
      exact hn (block_mem hd hg ht ⟨hlo, by omega⟩), hhi⟩
    simpa only [RestrictedThreeSum, candidate_eq_printed hd hg] using hc

private theorem printed_shape {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : Printed g d z) :
    z = 1 ∨ z = g ∨ (g+d ≤ z ∧ g+d-2 ≤ z % (5*g+2*d) ∧
      z % (5*g+2*d) ≤ 2*g+d ∧
      (z % (5*g+2*d) ≤ 2*g+d-2 ∨ z = z % (5*g+2*d))) := by
  rcases hz with h | h | rfl | rfl | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [Nat.mod_eq_of_lt (show 2*g+d-1 < 5*g+2*d by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show 2*g+d < 5*g+2*d by omega)]
    omega
  · omega

private theorem residue_gap {g d s : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hs : 2*g+d-2 < s ∧ s < (5*g+2*d)+(g+d-2)) :
    s % (5*g+2*d) < g+d-2 ∨ 2*g+d-2 < s % (5*g+2*d) := by
  by_cases h : s < 5*g+2*d
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : s = (5*g+2*d)+(s-(5*g+2*d)) := by omega
    have hr : s-(5*g+2*d) < 5*g+2*d := by omega
    conv_lhs => rw [he]
    simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hr]
    omega

private theorem three_sum_excluded {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : RestrictedThreeSum (Printed g d) z) :
    g+d < z ∧ ¬ Printed g d z := by
  obtain ⟨x, y, w, hxy, hyw, hx, hy, hw, rfl⟩ := hz
  have sx := printed_shape hd hg hx
  have sy := printed_shape hd hg hy
  have sw := printed_shape hd hg hw
  have hlo : 2*g+d < x+y+w := by omega
  have h1 : 1 % (5*g+2*d) = 1 := Nat.mod_eq_of_lt (by omega)
  have hgmod : g % (5*g+2*d) = g := Nat.mod_eq_of_lt (by omega)
  have hb : 2*g+d-2 < x%(5*g+2*d)+y%(5*g+2*d)+w%(5*g+2*d) ∧
      x%(5*g+2*d)+y%(5*g+2*d)+w%(5*g+2*d) < (5*g+2*d)+(g+d-2) := by
    rcases sx with rfl | rfl | sx <;>
      rcases sy with rfl | rfl | sy <;>
      rcases sw with rfl | rfl | sw
    all_goals simp only [h1, hgmod] at *
    all_goals omega
  have hm := residue_gap hd hg hb
  have he : (x+y+w)%(5*g+2*d) =
      (x%(5*g+2*d)+y%(5*g+2*d)+w%(5*g+2*d))%(5*g+2*d) := by
    simp [Nat.add_mod]
  constructor
  · omega
  · unfold Printed
    rw [he]
    omega

private theorem restricted_three_sum_eq_complement_printed {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    RestrictedThreeSum (Printed g d) z ↔ g+d < z ∧ ¬ Printed g d z :=
  ⟨three_sum_excluded hd hg, fun ⟨hz, hn⟩ => complement_covered hd hg hz hn⟩

/-- The restricted triple-sum set is exactly the complement above the third seed. -/
theorem restricted_three_sum_eq_complement {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    RestrictedThreeSum (A g d) z ↔ g+d < z ∧ z ∉ A g d := by
  simpa only [RestrictedThreeSum, candidate_eq_printed hd hg, mem_candidate_eq_printed hd hg] using
    (restricted_three_sum_eq_complement_printed (z := z) hd hg)

private def EarlierThreeSum (P : Nat → Prop) (n : Nat) : Prop :=
  ∃ x y w, x < y ∧ y < w ∧ w < n ∧ P x ∧ P y ∧ P w ∧ x+y+w = n

private def IsGreedy (g d : Nat) (P : Nat → Prop) : Prop :=
  (∀ n, n ≤ g+d → (P n ↔ n = 1 ∨ n = g ∨ n = g+d)) ∧
    ∀ n, g+d < n → (P n ↔ ¬ EarlierThreeSum P n)

private def Forbidden (s : List Nat) (n : Nat) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, ∃ w ∈ s, x < y ∧ y < w ∧ x+y+w = n

private def forbidden (s : List Nat) (n : Nat) : Bool :=
  s.any fun x => s.any fun y => s.any fun w => decide (x < y ∧ y < w ∧ x+y+w = n)

private theorem forbidden_correct (s : List Nat) (n : Nat) :
    forbidden s n = true ↔ Forbidden s n := by
  simp [forbidden,Forbidden,List.any_eq_true]

/-- Scan integers in order, retaining precisely the seeds until the third seed,
then admitting an integer exactly when no three distinct retained entries sum to it. -/
private def scan (g d : Nat) : Nat → List Nat
  | 0 => []
  | n+1 =>
    let s := scan g d n
    if n ≤ g+d then
      if n = 1 ∨ n = g ∨ n = g+d then n :: s else s
    else if forbidden s n then s else n :: s

private def ScanS (g d n : Nat) : Prop := n ∈ scan g d (n+1)

private instance scanDecidable (g d n : Nat) : Decidable (ScanS g d n) := inferInstanceAs (Decidable (_ ∈ _))

private theorem mem_scan_lt {g d n z : Nat} (hz : z ∈ scan g d n) : z < n := by
  induction n with
  | zero => simp [scan] at hz
  | succ n ih =>
    simp only [scan] at hz
    split_ifs at hz with h h' h'
    · rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact Nat.lt_succ_of_lt (ih hz)
    · exact Nat.lt_succ_of_lt (ih hz)
    · exact Nat.lt_succ_of_lt (ih hz)
    · rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact Nat.lt_succ_of_lt (ih hz)

private theorem mem_scan_before {g d n z : Nat} (hz : z < n) :
    z ∈ scan g d (n+1) ↔ z ∈ scan g d n := by
  simp only [scan]
  split_ifs <;> simp [show z ≠ n by omega]

private theorem mem_scan_iff_scan {g d n z : Nat} (hz : z < n) :
    z ∈ scan g d n ↔ ScanS g d z := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : z < n
    · rw [mem_scan_before h, ih h]
    · have : z = n := by omega
      subst z
      rfl

private theorem forbidden_iff_earlier {g d n : Nat} :
    Forbidden (scan g d n) n ↔ EarlierThreeSum (ScanS g d) n := by
  constructor
  · rintro ⟨x,hx,y,hy,w,hw,hxy,hyw,he⟩
    exact ⟨x,y,w,hxy,hyw,mem_scan_lt hw,
      (mem_scan_iff_scan (mem_scan_lt hx)).mp hx,
      (mem_scan_iff_scan (mem_scan_lt hy)).mp hy,
      (mem_scan_iff_scan (mem_scan_lt hw)).mp hw,he⟩
  · rintro ⟨x,y,w,hxy,hyw,hwn,hx,hy,hw,he⟩
    exact ⟨x,(mem_scan_iff_scan (by omega)).mpr hx,
      y,(mem_scan_iff_scan (by omega)).mpr hy,
      w,(mem_scan_iff_scan hwn).mpr hw,hxy,hyw,he⟩

private theorem scan_isGreedy (g d : Nat) : IsGreedy g d (ScanS g d) := by
  constructor
  · intro n hn
    have hnot : n ∉ scan g d n := fun h => Nat.lt_irrefl n (mem_scan_lt h)
    simp only [ScanS,scan,if_pos hn]
    by_cases h : n = 1 ∨ n = g ∨ n = g+d <;> simp [h,hnot]
  · intro n hn
    have hnot : n ∉ scan g d n := fun h => Nat.lt_irrefl n (mem_scan_lt h)
    rw [← forbidden_iff_earlier,← forbidden_correct]
    simp only [ScanS,scan,if_neg (show ¬ n ≤ g+d by omega)]
    by_cases h : forbidden (scan g d n) n = true <;> simp [h,hnot]

private theorem greedy_unique {g d : Nat} {P Q : Nat → Prop}
    (hP : IsGreedy g d P) (hQ : IsGreedy g d Q) : ∀ n, P n ↔ Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ g+d
    · exact (hP.1 n hn).trans (hQ.1 n hn).symm
    · rw [hP.2 n (by omega),hQ.2 n (by omega)]
      apply not_congr
      constructor
      · rintro ⟨x,y,w,hxy,hyw,hwn,hx,hy,hw,he⟩
        exact ⟨x,y,w,hxy,hyw,hwn,(ih x (by omega)).mp hx,
          (ih y (by omega)).mp hy,(ih w hwn).mp hw,he⟩
      · rintro ⟨x,y,w,hxy,hyw,hwn,hx,hy,hw,he⟩
        exact ⟨x,y,w,hxy,hyw,hwn,(ih x (by omega)).mpr hx,
          (ih y (by omega)).mpr hy,(ih w hwn).mpr hw,he⟩

private theorem printed_positive {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (hz : Printed g d z) : 0 < z := by
  have := printed_shape hd hg hz
  omega

private theorem earlier_iff_restricted {g d n : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    EarlierThreeSum (Printed g d) n ↔ RestrictedThreeSum (Printed g d) n := by
  constructor
  · rintro ⟨x,y,w,hxy,hyw,_,hx,hy,hw,he⟩
    exact ⟨x,y,w,hxy,hyw,hx,hy,hw,he⟩
  · rintro ⟨x,y,w,hxy,hyw,hx,hy,hw,he⟩
    have := printed_positive hd hg hx
    exact ⟨x,y,w,hxy,hyw,by omega,hx,hy,hw,he⟩

private theorem printed_isGreedy {g d : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    IsGreedy g d (Printed g d) := by
  constructor
  · intro n hn
    rw [printed_initial hd hg (by omega)]
    omega
  · intro n hn
    have hc : RestrictedThreeSum (Printed g d) n ↔ g+d < n ∧ ¬ Printed g d n := by
      simpa only [RestrictedThreeSum, candidate_eq_printed hd hg,
        mem_candidate_eq_printed hd hg] using
        (restricted_three_sum_eq_complement (z := n) hd hg)
    rw [earlier_iff_restricted hd hg, hc]
    simp [hn]

/-- Conjecture 17 of Bosma et al., JIS 28 (2025), Article 25.3.8, as printed. -/
private theorem scan_conjecture17 {g d : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) (z : Nat) :
    ScanS g d z ↔ z = 1 ∨ z = g ∨ z = 2*g+d-1 ∨ z = 2*g+d ∨
      (g+d ≤ z ∧ g+d-2 ≤ z % (5*g+2*d) ∧ z % (5*g+2*d) ≤ 2*g+d-2) :=
  greedy_unique (scan_isGreedy g d) (printed_isGreedy hd hg) z

private theorem next_exists (s : List Nat) :
    ∃ n, s.headD 0 < n ∧ forbidden s n = false := by
  refine ⟨3*s.sum+s.headD 0+1, by omega, ?_⟩
  rw [Bool.eq_false_iff]
  intro hf
  obtain ⟨x, hx, y, hy, w, hw, _, _, he⟩ := (forbidden_correct s _).mp hf
  have := List.le_sum_of_mem hx
  have := List.le_sum_of_mem hy
  have := List.le_sum_of_mem hw
  omega

/-- Reversed prefixes of the literal greedy sequence: start with the three seeds,
then prepend the least larger integer not a sum of three distinct earlier entries. -/
def greedyPrefix (g d : Nat) : Nat → List Nat :=
  Nat.rec [g+d, g, 1] (fun _ s => Nat.find (next_exists s) :: s)

/-- Membership in the greedy sequence generated by the least-next-entry rule. -/
def S (g d z : Nat) : Prop := ∃ n, z ∈ greedyPrefix g d n

private theorem greedy_prefix_invariant {g d : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g)
    (n : Nat) :
    g+d+n ≤ (greedyPrefix g d n).headD 0 ∧
      ∀ z, z ∈ greedyPrefix g d n ↔
        z ≤ (greedyPrefix g d n).headD 0 ∧ ScanS g d z := by
  induction n with
  | zero =>
    constructor
    · simp [greedyPrefix]
    · intro z
      change z ∈ [g+d, g, 1] ↔ z ≤ g+d ∧ ScanS g d z
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro hz
        have hle : z ≤ g+d := by omega
        exact ⟨hle, ((scan_isGreedy g d).1 z hle).mpr (by omega)⟩
      · rintro ⟨hle, hz⟩
        have := ((scan_isGreedy g d).1 z hle).mp hz
        omega
  | succ n ih =>
    let s := greedyPrefix g d n
    let u := Nat.find (next_exists s)
    change g+d+n ≤ s.headD 0 ∧ ∀ z, z ∈ s ↔ z ≤ s.headD 0 ∧ ScanS g d z at ih
    have hu : s.headD 0 < u ∧ forbidden s u = false := Nat.find_spec (next_exists s)
    have hmin {v : Nat} (hv : s.headD 0 < v) (hvu : v < u) : Forbidden s v := by
      have hn := Nat.find_min (next_exists s) hvu
      have hb : forbidden s v = true := by
        cases hb : forbidden s v <;> simp_all
      exact (forbidden_correct s v).mp hb
    have hgap {v : Nat} (hv : s.headD 0 < v) (hvu : v < u) : ¬ ScanS g d v := by
      intro hS
      obtain ⟨x, hx, y, hy, w, hw, hxy, hyw, he⟩ := hmin hv hvu
      have hx' := (ih.2 x).mp hx
      have hy' := (ih.2 y).mp hy
      have hw' := (ih.2 w).mp hw
      exact ((scan_isGreedy g d).2 v (by omega)).mp hS
        ⟨x,y,w,hxy,hyw,by omega,hx'.2,hy'.2,hw'.2,he⟩
    have huS : ScanS g d u := by
      apply ((scan_isGreedy g d).2 u (by omega)).mpr
      rintro ⟨x,y,w,hxy,hyw,hwu,hx,hy,hw,he⟩
      have hbound {v : Nat} (hv : v < u) (hS : ScanS g d v) : v ∈ s := by
        apply (ih.2 v).mpr
        exact ⟨by by_contra h; exact hgap (by omega) hv hS, hS⟩
      have hf := (forbidden_correct s u).mpr
        ⟨x,hbound (by omega) hx,y,hbound (by omega) hy,w,hbound hwu hw,hxy,hyw,he⟩
      rw [hu.2] at hf
      contradiction
    change g+d+(n+1) ≤ u ∧ ∀ z, z ∈ u :: s ↔ z ≤ u ∧ ScanS g d z
    constructor
    · omega
    · intro z
      rw [List.mem_cons]
      constructor
      · rintro (rfl | hz)
        · exact ⟨le_rfl, huS⟩
        · have hz' := (ih.2 z).mp hz
          exact ⟨by omega, hz'.2⟩
      · rintro ⟨hle, hz⟩
        by_cases heq : z = u
        · exact Or.inl heq
        · right
          apply (ih.2 z).mpr
          exact ⟨by by_contra h; exact hgap (by omega) (by omega) hz, hz⟩

private theorem greedy_membership_eq_scan {g d z : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) :
    S g d z ↔ ScanS g d z := by
  constructor
  · rintro ⟨n, hn⟩
    exact ((greedy_prefix_invariant hd hg n).2 z).mp hn |>.2
  · intro hz
    have hi := greedy_prefix_invariant hd hg z
    exact ⟨z, (hi.2 z).mpr ⟨by omega, hz⟩⟩

/-- The full printed two-parameter characterization of greedy three-sumfree membership. -/
theorem conjecture17 {g d : Nat} (hd : 2 ≤ d) (hg : d+1 ≤ g) (z : Nat) :
    S g d z ↔ z = 1 ∨ z = g ∨ z = 2*g+d-1 ∨ z = 2*g+d ∨
      (g+d ≤ z ∧ g+d-2 ≤ z % (5*g+2*d) ∧ z % (5*g+2*d) ≤ 2*g+d-2) := by
  exact (greedy_membership_eq_scan hd hg).trans (scan_conjecture17 hd hg z)

theorem s_eq_A {g d : Nat} (hd : 2 <= d) (hg : d+1 <= g) : (S g d) = A g d := by
  funext z
  exact propext ((conjecture17 hd hg z).trans (candidate_eq_printed hd hg).symm)

-- The prefix invariant connects these independent scans to the literal greedy rule.
example : (scan 3 2 61).reverse =
    [1,3,5,6,7,8,22,23,24,25,41,42,43,44,60] := by decide

example : (scan 4 2 55).reverse =
    [1,4,6,7,8,9,10,28,29,30,31,32,52,53,54] := by decide

example : (scan 5 3 69).reverse =
    [1,5,8,9,10,11,12,13,37,38,39,40,41,42,68] := by decide


example : ∃ g d : Nat, 2 ≤ d ∧ d+1 ≤ g := ⟨3, 2, by decide⟩

example : Nat × Nat × Nat := (3, 2, 5)

example : S 3 2 6 ∧ ¬ S 3 2 9 := by
  constructor <;> rw [conjecture17 (by decide) (by decide)] <;> decide

#print axioms initial_gap_covered
#print axioms periodic_gap_covered
#print axioms restricted_three_sum_eq_complement
#print axioms conjecture17

end D5.S1.Words.Sumfree.GreedyThreeSumfreeTwoParameter
