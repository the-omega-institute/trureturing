/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan
   mirror-E: none(waiver:scan-characterization)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Avoidance is equivalent to the oldest-or-second scan with a forced next closure. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs

/-- At a closure there cannot be two older open arcs. After closing a second-oldest
arc with a younger open arc present, the next closure must close the older arc.
The interval condition allows any number of intervening openings. -/
def ScanRules {n : ℕ} (m : Matching n) : Prop :=
  (∀ t x y, m.1 t < t → x < y → y < m.1 t →
    t ≤ m.1 x → t ≤ m.1 y → False) ∧
  (∀ t x y u, m.1 t < t → x < m.1 t → t ≤ m.1 x →
    m.1 t < y → y < t → t ≤ m.1 y → t < u → m.1 u < u →
    (∀ v, t < v → v < u → v < m.1 v) → m.1 u = x)

/-- The scan characterization, including the height-two exception and openings
between the second-oldest closure and the forced oldest closure. -/
theorem scan_characterization {n : ℕ} (m : Matching n) :
    AvoidsP1 m ↔ ScanRules m := by
  classical
  have inv : ∀ v, m.1 (m.1 v) = v := fun v => (m.2 v).1
  have inj : Function.Injective m.1 := Function.LeftInverse.injective inv
  have neq : ∀ v, m.1 v ≠ v := fun v => (m.2 v).2
  have occurrence (p : Fin 3 → Fin 3) (a b c : Fin (2 * n))
      (hab : a < b) (hbc : b < c)
      (ha : c < m.1 a) (hb : c < m.1 b) (hc : c < m.1 c)
      (hp : ∀ i j : Fin 3,
        m.1 (![a, b, c] i) < m.1 (![a, b, c] j) ↔ p j < p i) :
      Occurs m p := by
    refine ⟨![a, b, c], ?_, ?_, hp⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
      all_goals omega
    · intro i
      fin_cases i <;> simpa
  have firstClosure (t r : Fin (2 * n)) (htr : t < r) (hr : m.1 r < r) :
      ∃ u, t < u ∧ u ≤ r ∧ m.1 u < u ∧
        ∀ v, t < v → v < u → v < m.1 v := by
    let s := Finset.univ.filter fun v => t < v ∧ m.1 v < v
    have hrs : r ∈ s := by simp [s, htr, hr]
    have hs : s.Nonempty := ⟨r, hrs⟩
    refine ⟨s.min' hs, ?_, Finset.min'_le s r hrs, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2.1
    · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2.2
    · intro v htv hvu
      have hnot : ¬ m.1 v < v := by
        intro h
        have hvs : v ∈ s := by simp [s, htv, h]
        exact (not_lt_of_ge (Finset.min'_le s v hvs)) hvu
      have := neq v
      omega
  constructor
  · intro avoid
    have rank (t x y : Fin (2 * n)) (ht : m.1 t < t)
        (hxy : x < y) (hy : y < m.1 t) (hx : t ≤ m.1 x) (hyy : t ≤ m.1 y) :
        False := by
      have hxt : t < m.1 x := by
        have hne : m.1 x ≠ t := fun h => by
          have := congrArg m.1 h
          rw [inv] at this
          omega
        omega
      have hyt : t < m.1 y := by
        have hne : m.1 y ≠ t := fun h => by
          have := congrArg m.1 h
          rw [inv] at this
          omega
        omega
      have hpartners : m.1 x ≠ m.1 y := fun h => by
        have := inj h
        omega
      by_cases h : m.1 x < m.1 y
      · apply avoid ![1, 0, 2] (by simp [P1])
        apply occurrence ![1, 0, 2] x y (m.1 t) hxy hy
          (by omega) (by omega) (by simpa [inv] using ht)
        intro i j
        fin_cases i <;> fin_cases j <;> simp [inv] <;> omega
      · apply avoid ![0, 1, 2] (by simp [P1])
        apply occurrence ![0, 1, 2] x y (m.1 t) hxy hy
          (by omega) (by omega) (by simpa [inv] using ht)
        intro i j
        fin_cases i <;> fin_cases j <;> simp [inv] <;> omega
    refine ⟨rank, ?_⟩
    intro t x y u ht hxb htx hby hyt hty htu hu between
    by_contra hz
    have hxu : u < m.1 x := by
      have hxt : t < m.1 x := by
        have hne : m.1 x ≠ t := fun h => by
          have := congrArg m.1 h
          rw [inv] at this
          omega
        omega
      by_cases h : m.1 x < u
      · have hb := between (m.1 x) hxt h
        rw [inv] at hb
        omega
      · have hne : m.1 x ≠ u := fun h => hz (by rw [← h, inv])
        omega
    have hyu : u ≤ m.1 y := by
      by_contra h
      have hyt' : t < m.1 y := by
        have hne : m.1 y ≠ t := fun he => by
          have := congrArg m.1 he
          rw [inv] at this
          omega
        omega
      have hb := between (m.1 y) hyt' (by omega)
      rw [inv] at hb
      omega
    have hzb : m.1 t < m.1 u := by
      by_contra h
      have hne : m.1 u ≠ m.1 t := fun he => by
        have := inj he
        omega
      have hlt : m.1 u < m.1 t := by omega
      rcases lt_or_gt_of_ne hz with hzx | hxz
      · exact rank t (m.1 u) x ht hzx hxb (by rw [inv]; omega) htx
      · exact rank t x (m.1 u) ht hxz hlt htx (by rw [inv]; omega)
    by_cases hzt : m.1 u < t
    · apply avoid ![0, 2, 1] (by simp [P1])
      apply occurrence ![0, 2, 1] x (m.1 t) (m.1 u) hxb hzb
        (by omega) (by simpa [inv] using hzt) (by simpa [inv] using hu)
      intro i j
      fin_cases i <;> fin_cases j <;> simp [inv] <;> omega
    · have hneqt : m.1 u ≠ t := fun he => by
        have := congrArg m.1 he
        rw [inv] at this
        omega
      exact rank u x y hu (by omega) (by omega) (by omega) hyu
  · rintro ⟨rank, force⟩ p hp ⟨l, mono, eligible, order⟩
    have h01 : l 0 < l 1 := mono (by decide)
    have h12 : l 1 < l 2 := mono (by decide)
    have h0 := eligible 0
    have h1 := eligible 1
    have h2 := eligible 2
    have hx : m.1 (l 0) < m.1 (l 1) ↔ p 1 < p 0 := order 0 1
    have hy : m.1 (l 0) < m.1 (l 2) ↔ p 2 < p 0 := order 0 2
    have hz : m.1 (l 1) < m.1 (l 2) ↔ p 2 < p 1 := order 1 2
    have distinct01 : m.1 (l 0) ≠ m.1 (l 1) := fun h => by
      have := inj h
      omega
    have distinct02 : m.1 (l 0) ≠ m.1 (l 2) := fun h => by
      have := inj h
      omega
    have distinct12 : m.1 (l 1) ≠ m.1 (l 2) := fun h => by
      have := inj h
      omega
    simp only [P1, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · simp at hx hy hz
      exact rank (m.1 (l 2)) (l 0) (l 1) (by rw [inv]; exact h2)
        h01 (by rw [inv]; exact h12) (by omega) (by omega)
    · simp at hx hy hz
      have hclose : m.1 (l 2) < m.1 (l 0) := by omega
      have hfirst : m.1 (l 1) < m.1 (l 2) := by omega
      obtain ⟨u, htu, hur, hu, between⟩ := firstClosure
        (m.1 (l 1)) (m.1 (l 2)) hfirst (by rw [inv]; exact h2)
      have forced := force (m.1 (l 1)) (l 0) (l 2) u
        (by rw [inv]; omega) (by rw [inv]; exact h01) (by omega)
        (by rw [inv]; exact h12) h1 (by omega) htu hu between
      have := congrArg m.1 forced
      rw [inv] at this
      omega
    · simp at hx hy hz
      exact rank (m.1 (l 2)) (l 0) (l 1) (by rw [inv]; exact h2)
        h01 (by rw [inv]; exact h12) (by omega) (by omega)

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings
