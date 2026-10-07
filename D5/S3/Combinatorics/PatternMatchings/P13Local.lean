/- GID: D5/S3/Combinatorics/PatternMatchings/P13Local
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Local
   mirror-E: none(waiver:normalized-ranked-scan)
   anchors: []
   utility: none
   digest: Source P13 avoidance determines the exact future order at every closure. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsDecoder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

open TripleAvoidingMatchingsDefs

/-- Source labels, with complementary right-endpoint ranks. -/
def P13 : Set (Fin 3 → Fin 3) := {![0, 2, 1], ![1, 0, 2], ![2, 1, 0]}

/-- Avoidance on actual perfect matchings, retaining the all-open-before-close condition. -/
def Avoids {n : ℕ} (m : Matching n) : Prop := ∀ p ∈ P13, ¬ Occurs m p

/-- A chronological closing word on three eligible arcs in opening order. -/
def ClosingOccurs {n : ℕ} (m : Matching n) (w : Fin 3 → Fin 3) : Prop :=
  ∃ l : Fin 3 → Fin (2 * n), StrictMono l ∧ (∀ i, l 2 < m.1 (l i)) ∧
    StrictMono (fun i => m.1 (l (w i)))

private theorem source_conversion {n : ℕ} (m : Matching n) :
    (Occurs m ![0, 2, 1] ↔ ClosingOccurs m ![1, 2, 0]) ∧
    (Occurs m ![1, 0, 2] ↔ ClosingOccurs m ![2, 0, 1]) ∧
    (Occurs m ![2, 1, 0] ↔ ClosingOccurs m ![0, 1, 2]) := by
  have conv (p w : Fin 3 → Fin 3)
      (h : ∀ i j : Fin 3, i < j ↔ p (w j) < p (w i))
      (hw : Function.Bijective w) : Occurs m p ↔ ClosingOccurs m w := by
    constructor
    · rintro ⟨l, hl, he, ho⟩
      refine ⟨l, hl, he, ?_⟩
      intro i j hij
      exact (ho (w i) (w j)).mpr ((h i j).mp hij)
    · rintro ⟨l, hl, he, ho⟩
      refine ⟨l, hl, he, ?_⟩
      intro i j
      obtain ⟨a, rfl⟩ := hw.2 i
      obtain ⟨b, rfl⟩ := hw.2 j
      exact ho.lt_iff_lt.trans (h a b)
  exact ⟨conv _ _ (by decide) (by decide),
    conv _ _ (by decide) (by decide), conv _ _ (by decide) (by decide)⟩

/-- Among two surviving openers x<y, x closes first precisely when the
just-closed opener lies strictly between them. -/
def FutureOrder {n : ℕ} (m : Matching n) : Prop :=
  ∀ t x y, m.1 t < t → x < y → y < t → t < m.1 x → t < m.1 y →
    (m.1 x < m.1 y ↔ x < m.1 t ∧ m.1 t < y)

private theorem closing_triples {n : ℕ} (m : Matching n) :
    Avoids m ↔ ∀ a b c : Fin (2 * n), a < b → b < c →
      c < m.1 a → c < m.1 b → c < m.1 c →
      ¬ ((m.1 a < m.1 b ∧ m.1 b < m.1 c) ∨
         (m.1 b < m.1 c ∧ m.1 c < m.1 a) ∨
         (m.1 c < m.1 a ∧ m.1 a < m.1 b)) := by
  have conv := source_conversion m
  have word (w : Fin 3 → Fin 3) (a b c : Fin (2 * n))
      (hab : a < b) (hbc : b < c)
      (ha : c < m.1 a) (hb : c < m.1 b) (hc : c < m.1 c)
      (ho : StrictMono (fun i => m.1 (![a, b, c] (w i)))) :
      ClosingOccurs m w := by
    refine ⟨![a, b, c], ?_, ?_, ho⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i
      fin_cases i <;> simpa
  constructor
  · intro hav a b c hab hbc ha hb hc hbad
    rcases hbad with h | h | h
    · apply hav ![2, 1, 0] (by simp [P13])
      apply conv.2.2.mpr
      apply word _ a b c hab hbc ha hb hc
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · apply hav ![0, 2, 1] (by simp [P13])
      apply conv.1.mpr
      apply word _ a b c hab hbc ha hb hc
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · apply hav ![1, 0, 2] (by simp [P13])
      apply conv.2.1.mpr
      apply word _ a b c hab hbc ha hb hc
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · intro h p hp hocc
    simp only [P13, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · obtain ⟨l, hl, he, ho⟩ := conv.1.mp hocc
      apply h (l 0) (l 1) (l 2) (hl (by decide)) (hl (by decide))
        (he 0) (he 1) (he 2)
      exact Or.inr (Or.inl ⟨ho (by decide : (0 : Fin 3) < 1),
        ho (by decide : (1 : Fin 3) < 2)⟩)
    · obtain ⟨l, hl, he, ho⟩ := conv.2.1.mp hocc
      apply h (l 0) (l 1) (l 2) (hl (by decide)) (hl (by decide))
        (he 0) (he 1) (he 2)
      exact Or.inr (Or.inr ⟨ho (by decide : (0 : Fin 3) < 1),
        ho (by decide : (1 : Fin 3) < 2)⟩)
    · obtain ⟨l, hl, he, ho⟩ := conv.2.2.mp hocc
      apply h (l 0) (l 1) (l 2) (hl (by decide)) (hl (by decide))
        (he 0) (he 1) (he 2)
      exact Or.inl ⟨ho (by decide : (0 : Fin 3) < 1),
        ho (by decide : (1 : Fin 3) < 2)⟩

/-- The exact future-order criterion on every completed matching. -/
theorem future_order_iff {n : ℕ} (m : Matching n) : Avoids m ↔ FutureOrder m := by
  rw [closing_triples]
  have inv : ∀ v, m.1 (m.1 v) = v := fun v => (m.2 v).1
  have inj : Function.Injective m.1 := Function.LeftInverse.injective inv
  constructor
  · intro avoid t x y ht hxy hyt hx hy
    have hxz : x ≠ m.1 t := by
      intro he
      rw [he, inv] at hx
      exact lt_irrefl _ hx
    have hyz : y ≠ m.1 t := by
      intro he
      rw [he, inv] at hy
      exact lt_irrefl _ hy
    by_cases hzx : m.1 t < x
    · have bad := avoid (m.1 t) x y hzx hxy (by simpa [inv] using hyt)
        (by omega) (by omega)
      simp only [inv] at bad
      constructor
      · intro ho
        exact (bad (Or.inl ⟨hx, ho⟩)).elim
      · intro ho
        omega
    · by_cases hyz' : y < m.1 t
      · have bad := avoid x y (m.1 t) hxy hyz' (by omega) (by omega)
          (by simpa [inv] using ht)
        simp only [inv] at bad
        constructor
        · intro ho
          exact (bad (Or.inr (Or.inr ⟨hx, ho⟩))).elim
        · intro ho
          omega
      · have hxz' : x < m.1 t := by omega
        have hzy : m.1 t < y := by omega
        have bad := avoid x (m.1 t) y hxz' hzy (by omega)
          (by simpa [inv] using hyt) (by omega)
        simp only [inv] at bad
        have hne : m.1 x ≠ m.1 y := fun h => ne_of_lt hxy (inj h)
        constructor
        · intro _
          exact ⟨hxz', hzy⟩
        · intro _
          by_contra ho
          have ho' : m.1 y < m.1 x := by omega
          exact bad (Or.inr (Or.inl ⟨hy, ho'⟩))
  · intro future a b c hab hbc ha hb hc hbad
    rcases hbad with h | h | h
    · have rule := future (m.1 a) b c (by rw [inv]; omega) hbc
        (by omega) h.1 (by omega)
      rw [inv] at rule
      have hh := rule.mp h.2
      omega
    · have rule := future (m.1 b) a c (by rw [inv]; omega)
        (by omega) hb (by omega) h.1
      rw [inv] at rule
      have hh := rule.mpr ⟨hab, hbc⟩
      omega
    · have rule := future (m.1 c) a b (by rw [inv]; omega) hab
        (by omega) h.1 (by omega)
      rw [inv] at rule
      have hh := rule.mp h.2
      omega

end D5.S3.Combinatorics.PatternMatchings.P13

