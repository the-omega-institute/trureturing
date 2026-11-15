/- GID: D5/S3/Combinatorics/Permutation/Verkama62Persistence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Persistence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A degree-two singleton preserves a terminal 3412 after a fresh northeast ear. -/

import D5.S3.Combinatorics.Permutation.Verkama62Local

/-! The three extremal cases for a singleton of old-neighbour degree two. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)

/-- Old points joined to an inserted point by an inversion. -/
def neighbours {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (x : Fin n) : Finset (Fin n) :=
  S.filter fun i => (i < x ∧ π x < π i) ∨ (x < i ∧ π i < π x)

private theorem cutoff_two {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (a b c : α) (z : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : f a < f b) (hbc : f b < f c)
    (htop : ∀ i ∈ S, f i ≤ f a ∨ i = b ∨ i = c)
    (hne : ∀ i ∈ S, f i ≠ z)
    (hcard : (S.filter fun i => z < f i).card = 2) : f a < z ∧ z < f b := by
  have hneab : a ≠ b := by intro h; subst h; omega
  have hneac : a ≠ c := by intro h; subst h; omega
  have hnebc : b ≠ c := by intro h; subst h; omega
  constructor
  · by_contra h
    have hz : z < f a := by have := hne a ha; omega
    have hsub : {a, b, c} ⊆ S.filter fun i => z < f i := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨ha, hz⟩
      · exact Finset.mem_filter.mpr ⟨hb, by omega⟩
      · exact Finset.mem_filter.mpr ⟨hc, by omega⟩
    have hcount := Finset.card_le_card hsub
    have hthree : ({a, b, c} : Finset α).card = 3 := by
      simp [hneab, hneac, hnebc]
    rw [hthree, hcard] at hcount
    omega
  · by_contra h
    have hz : f b < z := by have := hne b hb; omega
    have hsub : (S.filter fun i => z < f i) ⊆ {c} := by
      intro i hi
      obtain ⟨hi, hzi⟩ := Finset.mem_filter.mp hi
      rcases htop i hi with hia | rfl | rfl
      · omega
      · omega
      · simp
    have hcount := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcount
    omega

/-- Inserting exactly one point with two old neighbours into a fresh state leaves
    a terminal 3412, even if the maximum or rightmost point changes. -/
theorem Fresh.singleton_terminal {n : ℕ} {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} (t : Fresh π S) (x : Fin n) (hx : x ∉ S)
    (hdegree : (neighbours π S x).card = 2) : Nonempty (Terminal π (insert x S)) := by
  by_cases hmax : π t.b < π x
  · have hall (i : Fin n) (hi : i ∈ S) : π i < π x :=
      (t.topmost i hi).trans_lt hmax
    have hfilter : neighbours π S x = S.filter (fun i => x.val < i.val) := by
      ext i
      simp only [neighbours, Finset.mem_filter]
      constructor
      · rintro ⟨hi, h | h⟩
        · have := hall i hi; omega
        · exact ⟨hi, h.1⟩
      · rintro ⟨hi, h⟩
        exact ⟨hi, Or.inr ⟨h, hall i hi⟩⟩
    have hcut := cutoff_two S Fin.val t.b t.c t.d x.val t.hb t.hc t.hd t.hbc t.hcd
      (fun i hi => t.right i hi)
      (by intro i hi h; exact hx (Fin.ext h ▸ hi)) (by rw [← hfilter]; exact hdegree)
    refine ⟨{
      a := t.b, b := x, c := t.c, d := t.d
      ha := Finset.mem_insert_of_mem t.hb
      hb := Finset.mem_insert_self _ _
      hc := Finset.mem_insert_of_mem t.hc
      hd := Finset.mem_insert_of_mem t.hd
      hab := hcut.1, hbc := hcut.2, hcd := t.hcd
      hval₁ := t.hval₁
      hval₂ := t.hval₂.trans t.hval₃
      hval₃ := hmax
      rightmost := ?_
      topmost := ?_ }⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact (hcut.2.trans t.hcd).le
      · exact t.rightmost i hi
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact (hall i hi).le
  · by_cases hright : t.d < x
    · have hall (i : Fin n) (hi : i ∈ S) : i < x :=
        (t.rightmost i hi).trans_lt hright
      have hfilter : neighbours π S x = S.filter (fun i => (π x).val < (π i).val) := by
        ext i
        simp only [neighbours, Finset.mem_filter]
        constructor
        · rintro ⟨hi, h | h⟩
          · exact ⟨hi, h.2⟩
          · have := hall i hi; omega
        · rintro ⟨hi, h⟩
          exact ⟨hi, Or.inl ⟨hall i hi, h⟩⟩
      have hcut := cutoff_two S (fun i => (π i).val) t.d t.a t.b (π x).val
        t.hd t.ha t.hb t.hval₂ t.hval₃ (fun i hi => t.top i hi)
        (by intro i hi h; exact hx (π.injective (Fin.ext h) ▸ hi))
        (by rw [← hfilter]; exact hdegree)
      refine ⟨{
        a := t.a, b := t.b, c := t.d, d := x
        ha := Finset.mem_insert_of_mem t.ha
        hb := Finset.mem_insert_of_mem t.hb
        hc := Finset.mem_insert_of_mem t.hd
        hd := Finset.mem_insert_self _ _
        hab := t.hab, hbc := t.hbc.trans t.hcd, hcd := hright
        hval₁ := hcut.1, hval₂ := hcut.2, hval₃ := t.hval₃
        rightmost := ?_
        topmost := ?_ }⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact le_rfl
        · exact (hall i hi).le
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact (hcut.2.trans t.hval₃).le
        · exact t.topmost i hi
    · refine ⟨{ t.toTerminal with
        ha := Finset.mem_insert_of_mem t.ha
        hb := Finset.mem_insert_of_mem t.hb
        hc := Finset.mem_insert_of_mem t.hc
        hd := Finset.mem_insert_of_mem t.hd
        rightmost := ?_
        topmost := ?_ }⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact le_of_not_gt hright
        · exact t.rightmost i hi
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact le_of_not_gt hmax
        · exact t.topmost i hi

/-- A fresh state followed by zero or one degree-two singleton cannot precede
    a northeast double ear in a 351624-avoiding permutation. -/
theorem Fresh.no_cheap_double {n : ℕ} {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} (t : Fresh π S) (havoid : ¬ Contains pattern π) :
    IsEmpty (Double π S) ∧
      ∀ x, x ∉ S → (neighbours π S x).card = 2 → IsEmpty (Double π (insert x S)) := by
  constructor
  · exact ⟨fun e => havoid (t.toTerminal.forces e)⟩
  · intro x hx hd
    obtain ⟨terminal⟩ := t.singleton_terminal x hx hd
    exact ⟨fun e => havoid (terminal.forces e)⟩

end D5.S3.Combinatorics.Permutation.Verkama62Local
