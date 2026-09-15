/- GID: D5/S1/Digit/Infinite/InfiniteSuccessorFibres
   generality: G
   mirror-B: D5/B/S1/Digit/Infinite/InfiniteSuccessorFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The legal infinite digit successor is surjective with two alternating predecessors of zero and unique predecessors elsewhere. -/

import D5.S1.Digit.Infinite.SuccessorContinuity

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.InfiniteSuccessorFibres

open D5.S1.Digit.Infinite.SuccessorContinuity

/-- The successor preserves legality and is surjective. The zero sequence has precisely the
predecessors with ones at even positions and at odd positions; every nonzero sequence has a unique
predecessor. -/
theorem next_fibres :
    (∀ x : LegalDigits, ∀ j, ¬ (next x.val j = true ∧ next x.val (j + 1) = true)) ∧
    (∀ y : LegalDigits, ∃ x : LegalDigits, next x.val = y.val) ∧
    (∀ x : LegalDigits, next x.val = (fun _ => false) ↔
      (x.val = fun i => decide (i % 2 = 0)) ∨ (x.val = fun i => decide (i % 2 = 1))) ∧
    (∀ y : LegalDigits, y.val ≠ (fun _ => false) →
      ∃! x : LegalDigits, next x.val = y.val) := by
  classical
  have lands (x : LegalDigits) :
      ∀ i, ¬ (next x.val i = true ∧ next x.val (i + 1) = true) := by
    intro i hi
    by_cases h : ∃ j, x.val j = false ∧ x.val (j + 1) = false
    · let k := Nat.find h
      have hk := Nat.find_spec h
      change x.val k = false ∧ x.val (k + 1) = false at hk
      simp only [next, dif_pos h] at hi
      change (if i < k then false else if i = k then true else x.val i) = true ∧
        (if i + 1 < k then false else if i + 1 = k then true else x.val (i + 1)) = true at hi
      by_cases hik : i < k
      · simpa only [if_pos hik, Bool.false_eq_true] using hi.1
      · by_cases heq : i = k
        · subst i
          have : (false : Bool) = true := by
            simpa only [if_neg (show ¬ k + 1 < k by omega),
              if_neg (show k + 1 ≠ k by omega), hk.2] using hi.2
          contradiction
        · have hki : k < i := by omega
          have h1 : x.val i = true := by simpa only [if_neg hik, if_neg heq] using hi.1
          have h2 : x.val (i + 1) = true := by
            simpa only [if_neg (show ¬ i + 1 < k by omega),
              if_neg (show i + 1 ≠ k by omega)] using hi.2
          exact x.property i ⟨h1, h2⟩
    · simpa [next, h] using hi.1
  have zero_iff (x : LegalDigits) : next x.val = (fun _ => false) ↔
      ¬ ∃ j, x.val j = false ∧ x.val (j + 1) = false := by
    constructor
    · intro hz hp
      have hv : next x.val (Nat.find hp) = true := by
        simp only [next, dif_pos hp, Nat.lt_irrefl, if_false, if_true]
      have hf := congrFun hz (Nat.find hp)
      rw [hv] at hf
      contradiction
    · intro hp
      simp only [next, dif_neg hp]
  have zero_fibre (x : LegalDigits) : next x.val = (fun _ => false) ↔
      (x.val = fun i => decide (i % 2 = 0)) ∨
      (x.val = fun i => decide (i % 2 = 1)) := by
    rw [zero_iff]
    constructor
    · intro hp
      have step (i : ℕ) : x.val (i + 1) = !(x.val i) := by
        have h11 := x.property i
        have h00 : ¬ (x.val i = false ∧ x.val (i + 1) = false) :=
          fun hi => hp ⟨i, hi⟩
        cases h0 : x.val i <;> cases h1 : x.val (i + 1) <;> simp_all
      have alternating (i : ℕ) :
          x.val i = if i % 2 = 0 then x.val 0 else !(x.val 0) := by
        induction i with
        | zero => simp
        | succ i ih =>
          rw [step, ih]
          by_cases hi : i % 2 = 0
          · have hs : (i + 1) % 2 ≠ 0 := by omega
            simp [hi, hs]
          · have hs : (i + 1) % 2 = 0 := by omega
            simp [hi, hs]
      cases h0 : x.val 0
      · right
        funext i
        rw [alternating, h0]
        by_cases hi : i % 2 = 0
        · have hi1 : i % 2 ≠ 1 := by omega
          simp [hi]
        · have hi1 : i % 2 = 1 := by omega
          simp [hi1]
      · left
        funext i
        rw [alternating, h0]
        simp
    · rintro (hx | hx) ⟨j, hj, hj1⟩
      · rw [hx] at hj hj1
        simp only [decide_eq_false_iff_not] at hj hj1
        omega
      · rw [hx] at hj hj1
        simp only [decide_eq_false_iff_not] at hj hj1
        omega
  have predecessor (y : LegalDigits) (hne : y.val ≠ (fun _ => false)) :
      ∃ x : LegalDigits, next x.val = y.val := by
    have hy : ∃ i, y.val i = true := by
      by_contra h
      apply hne
      funext i
      cases hi : y.val i
      · rfl
      · exact False.elim (h ⟨i, hi⟩)
    let k := Nat.find hy
    have hyk : y.val k = true := Nat.find_spec hy
    have hyk1 : y.val (k + 1) = false := by
      cases hi : y.val (k + 1)
      · rfl
      · exact False.elim (y.property k ⟨hyk, hi⟩)
    let f : ℕ → Bool := fun i => if i ≤ k then decide (i % 2 ≠ k % 2) else y.val i
    have fk : f k = false := by simp [f]
    have fk1 : f (k + 1) = false := by simp [f, hyk1]
    have legal : ∀ i, ¬ (f i = true ∧ f (i + 1) = true) := by
      intro i ⟨hi, hi1⟩
      by_cases hik1 : i + 1 ≤ k
      · have hik : i ≤ k := by omega
        simp only [f, if_pos hik, decide_eq_true_eq] at hi
        simp only [f, if_pos hik1, decide_eq_true_eq] at hi1
        omega
      · by_cases hik : i ≤ k
        · have heq : i = k := by omega
          subst i
          rw [fk] at hi
          contradiction
        · simp only [f, if_neg hik] at hi
          simp only [f, if_neg hik1] at hi1
          exact y.property i ⟨hi, hi1⟩
    have minimal : ∀ i < k, ¬ (f i = false ∧ f (i + 1) = false) := by
      intro i hik ⟨hi, hi1⟩
      simp only [f, if_pos (show i ≤ k by omega), decide_eq_false_iff_not, not_not] at hi
      simp only [f, if_pos (show i + 1 ≤ k by omega), decide_eq_false_iff_not,
        not_not] at hi1
      omega
    have hp : ∃ i, f i = false ∧ f (i + 1) = false := ⟨k, fk, fk1⟩
    have hfirst : Nat.find hp = k := (Nat.find_eq_iff hp).mpr ⟨⟨fk, fk1⟩, minimal⟩
    refine ⟨⟨f, legal⟩, ?_⟩
    funext i
    change next f i = y.val i
    simp only [next, dif_pos hp, hfirst]
    by_cases hik : i < k
    · rw [if_pos hik]
      have hmin : y.val i ≠ true := Nat.find_min hy hik
      cases hi : y.val i
      · rfl
      · exact False.elim (hmin hi)
    · rw [if_neg hik]
      by_cases heq : i = k
      · subst i
        simp only [if_true, hyk]
      · rw [if_neg heq]
        exact if_neg (show ¬ i ≤ k by omega)
  have onto : ∀ y : LegalDigits, ∃ x : LegalDigits, next x.val = y.val := by
    intro y
    by_cases hy : y.val = (fun _ => false)
    · let u : LegalDigits := ⟨fun i => decide (i % 2 = 0), by
        intro i hi
        simp only [decide_eq_true_eq] at hi
        omega⟩
      exact ⟨u, ((zero_fibre u).mpr (Or.inl rfl)).trans hy.symm⟩
    · exact predecessor y hy
  have backward (a : LegalDigits) (i : ℕ)
      (h00 : ¬ (a.val i = false ∧ a.val (i + 1) = false)) :
      a.val i = !(a.val (i + 1)) := by
    have h11 := a.property i
    cases h0 : a.val i <;> cases h1 : a.val (i + 1) <;> simp_all
  have prefix_unique : ∀ (k : ℕ) (a b : LegalDigits),
      (∀ i < k, ¬ (a.val i = false ∧ a.val (i + 1) = false)) →
      (∀ i < k, ¬ (b.val i = false ∧ b.val (i + 1) = false)) →
      a.val k = b.val k → ∀ i ≤ k, a.val i = b.val i := by
    intro k
    induction k with
    | zero =>
      intro a b ha hb he i hi
      have hi0 : i = 0 := by omega
      subst i
      exact he
    | succ k ih =>
      intro a b ha hb he i hi
      have he' : a.val k = b.val k := by
        rw [backward a k (ha k (by omega)), backward b k (hb k (by omega)), he]
      by_cases hik : i ≤ k
      · exact ih a b (fun j hj => ha j (by omega))
          (fun j hj => hb j (by omega)) he' i hik
      · have hi' : i = k + 1 := by omega
        subst i
        exact he
  refine ⟨lands, onto, zero_fibre, ?_⟩
  intro y hne
  obtain ⟨x, hx⟩ := onto y
  refine ⟨x, hx, ?_⟩
  intro z hz
  have px : ∃ j, x.val j = false ∧ x.val (j + 1) = false := by
    by_contra hp
    exact hne (hx.symm.trans ((zero_iff x).mpr hp))
  have pz : ∃ j, z.val j = false ∧ z.val (j + 1) = false := by
    by_contra hp
    exact hne (hz.symm.trans ((zero_iff z).mpr hp))
  have outputs : next z.val = next x.val := hz.trans hx.symm
  have same : Nat.find pz = Nat.find px := by
    apply Nat.le_antisymm
    · by_contra hle
      have hlt : Nat.find px < Nat.find pz := by omega
      have hi := congrFun outputs (Nat.find px)
      simp only [next, dif_pos pz, dif_pos px, if_pos hlt, Nat.lt_irrefl,
        if_false, if_true] at hi
      contradiction
    · by_contra hle
      have hlt : Nat.find pz < Nat.find px := by omega
      have hi := congrFun outputs (Nat.find pz)
      simp only [next, dif_pos pz, dif_pos px, if_pos hlt, Nat.lt_irrefl,
        if_false, if_true] at hi
      contradiction
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ Nat.find pz
  · apply prefix_unique (Nat.find pz) z x
        (fun j hj => Nat.find_min pz hj)
        (fun j hj => Nat.find_min px (by omega)) _ i hi
    exact (Nat.find_spec pz).1.trans (by rw [same]; exact (Nat.find_spec px).1.symm)
  · have hlt : ¬ i < Nat.find pz := by omega
    have heq : i ≠ Nat.find pz := by omega
    have he := congrFun outputs i
    simpa only [next, dif_pos pz, dif_pos px, ← same, if_neg hlt, if_neg heq] using he

end D5.S1.Digit.Infinite.InfiniteSuccessorFibres
