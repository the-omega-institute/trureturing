/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineClassicalSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineClassicalSplit
   mirror-E: none(waiver:classical-maximum-pattern-decomposition)
   anchors: []
   utility: none
   digest: Splitting at the maximum characterizes 231 avoidance by separated avoiding parts. -/

import D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalSplit

open D5.S3.Combinatorics Nonnesting

theorem avoids231_maxSplit_iff (left right : List ℕ) (maximum : ℕ)
    (hmax : ∀ value ∈ left ++ right, value < maximum)
    (hnodup : (left ++ maximum :: right).Nodup) :
    ¬ NonnestingDefs.Occurs [2, 3, 1] (left ++ maximum :: right) ↔
      ¬ NonnestingDefs.Occurs [2, 3, 1] left ∧
      ¬ NonnestingDefs.Occurs [2, 3, 1] right ∧
      ∀ lower ∈ left, ∀ upper ∈ right, lower < upper := by
  have hheredity (word : List ℕ) (hword : word.Sublist (left ++ maximum :: right))
      (hocc : NonnestingDefs.Occurs [2, 3, 1] word) :
      NonnestingDefs.Occurs [2, 3, 1] (left ++ maximum :: right) := by
    obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
    exact ⟨values, hstep, fun rank hlo hhi => hword.subset (hmem rank hlo hhi),
      hsub.trans hword, by simp⟩
  have hsplit (first second last : ℕ)
      (hsub : [first, second, last].Sublist (left ++ maximum :: right)) :
      [first, second, last].Sublist left ∨
      (first ∈ left ∧ [second, last].Sublist (maximum :: right)) ∨
      ([first, second].Sublist left ∧ last ∈ maximum :: right) ∨
      [first, second, last].Sublist (maximum :: right) := by
    obtain ⟨selectedLeft, suffix, heq, hprefix, hsuffix⟩ :=
      List.sublist_append_iff.mp hsub
    cases selectedLeft with
    | nil =>
      simp only [List.nil_append] at heq
      exact Or.inr (Or.inr (Or.inr (heq ▸ hsuffix)))
    | cons head tail =>
      cases tail with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, heq⟩ := heq
        exact Or.inr (Or.inl ⟨List.singleton_sublist.mp hprefix, heq ▸ hsuffix⟩)
      | cons middle tail =>
        cases tail with
        | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl, heq⟩ := heq
          exact Or.inr (Or.inr (Or.inl ⟨hprefix,
            List.singleton_sublist.mp (heq ▸ hsuffix)⟩))
        | cons final tail =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl, rfl, heq⟩ := heq
          have hnil : tail = [] := (List.append_eq_nil_iff.mp heq.symm).1
          subst tail
          exact Or.inl hprefix
  constructor
  · intro havoid
    refine ⟨fun hocc => havoid (hheredity left (List.sublist_append_left _ _) hocc),
      fun hocc => havoid (hheredity right
        ((List.Sublist.refl right).cons maximum |>.trans
          (List.sublist_append_right left (maximum :: right))) hocc), ?_⟩
    intro lower hlower upper hupper
    have hne : lower ≠ upper :=
      (List.nodup_append.mp hnodup).2.2 lower hlower upper (by simp [hupper])
    by_contra hnot
    have hhigh := hmax lower (by simp [hlower])
    let values : ℕ → ℕ := fun rank => if rank = 1 then upper
      else if rank = 2 then lower else maximum
    have hsub : ([2, 3, 1].map values).Sublist (left ++ maximum :: right) := by
      have hs := (List.singleton_sublist.mpr hlower).append
        ((List.singleton_sublist.mpr hupper).cons_cons maximum)
      simpa [values] using hs
    apply havoid
    refine ⟨values, ?_, ?_, hsub, by simp⟩
    · intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 := by change rank < 3 at hhi; omega
      rcases hc with rfl | rfl <;> simp [values] <;> omega
    · intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by change rank ≤ 3 at hhi; omega
      rcases hc with rfl | rfl | rfl <;> simp [values, hlower, hupper]
  · rintro ⟨hleft, hright, hseparate⟩ ⟨values, hstep, _, hsub, _⟩
    have h12 : values 1 < values 2 := hstep 1 (by omega) (by decide)
    have h23 : values 2 < values 3 := hstep 2 (by omega) (by decide)
    simp only [List.map_cons, List.map_nil] at hsub
    have hocc (word : List ℕ) (hs : [values 2, values 3, values 1].Sublist word) :
        NonnestingDefs.Occurs [2, 3, 1] word := by
      refine ⟨values, hstep, ?_, by simpa using hs, by simp⟩
      intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by change rank ≤ 3 at hhi; omega
      apply hs.subset
      rcases hc with rfl | rfl | rfl <;> simp
    have hlast (upper : ℕ) (hupper : upper ∈ maximum :: right)
        (lower : ℕ) (hlower : lower ∈ left) : lower < upper := by
      rcases List.mem_cons.mp hupper with rfl | hupper
      · exact hmax lower (by simp [hlower])
      · exact hseparate lower hlower upper hupper
    rcases hsplit _ _ _ hsub with hwhole | ⟨hfirst, htail⟩ |
      ⟨hprefix, hfinal⟩ | hwhole
    · exact hleft (hocc left hwhole)
    · have hfinal := htail.subset (show values 1 ∈ [values 3, values 1] by simp)
      have hlt := hlast _ hfinal _ hfirst
      omega
    · have hfirst := hprefix.subset (show values 2 ∈ [values 2, values 3] by simp)
      have hlt := hlast _ hfinal _ hfirst
      omega
    · rcases List.sublist_cons_iff.mp hwhole with hs | ⟨tail, heq, htail⟩
      · exact hright (hocc right hs)
      · simp only [List.cons.injEq] at heq
        obtain ⟨heq, rfl⟩ := heq
        have hmem := htail.subset (show values 3 ∈ [values 3, values 1] by simp)
        have hlt := hmax (values 3) (by simp [hmem])
        omega

theorem avoids4123_maxSplit_iff (left right : List ℕ) (maximum : ℕ)
    (hmax : ∀ value ∈ left ++ right, value < maximum)
    (hseparate : ∀ lower ∈ left, ∀ upper ∈ right, lower < upper) :
    ¬ NonnestingDefs.Occurs [4, 1, 2, 3] (left ++ maximum :: right) ↔
      ¬ NonnestingDefs.Occurs [4, 1, 2, 3] left ∧
      ¬ NonnestingDefs.Occurs [1, 2, 3] right := by
  have hlower (lower : ℕ) (hlower : lower ∈ left) (upper : ℕ)
      (hupper : upper ∈ maximum :: right) : lower < upper := by
    rcases List.mem_cons.mp hupper with rfl | hupper
    · exact hmax lower (by simp [hlower])
    · exact hseparate lower hlower upper hupper
  have hright123 (values : ℕ → ℕ)
      (hstep : ∀ rank, 1 ≤ rank → rank < 4 → values rank < values (rank + 1))
      (hsub : [values 1, values 2, values 3].Sublist right) :
      NonnestingDefs.Occurs [1, 2, 3] right := by
    refine ⟨values, ?_, ?_, by simpa using hsub, by simp⟩
    · intro rank hlo hhi
      exact hstep rank hlo (by change rank < 3 at hhi; omega)
    · intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by change rank ≤ 3 at hhi; omega
      apply hsub.subset
      rcases hc with rfl | rfl | rfl <;> simp
  constructor
  · intro havoid
    constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      apply havoid
      refine ⟨values, hstep, ?_, hsub.trans (List.sublist_append_left _ _), by simp⟩
      intro rank hlo hhi
      exact List.mem_append_left _ (hmem rank hlo hhi)
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      let extended : ℕ → ℕ := fun rank => if rank = 4 then maximum else values rank
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by decide)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by decide)
      have h3max : values 3 < maximum := hmax _ (by
        simp only [List.mem_append]
        exact Or.inr (hmem 3 (by omega) (by decide)))
      apply havoid
      refine ⟨extended, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by change rank < 4 at hhi; omega
        rcases hc with rfl | rfl | rfl
        · simpa only [extended, Nat.reduceEqDiff, ↓reduceIte] using h12
        · simpa only [extended, Nat.reduceEqDiff, ↓reduceIte] using h23
        · simpa only [extended, Nat.reduceEqDiff, ↓reduceIte] using h3max
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          change rank ≤ 4 at hhi
          omega
        rcases hc with rfl | rfl | rfl | rfl
        · simp [extended, hmem 1 (by omega) (by decide)]
        · simp [extended, hmem 2 (by omega) (by decide)]
        · simp [extended, hmem 3 (by omega) (by decide)]
        · simp [extended]
      · have ht : [values 1, values 2, values 3].Sublist right := by
          simpa using hsub
        have hs : [maximum, values 1, values 2, values 3].Sublist
            (left ++ maximum :: right) :=
          (ht.cons_cons maximum).trans (List.sublist_append_right _ _)
        simpa [extended] using hs
  · rintro ⟨hleft, hright⟩ ⟨values, hstep, _, hsub, _⟩
    have h12 : values 1 < values 2 := hstep 1 (by omega) (by decide)
    have h23 : values 2 < values 3 := hstep 2 (by omega) (by decide)
    have h34 : values 3 < values 4 := hstep 3 (by omega) (by decide)
    simp only [List.map_cons, List.map_nil] at hsub
    have hselectedBound (value : ℕ) (hvalue : value ∈ [values 4, values 1, values 2,
        values 3]) : value ≤ values 4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvalue
      rcases hvalue with rfl | rfl | rfl | rfl <;> omega
    obtain ⟨selectedLeft, selectedRight, heq, hselectedLeft, hselectedRight⟩ :=
      List.sublist_append_iff.mp hsub
    by_cases hfirst : values 4 ∈ left
    · have hnil : selectedRight = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value hvalue
        have hr := hselectedRight.subset hvalue
        have hs : value ∈ [values 4, values 1, values 2, values 3] := by
          rw [heq]
          exact List.mem_append_right _ hvalue
        have hb := hselectedBound value hs
        have hl := hlower _ hfirst _ hr
        omega
      have hwhole : [values 4, values 1, values 2, values 3].Sublist left := by
        simp only [hnil, List.append_nil] at heq
        rw [heq]
        exact hselectedLeft
      apply hleft
      refine ⟨values, hstep, ?_, by simpa using hwhole, by simp⟩
      intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
        change rank ≤ 4 at hhi
        omega
      apply hwhole.subset
      rcases hc with rfl | rfl | rfl | rfl <;> simp
    · have hnil : selectedLeft = [] := by
        cases selectedLeft with
        | nil => rfl
        | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at heq
          have hmem : head ∈ left := hselectedLeft.subset (by simp)
          exact False.elim (hfirst (heq.1 ▸ hmem))
      have hwhole : [values 4, values 1, values 2, values 3].Sublist
          (maximum :: right) := by
        simp only [hnil, List.nil_append] at heq
        rw [heq]
        exact hselectedRight
      rcases List.sublist_cons_iff.mp hwhole with hs | ⟨tail, heq, htail⟩
      · have ht : [values 1, values 2, values 3].Sublist right :=
          (List.Sublist.refl [values 1, values 2, values 3]).cons (values 4) |>.trans hs
        exact hright (hright123 values hstep ht)
      · simp only [List.cons.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        exact hright (hright123 values hstep htail)

end D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalSplit
