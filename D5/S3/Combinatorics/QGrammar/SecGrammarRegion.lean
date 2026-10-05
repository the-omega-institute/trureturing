/- GID: D5/S3/Combinatorics/QGrammar/SecGrammarRegion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QGrammar/SecGrammarRegion
   mirror-E: none(waiver:sec-grammar-reachable-region)
   anchors: [mathlib/module/Mathlib.Data.Finset.Prod]
   utility: none
   digest: An exhaustive predecessor construction identifies the exact reachable tuple region. -/

import D5.S3.Combinatorics.QGrammar.SecGrammarTransitions
import Mathlib.Data.Finset.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.QGrammar.SecGrammar

open SecGrammarDefs

/-- The finite tuple region. The equation with r records the number of constant branches. -/
noncomputable def region (n : ℕ) : Finset (Bool × ℕ × ℕ × ℕ) := by
  classical
  exact (Finset.univ.product ((Finset.range (n + 1)).product
    ((Finset.range (n + 1)).product (Finset.range (n + 1))))).filter fun q =>
    let f := q.1
    let j := q.2.1
    let a := q.2.2.1
    let b := q.2.2.2
    if f then
      (j = 0 ∧ a = n ∧ b = 0) ∨
      ∃ r ≤ n, n = a + b + 2 * r ∧ 1 ≤ a ∧ 1 ≤ j ∧
        (if r = 0 then a + j ≤ n else
          j + 2 ≤ n ∧ a + j + 1 ≤ n ∧ (2 ≤ r → 2 ≤ j))
    else
      (j = 1 ∧ n = a + 2 ∧ b = 0) ∨
      2 ≤ j ∧ j + 1 ≤ n ∧ ∃ r ≤ n, n = a + b + 2 * r ∧
        (if r = 0 then 1 ≤ a ∧ 4 ≤ a + j ∧ a + 1 ≤ n
          else if r = 1 then 3 ≤ a + j else True)

/-- Both inclusions of the region follow from actual positional branches and an
exhaustive predecessor partition, including zero-total B-layers. -/
theorem reachable_region (n : ℕ) (hn : 1 ≤ n) :
    (deriv^[n] (Finsupp.single [(true, 0)] 1)).support =
      (region n).image (fun q => encode q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  classical
  have mem (m : ℕ) (f : Bool) (j a b : ℕ) :
      (f, j, a, b) ∈ region m ↔ j ≤ m ∧ a ≤ m ∧ b ≤ m ∧
        if f then
          (j = 0 ∧ a = m ∧ b = 0) ∨
          ∃ r ≤ m, m = a + b + 2 * r ∧ 1 ≤ a ∧ 1 ≤ j ∧
            (if r = 0 then a + j ≤ m else
              j + 2 ≤ m ∧ a + j + 1 ≤ m ∧ (2 ≤ r → 2 ≤ j))
        else
          (j = 1 ∧ m = a + 2 ∧ b = 0) ∨
          2 ≤ j ∧ j + 1 ≤ m ∧ ∃ r ≤ m, m = a + b + 2 * r ∧
            (if r = 0 then 1 ≤ a ∧ 4 ≤ a + j ∧ a + 1 ≤ m
              else if r = 1 then 3 ≤ a + j else True) := by
    simp only [region, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_univ,
      Finset.mem_range, Nat.lt_succ_iff, true_and, and_assoc]
  have A (m j a b r : ℕ) (ht : m = a + b + 2 * r) (ha : 1 ≤ a) (hj : 1 ≤ j)
      (hl : if r = 0 then a + j ≤ m else
        j + 2 ≤ m ∧ a + j + 1 ≤ m ∧ (2 ≤ r → 2 ≤ j)) :
      (true, j, a, b) ∈ region m := by
    rw [mem]
    refine ⟨?_, by omega, by omega, Or.inr ⟨r, by omega, ht, ha, hj, hl⟩⟩
    split_ifs at hl <;> omega
  have B (m j a b r : ℕ) (ht : m = a + b + 2 * r) (hj : 2 ≤ j)
      (hjm : j + 1 ≤ m)
      (hl : if r = 0 then 1 ≤ a ∧ 4 ≤ a + j ∧ a + 1 ≤ m
        else if r = 1 then 3 ≤ a + j else True) :
      (false, j, a, b) ∈ region m := by
    rw [mem]
    exact ⟨by omega, by omega, by omega,
      Or.inr ⟨hj, hjm, r, by omega, ht, hl⟩⟩
  have Ae (m : ℕ) : (true, 0, m, 0) ∈ region m := by simp [mem]
  have Be (m a : ℕ) (hm : m = a + 2) : (false, 1, a, 0) ∈ region m := by
    rw [mem]
    exact ⟨by omega, by omega, by omega, Or.inl ⟨rfl, hm, rfl⟩⟩
  have dataA (m j a b : ℕ) (hm : 1 ≤ m) (hq : (true, j, a, b) ∈ region m) :
      ∃ r, m = a + b + 2 * r ∧ 1 ≤ a ∧
        ((j = 0 ∧ r = 0 ∧ b = 0) ∨
          (1 ≤ j ∧ if r = 0 then a + j ≤ m else
            j + 2 ≤ m ∧ a + j + 1 ≤ m ∧ (2 ≤ r → 2 ≤ j))) := by
    rw [mem] at hq
    rcases hq.2.2.2 with ⟨rfl, rfl, rfl⟩ | ⟨r, _, ht, ha, hj, hl⟩
    · exact ⟨0, by omega, hm, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨r, ht, ha, Or.inr ⟨hj, hl⟩⟩
  have dataB (m j a b : ℕ) (hq : (false, j, a, b) ∈ region m) :
      ∃ r, m = a + b + 2 * r ∧
        ((j = 1 ∧ r = 1 ∧ b = 0) ∨
          (2 ≤ j ∧ j + 1 ≤ m ∧
            if r = 0 then 1 ≤ a ∧ 4 ≤ a + j ∧ a + 1 ≤ m
            else if r = 1 then 3 ≤ a + j else True)) := by
    rw [mem] at hq
    rcases hq.2.2.2 with ⟨rfl, ht, rfl⟩ | ⟨hj, hjm, r, _, ht, hl⟩
    · exact ⟨1, by omega, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨r, ht, Or.inr ⟨hj, hjm, hl⟩⟩
  have step (m : ℕ) (hm : 2 ≤ m) (z : List Var) :
      (∃ q ∈ region (m - 1), ∃ p < (encode q.1 q.2.1 q.2.2.1 q.2.2.2).length,
        ∃ t ∈ (rule ((encode q.1 q.2.1 q.2.2.1 q.2.2.2).getD p (false, 0))).support,
          dio ((encode q.1 q.2.1 q.2.2.1 q.2.2.2).take p ++ t ++
            up ((encode q.1 q.2.1 q.2.2.1 q.2.2.2).drop (p + 1))) = z) ↔
      ∃ q ∈ region m, encode q.1 q.2.1 q.2.2.1 q.2.2.2 = z := by
    constructor
    · rintro ⟨⟨f, j, a, b⟩, hq, p, hp, t, ht, hz⟩
      cases f
      · obtain ⟨r, htotal, loc⟩ := dataB (m - 1) j a b hq
        have hj : 1 ≤ j := by rcases loc with h | h <;> omega
        have tbl := (transitions false j a b hj z).mp ⟨p, hp, t, ht, hz⟩
        simp only [Bool.false_eq_true, ↓reduceIte] at tbl
        rcases tbl with he | ⟨s, hs, he⟩ | ⟨s, hs, he⟩ | ⟨s, hs, he⟩ | ⟨s, hs, he⟩
        · refine ⟨(true, j, 1, a + b), ?_, he.symm⟩
          apply A _ _ _ _ (r)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
          all_goals (try split_ifs at *) <;> omega
        · refine ⟨(false, j + 1, a - s, s + b + 1), ?_, he.symm⟩
          apply B _ _ _ _ (r)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
          all_goals (try split_ifs at *) <;> omega
        · refine ⟨(false, j + 1, a - s - 1, s + b), ?_, he.symm⟩
          apply B _ _ _ _ (r + 1)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
          all_goals (try split_ifs at *) <;> omega
        · refine ⟨(false, j, a + b - s, s + 1), ?_, he.symm⟩
          apply B _ _ _ _ (r)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
          all_goals (try split_ifs at *) <;> omega
        · refine ⟨(false, j, a + b - s - 1, s), ?_, he.symm⟩
          apply B _ _ _ _ (r + 1)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
          all_goals (try split_ifs at *) <;> omega
      · obtain ⟨r, htotal, ha, loc⟩ := dataA (m - 1) j a b (by omega) hq
        have tbl := (transitions true j a b ha z).mp ⟨p, hp, t, ht, hz⟩
        simp only [↓reduceIte] at tbl
        rcases tbl with he | ⟨s, hs, he⟩ | ⟨s, hs, hsa, he⟩ | he |
          ⟨s, hs, he⟩ | ⟨s, hs, he⟩
        · refine ⟨(true, j, a + 1, b), ?_, he.symm⟩
          rcases loc with ⟨rfl, rfl, rfl⟩ | ⟨hj, hl⟩
          · have heq : a + 1 = m := by omega
            rw [heq]
            exact Ae m
          · apply A _ _ _ _ r
            all_goals (try split_ifs at *) <;> omega
        · refine ⟨(true, j + 1, a - s, s + b + 1), ?_, he.symm⟩
          apply A _ _ _ _ (r)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
          all_goals (try split_ifs at *) <;> omega
        · refine ⟨(true, j + 1, a - s - 1, s + b), ?_, he.symm⟩
          apply A _ _ _ _ (r + 1)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
          all_goals (try split_ifs at *) <;> omega
        · refine ⟨(false, j + 1, a + b - 1, 0), ?_, he.symm⟩
          rcases loc with ⟨rfl, rfl, rfl⟩ | ⟨hj, hl⟩
          · exact Be m (a - 1) (by omega)
          · apply B _ _ _ _ (r + 1)
            all_goals (try split_ifs at *) <;> omega
        · refine ⟨(false, j + 1, a + b - s, s + 1), ?_, he.symm⟩
          apply B _ _ _ _ (r)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
          all_goals (try split_ifs at *) <;> omega
        · refine ⟨(false, j + 1, a + b - s - 1, s), ?_, he.symm⟩
          apply B _ _ _ _ (r + 1)
          all_goals rcases loc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
          all_goals (try split_ifs at *) <;> omega
    · rintro ⟨⟨f, j, a, b⟩, hq, rfl⟩
      cases f
      · obtain ⟨r, htotal, loc⟩ := dataB m j a b hq
        rcases loc with ⟨rfl, rfl, rfl⟩ | ⟨hj, hjm, hl⟩
        · refine ⟨(true, 0, m - 1, 0), Ae _, ?_⟩
          apply (transitions true 0 (m - 1) 0 (by dsimp; omega) _).mpr
          simp only [↓reduceIte]
          apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
          congr 1 <;> omega
        · by_cases hr0 : r = 0
          · subst r
            have hb : 1 ≤ b := by simp only [↓reduceIte] at hl; omega
            by_cases hc : j = 2 ∨ b = 1
            · refine ⟨(true, j - 1, 1, m - 2), ?_, ?_⟩
              · apply A _ _ _ _ 0
                all_goals (try simp only [↓reduceIte] at *) <;> omega
              · apply (transitions true (j - 1) 1 (m - 2) (by dsimp; omega) _).mpr
                simp only [↓reduceIte]
                apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
                refine ⟨b - 1, ?_, ?_⟩
                · simp only [↓reduceIte] at hl
                  omega
                · congr 1 <;> omega
            · refine ⟨(false, j - 1, m - 2, 1), ?_, ?_⟩
              · apply B _ _ _ _ 0
                all_goals (try simp only [↓reduceIte] at *) <;> omega
              · apply (transitions false (j - 1) (m - 2) 1 (by dsimp; omega) _).mpr
                simp only [Bool.false_eq_true, ↓reduceIte]
                apply Or.inr ∘ Or.inl
                refine ⟨b - 2, ?_, ?_⟩
                · dsimp at hl
                  omega
                · congr 1 <;> omega
          · by_cases hr1 : r = 1
            · subst r
              simp only [one_ne_zero, ↓reduceIte] at hl
              by_cases ha : 1 ≤ a
              · refine ⟨(true, j - 1, 1, a + b), ?_, ?_⟩
                · apply A _ _ _ _ 0
                  all_goals (try simp only [↓reduceIte]) <;> omega
                · apply (transitions true (j - 1) 1 (a + b) (by dsimp; omega) _).mpr
                  simp only [↓reduceIte]
                  apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
                  refine ⟨b, by omega, ?_⟩
                  congr 1 <;> omega
              · have ha0 : a = 0 := by omega
                subst a
                refine ⟨(false, j - 1, 2, b - 1), ?_, ?_⟩
                · apply B _ _ _ _ 0
                  all_goals (try simp only [↓reduceIte]) <;> omega
                · apply (transitions false (j - 1) 2 (b - 1) (by dsimp; omega) _).mpr
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  apply Or.inr ∘ Or.inr ∘ Or.inl
                  refine ⟨1, by omega, ?_⟩
                  congr 1 <;> omega
            · have hr : 2 ≤ r := by omega
              by_cases hlast : j = m - 1
              · refine ⟨(false, j - 1, a + 1, b), ?_, ?_⟩
                · apply B _ _ _ _ (r - 1)
                  all_goals (try split_ifs) <;> omega
                · apply (transitions false (j - 1) (a + 1) b (by dsimp; omega) _).mpr
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  apply Or.inr ∘ Or.inr ∘ Or.inl
                  refine ⟨0, by omega, ?_⟩
                  congr 1 <;> omega
              · by_cases hcorner : r = 2 ∧ j = 2 ∧ a = 0
                · obtain ⟨rfl, rfl, rfl⟩ := hcorner
                  refine ⟨(false, 1, b + 1, 0), Be _ _ (by omega), ?_⟩
                  apply (transitions false 1 (b + 1) 0 (by dsimp; omega) _).mpr
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  apply Or.inr ∘ Or.inr ∘ Or.inl
                  refine ⟨b, by omega, ?_⟩
                  congr 1 <;> omega
                · refine ⟨(false, j, a, b + 1), ?_, ?_⟩
                  · apply B _ _ _ _ (r - 1)
                    all_goals (try split_ifs) <;> omega
                  · apply (transitions false j a (b + 1) (by dsimp; omega) _).mpr
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
                    refine ⟨b, by omega, ?_⟩
                    congr 1 <;> omega
      · obtain ⟨r, htotal, ha, loc⟩ := dataA m j a b (by omega) hq
        rcases loc with ⟨rfl, rfl, rfl⟩ | ⟨hj, hl⟩
        · refine ⟨(true, 0, m - 1, 0), Ae _, ?_⟩
          apply (transitions true 0 (m - 1) 0 (by dsimp; omega) _).mpr
          simp only [↓reduceIte]
          apply Or.inl
          congr 1 <;> omega
        · by_cases ha2 : 2 ≤ a
          · refine ⟨(true, j, a - 1, b), ?_, ?_⟩
            · apply A _ _ _ _ r
              all_goals (try split_ifs at *) <;> omega
            · apply (transitions true j (a - 1) b (by dsimp; omega) _).mpr
              simp only [↓reduceIte]
              apply Or.inl
              congr 1 <;> omega
          · have ha1 : a = 1 := by omega
            subst a
            by_cases hr0 : r = 0
            · subst r
              by_cases hj1 : j = 1
              · subst j
                refine ⟨(true, 0, m - 1, 0), Ae _, ?_⟩
                apply (transitions true 0 (m - 1) 0 (by dsimp; omega) _).mpr
                simp only [↓reduceIte]
                apply Or.inr ∘ Or.inl
                refine ⟨m - 2, by omega, ?_⟩
                congr 1 <;> omega
              · refine ⟨(true, j - 1, 1, m - 2), ?_, ?_⟩
                · apply A _ _ _ _ 0
                  all_goals (try simp only [↓reduceIte] at *) <;> omega
                · apply (transitions true (j - 1) 1 (m - 2) (by dsimp; omega) _).mpr
                  simp only [↓reduceIte]
                  apply Or.inr ∘ Or.inl
                  refine ⟨0, by omega, ?_⟩
                  congr 1 <;> omega
            · by_cases hj1 : j = 1
              · subst j
                refine ⟨(false, 1, m - 3, 0), Be _ _ (by (try split_ifs at *) <;> omega), ?_⟩
                apply (transitions false 1 (m - 3) 0 (by dsimp; omega) _).mpr
                simp only [Bool.false_eq_true, ↓reduceIte]
                apply Or.inl
                congr 1 <;> (try split_ifs at *) <;> omega
              · refine ⟨(false, j, b, 0), ?_, ?_⟩
                · apply B _ _ _ _ r
                  all_goals (try split_ifs at *) <;> omega
                · apply (transitions false j b 0 (by dsimp; omega) _).mpr
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact Or.inl (by simp)
  have base : (deriv (Finsupp.single [(true, 0)] 1)).support =
      (region 1).image (fun q => encode q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    have hderiv : (deriv (Finsupp.single [(true, 0)] 1)).support =
        {encode true 0 1 0} := by
      simp [deriv, derivWord, rule, dio, up, List.insertionSort, List.orderedInsert,
        dioLe, encode, Finsupp.sum_single_index]
    rw [hderiv]
    ext z
    simp only [Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro rfl
      exact ⟨(true, 0, 1, 0), Ae 1, rfl⟩
    · rintro ⟨⟨f, j, a, b⟩, hq, rfl⟩
      rw [mem] at hq
      cases f
      · simp only [Bool.false_eq_true, ↓reduceIte] at hq
        rcases hq.2.2.2 with h | ⟨_, _, r, _, ht, hl⟩ <;> omega
      · simp only [↓reduceIte] at hq
        rcases hq.2.2.2 with ⟨rfl, rfl, rfl⟩ | ⟨r, _, ht, ha, hj, hl⟩
        · rfl
        · split_ifs at hl <;> omega
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [Function.iterate_one, Nat.zero_add] using base
    · have hn' : 1 ≤ n := by omega
      ext z
      rw [(support_reduction n).2 z]
      simp only [ih hn', Finset.mem_image]
      constructor
      · rintro ⟨w, ⟨q, hq, rfl⟩, p, hp, t, ht, hz⟩
        have hh := (step (n + 1) (by omega) z).mp ⟨q, by simpa using hq, p, hp, t, ht, hz⟩
        exact hh
      · intro hz
        obtain ⟨q, hq, p, hp, t, ht, he⟩ := (step (n + 1) (by omega) z).mpr hz
        exact ⟨encode q.1 q.2.1 q.2.2.1 q.2.2.2,
          ⟨q, by simpa using hq, rfl⟩, p, hp, t, ht, he⟩

end D5.S3.Combinatorics.QGrammar.SecGrammar
