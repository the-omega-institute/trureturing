/- GID: D5/S3/Combinatorics/QGrammar/SecGrammarTransitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QGrammar/SecGrammarTransitions
   mirror-E: none(waiver:sec-grammar-transition-table)
   anchors: []
   utility: none
   digest: Exhaustive positional branches and their inverse position witnesses on Sec tuples. -/

import D5.S3.Combinatorics.QGrammar.SecGrammarWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QGrammar.SecGrammar

open SecGrammarDefs

/-- The exact successors, including the last-high-constant A-to-B boundary. -/
theorem transitions (f : Bool) (j a b : ℕ)
    (hf : if f then 1 ≤ a else 1 ≤ j) (z : List Var) :
    (∃ p < (encode f j a b).length,
      ∃ t ∈ (rule ((encode f j a b).getD p (false, 0))).support,
        dio ((encode f j a b).take p ++ t ++ up ((encode f j a b).drop (p + 1))) = z) ↔
    if f then
      z = encode true j (a + 1) b ∨
      (∃ p < a, z = encode true (j + 1) (a - p) (p + b + 1)) ∨
      (∃ p < a, p + 1 < a ∧ z = encode true (j + 1) (a - p - 1) (p + b)) ∨
      z = encode false (j + 1) (a + b - 1) 0 ∨
      (∃ s < b, z = encode false (j + 1) (a + b - s) (s + 1)) ∨
      (∃ s < b, z = encode false (j + 1) (a + b - s - 1) s)
    else
      z = encode true j 1 (a + b) ∨
      (∃ p < a, z = encode false (j + 1) (a - p) (p + b + 1)) ∨
      (∃ p < a, z = encode false (j + 1) (a - p - 1) (p + b)) ∨
      (∃ s < b, z = encode false j (a + b - s) (s + 1)) ∨
      (∃ s < b, z = encode false j (a + b - s - 1) s) := by
  classical
  have : Std.Total dioLe := ⟨by
    rintro ⟨x, i⟩ ⟨y, k⟩
    cases x <;> cases y <;> simp [dioLe] <;> omega⟩
  have : IsTrans Var dioLe := ⟨by
    rintro ⟨x, i⟩ ⟨y, k⟩ ⟨v, l⟩ h h'
    cases x <;> cases y <;> cases v <;> simp_all [dioLe] <;> omega⟩
  have : Std.Antisymm dioLe := ⟨by
    rintro ⟨x, i⟩ ⟨y, k⟩ h h'
    cases x <;> cases y <;> simp_all [dioLe, Prod.ext_iff] <;> omega⟩
  have sorted (g : Bool) (k c d : ℕ) (hk : if g then True else 1 ≤ k) :
      (encode g k c d).Pairwise dioLe := by
    cases g <;> simp_all [encode, List.pairwise_append, List.pairwise_replicate,
      List.mem_replicate, dioLe] <;> omega
  have canon (raw : List Var) (g : Bool) (k c d : ℕ)
      (hk : if g then True else 1 ≤ k)
      (hc : ∀ v, raw.count v = (encode g k c d).count v) : dio raw = encode g k c d := by
    have hperm := (List.perm_insertionSort dioLe raw).trans (List.perm_iff_count.mpr hc)
    exact hperm.eq_of_pairwise' (List.pairwise_insertionSort dioLe raw) (sorted g k c d hk)
  have block (L S : List Var) (v : Var) (r p : ℕ) (hp : p < r) :
      (L ++ List.replicate r v ++ S).take (L.length + p) = L ++ List.replicate p v ∧
      (L ++ List.replicate r v ++ S).drop (L.length + p + 1) =
        List.replicate (r - p - 1) v ++ S ∧
      (L ++ List.replicate r v ++ S).getD (L.length + p) (false, 0) = v := by
    refine ⟨?_, ?_, ?_⟩
    · simp (disch := omega) [List.take_append, List.take_of_length_le,
        Nat.sub_eq_zero_of_le]
    · simp (disch := omega) [List.drop_append, Nat.sub_eq_zero_of_le,
        List.drop_eq_nil_of_le, Nat.sub_sub]
      congr 2
      omega
    · rw [List.append_assoc, List.getD_append_right L _ _ _ (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getD_append _ S _ p (by simp; omega), List.getD_replicate v hp]
  have rules (v : Var) (t : List Var) : t ∈ (rule v).support ↔
      t = [v, (false, v.2 + 1)] ∨ (v.1 = false ∧ t = []) := by
    rcases v with ⟨v, k⟩
    cases v
    · by_cases h₀ : t = []
      · subst t
        simp [rule, Finsupp.mem_support_iff]
      · by_cases h₁ : t = [(false, k), (false, k + 1)]
        · subst t
          simp [rule, Finsupp.mem_support_iff]
        · simp [rule, Finsupp.mem_support_iff, h₀, h₁]
    · simp [rule]
  cases f
  · simp only [Bool.false_eq_true, ↓reduceIte] at hf ⊢
    have high (p : ℕ) (hp : p < a) :
        (encode false j a b).getD (p) (false, 0) = (false, j) ∧
        dio ((encode false j a b).take (p) ++ [(false, j), (false, ((false, j)).2 + 1)] ++
          up ((encode false j a b).drop (p + 1))) = encode false (j + 1) (a - p) (p + b + 1) ∧
        dio ((encode false j a b).take (p) ++ [] ++
          up ((encode false j a b).drop (p + 1))) = encode false (j + 1) (a - p - 1) (p + b) := by
      have hh :
          (encode false j a b).take (p) = [] ++ List.replicate p (false, j) ∧
          (encode false j a b).drop (p + 1) = List.replicate (a - p - 1) (false, j) ++ [(true, j)]
            ++ List.replicate b (false, j - 1) ∧
          (encode false j a b).getD (p) (false, 0) = (false, j) := by
        simpa [encode, List.append_assoc] using block ([]) ([(true, j)] ++ List.replicate b
          (false, j - 1)) (false, j) a p hp
      obtain ⟨ht, hd, hg⟩ := hh
      refine ⟨hg, ?_, ?_⟩
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons,
            Nat.sub_add_cancel hf] <;>
            split_ifs <;> omega
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons,
            Nat.sub_add_cancel hf] <;>
            split_ifs <;> omega
    have low (s : ℕ) (hp : s < b) :
        (encode false j a b).getD (a + 1 + s) (false, 0) = (false, j - 1) ∧
        dio ((encode false j a b).take (a + 1 + s) ++ [(false, j - 1), (false, ((false, j - 1)).2
          + 1)] ++
          up ((encode false j a b).drop (a + 1 + s + 1))) = encode false j (a + b - s) (s + 1) ∧
        dio ((encode false j a b).take (a + 1 + s) ++ [] ++
          up ((encode false j a b).drop (a + 1 + s + 1))) = encode false j (a + b - s - 1) s := by
      have hh :
          (encode false j a b).take (a + 1 + s) = List.replicate a (false, j) ++ [(true, j)] ++
            List.replicate s (false, j - 1) ∧
          (encode false j a b).drop (a + 1 + s + 1) = List.replicate (b - s - 1) (false, j - 1) ++
            [] ∧
          (encode false j a b).getD (a + 1 + s) (false, 0) = (false, j - 1) := by
        simpa [encode, List.append_assoc] using block (List.replicate a (false, j) ++ [(true, j)])
          ([]) (false, j - 1) b s hp
      obtain ⟨ht, hd, hg⟩ := hh
      refine ⟨hg, ?_, ?_⟩
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons,
            Nat.sub_add_cancel hf] <;>
            split_ifs <;> omega
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons,
            Nat.sub_add_cancel hf] <;>
            split_ifs <;> omega
    have middle :
        (encode false j a b).getD (a) (false, 0) = (true, j) ∧
        dio ((encode false j a b).take (a) ++ [(true, j), (false, ((true, j)).2 + 1)] ++
          up ((encode false j a b).drop (a + 1))) = encode true j 1 (a + b) := by
      have hh :
          (encode false j a b).take (a) = List.replicate a (false, j) ++ List.replicate 0 (true,
            j) ∧
          (encode false j a b).drop (a + 1) = List.replicate (1 - 0 - 1) (true, j) ++
            List.replicate b (false, j - 1) ∧
          (encode false j a b).getD (a) (false, 0) = (true, j) := by
        simpa [encode, List.append_assoc] using block (List.replicate a (false, j))
          (List.replicate b (false, j - 1)) (true, j) 1 0 (by decide)
      obtain ⟨ht, hd, hg⟩ := hh
      refine ⟨hg, ?_⟩
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons,
            Nat.sub_add_cancel hf] <;>
            split_ifs <;> omega
    have len : (encode false j a b).length = a + 1 + b := by simp [encode]; omega
    constructor
    · rintro ⟨p, hp, t, ht, hz⟩
      rw [len] at hp
      rcases (rules _ _).mp ht with rfl | ⟨hv, rfl⟩
      · by_cases hpa : p < a
        · obtain ⟨hg, he, _⟩ := high p hpa
          rw [hg] at hz
          exact Or.inr (Or.inl ⟨p, hpa, hz.symm.trans he⟩)
        · by_cases hpe : p = a
          · subst p
            rw [middle.1] at hz
            exact Or.inl (hz.symm.trans middle.2)
          · let s := p - a - 1
            have hps : p = a + 1 + s := by dsimp [s]; omega
            have hs : s < b := by omega
            obtain ⟨hg, he, _⟩ := low s hs
            rw [hps, hg] at hz
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, hz.symm.trans he⟩)))
      · by_cases hpa : p < a
        · obtain ⟨_, _, he⟩ := high p hpa
          exact Or.inr (Or.inr (Or.inl ⟨p, hpa, hz.symm.trans he⟩))
        · by_cases hpe : p = a
          · subst p
            rw [middle.1] at hv
            simp at hv
          · let s := p - a - 1
            have hps : p = a + 1 + s := by dsimp [s]; omega
            have hs : s < b := by omega
            obtain ⟨_, _, he⟩ := low s hs
            rw [hps] at hz
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, hz.symm.trans he⟩)))
    · rintro (he | ⟨p, hp, he⟩ | ⟨p, hp, he⟩ | ⟨s, hs, he⟩ | ⟨s, hs, he⟩)
      · refine ⟨a, by omega, [(true, j), (false, j + 1)], ?_, middle.2.trans he.symm⟩
        rw [middle.1, rules]
        simp
      · obtain ⟨hg, he', _⟩ := high p hp
        refine ⟨p, by omega, [(false, j), (false, j + 1)], ?_, he'.trans he.symm⟩
        rw [hg, rules]
        simp
      · obtain ⟨hg, _, he'⟩ := high p hp
        refine ⟨p, by omega, [], ?_, he'.trans he.symm⟩
        rw [hg, rules]
        simp
      · obtain ⟨hg, he', _⟩ := low s hs
        refine ⟨a + 1 + s, by omega,
          [(false, j - 1), (false, (j - 1) + 1)], ?_, he'.trans he.symm⟩
        rw [hg, rules]
        simp
      · obtain ⟨hg, _, he'⟩ := low s hs
        refine ⟨a + 1 + s, by omega, [], ?_, he'.trans he.symm⟩
        rw [hg, rules]
        simp
  · simp only [↓reduceIte] at hf ⊢
    have high (p : ℕ) (hp : p < a) :
        (encode true j a b).getD (p) (false, 0) = (false, j + 1) ∧
        dio ((encode true j a b).take (p) ++ [(false, j + 1), (false, ((false, j + 1)).2 + 1)] ++
          up ((encode true j a b).drop (p + 1))) = encode true (j + 1) (a - p) (p + b + 1) ∧
        dio ((encode true j a b).take (p) ++ [] ++
          up ((encode true j a b).drop (p + 1))) = if p + 1 < a then encode true (j + 1) (a - p -
            1) (p + b)
          else encode false (j + 1) (a + b - 1) 0 := by
      have hh :
          (encode true j a b).take (p) = [] ++ List.replicate p (false, j + 1) ∧
          (encode true j a b).drop (p + 1) = List.replicate (a - p - 1) (false, j + 1) ++
            List.replicate b (false, j) ++ [(true, j)] ∧
          (encode true j a b).getD (p) (false, 0) = (false, j + 1) := by
        simpa [encode, List.append_assoc] using block ([]) (List.replicate b (false, j) ++ [(true,
          j)]) (false, j + 1) a p hp
      obtain ⟨ht, hd, hg⟩ := hh
      refine ⟨hg, ?_, ?_⟩
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons]
            <;>
            split_ifs <;> omega
      · rw [ht, hd]
        split_ifs with he
        · apply canon
          · simp <;> omega
          · rintro ⟨v, i⟩
            cases v <;> simp [encode, up, List.count_append, List.count_replicate,
              List.count_cons] <;>
              split_ifs <;> omega
        · apply canon
          · simp <;> omega
          · rintro ⟨v, i⟩
            cases v <;> simp [encode, up, List.count_append, List.count_replicate,
              List.count_cons] <;>
              split_ifs <;> omega
    have low (s : ℕ) (hp : s < b) :
        (encode true j a b).getD (a + s) (false, 0) = (false, j) ∧
        dio ((encode true j a b).take (a + s) ++ [(false, j), (false, ((false, j)).2 + 1)] ++
          up ((encode true j a b).drop (a + s + 1))) = encode false (j + 1) (a + b - s) (s + 1) ∧
        dio ((encode true j a b).take (a + s) ++ [] ++
          up ((encode true j a b).drop (a + s + 1))) = encode false (j + 1) (a + b - s - 1) s := by
      have hh :
          (encode true j a b).take (a + s) = List.replicate a (false, j + 1) ++ List.replicate s
            (false, j) ∧
          (encode true j a b).drop (a + s + 1) = List.replicate (b - s - 1) (false, j) ++ [(true,
            j)] ∧
          (encode true j a b).getD (a + s) (false, 0) = (false, j) := by
        simpa [encode, List.append_assoc] using block (List.replicate a (false, j + 1)) ([(true,
          j)]) (false, j) b s hp
      obtain ⟨ht, hd, hg⟩ := hh
      refine ⟨hg, ?_, ?_⟩
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons]
            <;>
            split_ifs <;> omega
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons]
            <;>
            split_ifs <;> omega
    have middle :
        (encode true j a b).getD (a + b) (false, 0) = (true, j) ∧
        dio ((encode true j a b).take (a + b) ++ [(true, j), (false, ((true, j)).2 + 1)] ++
          up ((encode true j a b).drop (a + b + 1))) = encode true j (a + 1) b := by
      have hh :
          (encode true j a b).take (a + b) = List.replicate a (false, j + 1) ++ List.replicate b
            (false, j) ++ List.replicate 0 (true, j) ∧
          (encode true j a b).drop (a + b + 1) = List.replicate (1 - 0 - 1) (true, j) ++ [] ∧
          (encode true j a b).getD (a + b) (false, 0) = (true, j) := by
        simpa [encode, List.append_assoc] using block (List.replicate a (false, j + 1) ++
          List.replicate b (false, j)) ([]) (true, j) 1 0 (by decide)
      obtain ⟨ht, hd, hg⟩ := hh
      refine ⟨hg, ?_⟩
      · rw [ht, hd]
        apply canon
        · simp <;> omega
        · rintro ⟨v, i⟩
          cases v <;> simp [encode, up, List.count_append, List.count_replicate, List.count_cons]
            <;>
            split_ifs <;> omega
    have len : (encode true j a b).length = a + b + 1 := by simp [encode]; omega
    constructor
    · rintro ⟨p, hp, t, ht, hz⟩
      rw [len] at hp
      rcases (rules _ _).mp ht with rfl | ⟨hv, rfl⟩
      · by_cases hpa : p < a
        · obtain ⟨hg, he, _⟩ := high p hpa
          rw [hg] at hz
          exact Or.inr (Or.inl ⟨p, hpa, hz.symm.trans he⟩)
        · by_cases hpl : p < a + b
          · let s := p - a
            have hps : p = a + s := by dsimp [s]; omega
            have hs : s < b := by omega
            obtain ⟨hg, he, _⟩ := low s hs
            rw [hps, hg] at hz
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, hz.symm.trans he⟩))))
          · have hpe : p = a + b := by omega
            subst p
            rw [middle.1] at hz
            exact Or.inl (hz.symm.trans middle.2)
      · by_cases hpa : p < a
        · obtain ⟨_, _, he⟩ := high p hpa
          by_cases hpe : p + 1 < a
          · rw [if_pos hpe] at he
            exact Or.inr (Or.inr (Or.inl ⟨p, hpa, hpe, hz.symm.trans he⟩))
          · rw [if_neg hpe] at he
            exact Or.inr (Or.inr (Or.inr (Or.inl (hz.symm.trans he))))
        · by_cases hpl : p < a + b
          · let s := p - a
            have hps : p = a + s := by dsimp [s]; omega
            have hs : s < b := by omega
            obtain ⟨_, _, he⟩ := low s hs
            rw [hps] at hz
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, hz.symm.trans he⟩))))
          · have hpe : p = a + b := by omega
            subst p
            rw [middle.1] at hv
            simp at hv
    · rintro (he | ⟨p, hp, he⟩ | ⟨p, hp, hpe, he⟩ | he | ⟨s, hs, he⟩ | ⟨s, hs, he⟩)
      · refine ⟨a + b, by omega, [(true, j), (false, j + 1)], ?_,
          middle.2.trans he.symm⟩
        rw [middle.1, rules]
        simp
      · obtain ⟨hg, he', _⟩ := high p hp
        refine ⟨p, by omega, [(false, j + 1), (false, (j + 1) + 1)], ?_,
          he'.trans he.symm⟩
        rw [hg, rules]
        simp
      · obtain ⟨hg, _, he'⟩ := high p hp
        rw [if_pos hpe] at he'
        refine ⟨p, by omega, [], ?_, he'.trans he.symm⟩
        rw [hg, rules]
        simp
      · have hp : a - 1 < a := by omega
        obtain ⟨hg, _, he'⟩ := high (a - 1) hp
        rw [if_neg (by omega)] at he'
        refine ⟨a - 1, by omega, [], ?_, he'.trans he.symm⟩
        rw [hg, rules]
        simp
      · obtain ⟨hg, he', _⟩ := low s hs
        refine ⟨a + s, by omega, [(false, j), (false, j + 1)], ?_,
          he'.trans he.symm⟩
        rw [hg, rules]
        simp
      · obtain ⟨hg, _, he'⟩ := low s hs
        refine ⟨a + s, by omega, [], ?_, he'.trans he.symm⟩
        rw [hg, rules]
        simp

end D5.S3.Combinatorics.QGrammar.SecGrammar
