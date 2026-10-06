/- GID: D5/S3/Combinatorics/RegularInduced/DysonMcKayBags
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RegularInduced/DysonMcKayBags
   mirror-E: none(waiver:explicit-bag-selection-realization)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact same-degree component spectra characterize regular induced unions. -/

import Mathlib.Tactic
import D5.S3.Combinatorics.RegularInduced.DysonMcKayDefs
import D5.S3.Combinatorics.RegularInduced.DysonMcKaySpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators Fin.NatCast

namespace D5.S3.Combinatorics.RegularInduced.DysonMcKay

open DysonMcKayDefs

open Classical in
/-- The exact order spectrum of a disjoint union is the sum of its component
spectra at one common degree. This includes the literal three-cycle products. -/
theorem regular_union_order_spectrum (comps : List (ℕ × ℕ)) (hadm : Admissible comps)
    (p : ℕ) : HasRegularInduced comps p ↔
    ∃ q : ℕ, 0 < q ∧ ∃ m : Fin comps.length → ℕ, (∑ i, m i) = p ∧
      ∀ i, if (comps.get i).1 = 3 then
        m i = 0 ∨ (m i = q ∧ q ≤ 3 * (comps.get i).2) else
        (∃ k : ℕ, m i = k * q ∧ 2 * k ≤ (comps.get i).1 ∧
          ((comps.get i).2 < q → 3 * k ≤ (comps.get i).1) ∧
          (2 * (comps.get i).2 < q → k = 0)) ∨
        (3 * m i = (comps.get i).1 * q ∧ 3 ≤ q ∧ q ≤ 3 * (comps.get i).2 ∧
          (3 ∣ (comps.get i).1 ∨ 3 ∣ q)) := by
  classical
  have hmodel : HasRegularInduced comps p ↔
      ∃ q : ℕ, 0 < q ∧ ∃ x : (i : Fin comps.length) → Fin (comps.get i).1 → ℕ,
        (∀ i a, x i a ≤ (comps.get i).2) ∧ (∑ i, ∑ a, x i a) = p ∧
        ∀ i a, 0 < x i a →
          (∑ b ∈ univ.filter (fun b : Fin (comps.get i).1 =>
            CycleClose (comps.get i).1 a.val b.val), x i b) = q := by
    classical
    let B := Σ i : Fin comps.length, Fin (comps.get i).1
    let key : Vert comps → B := fun v => ⟨v.1, v.2.1⟩
    let close : B → B → Prop := fun u v =>
      ∃ _ : u.1 = v.1, CycleClose (comps.get u.1).1 u.2.val v.2.val
    have hsym (u v : B) : close u v → close v u := by
      rcases u with ⟨i, a⟩
      rcases v with ⟨j, b⟩
      rintro ⟨h, hc⟩
      cases h
      refine ⟨rfl, ?_⟩
      rcases hc with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    have hadj (u v : Vert comps) :
        (unionGraph comps).Adj u v ↔ u ≠ v ∧ close (key u) (key v) := by
      change (u ≠ v ∧ (close (key u) (key v) ∨ close (key v) (key u))) ↔ _
      constructor
      · rintro ⟨hne, hc | hc⟩
        · exact ⟨hne, hc⟩
        · exact ⟨hne, hsym _ _ hc⟩
      · rintro ⟨hne, hc⟩
        exact ⟨hne, Or.inl hc⟩
    let count (S : Finset (Vert comps)) (b : B) := (S.filter fun v => key v = b).card
    have htotal (S : Finset (Vert comps)) :
        S.card = ∑ i, ∑ a, count S ⟨i, a⟩ := by
      have he := Finset.card_eq_sum_card_fiberwise
        (s := S) (t := (univ : Finset B)) (f := key) (fun _ _ => mem_univ _)
      change S.card = ∑ b : B, count S b at he
      rw [Fintype.sum_sigma] at he
      exact he
    have hclosed (S : Finset (Vert comps)) (i : Fin comps.length)
        (a : Fin (comps.get i).1) :
        (S.filter fun w => close ⟨i, a⟩ (key w)).card =
          ∑ b ∈ univ.filter (fun b : Fin (comps.get i).1 =>
            CycleClose (comps.get i).1 a.val b.val), count S ⟨i, b⟩ := by
      have he := Finset.sum_card_fiberwise_eq_card_filter S
        (univ.filter fun b : B => close ⟨i, a⟩ b) key
      simp only [mem_filter, mem_univ, true_and] at he
      rw [← he]
      rw [Finset.sum_filter]
      change (∑ b : B, if close ⟨i, a⟩ b then count S b else 0) = _
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single i]
      · simp only [close, exists_const, Finset.sum_filter]
      · intro j hj hji
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ close ⟨i, a⟩ ⟨j, b⟩ := by
          rintro ⟨h, _⟩
          exact hji h.symm
        simp [hn]
      · simp
    have hdegree (S : Finset (Vert comps)) (v : Vert comps) (hv : v ∈ S) :
        (S.filter fun w => close (key v) (key w)).card =
          (S.filter fun w => (unionGraph comps).Adj v w).card + 1 := by
      have he : S.filter (fun w => close (key v) (key w)) =
          insert v (S.filter fun w => (unionGraph comps).Adj v w) := by
        ext w
        simp only [mem_filter, mem_insert, hadj]
        constructor
        · rintro ⟨hw, hc⟩
          by_cases h : w = v
          · exact Or.inl h
          · exact Or.inr ⟨hw, Ne.symm h, hc⟩
        · rintro (rfl | ⟨hw, hne, hc⟩)
          · exact ⟨hv, rfl, Or.inl rfl⟩
          · exact ⟨hw, hc⟩
      rw [he, Finset.card_insert_of_notMem]
      simp
    have hfull (i : Fin comps.length) (a : Fin (comps.get i).1) :
        ((univ : Finset (Vert comps)).filter fun v => key v = ⟨i, a⟩).card =
          (comps.get i).2 := by
      calc
        _ = (univ : Finset (Fin (comps.get i).2)).card := by
          symm
          apply Finset.card_bij (fun b _ => (⟨i, a, b⟩ : Vert comps))
          · intro b hb
            simp [key]
          · intro b hb c hc he
            have h := (Sigma.ext_iff.mp he).2
            exact (Prod.mk.inj (eq_of_heq h)).2
          · intro v hv
            have hk := (mem_filter.mp hv).2
            rcases v with ⟨j, b, c⟩
            have hi := congrArg Sigma.fst hk
            dsimp [key] at hi hk
            cases hi
            have hb : b = a := eq_of_heq (Sigma.ext_iff.mp hk).2
            cases hb
            exact ⟨c, mem_univ _, rfl⟩
        _ = _ := by simp
    constructor
    · rintro ⟨S, hp, d, hd⟩
      refine ⟨d + 1, by omega, fun i a => count S ⟨i, a⟩, ?_, ?_, ?_⟩
      · intro i a
        have he := Finset.card_le_card (Finset.filter_subset_filter
          (p := fun v : Vert comps => key v = ⟨i, a⟩) (Finset.subset_univ S))
        exact he.trans_eq (hfull i a)
      · exact (htotal S).symm.trans hp
      · intro i a ha
        obtain ⟨v, hv⟩ := Finset.card_pos.mp ha
        have hvs := (mem_filter.mp hv).1
        have hk := (mem_filter.mp hv).2
        have he := hdegree S v hvs
        rw [hk, hclosed S i a, hd v hvs] at he
        exact he
    · rintro ⟨q, hq, x, hx, hp, he⟩
      let S : Finset (Vert comps) := univ.filter fun v => v.2.2.val < x v.1 v.2.1
      have hcount (i : Fin comps.length) (a : Fin (comps.get i).1) :
          count S ⟨i, a⟩ = x i a := by
        let t : Finset (Fin (comps.get i).2) := univ.filter fun b => b.val < x i a
        have ht : t.card = x i a := by
          calc
            t.card = (univ : Finset (Fin (x i a))).card := by
              symm
              apply Finset.card_bij (fun b _ =>
                (⟨b.val, lt_of_lt_of_le b.isLt (hx i a)⟩ : Fin (comps.get i).2))
              · intro b hb
                simp [t, b.isLt]
              · intro b hb c hc he
                exact Fin.ext (congrArg (fun z : Fin (comps.get i).2 => z.val) he)
              · intro b hb
                have hlt : b.val < x i a := (mem_filter.mp hb).2
                exact ⟨⟨b.val, hlt⟩, mem_univ _, Fin.ext rfl⟩
            _ = x i a := by simp
        calc
          count S ⟨i, a⟩ = t.card := by
            symm
            apply Finset.card_bij (fun b _ => (⟨i, a, b⟩ : Vert comps))
            · intro b hb
              simpa [S, key, t] using hb
            · intro b hb c hc he
              have h := (Sigma.ext_iff.mp he).2
              exact (Prod.mk.inj (eq_of_heq h)).2
            · intro v hv
              have hk := (mem_filter.mp hv).2
              have hs := (mem_filter.mp hv).1
              rcases v with ⟨j, b, c⟩
              have hi := congrArg Sigma.fst hk
              dsimp [key] at hi hk
              cases hi
              have hb : b = a := eq_of_heq (Sigma.ext_iff.mp hk).2
              cases hb
              refine ⟨c, ?_, rfl⟩
              simpa [S, t] using hs
          _ = x i a := ht
      refine ⟨S, ?_, q - 1, ?_⟩
      · rw [htotal]
        simpa only [hcount] using hp
      · intro v hv
        have hpos : 0 < x v.1 v.2.1 := by
          have ht := (mem_filter.mp hv).2
          omega
        have heq := hdegree S v hv
        change (S.filter fun w => close ⟨v.1, v.2.1⟩ (key w)).card = _ at heq
        rw [hclosed] at heq
        simp only [hcount] at heq
        rw [he v.1 v.2.1 hpos] at heq
        omega
  have hlocal {r s q m : ℕ} [NeZero r] (hr : 3 ≤ r) (hq : 0 < q) :
      (∃ x : Fin r → ℕ, (∀ a, x a ≤ s) ∧ (∑ a, x a) = m ∧
        ∀ a, 0 < x a →
          (∑ b ∈ univ.filter (fun b : Fin r => CycleClose r a.val b.val), x b) = q) ↔
      (if r = 3 then m = 0 ∨ (m = q ∧ q ≤ 3 * s) else
        (∃ k : ℕ, m = k * q ∧ 2 * k ≤ r ∧
          (s < q → 3 * k ≤ r) ∧ (2 * s < q → k = 0)) ∨
        (3 * m = r * q ∧ 3 ≤ q ∧ q ≤ 3 * s ∧ (3 ∣ r ∨ 3 ∣ q))) := by
    by_cases hr₃ : r = 3
    · subst r
      simp only [ite_true]
      have hclose (a b : Fin 3) : CycleClose 3 a.val b.val := by
        fin_cases a <;> fin_cases b <;> norm_num [CycleClose]
      have heq (x : Fin 3 → ℕ) (a : Fin 3) :
          (∑ b ∈ univ.filter (fun b : Fin 3 => CycleClose 3 a.val b.val), x b) =
            ∑ b, x b := by simp [hclose]
      constructor
      · rintro ⟨x, hx, hm, he⟩
        by_cases hz : m = 0
        · exact Or.inl hz
        · right
          have hpos : ∃ a, 0 < x a := by
            by_contra hn
            push Not at hn
            have hx₀ : ∀ a, x a = 0 := fun a => by have := hn a; omega
            simp [hx₀] at hm
            omega
          obtain ⟨a, ha⟩ := hpos
          have he' := he a ha
          rw [heq, hm] at he'
          have hsum := Finset.sum_le_sum (s := (univ : Finset (Fin 3)))
            (fun a _ => hx a)
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul, hm, he'] at hsum
          exact ⟨he', hsum⟩
      · rintro (hm₀ | ⟨hmq, hqs⟩)
        · subst m
          exact ⟨fun _ => 0, by simp, by simp, by simp⟩
        · subst m
          let a := min s q
          let b := min s (q - a)
          let c := q - a - b
          have ha : a ≤ s := by dsimp [a]; omega
          have hb : b ≤ s := by dsimp [b]; omega
          have hc : c ≤ s := by dsimp [c, b, a]; omega
          have habc : a + b + c = q := by dsimp [c, b, a]; omega
          let x : Fin 3 → ℕ := ![a, b, c]
          have hx : ∀ i, x i ≤ s := by intro i; fin_cases i <;> simp [x] <;> omega
          have hs : (∑ i, x i) = q := by
            simp [Fin.sum_univ_succ, x]
            omega
          exact ⟨x, hx, hs, fun i _ => (heq x i).trans hs⟩
    · have hr₄ : 4 ≤ r := by omega
      simp only [hr₃, ite_false]
      have hsuc (a : Fin r) : (a + 1).val = (a.val + 1) % r := by
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < r by omega)]
      have hclose (a b : Fin r) :
          CycleClose r a.val b.val ↔ b = a - 1 ∨ b = a ∨ b = a + 1 := by
        unfold CycleClose
        rw [← hsuc a, ← hsuc b]
        simp only [← Fin.ext_iff, eq_sub_iff_add_eq]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h.symm)
          · exact Or.inr (Or.inr h.symm)
          · exact Or.inl h
        · rintro (h | h | h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl h.symm
          · exact Or.inr (Or.inl h.symm)
      have hone : (1 : Fin r) ≠ 0 := by
        intro h
        have he := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (show 1 < r by omega)] at he
      have htwo : (2 : Fin r) ≠ 0 := by
        intro h
        have he := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (show 2 < r by omega)] at he
      have two : (2 : Fin r) = 1 + 1 := Nat.cast_add 1 1
      have heq (x : Fin r → ℕ) (a : Fin r) :
          (∑ b ∈ univ.filter (fun b : Fin r => CycleClose r a.val b.val), x b) =
            x (a - 1) + x a + x (a + 1) := by
        have hn₁ : a - 1 ≠ a := by
          intro h
          have he := sub_eq_iff_eq_add.mp h
          have hz : (0 : Fin r) = 1 := by
            apply add_left_cancel (a := a)
            simpa using he
          exact hone hz.symm
        have hn₂ : a ≠ a + 1 := by
          intro h
          have hz : (0 : Fin r) = 1 := by
            apply add_left_cancel (a := a)
            simpa using h
          exact hone hz.symm
        have hn₃ : a - 1 ≠ a + 1 := by
          intro h
          have he := sub_eq_iff_eq_add.mp h
          rw [add_assoc, ← two] at he
          have hz : (0 : Fin r) = 2 := by
            apply add_left_cancel (a := a)
            simpa using he
          exact htwo hz.symm
        have hf : univ.filter (fun b : Fin r => CycleClose r a.val b.val) =
            {a - 1, a, a + 1} := by
          ext b
          simp only [mem_filter, mem_univ, true_and, hclose, mem_insert, mem_singleton]
        rw [hf]
        simp [hn₁, hn₂, hn₃, add_assoc]
      rw [← cyclic_order_spectrum (m := m) hr₄ hq]
      constructor
      · rintro ⟨x, hx, hm, he⟩
        exact ⟨x, hx, hm, fun a ha => (heq x a).symm.trans (he a ha)⟩
      · rintro ⟨x, hx, hm, he⟩
        exact ⟨x, hx, hm, fun a ha => (heq x a).trans (he a ha)⟩
  constructor
  · intro h
    obtain ⟨q, hq, x, hx, hp, he⟩ := hmodel.mp h
    refine ⟨q, hq, fun i => ∑ a, x i a, hp, ?_⟩
    intro i
    have hr := (hadm _ (List.get_mem comps i)).1
    let : NeZero (comps.get i).1 := ⟨by omega⟩
    exact (hlocal hr hq).mp ⟨x i, hx i, rfl, he i⟩
  · rintro ⟨q, hq, m, hm, he⟩
    have hex : ∀ i : Fin comps.length, ∃ x : Fin (comps.get i).1 → ℕ,
        (∀ a, x a ≤ (comps.get i).2) ∧ (∑ a, x a) = m i ∧
        ∀ a, 0 < x a →
          (∑ b ∈ univ.filter (fun b : Fin (comps.get i).1 =>
            CycleClose (comps.get i).1 a.val b.val), x b) = q := by
      intro i
      have hr := (hadm _ (List.get_mem comps i)).1
      let : NeZero (comps.get i).1 := ⟨by omega⟩
      exact (hlocal hr hq).mpr (he i)
    choose x hx hm' he' using hex
    apply hmodel.mpr
    refine ⟨q, hq, x, hx, ?_, he'⟩
    simpa only [hm'] using hm

end D5.S3.Combinatorics.RegularInduced.DysonMcKay
