/- GID: D5/S3/Combinatorics/QGrammar/SecGrammarCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QGrammar/SecGrammarCounting
   mirror-E: none(waiver:sec-grammar-layer-count)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: A layer bijection and symbolic summation count the reachable region. -/

import D5.S3.Combinatorics.QGrammar.SecGrammarRegion
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.QGrammar.SecGrammar

open SecGrammarDefs Finset

/-- Reparametrizing each layer by its upper multiplicity gives triangular A-fibers
and rectangular B-fibers with one missing corner in each of the first two layers. -/
theorem region_count (n : ℕ) (hn : 1 ≤ n) : (region n).card = omegaFormula n := by
  classical
  have memR (f : Bool) (j a b : ℕ) :
      (f, j, a, b) ∈ region n ↔ j ≤ n ∧ a ≤ n ∧ b ≤ n ∧
        if f then
          (j = 0 ∧ a = n ∧ b = 0) ∨
          ∃ r ≤ n, n = a + b + 2 * r ∧ 1 ≤ a ∧ 1 ≤ j ∧
            (if r = 0 then a + j ≤ n else
              j + 2 ≤ n ∧ a + j + 1 ≤ n ∧ (2 ≤ r → 2 ≤ j))
        else
          (j = 1 ∧ n = a + 2 ∧ b = 0) ∨
          2 ≤ j ∧ j + 1 ≤ n ∧ ∃ r ≤ n, n = a + b + 2 * r ∧
            (if r = 0 then 1 ≤ a ∧ 4 ≤ a + j ∧ a + 1 ≤ n
              else if r = 1 then 3 ≤ a + j else True) := by
    simp only [region, mem_filter, product_eq_sprod, mem_product, mem_univ, mem_range,
      Nat.lt_succ_iff, true_and, and_assoc]
  by_cases h1 : n = 1
  · subst n
    have h : region 1 = {(true, 0, 1, 0)} := by
      ext ⟨f, j, a, b⟩
      rw [memR]
      simp only [mem_singleton, Prod.mk.injEq]
      cases f <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · constructor
        · intro h
          rcases h.2.2.2 with he | ⟨hj, hjn, r, hr, ht, hl⟩ <;> omega
        · rintro ⟨h, _⟩
          cases h
      · constructor
        · intro h
          rcases h.2.2.2 with he | ⟨r, hr, ht, ha, hj, hl⟩
          · exact ⟨trivial, he⟩
          · split_ifs at hl <;> omega
        · rintro ⟨_, rfl, rfl, rfl⟩
          simp
    simp [h, omegaFormula]
  by_cases h2 : n = 2
  · subst n
    have h : region 2 = {(true, 0, 2, 0), (true, 1, 1, 1), (false, 1, 0, 0)} := by
      ext ⟨f, j, a, b⟩
      rw [memR]
      simp only [mem_insert, mem_singleton, Prod.mk.injEq]
      cases f <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · constructor
        · intro h
          rcases h.2.2.2 with he | ⟨hj, hjn, r, hr, ht, hl⟩
          · right; right
            exact ⟨trivial, by omega, by omega, by omega⟩
          · omega
        · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl, rfl, rfl⟩)
          · cases h
          · cases h
          · simp
      · constructor
        · intro h
          rcases h.2.2.2 with he | ⟨r, hr, ht, ha, hj, hl⟩
          · exact Or.inl ⟨trivial, he⟩
          · right; left
            refine ⟨trivial, ?_, ?_, ?_⟩
            all_goals split_ifs at hl <;> omega
        · rintro (⟨_, rfl, rfl, rfl⟩ | ⟨_, rfl, rfl, rfl⟩ | ⟨h, _⟩)
          · simp
          · refine ⟨by omega, by omega, by omega, Or.inr ⟨0, by omega, ?_⟩⟩
            simp
          · cases h
    simp [h, omegaFormula]
  have hn3 : 3 ≤ n := by omega
  let U (f : Bool) (r : ℕ) : ℕ :=
    if f then (if r = 0 then n - 1 else n - 2 * r)
    else (if r = 0 then n - 1 else n - 2 * r + 1)
  let P (f : Bool) (r : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
    ((range (U f r)).sigma fun t =>
      if f then Icc (if r ≤ 1 then 1 else 2) (n - (t + 1) - (if r = 0 then 0 else 1))
      else Icc 2 (n - 1)).filter fun p =>
        f = true ∨ ¬(r ≤ 1 ∧ p.1 = 0 ∧ p.2 = 2)
  let T := (univ.product (range (n / 2 + 1))).sigma fun q => P q.1 q.2
  let E : Finset (Bool × ℕ × ℕ × ℕ) := {(true, 0, n, 0), (false, 1, n - 2, 0)}
  let F (p : Σ _ : Bool × ℕ, Σ _ : ℕ, ℕ) : Bool × ℕ × ℕ × ℕ :=
    let a := if p.1.1 || (p.1.2 == 0) then p.2.1 + 1 else p.2.1
    (p.1.1, p.2.2, a, n - 2 * p.1.2 - a)
  have memP (f : Bool) (r t j : ℕ) :
      (⟨t, j⟩ : Σ _ : ℕ, ℕ) ∈ P f r ↔ t < U f r ∧
        (if f then (if r ≤ 1 then 1 else 2) ≤ j ∧
          j ≤ n - (t + 1) - (if r = 0 then 0 else 1)
        else 2 ≤ j ∧ j ≤ n - 1) ∧
        (f = true ∨ ¬(r ≤ 1 ∧ t = 0 ∧ j = 2)) := by
    cases f <;> simp [P, mem_sigma, and_assoc]
  have data (p : Σ _ : Bool × ℕ, Σ _ : ℕ, ℕ) (hp : p ∈ T) :
      n = (F p).2.2.1 + (F p).2.2.2 + 2 * p.1.2 ∧
      (F p).2.1 ≥ (if p.1.1 then 1 else 2) := by
    rcases p with ⟨⟨f, r⟩, t, j⟩
    simp only [T, mem_sigma, product_eq_sprod, mem_product, mem_univ, true_and, mem_range] at hp
    rw [memP] at hp
    dsimp [F]
    have hr : 2 * r ≤ n := by omega
    cases f <;> by_cases h : r = 0 <;>
      simp [U, h] at hp ⊢ <;> (try split_ifs at hp) <;> omega
  have forward (p : Σ _ : Bool × ℕ, Σ _ : ℕ, ℕ) (hp : p ∈ T) :
      F p ∈ region n := by
    have ht := (data p hp).1
    rcases p with ⟨⟨f, r⟩, t, j⟩
    simp only [T, mem_sigma, product_eq_sprod, mem_product, mem_univ, true_and, mem_range] at hp
    rw [memP] at hp
    dsimp [F] at ht ⊢
    cases f <;> by_cases h : r = 0
    all_goals simp [U, h] at hp ht ⊢
    all_goals rw [memR]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte]
    · refine ⟨by omega, by omega, by omega, Or.inr ⟨by omega, by omega,
        r, by omega, (by omega), ?_⟩⟩
      simp [h]
      omega
    · refine ⟨by omega, by omega, by omega, Or.inr ⟨by omega, by omega,
        r, by omega, (by omega), ?_⟩⟩
      split_ifs <;> omega
    · refine ⟨by omega, by omega, by omega,
        Or.inr ⟨r, by omega, (by omega), by omega, by omega, ?_⟩⟩
      simp [h]
      omega
    · refine ⟨by omega, by omega, by omega,
        Or.inr ⟨r, by omega, (by omega), by omega, ?_, ?_⟩⟩
      all_goals split_ifs at hp ⊢ <;> omega
  have decomp : region n = E ∪ T.image F := by
    ext q
    rcases q with ⟨f, j, a, b⟩
    rw [mem_union, mem_image]
    constructor
    · rw [memR]
      intro hq
      cases f
      · rcases hq.2.2.2 with he | ⟨hj, hjn, r, hr, ht, hl⟩
        · left
          simp only [E, mem_insert, mem_singleton, Prod.mk.injEq]
          right
          exact ⟨trivial, by omega, by omega, by omega⟩
        · right
          let t := if r = 0 then a - 1 else a
          refine ⟨⟨(false, r), t, j⟩, ?_, ?_⟩
          · simp only [T, mem_sigma, product_eq_sprod, mem_product, mem_univ, true_and, mem_range]
            refine ⟨by omega, ?_⟩
            rw [memP]
            dsimp [t, U]
            split_ifs at hl ⊢ <;> omega
          · dsimp [F, t]
            split_ifs at hl ⊢ <;> simp_all
      · rcases hq.2.2.2 with he | ⟨r, hr, ht, ha, hj, hl⟩
        · left
          simp only [E, mem_insert, mem_singleton, Prod.mk.injEq]
          left
          exact ⟨trivial, he⟩
        · right
          refine ⟨⟨(true, r), a - 1, j⟩, ?_, ?_⟩
          · simp only [T, mem_sigma, product_eq_sprod, mem_product, mem_univ, true_and, mem_range]
            refine ⟨by omega, ?_⟩
            rw [memP]
            dsimp [U]
            split_ifs at hl ⊢ <;> simp only [true_or]
            all_goals refine ⟨by omega, ⟨by omega, by omega⟩, trivial⟩
          · dsimp [F]
            simp only [Prod.mk.injEq]
            exact ⟨trivial, trivial, by omega, by omega⟩
    · rintro (he | ⟨p, hp, he⟩)
      · simp only [E, mem_insert, mem_singleton] at he
        rcases he with he | he <;> cases he <;> rw [memR] <;> simp <;> omega
      · exact he ▸ forward p hp
  have inj : Set.InjOn F ↑T := by
    rintro ⟨⟨f, r⟩, t, j⟩ hp ⟨⟨g, s⟩, u, k⟩ hq he
    have ht := (data _ hp).1
    have hu := (data _ hq).1
    have hf : f = g := congrArg Prod.fst he
    subst g
    have hj : j = k := congrArg (fun q => q.2.1) he
    subst k
    have hr : r = s := by rw [he] at ht; dsimp [F] at ht hu; omega
    subst s
    have ha := congrArg (fun q => q.2.2.1) he
    dsimp [F] at ha
    split_ifs at ha <;> simp_all
  have disj : Disjoint E (T.image F) := by
    rw [disjoint_left]
    intro q he hi
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
    have hj := (data p hp).2
    simp only [E, mem_insert, mem_singleton] at he
    rcases he with he | he <;> rw [he] at hj
    · have hf := congrArg Prod.fst he
      simp only [F] at hf
      rw [hf] at hj
      simp at hj
    · have hf := congrArg Prod.fst he
      simp only [F] at hf
      rw [hf] at hj
      simp at hj
  have count : (region n).card = 2 + ∑ q ∈ univ.product (range (n / 2 + 1)),
      (P q.1 q.2).card := by
    rw [decomp, card_union_of_disjoint disj, card_image_iff.mpr inj]
    simp [E, T]
  have sumid (v : ℕ) : (∑ t ∈ range v, (t : ℚ)) = (v : ℚ) * (v - 1 : ℚ) / 2 := by
    by_cases hv : v = 0
    · subst v; simp
    have h := congrArg (fun x : ℕ => (x : ℚ)) (sum_range_id_mul_two v)
    push_cast at h
    rw [Nat.cast_sub (by omega : 1 ≤ v)] at h
    norm_num at h
    linarith
  have tri (v c : ℕ) (hc : c ≤ n) (hv : v ≤ n - c + 1) :
      (∑ t ∈ range v, ((n - t - c : ℕ) : ℚ)) =
        (v : ℚ) * (n - c : ℚ) - (v : ℚ) * (v - 1 : ℚ) / 2 := by
    have conv (t : ℕ) (ht : t ∈ range v) :
        ((n - t - c : ℕ) : ℚ) = (n : ℚ) - t - c := by
      have htv : t < v := mem_range.mp ht
      rw [Nat.cast_sub (by omega : c ≤ n - t), Nat.cast_sub (by omega : t ≤ n)]
    rw [sum_congr rfl conv]
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sumid]
    ring
  have Acard (r : ℕ) (hr : 2 * r ≤ n) :
      2 * ((P true r).card : ℚ) =
        if r = 0 then (n : ℚ) * (n - 1)
        else if r = 1 then (n - 1 : ℚ) * (n - 2)
        else (n - 2 * r : ℚ) * (n + 2 * r - 5) := by
    have he : P true r = (range (U true r)).sigma fun t =>
        Icc (if r ≤ 1 then 1 else 2) (n - (t + 1) - (if r = 0 then 0 else 1)) := by
      simp [P]
    rw [he, card_sigma, Nat.cast_sum]
    by_cases h0 : r = 0
    · subst r
      simp only [U, ↓reduceIte, zero_le, Nat.sub_zero]
      have hsum : (∑ t ∈ range (n - 1),
          ((Icc 1 (n - (t + 1))).card : ℚ)) =
          ∑ t ∈ range (n - 1), ((n - t - 1 : ℕ) : ℚ) := by
        apply sum_congr rfl
        intro t ht
        congr 1
        simp only [Nat.card_Icc]
        omega
      rw [hsum, tri (n - 1) 1 (by omega) (by omega)]
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
      ring
    · by_cases h1 : r = 1
      · subst r
        simp only [U, ↓reduceIte, one_ne_zero, le_refl]
        have hsum : (∑ t ∈ range (n - 2),
            ((Icc 1 (n - (t + 1) - 1)).card : ℚ)) =
            ∑ t ∈ range (n - 2), ((n - t - 2 : ℕ) : ℚ) := by
          apply sum_congr rfl
          intro t ht
          congr 1
          simp only [Nat.card_Icc]
          omega
        norm_num at *
        rw [hsum, tri (n - 2) 2 (by omega) (by omega)]
        rw [Nat.cast_sub (by omega : 2 ≤ n)]
        norm_num
        ring
      · have hr2 : 2 ≤ r := by omega
        have he1 : ¬ r ≤ 1 := by omega
        simp only [U, ↓reduceIte, h0, h1, he1]
        have hsum : (∑ t ∈ range (n - 2 * r),
            ((Icc 2 (n - (t + 1) - 1)).card : ℚ)) =
            ∑ t ∈ range (n - 2 * r), ((n - t - 3 : ℕ) : ℚ) := by
          apply sum_congr rfl
          intro t ht
          have htv : t < n - 2 * r := mem_range.mp ht
          congr 1
          simp only [Nat.card_Icc]
          omega
        rw [hsum, tri (n - 2 * r) 3 (by omega) (by omega)]
        rw [Nat.cast_sub hr]
        push_cast
        ring
  have Bcard (r : ℕ) (hr : 2 * r ≤ n) :
      ((P false r).card : ℚ) =
        if r ≤ 1 then (n - 1 : ℚ) * (n - 2) - 1
        else (n - 2 : ℚ) * (n - 2 * r + 1) := by
    let S := (range (U false r)).sigma fun _ : ℕ => Icc 2 (n - 1)
    have sc : S.card = U false r * (n - 2) := by
      simp [S, Nat.card_Icc]
      omega
    by_cases h : r ≤ 1
    · have he : P false r = S.erase ⟨0, 2⟩ := by
        ext ⟨t, j⟩
        simp [P, S, h, mem_sigma, Sigma.ext_iff, and_comm, and_left_comm, and_assoc]
      have hc : (⟨0, 2⟩ : Σ _ : ℕ, ℕ) ∈ S := by
        simp [S, mem_sigma, U]
        split_ifs <;> omega
      have heU : U false r = n - 1 := by
        dsimp [U]
        split_ifs <;> omega
      have hsc : 1 ≤ S.card := card_pos.mpr ⟨_, hc⟩
      rw [he, card_erase_of_mem hc, Nat.cast_sub hsc, sc, heU]
      rw [if_pos h]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n)]
      norm_num
    · have he : P false r = S := by simp [P, S, h]
      have h0 : r ≠ 0 := by omega
      rw [he, sc, if_neg h]
      simp only [U, Bool.false_eq_true, ↓reduceIte, h0]
      push_cast
      rw [Nat.cast_sub hr, Nat.cast_sub (by omega : 2 ≤ n)]
      push_cast
      ring
  let H (r : ℕ) : ℚ :=
    (n - 2 * r : ℚ) * (n + 2 * r - 5) + 2 * (n - 2 : ℚ) * (n - 2 * r + 1)
  have layer (r : ℕ) (hr : r ∈ range (n / 2 + 1)) :
      2 * ((P true r).card : ℚ) + 2 * ((P false r).card : ℚ) =
        if r = 0 then (n : ℚ) * (n - 1) + 2 * ((n - 1 : ℚ) * (n - 2) - 1)
        else if r = 1 then 3 * (n - 1 : ℚ) * (n - 2) - 2
        else H r := by
    have hrn : 2 * r ≤ n := by have := mem_range.mp hr; omega
    rw [Acard r hrn, Bcard r hrn]
    by_cases h0 : r = 0
    · subst r; norm_num
    · by_cases h1 : r = 1
      · subst r; norm_num; ring
      · have hr2 : ¬ r ≤ 1 := by omega
        simp only [h0, h1, hr2, ↓reduceIte, H]
        ring
  have hb : (univ : Finset Bool) = {false, true} := by decide
  have countQ := congrArg (fun x : ℕ => (x : ℚ)) count
  push_cast at countQ
  simp only [product_eq_sprod, sum_product, hb, sum_insert, sum_singleton, mem_singleton,
    Bool.false_eq_true, not_false_eq_true] at countQ
  have count2 : 2 * ((region n).card : ℚ) = 4 +
      ∑ r ∈ range (n / 2 + 1),
        if r = 0 then (n : ℚ) * (n - 1) + 2 * ((n - 1 : ℚ) * (n - 2) - 1)
        else if r = 1 then 3 * (n - 1 : ℚ) * (n - 2) - 2
        else H r := by
    rw [← sum_congr rfl layer, sum_add_distrib]
    simp only [← mul_sum]
    linarith [countQ]
  have head : 2 * ((region n).card : ℚ) = 6 * (n : ℚ) ^ 2 - 16 * n + 10 +
      ∑ t ∈ range (n / 2 - 1), H (t + 2) := by
    have he : n / 2 + 1 = 2 + (n / 2 - 1) := by omega
    rw [he, sum_range_add] at count2
    have hs : (∑ x ∈ range 2,
        if x = 0 then (n : ℚ) * (n - 1) + 2 * ((n - 1 : ℚ) * (n - 2) - 1)
        else if x = 1 then 3 * (n - 1 : ℚ) * (n - 2) - 2 else H x) =
        6 * (n : ℚ) ^ 2 - 16 * n + 6 := by
      simp only [sum_range_succ, sum_range_zero]
      norm_num
      ring
    rw [hs] at count2
    have ht : (∑ t ∈ range (n / 2 - 1),
        if 2 + t = 0 then (n : ℚ) * (n - 1) + 2 * ((n - 1 : ℚ) * (n - 2) - 1)
        else if 2 + t = 1 then 3 * (n - 1 : ℚ) * (n - 2) - 2 else H (2 + t)) =
        ∑ t ∈ range (n / 2 - 1), H (t + 2) := by
      apply sum_congr rfl
      intro t _
      rw [if_neg (by omega), if_neg (by omega), Nat.add_comm 2 t]
    rw [ht] at count2
    linarith
  have tailSum (l : ℕ) : 6 * (∑ t ∈ range l, H (t + 2)) =
      6 * (l : ℚ) * (3 * (n : ℚ) ^ 2 - 15 * n + 16) +
      3 * (2 - 4 * (n : ℚ)) * l * (l - 1) - 4 * (l : ℚ) * (l - 1) * (2 * l - 1) := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [sum_range_succ, mul_add, ih]
      simp only [H, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
  have total : 12 * ((region n).card : ℚ) =
      6 * (6 * (n : ℚ) ^ 2 - 16 * n + 10) +
      6 * ((n / 2 - 1 : ℕ) : ℚ) * (3 * (n : ℚ) ^ 2 - 15 * n + 16) +
      3 * (2 - 4 * (n : ℚ)) * ((n / 2 - 1 : ℕ) : ℚ) *
        (((n / 2 - 1 : ℕ) : ℚ) - 1) -
      4 * ((n / 2 - 1 : ℕ) : ℚ) * (((n / 2 - 1 : ℕ) : ℚ) - 1) *
        (2 * ((n / 2 - 1 : ℕ) : ℚ) - 1) := by
    linarith [head, tailSum (n / 2 - 1)]
  have hcast : ((n / 2 - 1 : ℕ) : ℚ) = (n / 2 : ℕ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n / 2)]
    norm_num
  rw [hcast] at total
  by_cases odd : n % 2 = 1
  · have hpar : n = 2 * (n / 2) + 1 := by omega
    have hq : (n : ℚ) = 2 * ((n / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast hpar
    have hp : 6 * ((region n).card : ℚ) =
        20 * ((n / 2 : ℕ) : ℚ) ^ 3 + 33 * ((n / 2 : ℕ) : ℚ) ^ 2 +
          ((n / 2 : ℕ) : ℚ) - 6 := by
      rw [hq] at total
      nlinarith only [total]
    have hlow : 6 ≤ 20 * (n / 2) ^ 3 + 33 * (n / 2) ^ 2 + n / 2 := by
      have hk : 1 ≤ n / 2 := by omega
      nlinarith [sq_nonneg (n / 2)]
    have hpNat : 6 * (region n).card =
        20 * (n / 2) ^ 3 + 33 * (n / 2) ^ 2 + n / 2 - 6 := by
      have hcast' : ((20 * (n / 2) ^ 3 + 33 * (n / 2) ^ 2 + n / 2 - 6 : ℕ) : ℚ) =
          20 * ((n / 2 : ℕ) : ℚ) ^ 3 + 33 * ((n / 2 : ℕ) : ℚ) ^ 2 +
            ((n / 2 : ℕ) : ℚ) - 6 := by
        rw [Nat.cast_sub hlow]; push_cast; rfl
      exact_mod_cast hp.trans hcast'.symm
    rw [omegaFormula, if_neg h1, if_neg h2, if_pos odd]
    exact Nat.eq_div_of_mul_eq_right (by decide) hpNat
  · have hpar : n = 2 * (n / 2) := by omega
    have hk : 2 ≤ n / 2 := by omega
    have hq : (n : ℚ) = 2 * ((n / 2 : ℕ) : ℚ) := by exact_mod_cast hpar
    have hp : 6 * ((region n).card : ℚ) =
        (20 * ((n / 2 : ℕ) : ℚ) - 17) * (((n / 2 : ℕ) : ℚ) + 1) *
          ((n / 2 : ℕ) : ℚ) := by
      rw [hq] at total
      nlinarith only [total]
    have hpNat : 6 * (region n).card = (20 * (n / 2) - 17) * (n / 2 + 1) * (n / 2) := by
      have hcast' : (((20 * (n / 2) - 17) * (n / 2 + 1) * (n / 2) : ℕ) : ℚ) =
          (20 * ((n / 2 : ℕ) : ℚ) - 17) * (((n / 2 : ℕ) : ℚ) + 1) *
            ((n / 2 : ℕ) : ℚ) := by
        push_cast
        rw [Nat.cast_sub (by omega : 17 ≤ 20 * (n / 2))]
        push_cast
        rfl
      exact_mod_cast hp.trans hcast'.symm
    rw [omegaFormula, if_neg h1, if_neg h2, if_neg odd]
    exact Nat.eq_div_of_mul_eq_right (by decide) hpNat

end D5.S3.Combinatorics.QGrammar.SecGrammar
