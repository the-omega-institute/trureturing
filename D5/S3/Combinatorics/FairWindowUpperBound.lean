/- GID: D5/S3/Combinatorics/FairWindowUpperBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FairWindowUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed fair-window tables attain a reciprocal bound with collision correction. -/

import D5.S3.Combinatorics.FairWindowMinimizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FairWindowUpperBound

open scoped BigOperators
open D5.S3.Combinatorics.FairWindowDefect
open D5.S3.Combinatorics.FairWindowMinimizer

set_option maxHeartbeats 1200000 in
-- The collision equivalence and the three nested finite averages elaborate together.
/-- For every admissible word length there is one fixed deterministic window
table attaining the finite fair-source upper bound. -/
theorem fair_window_defect_upper_bound (R m : ℕ) (hm : 1 ≤ m) (hmR : m ≤ R) :
    ∃ f : (Fin R → Fin 2) → Fin 2,
      fairDefect R f ≤ 1 / (R - m + 2 : ℚ) +
        ((R - m + 2).choose 2 : ℚ) / 2 ^ m := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmR
  have hcollision (a b : Fin (k + 2)) (hab : a < b) :
      (𝔼 v : Fin (m + k + 1) → Fin 2,
        if word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b then (1 : ℚ) else 0) =
          1 / 2 ^ m := by
    let d := b.val - a.val
    have hd : 0 < d := by dsimp [d]; exact Nat.sub_pos_of_lt hab
    have had : a.val + d = b.val := by dsimp [d]; omega
    let C := {v : Fin (m + k + 1) → Fin 2 //
      word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b}
    let keep (i : Fin (k + 1)) : Fin (m + k + 1) :=
      ⟨if i.val < b.val then i.val else i.val + m, by split_ifs <;> omega⟩
    let collapse (j : Fin (m + k + 1)) : Fin (k + 1) :=
      ⟨if j.val < a.val then j.val else
        if j.val < b.val + m then a.val + (j.val - a.val) % d else j.val - m, by
          have hb := b.isLt
          have hmod := Nat.mod_lt (j.val - a.val) hd
          split_ifs <;> omega⟩
    have hkeep (i : Fin (k + 1)) : collapse (keep i) = i := by
      apply Fin.ext
      by_cases hib : i.val < b.val
      · by_cases hia : i.val < a.val
        · simp [collapse, keep, hib, hia]
        · have hi : i.val - a.val < d := by omega
          simp [collapse, keep, hib, hia, show i.val < b.val + m by omega,
            Nat.mod_eq_of_lt hi]
          omega
      · simp [collapse, keep, hib, show ¬ i.val + m < a.val by omega,
          show ¬ i.val + m < b.val + m by omega]
    have hcollapse (i : Fin m) :
        collapse ⟨a.val + i.val, by omega⟩ = collapse ⟨b.val + i.val, by omega⟩ := by
      apply Fin.ext
      have hleft : a.val + i.val < b.val + m := by omega
      have hright : b.val + i.val < b.val + m := by omega
      simp only [collapse, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte,
        hleft, hright]
      have hba : ¬ b.val + i.val < a.val := by omega
      simp only [hba, ↓reduceIte]
      have he : b.val + i.val - a.val = i.val + d := by omega
      rw [Nat.add_sub_cancel_left, he, Nat.add_mod_right]
    let restrict (x : C) : Fin (k + 1) → Fin 2 := fun i => x.val (keep i)
    have hperiod (x : C) :
        List.HasPeriod (List.ofFn (fun i : Fin (m + d) =>
          x.val ⟨a.val + i.val, by omega⟩)) d := by
      rw [List.hasPeriod_iff_getElem?]
      intro i hi
      have him : i < m := by simpa using hi
      have hfirst : i < m + d := by omega
      have hsecond : i + d < m + d := by omega
      have hx := congr_fun x.property (⟨i, him⟩ : Fin m)
      have he : a.val + (i + d) = b.val + i := by omega
      simpa [List.getElem?_ofFn, hfirst, hsecond, word, he] using congrArg some hx
    have hrestore (x : C) (j : Fin (m + k + 1)) : x.val (keep (collapse j)) = x.val j := by
      by_cases hja : j.val < a.val
      · apply congrArg x.val
        apply Fin.ext
        simp [collapse, keep, hja, show j.val < b.val by omega]
      · by_cases hjb : j.val < b.val + m
        · have hj : j.val - a.val < m + d := by omega
          have hmod : (j.val - a.val) % d < m + d := by
            have := Nat.mod_lt (j.val - a.val) hd; omega
          have hp := (hperiod x).getElem?_mod d (j.val - a.val)
            (List.ofFn (fun i : Fin (m + d) => x.val ⟨a.val + i.val, by omega⟩))
            (by simpa using hj)
          have hrep : a.val + (j.val - a.val) % d < b.val := by
            have := Nat.mod_lt (j.val - a.val) hd; omega
          have he : a.val + (j.val - a.val) = j.val := by omega
          simpa [List.getElem?_ofFn, hj, hmod, collapse, keep, hja, hjb, hrep, he]
            using hp
        · apply congrArg x.val
          apply Fin.ext
          have ht : ¬ j.val - m < b.val := by omega
          simp [collapse, keep, hja, hjb, ht]
          omega
    have hbij : Function.Bijective restrict := by
      constructor
      · intro x y he
        apply Subtype.ext
        funext j
        rw [← hrestore x j, ← hrestore y j]
        exact congr_fun he (collapse j)
      · intro y
        let x : Fin (m + k + 1) → Fin 2 := fun j => y (collapse j)
        have hx : word (m := m) (k := k + 1) x a = word (m := m) (k := k + 1) x b := by
          funext i
          exact congrArg y (hcollapse i)
        refine ⟨⟨x, hx⟩, ?_⟩
        funext i
        exact congrArg y (hkeep i)
    have hc : Fintype.card C = 2 ^ (k + 1) := by
      simpa using Fintype.card_congr (Equiv.ofBijective restrict hbij)
    have hsum : (∑ v : Fin (m + k + 1) → Fin 2,
        if word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b then (1 : ℚ) else 0) =
          2 ^ (k + 1) := by
      have he : (Fintype.card C : ℚ) = 2 ^ (k + 1) := by exact_mod_cast hc
      simpa [C, Fintype.card_subtype, Finset.sum_boole] using he
    rw [Finset.expect_eq_sum_div_card, hsum]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rw [show m + k + 1 = m + (k + 1) by omega, pow_add]
    field_simp
    simp [pow_add, mul_comm, mul_left_comm]
  let bad (v : Fin (m + k + 1) → Fin 2) :=
    ¬ Function.Injective (word (m := m) (k := k + 1) v)
  have hpoint (v : Fin (m + k + 1) → Fin 2) :
      (if bad v then (1 : ℚ) else 0) ≤
        ∑ b : Fin (k + 2), ∑ a ∈ Finset.Iio b,
          if word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b
          then (1 : ℚ) else 0 := by
    by_cases hv : bad v
    · have hex : ∃ a b : Fin (k + 2), a < b ∧
          word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b := by
        have hn : ¬ Function.Injective (word (m := m) (k := k + 1) v) := hv
        simp only [Function.Injective, not_forall] at hn
        obtain ⟨a, b, hab⟩ := hn
        have he : word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b ∧ a ≠ b := by
          tauto
        rcases lt_or_gt_of_ne he.2 with h | h
        · exact ⟨a, b, h, he.1⟩
        · exact ⟨b, a, h, he.1.symm⟩
      obtain ⟨a, b, hab, he⟩ := hex
      rw [if_pos hv]
      calc
        1 = if word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b
            then (1 : ℚ) else 0 := by simp [he]
        _ ≤ ∑ i ∈ Finset.Iio b,
            if word (m := m) (k := k + 1) v i = word (m := m) (k := k + 1) v b
            then (1 : ℚ) else 0 := by
          apply Finset.single_le_sum (s := Finset.Iio b)
            (f := fun i : Fin (k + 2) => if word (m := m) (k := k + 1) v i =
              word (m := m) (k := k + 1) v b then (1 : ℚ) else 0)
          · intro i _; split_ifs <;> norm_num
          · exact Finset.mem_Iio.mpr hab
        _ ≤ _ := by
          apply Finset.single_le_sum (s := Finset.univ)
            (f := fun b : Fin (k + 2) => ∑ a ∈ Finset.Iio b,
              if word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b
              then (1 : ℚ) else 0)
          · intro i _; apply Finset.sum_nonneg; intro j _; split_ifs <;> norm_num
          · exact Finset.mem_univ b
    · rw [if_neg hv]
      apply Finset.sum_nonneg
      intro b _
      apply Finset.sum_nonneg
      intro a _
      split_ifs <;> norm_num
  have hcount : (∑ b : Fin (k + 2), (Finset.Iio b).card) = (k + 2).choose 2 := by
    simp only [Fin.card_Iio]
    calc
      (∑ b : Fin (k + 2), b.val) = ∑ i ∈ Finset.range (k + 2), i :=
        Fin.sum_univ_eq_sum_range (fun i => i) (k + 2)
      _ = (k + 2).choose 2 := by rw [Finset.sum_range_id, Nat.choose_two_right]
  have hbad : (𝔼 v : Fin (m + k + 1) → Fin 2, if bad v then (1 : ℚ) else 0) ≤
      ((k + 2).choose 2 : ℚ) / 2 ^ m := by
    calc
      _ ≤ 𝔼 v : Fin (m + k + 1) → Fin 2,
          ∑ b : Fin (k + 2), ∑ a ∈ Finset.Iio b,
            if word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b
            then (1 : ℚ) else 0 := Finset.expect_le_expect (fun v _ => hpoint v)
      _ = ∑ b : Fin (k + 2), ∑ a ∈ Finset.Iio b,
          (𝔼 v : Fin (m + k + 1) → Fin 2,
            if word (m := m) (k := k + 1) v a = word (m := m) (k := k + 1) v b
            then (1 : ℚ) else 0) := by simp_rw [Finset.expect_sum_comm]
      _ = ∑ b : Fin (k + 2), ∑ _a ∈ Finset.Iio b, (1 / 2 ^ m : ℚ) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a ha
        exact hcollision a b (Finset.mem_Iio.mp ha)
      _ = ((k + 2).choose 2 : ℚ) / 2 ^ m := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        have hc : (∑ b : Fin (k + 2), ((Finset.Iio b).card : ℚ)) = (k + 2).choose 2 :=
          by exact_mod_cast hcount
        rw [hc]
        ring
  have hcontext (v : Fin (m + k + 1) → Fin 2) :
      (𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
        𝔼 β : (Fin m → Fin 2) → Fin 2, defect (table m k ρ β) v) ≤
          1 / (k + 2 : ℚ) + if bad v then 1 else 0 := by
    by_cases hv : bad v
    · rw [if_pos hv]
      have hle : (𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
          𝔼 β : (Fin m → Fin 2) → Fin 2, defect (table m k ρ β) v) ≤ 1 := by
        apply Finset.expect_le Finset.univ_nonempty
        intro ρ _
        apply Finset.expect_le Finset.univ_nonempty
        intro β _
        unfold defect
        split_ifs <;> norm_num
      exact hle.trans (le_add_of_nonneg_left (by positivity))
    · have hgood : Function.Injective (word (m := m) (k := k + 1) v) := by simpa [bad] using hv
      rw [good_context_average m k hm v hgood, if_neg hv, add_zero]
  have hfair (f : (Fin (m + k) → Fin 2) → Fin 2) :
      fairDefect (m + k) f = 𝔼 v : Fin (m + k + 1) → Fin 2, defect f v := by
    rw [Fintype.expect_eq_sum_div_card]
    simp [fairDefect]
  have havg : (𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
      𝔼 β : (Fin m → Fin 2) → Fin 2, fairDefect (m + k) (table m k ρ β)) ≤
        1 / (k + 2 : ℚ) + ((k + 2).choose 2 : ℚ) / 2 ^ m := by
    simp_rw [hfair]
    calc
      _ = 𝔼 v : Fin (m + k + 1) → Fin 2,
          𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
            𝔼 β : (Fin m → Fin 2) → Fin 2, defect (table m k ρ β) v := by
        calc
          _ = 𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
              𝔼 v : Fin (m + k + 1) → Fin 2,
                𝔼 β : (Fin m → Fin 2) → Fin 2, defect (table m k ρ β) v := by
            apply Finset.expect_congr rfl
            intro ρ _
            exact Finset.expect_comm _ _ _
          _ = _ := Finset.expect_comm _ _ _
      _ ≤ 𝔼 v : Fin (m + k + 1) → Fin 2,
          (1 / (k + 2 : ℚ) + if bad v then 1 else 0) :=
        Finset.expect_le_expect (fun v _ => hcontext v)
      _ = 1 / (k + 2 : ℚ) + (𝔼 v : Fin (m + k + 1) → Fin 2,
          if bad v then (1 : ℚ) else 0) := by rw [Finset.expect_add_distrib, Fintype.expect_const]
      _ ≤ _ := add_le_add (le_refl _) hbad
  obtain ⟨ρ, _, hρ⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty havg
  obtain ⟨β, _, hβ⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty hρ
  refine ⟨table m k ρ β, ?_⟩
  simpa only [Nat.add_sub_cancel_left, Nat.cast_add, add_sub_cancel_left] using hβ

#print axioms fair_window_defect_upper_bound

end D5.S3.Combinatorics.FairWindowUpperBound
