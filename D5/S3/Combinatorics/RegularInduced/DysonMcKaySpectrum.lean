/- GID: D5/S3/Combinatorics/RegularInduced/DysonMcKaySpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RegularInduced/DysonMcKaySpectrum
   mirror-E: none(waiver:finite-cycle-count-classification)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact cyclic count spectra with constructive packet and full-support witnesses. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators Fin.NatCast

namespace D5.S3.Combinatorics.RegularInduced.DysonMcKay

/-- Exact possible total orders of bounded regular cyclic bag counts, including
empty selections, clique packets, and the period-three full-support branch. -/
theorem cyclic_order_spectrum {r s q m : ℕ} [NeZero r]
    (hr : 4 ≤ r) (hq : 0 < q) :
    (∃ x : Fin r → ℕ, (∀ i, x i ≤ s) ∧ (∑ i, x i) = m ∧
      ∀ i, 0 < x i → x (i - 1) + x i + x (i + 1) = q) ↔
    (∃ k : ℕ, m = k * q ∧ 2 * k ≤ r ∧
      (s < q → 3 * k ≤ r) ∧ (2 * s < q → k = 0)) ∨
    (3 * m = r * q ∧ 3 ≤ q ∧ q ≤ 3 * s ∧ (3 ∣ r ∨ 3 ∣ q)) := by
  classical
  have hclass (x : Fin r → ℕ) (hx : ∀ i, x i ≤ s) 
    (hreg : ∀ i, 0 < x i → x (i - 1) + x i + x (i + 1) = q) :
    (∃ k : ℕ, (∑ i, x i) = k * q ∧ 2 * k ≤ r ∧
      (s < q → 3 * k ≤ r) ∧ (2 * s < q → k = 0)) ∨
    ((∀ i, 0 < x i) ∧ (∀ i, x i = x (i + 3)) ∧
      3 * (∑ i, x i) = r * q ∧ 3 ≤ q ∧ q ≤ 3 * s ∧ (3 ∣ r ∨ 3 ∣ q)) := by
    classical
    have two : (2 : Fin r) = 1 + 1 := by
      exact (Nat.cast_add 1 1).trans (by rfl)
    have three : (3 : Fin r) = 1 + 1 + 1 := by
      change (Nat.cast 3 : Fin r) = _
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add]
      change (2 : Fin r) + 1 = _
      rw [two]
    have hshift (f : Fin r → ℕ) (a : Fin r) :
        (∑ i, f (i + a)) = ∑ i, f i := by
      exact (Fintype.sum_equiv (Equiv.addRight a) (fun i => f (i + a)) f
        (fun _ => rfl))
    by_cases hall : ∀ i, 0 < x i
    · right
      have hperiod (i : Fin r) : x i = x (i + 3) := by
        have h₁ := hreg (i + 1) (hall (i + 1))
        have h₂ := hreg (i + 2) (hall (i + 2))
        have e₁ : i + 1 - 1 = i := by abel
        have e₂ : i + 2 - 1 = i + 1 := by
          rw [two]
          abel
        have e₃ : i + 1 + 1 = i + 2 := by
          rw [two]
          abel
        have e₄ : i + 2 + 1 = i + 3 := by rw [two, three]; abel
        rw [e₁, e₃] at h₁
        rw [e₂, e₄] at h₂
        omega
      have hsum := congrArg (fun f : Fin r → ℕ => ∑ i, f i)
        (funext fun i => hreg i (hall i))
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at hsum
      have hminus : (∑ i, x (i - 1)) = ∑ i, x i := by
        simpa only [sub_eq_add_neg] using hshift x (-1)
      rw [hminus, hshift x 1] at hsum
      have hsum' : 3 * (∑ i, x i) = r * q := by omega
      have h₀ := hreg 0 (hall 0)
      have h₁ := hall (-1)
      have h₂ := hall 0
      have h₃ := hall 1
      have h₄ := hx (-1)
      have h₅ := hx 0
      have h₆ := hx 1
      simp only [zero_sub, zero_add] at h₀
      have hdiv : 3 ∣ r * q := ⟨∑ i, x i, by omega⟩
      exact ⟨hall, hperiod, hsum', by omega, by omega, Nat.prime_three.dvd_mul.mp hdiv⟩
    · left
      have hno : ∀ i, ¬ (0 < x i ∧ 0 < x (i + 1) ∧ 0 < x (i + 2)) := by
        intro i hi
        have hwalk : ∀ n : ℕ,
            0 < x (i + (Nat.cast n : Fin r)) ∧
            0 < x (i + (Nat.cast n : Fin r) + 1) ∧
            0 < x (i + (Nat.cast n : Fin r) + 2) := by
          intro n
          induction n with
          | zero => simpa using hi
          | succ n ih =>
            have h₁ := hreg (i + (Nat.cast n : Fin r) + 1) ih.2.1
            have h₂ := hreg (i + (Nat.cast n : Fin r) + 2) ih.2.2
            have e₁ : i + (Nat.cast n : Fin r) + 1 - 1 = i + (Nat.cast n : Fin r) := by
              abel
            have e₂ : i + (Nat.cast n : Fin r) + 2 - 1 = i + (Nat.cast n : Fin r) + 1 := by
              rw [two]
              abel
            have e₃ : i + (Nat.cast n : Fin r) + 1 + 1 = i + (Nat.cast n : Fin r) + 2 := by
              rw [two]
              abel
            rw [e₁, e₃] at h₁
            rw [e₂] at h₂
            have hlast : 0 < x (i + (Nat.cast n : Fin r) + 2 + 1) := by omega
            have en : (Nat.cast (n + 1) : Fin r) = (Nat.cast n : Fin r) + 1 := by simp
            rw [en]
            constructor
            · simpa only [add_assoc] using ih.2.1
            constructor
            · simpa only [two, add_assoc] using ih.2.2
            · simpa only [two, add_assoc] using hlast
        apply hall
        intro j
        have hw := (hwalk (j - i).val).1
        have e : (Nat.cast (j - i).val : Fin r) = j - i := by simp
        rw [e] at hw
        simpa using hw
      let H : Finset (Fin r) := univ.filter fun i => 0 < x i ∧ x (i - 1) = 0
      have hmem (i : Fin r) : i ∈ H ↔ 0 < x i ∧ x (i - 1) = 0 := by
        simp [H]
      have hpacket (i : Fin r) (hi : i ∈ H) : x i + x (i + 1) = q := by
        have hm := (hmem i).mp hi
        have he := hreg i hm.1
        rw [hm.2] at he
        omega
      have hsplit (i : Fin r) :
          x i = (if i ∈ H then x i else 0) +
            (if i - 1 ∈ H then x i else 0) := by
        by_cases hz : x i = 0
        · simp [hz]
        · have hp : 0 < x i := by omega
          by_cases hl : x (i - 1) = 0
          · have hi : i ∈ H := (hmem i).mpr ⟨hp, hl⟩
            have hn : i - 1 ∉ H := by simp [hmem, hl]
            simp [hi, hn]
          · have hn : i ∉ H := by simp [hmem, hl]
            have hh : x (i - 1 - 1) = 0 := by
              have he := hno (i - 1 - 1)
              have e₁ : i - 1 - 1 + 1 = i - 1 := by abel
              have e₂ : i - 1 - 1 + 2 = i := by
                rw [two]
                abel
              rw [e₁, e₂] at he
              omega
            have hi : i - 1 ∈ H := (hmem (i - 1)).mpr ⟨by omega, hh⟩
            simp [hn, hi]
      have hcount : (∑ i, x i) = H.card * q := by
        have hs := congrArg (fun f : Fin r → ℕ => ∑ i, f i) (funext hsplit)
        rw [Finset.sum_add_distrib] at hs
        have hsecond : (∑ i, if i - 1 ∈ H then x i else 0) =
            ∑ i, if i ∈ H then x (i + 1) else 0 := by
          have he := hshift (fun i => if i - 1 ∈ H then x i else 0) 1
          simpa using he.symm
        rw [hsecond, ← Finset.sum_add_distrib] at hs
        simp only [ite_add_ite, add_zero] at hs
        rw [← Finset.sum_filter] at hs
        have he : ∑ i ∈ H, (x i + x (i + 1)) = H.card * q := by
          simp only [Finset.sum_congr rfl hpacket, Finset.sum_const, smul_eq_mul]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hs
        exact hs.trans he
      have hinj (a : Fin r) : Function.Injective (fun i : Fin r => i + a) := by
        intro i j h
        exact add_right_cancel h
      have hdisj : Disjoint H (H.image fun i => i + 1) := by
        rw [Finset.disjoint_left]
        intro i hi hj
        rcases Finset.mem_image.mp hj with ⟨j, hjmem, rfl⟩
        have he := (hmem (j + 1)).mp hi
        have hj' := (hmem j).mp hjmem
        simp only [add_sub_cancel_right] at he
        omega
      have htwo : 2 * H.card ≤ r := by
        have hc := Finset.card_le_card (Finset.subset_univ (H ∪ H.image (fun i => i + 1)))
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (hinj 1)]
          at hc
        simpa only [Finset.card_univ, Fintype.card_fin, two_mul] using hc
      refine ⟨H.card, hcount, htwo, ?_, ?_⟩
      · intro hsq
        have hright (i : Fin r) (hi : i ∈ H) : 0 < x (i + 1) := by
          have hp := hpacket i hi
          have hb := hx i
          omega
        have hdisj₂ : Disjoint H (H.image fun i => i + 2) := by
          rw [Finset.disjoint_left]
          intro i hi hj
          rcases Finset.mem_image.mp hj with ⟨j, hjmem, rfl⟩
          have he := (hmem (j + 2)).mp hi
          have hp := hright j hjmem
          have ee : j + 2 - 1 = j + 1 := by
            rw [two]
            abel
          rw [ee] at he
          omega
        have hdisj₃ : Disjoint (H.image fun i => i + 1) (H.image fun i => i + 2) := by
          rw [Finset.disjoint_left]
          intro i hi hj
          rcases Finset.mem_image.mp hi with ⟨a, ha, rfl⟩
          rcases Finset.mem_image.mp hj with ⟨b, hb, he⟩
          have he' : a = b + 1 := by
            apply add_right_cancel (b := (1 : Fin r))
            calc
              a + 1 = b + 2 := he.symm
              _ = b + 1 + 1 := by
                rw [two]
                abel
          rw [he'] at ha
          exact Finset.disjoint_left.mp hdisj ha (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
        have hc := Finset.card_le_card (Finset.subset_univ
          ((H ∪ H.image (fun i => i + 1)) ∪ H.image (fun i => i + 2)))
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj₂, hdisj₃⟩),
          Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (hinj 1),
          Finset.card_image_of_injective _ (hinj 2),
          Finset.card_univ, Fintype.card_fin] at hc
        omega
      · intro hbig
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hp := hpacket i hi
        have h₁ := hx i
        have h₂ := hx (i + 1)
        omega
  have hfull : (∃ x : Fin r → ℕ, (∀ i, 0 < x i ∧ x i ≤ s) ∧
      ∀ i, x (i - 1) + x i + x (i + 1) = q) ↔
      3 ≤ q ∧ q ≤ 3 * s ∧ (3 ∣ r ∨ 3 ∣ q) := by
    classical
    constructor
    · rintro ⟨x, hx, he⟩
      have h₀ := he 0
      have h₁ := hx (-1)
      have h₂ := hx 0
      have h₃ := hx 1
      simp only [zero_sub, zero_add] at h₀
      have hshift (a : Fin r) : (∑ i, x (i + a)) = ∑ i, x i :=
        Fintype.sum_equiv (Equiv.addRight a) (fun i => x (i + a)) x (fun _ => rfl)
      have hsum := congrArg (fun f : Fin r → ℕ => ∑ i, f i) (funext he)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, sub_eq_add_neg] at hsum
      rw [hshift (-1), hshift 1] at hsum
      have hdiv : 3 ∣ r * q := ⟨∑ i, x i, by omega⟩
      exact ⟨by omega, by omega, Nat.prime_three.dvd_mul.mp hdiv⟩
    · rintro ⟨hq, hqs, hdiv⟩
      have hs : 1 ≤ s := by omega
      rcases hdiv with hr₃ | hq₃
      · let a := min s (q - 2)
        let b := min s (q - a - 1)
        let c := q - a - b
        have ha : 1 ≤ a ∧ a ≤ s := by dsimp [a]; omega
        have hb : 1 ≤ b ∧ b ≤ s := by dsimp [b, a]; omega
        have hc : 1 ≤ c ∧ c ≤ s := by dsimp [c, b, a]; omega
        have habc : a + b + c = q := by dsimp [c, b, a]; omega
        let x : Fin r → ℕ := fun i =>
          if i.val % 3 = 0 then a else if i.val % 3 = 1 then b else c
        refine ⟨x, ?_, ?_⟩
        · intro i
          dsimp [x]
          split_ifs <;> omega
        · have htwo : (2 : Fin r) = 1 + 1 := Nat.cast_add 1 1
          have hnext (i : Fin r) (n : ℕ) :
              (i + (Nat.cast n : Fin r)).val % 3 = (i.val + n) % 3 := by
            rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod,
              Nat.mod_mod_of_dvd _ hr₃]
          have htriple (i : Fin r) : x i + x (i + 1) + x (i + 2) = q := by
            have h₁ := hnext i 1
            have h₂ := hnext i 2
            change (i + 1).val % 3 = (i.val + 1) % 3 at h₁
            change (i + 2).val % 3 = (i.val + 2) % 3 at h₂
            have hi : i.val % 3 < 3 := Nat.mod_lt _ (by omega)
            have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
            rcases hm with hm | hm | hm
            all_goals
              have hn₁ : (i.val + 1) % 3 = (i.val % 3 + 1) % 3 := by omega
              have hn₂ : (i.val + 2) % 3 = (i.val % 3 + 2) % 3 := by omega
              simp [x, h₁, h₂, hn₁, hn₂, hm]
              omega
          intro i
          have he := htriple (i - 1)
          have hidx : i - 1 + 2 = i + 1 := by rw [htwo]; abel
          simpa only [sub_add_cancel, hidx] using he
      · rcases hq₃ with ⟨m, hm⟩
        refine ⟨fun _ => m, ?_, ?_⟩
        · intro i
          dsimp
          constructor <;> omega
        · intro i
          dsimp
          omega
  have hpack (k : ℕ) (h : (q ≤ s ∧ 2 * k ≤ r) ∨ (q ≤ 2 * s ∧ 3 * k ≤ r)) :
    ∃ x : Fin r → ℕ, (∀ i, x i ≤ s) ∧ (∑ i, x i) = k * q ∧
      ∀ i, 0 < x i → x (i - 1) + x i + x (i + 1) = q := by
    classical
    obtain ⟨t, a, b, ht, ha, hbs, hab, hk, hbzero⟩ :
        ∃ t a b : ℕ, (t = 2 ∨ t = 3) ∧ (0 < a ∧ a ≤ s) ∧ b ≤ s ∧
          a + b = q ∧ t * k ≤ r ∧ (t = 2 → b = 0) := by
      rcases h with ⟨hs, hk⟩ | ⟨hs, hk⟩
      · exact ⟨2, q, 0, Or.inl rfl, ⟨hq, hs⟩, by omega, by omega, hk, fun _ => rfl⟩
      · refine ⟨3, min s q, q - min s q, Or.inr rfl, ?_, ?_, ?_, hk, by omega⟩
        all_goals omega
    have htpos : 0 < t := by omega
    have htbound : t ≤ 3 := by omega
    let f : Fin k → Fin r := fun j => ⟨t * j.val, by nlinarith [j.isLt]⟩
    let H : Finset (Fin r) := univ.image f
    have hcard : H.card = k := by
      have hinj : Function.Injective f := by
        intro i j he
        have hv := congrArg Fin.val he
        dsimp [f] at hv
        apply Fin.ext
        nlinarith
      simp [H, Finset.card_image_of_injective _ hinj]
    have hsep (m : ℕ) (hm : 0 < m) (hmt : m < t) :
        Disjoint H (H.image fun i => i + (Nat.cast m : Fin r)) := by
      rw [Finset.disjoint_left]
      intro u hu hv
      rcases mem_image.mp hu with ⟨i, hi, rfl⟩
      rcases mem_image.mp hv with ⟨v, hv, he⟩
      rcases mem_image.mp hv with ⟨j, hj, rfl⟩
      have hlt : t * j.val + m < r := by nlinarith [j.isLt]
      have hm' : m < r := by omega
      have hev := congrArg Fin.val he
      change ((t * j.val + m % r) % r) = t * i.val at hev
      rw [Nat.mod_eq_of_lt hm', Nat.mod_eq_of_lt hlt] at hev
      have hemod := congrArg (fun n : ℕ => n % t) hev
      rw [Nat.add_mod] at hemod
      simp only [Nat.mul_mod_right, Nat.mod_eq_of_lt hmt, zero_add] at hemod
      omega
    have hsep₁ := hsep 1 (by omega) (by omega)
    have hsep₂ (hb : 0 < b) : Disjoint H (H.image fun i => i + 2) := by
      have ht₃ : t = 3 := by
        rcases ht with ht | ht
        · have := hbzero ht
          omega
        · exact ht
      exact hsep 2 (by omega) (by omega)
    have hprev (i : Fin r) (hi : i ∈ H) : i - 1 ∉ H := by
      intro hj
      exact Finset.disjoint_left.mp hsep₁ hi
        (mem_image.mpr ⟨i - 1, hj, by simp⟩)
    have hnext (i : Fin r) (hi : i ∈ H) : i + 1 ∉ H := by
      intro hj
      exact Finset.disjoint_left.mp hsep₁ hj (mem_image.mpr ⟨i, hi, rfl⟩)
    have two : (2 : Fin r) = 1 + 1 := Nat.cast_add 1 1
    have hprev₂ (i : Fin r) (hi : i ∈ H) (hb : 0 < b) : i - 1 - 1 ∉ H := by
      intro hj
      exact Finset.disjoint_left.mp (hsep₂ hb) hi
        (mem_image.mpr ⟨i - 1 - 1, hj, by rw [two]; abel⟩)
    have hnext₂ (i : Fin r) (hi : i ∈ H) (hb : 0 < b) : i + 2 ∉ H := by
      intro hj
      exact Finset.disjoint_left.mp (hsep₂ hb) hj (mem_image.mpr ⟨i, hi, rfl⟩)
    let x : Fin r → ℕ := fun i => if i ∈ H then a else if i - 1 ∈ H then b else 0
    have hx₀ (i : Fin r) (hi : i ∈ H) : x i = a := by simp [x, hi]
    have hx₁ (i : Fin r) (hi : i ∈ H) : x (i + 1) = b := by
      simp [x, hnext i hi, hi]
    have hxprev (i : Fin r) (hi : i ∈ H) : x (i - 1) = 0 := by
      by_cases hb : b = 0
      · simp [x, hprev i hi, hb]
      · simp [x, hprev i hi, hprev₂ i hi (by omega)]
    have hx₂ (i : Fin r) (hi : i ∈ H) (hb : 0 < b) : x (i + 2) = 0 := by
      have he : i + 2 - 1 = i + 1 := by rw [two]; abel
      simp [x, hnext₂ i hi hb, he, hnext i hi]
    refine ⟨x, ?_, ?_, ?_⟩
    · intro i
      dsimp [x]
      split_ifs <;> omega
    · have hsplit (i : Fin r) :
          x i = (if i ∈ H then a else 0) + (if i - 1 ∈ H then b else 0) := by
        by_cases hi : i ∈ H
        · simp [x, hi, hprev i hi]
        · simp [x, hi]
      have hs := congrArg (fun f : Fin r → ℕ => ∑ i, f i) (funext hsplit)
      rw [Finset.sum_add_distrib] at hs
      have hshift : (∑ i : Fin r, if i - 1 ∈ H then b else 0) =
          ∑ i : Fin r, if i ∈ H then b else 0 := by
        have he := Fintype.sum_equiv (Equiv.addRight (1 : Fin r))
          (fun i => if i ∈ H then b else 0) (fun i => if i - 1 ∈ H then b else 0)
          (fun i => by simp)
        exact he.symm
      rw [hshift, ← Finset.sum_filter, ← Finset.sum_filter] at hs
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
        smul_eq_mul, hcard] at hs
      nlinarith
    · intro i hi
      by_cases hh : i ∈ H
      · rw [hxprev i hh, hx₀ i hh, hx₁ i hh]
        omega
      · have hh' : i - 1 ∈ H := by
          by_contra hn
          simp [x, hh, hn] at hi
        have hb : 0 < b := by simpa [x, hh, hh'] using hi
        have hi₀ := hx₀ (i - 1) hh'
        have hi₁ := hx₁ (i - 1) hh'
        have hi₂ := hx₂ (i - 1) hh' hb
        have he : i - 1 + 2 = i + 1 := by rw [two]; abel
        simp only [sub_add_cancel, he] at hi₁ hi₂
        rw [hi₀, hi₁, hi₂]
        exact hab
  constructor
  · rintro ⟨x, hx, hm, he⟩
    rcases hclass x hx he with hc | hf
    · left
      rcases hc with ⟨k, hk, hk₂, hk₃, hk₀⟩
      exact ⟨k, hm.symm.trans hk, hk₂, hk₃, hk₀⟩
    · right
      rcases hf with ⟨_, _, hs, hq₃, hqs, hd⟩
      exact ⟨by omega, hq₃, hqs, hd⟩
  · rintro (⟨k, hm, hk₂, hk₃, hk₀⟩ | ⟨hm, hq₃, hqs, hd⟩)
    · by_cases hk : k = 0
      · subst k
        have hm₀ : m = 0 := by simpa using hm
        subst m
        exact ⟨fun _ => 0, by simp, by simp, by simp⟩
      · have hqs : q ≤ 2 * s := by
          by_contra hn
          exact hk (hk₀ (by omega))
        have hc : (q ≤ s ∧ 2 * k ≤ r) ∨ (q ≤ 2 * s ∧ 3 * k ≤ r) := by
          by_cases hsmall : q ≤ s
          · exact Or.inl ⟨hsmall, hk₂⟩
          · exact Or.inr ⟨hqs, hk₃ (by omega)⟩
        rcases hpack k hc with ⟨x, hx, hs, he⟩
        exact ⟨x, hx, hs.trans hm.symm, he⟩
    · rcases hfull.mpr ⟨hq₃, hqs, hd⟩ with ⟨x, hx, he⟩
      have hs := congrArg (fun f : Fin r → ℕ => ∑ i, f i) (funext he)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, sub_eq_add_neg] at hs
      have hshift (a : Fin r) : (∑ i, x (i + a)) = ∑ i, x i :=
        Fintype.sum_equiv (Equiv.addRight a) (fun i => x (i + a)) x (fun _ => rfl)
      rw [hshift (-1), hshift 1] at hs
      exact ⟨x, fun i => (hx i).2, by omega, fun i _ => he i⟩

end D5.S3.Combinatorics.RegularInduced.DysonMcKay
