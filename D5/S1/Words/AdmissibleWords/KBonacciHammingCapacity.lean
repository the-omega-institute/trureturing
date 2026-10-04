/- GID: D5/S1/Words/AdmissibleWords/KBonacciHammingCapacity
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciHammingCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp Hamming capacity and actual-length lower bounds in the common remainder image. -/

import D5.S1.Words.ClosedRunStarts
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciHammingCapacity

open Finset Polynomial
open D5.S0.Tower.DBonacci.Names D5.S1.Words.ClosedRunStarts

/-- Sharp one-bit capacity, explicit shortest words, and the charge bound for every
actual realization in the original common polynomial remainder image. -/
theorem kbonacci_actual_hamming_capacity (k : ℕ) (hk : 2 ≤ k) :
    let wt := fun {n : ℕ} (w : Fin n → Bool) => (univ.filter (fun i => w i = true)).card
    let B := fun n (i : Fin n) => decide (i.val % k < k - 1)
    let p := fun c => if c = 0 then 0 else c + (c - 1) / (k - 1)
    let W := fun c => B (p c)
    (∀ n (w : Fin n → Bool), DBonacciAdmissible k n w → wt w ≤ n - n / k) ∧
    (∀ n, DBonacciAdmissible k n (B n) ∧ wt (B n) = n - n / k) ∧
    p 0 = 0 ∧
    (∀ c, DBonacciAdmissible k (p c) (W c) ∧ wt (W c) = c ∧
      (∀ n (w : Fin n → Bool), DBonacciAdmissible k n w → wt w = c → p c ≤ n) ∧
      (0 < c →
        let t := (c - 1) / (k - 1)
        let u := c - t * (k - 1)
        1 ≤ u ∧ u ≤ k - 1 ∧ p c = t * k + u ∧
        (∀ j r : ℕ, j < t → r < k → ∀ i : Fin (p c),
          i.val = j * k + r → W c i = decide (r < k - 1)) ∧
        (∀ i : Fin (p c), t * k ≤ i.val → W c i = true))) ∧
    (∀ (d : ℕ) (A : Finset ℕ), 2 ≤ d → A.Nonempty → (∀ a ∈ A, 2 ≤ a) →
      let Phi := fun a => (X ^ a - ∑ j ∈ range a, X ^ j : (ZMod d)[X])
      let O := fun P : (ZMod d)[X] => fun a : {a // a ∈ A} => P %ₘ Phi a.val
      let H := {y // y ∈ Set.range O}
      let q := A.lcm (fun a => Nat.gcd d (a - 1))
      let Pw := fun {n : ℕ} (w : Fin n → Bool) =>
        ∑ i : Fin n, monomial i.val (if w i then 1 else 0 : ZMod d)
      q ∣ d ∧ ∃ chi : H → ZMod q,
        (∀ P : (ZMod d)[X], chi ⟨O P, ⟨P, rfl⟩⟩ = ((P.eval 1).val : ZMod q)) ∧
        (∀ n (w : Fin n → Bool), chi ⟨O (Pw w), ⟨Pw w, rfl⟩⟩ = (wt w : ZMod q)) ∧
        (∀ (y : H) (c : ℕ), 2 ≤ q → 1 ≤ c → c < q → chi y = (c : ZMod q) →
          ∀ n (w : Fin n → Bool), DBonacciAdmissible k n w → O (Pw w) = y.val →
            p c ≤ n)) := by
  classical
  dsimp only
  let wt := fun {n : ℕ} (w : Fin n → Bool) => (univ.filter (fun i => w i = true)).card
  let B := fun n (i : Fin n) => decide (i.val % k < k - 1)
  let p := fun c => if c = 0 then 0 else c + (c - 1) / (k - 1)
  let W := fun c => B (p c)
  have hkp : 0 < k := by omega
  have hkm : 0 < k - 1 := by omega
  have hks : k - 1 + 1 = k := by omega
  have hsplit : ∀ n (w : Fin n → Bool),
      wt w + (univ.filter (fun i => w i = false)).card = n := by
    intro n w
    have h := card_filter_add_card_filter_not (s := univ) (fun i : Fin n => w i = true)
    simpa [wt, Bool.not_eq_true] using h
  have hshort : ∀ n (w : Fin n → Bool), n < k → DBonacciAdmissible k n w := by
    intro n w hn
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    subst k
    exact runAdmissible_eq_true_of_length_le m m n w (by omega) le_rfl
  have hcapacity : ∀ n (w : Fin n → Bool),
      DBonacciAdmissible k n w → wt w ≤ n - n / k := by
    intro n w hw
    by_cases hkn : k ≤ n
    · have hav := (closed_word_run_start_equivalence n k hkp hkn w).1.mp hw
      have hz : ∀ j : Fin (n / k), ∃ z : Fin n,
          j.val * k ≤ z.val ∧ z.val < (j.val + 1) * k ∧ w z = false := by
        intro j
        have hend : (j.val + 1) * k ≤ n :=
          (Nat.mul_le_mul_right k j.isLt).trans (Nat.div_mul_le_self n k)
        by_contra hnone
        apply hav (j.val * k)
        refine ⟨by nlinarith, ?_⟩
        intro i hlo hhi
        cases hbit : w i with
        | false => exact False.elim (hnone ⟨i, hlo, by nlinarith, hbit⟩)
        | true => rfl
      let f : Fin (n / k) → {i : Fin n // w i = false} :=
        fun j => ⟨Classical.choose (hz j), (Classical.choose_spec (hz j)).2.2⟩
      have hf : Function.Injective f := by
        intro j l he
        have heval : (Classical.choose (hz j)).val = (Classical.choose (hz l)).val :=
          congrArg (fun i : {i : Fin n // w i = false} => i.val.val) he
        have hj := Classical.choose_spec (hz j)
        have hl := Classical.choose_spec (hz l)
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hmul := Nat.mul_le_mul_right k hlt
          nlinarith
        · have hmul := Nat.mul_le_mul_right k hgt
          nlinarith
      have hcard := Fintype.card_le_of_injective f hf
      have hzcount : n / k ≤ (univ.filter (fun i : Fin n => w i = false)).card := by
        simpa [Fintype.card_subtype] using hcard
      have hs := hsplit n w
      omega
    · have hs := hsplit n w
      rw [Nat.div_eq_of_lt (by omega : n < k)]
      omega
  have hperiod : ∀ n, DBonacciAdmissible k n (B n) ∧ wt (B n) = n - n / k := by
    intro n
    have hlegal : DBonacciAdmissible k n (B n) := by
      by_cases hkn : k ≤ n
      · apply (closed_word_run_start_equivalence n k hkp hkn (B n)).1.mpr
        intro s hb
        have hm := Nat.mod_lt s hkp
        have he := Nat.mod_add_div s k
        let z := s / k * k + (k - 1)
        have hsz : s ≤ z := by dsimp [z]; nlinarith
        have hzs : z < s + k := by
          have hsl := Nat.div_mul_le_self s k
          dsimp [z]
          omega
        have hzn : z < n := lt_of_lt_of_le hzs hb.1
        have hrem : z % k = k - 1 := by
          simp [z, Nat.add_mod, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        have hfalse : B n ⟨z, hzn⟩ = false := by simp [B, hrem]
        have ht := hb.2 ⟨z, hzn⟩ hsz hzs
        simp [hfalse] at ht
      · exact hshort n (B n) (by omega)
    have hzrem : ∀ i : Fin n, B n i = false ↔ i.val % k = k - 1 := by
      intro i
      have hm := Nat.mod_lt i.val hkp
      simp only [B, decide_eq_false_iff_not]
      omega
    let f : Fin (n / k) → {i : Fin n // B n i = false} := fun j =>
      ⟨⟨j.val * k + (k - 1), by
        have he := (Nat.mul_le_mul_right k j.isLt).trans (Nat.div_mul_le_self n k)
        nlinarith⟩, (hzrem _).mpr (by
          simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : k - 1 < k)])⟩
    have hiq : ∀ i : {i : Fin n // B n i = false}, i.val.val / k < n / k := by
      intro i
      have hr := (hzrem i.val).mp i.property
      have he := Nat.mod_add_div i.val.val k
      have hn := i.val.isLt
      have hmul : (i.val.val / k + 1) * k ≤ n := by nlinarith
      have hdiv := (Nat.le_div_iff_mul_le hkp).mpr hmul
      omega
    let e : Fin (n / k) ≃ {i : Fin n // B n i = false} :=
      { toFun := f
        invFun := fun i => ⟨i.val.val / k, hiq i⟩
        left_inv := by
          intro j
          apply Fin.ext
          change (j.val * k + (k - 1)) / k = j.val
          apply Nat.div_eq_of_lt_le <;> nlinarith
        right_inv := by
          intro i
          apply Subtype.ext
          apply Fin.ext
          have hr := (hzrem i.val).mp i.property
          have he := Nat.mod_add_div i.val.val k
          dsimp [f]
          nlinarith }
    have hzcount : (univ.filter (fun i : Fin n => B n i = false)).card = n / k := by
      have hc := Fintype.card_congr e
      simpa [Fintype.card_subtype] using hc.symm
    refine ⟨hlegal, ?_⟩
    have hs := hsplit n (B n)
    omega
  have hinverse : ∀ c n : ℕ, c ≤ n - n / k → p c ≤ n := by
    intro c n hc
    by_cases hcz : c = 0
    · simp [p, hcz]
    · have he := Nat.mod_add_div n k
      have hr := Nat.mod_lt n hkp
      have hdle := Nat.div_le_self n k
      have hcn : c + n / k ≤ n := by omega
      have hcs : c - 1 + 1 = c := by omega
      have hd : (c - 1) / (k - 1) ≤ n / k := by
        apply Nat.lt_succ_iff.mp
        apply (Nat.div_lt_iff_lt_mul hkm).mpr
        nlinarith
      simp only [p, if_neg hcz]
      omega
  have hwords : ∀ c, DBonacciAdmissible k (p c) (W c) ∧ wt (W c) = c ∧
      (∀ n (w : Fin n → Bool), DBonacciAdmissible k n w → wt w = c → p c ≤ n) ∧
      (0 < c →
        let t := (c - 1) / (k - 1)
        let u := c - t * (k - 1)
        1 ≤ u ∧ u ≤ k - 1 ∧ p c = t * k + u ∧
        (∀ j r : ℕ, j < t → r < k → ∀ i : Fin (p c),
          i.val = j * k + r → W c i = decide (r < k - 1)) ∧
        (∀ i : Fin (p c), t * k ≤ i.val → W c i = true)) := by
    intro c
    have hmin : ∀ n (w : Fin n → Bool), DBonacciAdmissible k n w → wt w = c → p c ≤ n := by
      intro n w hw hwt
      exact hinverse c n (hwt ▸ hcapacity n w hw)
    by_cases hcz : c = 0
    · subst c
      refine ⟨(hperiod (p 0)).1, ?_, hmin, ?_⟩
      · simpa [W, p] using (hperiod (p 0)).2
      · omega
    · let t := (c - 1) / (k - 1)
      let u := c - t * (k - 1)
      have he := Nat.mod_add_div (c - 1) (k - 1)
      have hr := Nat.mod_lt (c - 1) hkm
      change (c - 1) % (k - 1) + (k - 1) * t = c - 1 at he
      rw [Nat.mul_comm (k - 1) t] at he
      have hu : 1 ≤ u ∧ u ≤ k - 1 := by dsimp [u]; omega
      have hcu : c = t * (k - 1) + u := by dsimp [u]; omega
      have hp : p c = t * k + u := by
        simp only [p, if_neg hcz]
        change c + t = t * k + u
        nlinarith
      have hdiv : p c / k = t := by
        apply Nat.div_eq_of_lt_le
        · rw [hp]; omega
        · rw [hp]; nlinarith [hu.2]
      refine ⟨(hperiod (p c)).1, ?_, hmin, ?_⟩
      · have hs := (hperiod (p c)).2
        change wt (B (p c)) = c
        rw [hs, hdiv, hp]
        have hprod : t * k = t * (k - 1) + t := by nlinarith
        rw [hprod]
        omega
      · intro _
        change 1 ≤ u ∧ u ≤ k - 1 ∧ p c = t * k + u ∧ _
        refine ⟨hu.1, hu.2, hp, ?_, ?_⟩
        · intro j r hj hrr i hi
          simp [W, B, hi, Nat.add_mod, Nat.mod_eq_of_lt hrr]
        · intro i hi
          change t * k ≤ i.val at hi
          have hib : i.val < t * k + u := lt_of_lt_of_eq i.isLt hp
          have hrem : i.val % k < k - 1 := by
            have hdecomp : i.val = t * k + (i.val - t * k) := by omega
            have hsmall : i.val - t * k < k - 1 := by omega
            rw [hdecomp]
            simpa [Nat.add_mod, Nat.mod_eq_of_lt (by omega : i.val - t * k < k)] using hsmall
          simp [W, B, hrem]
  refine ⟨hcapacity, hperiod, by simp, hwords, ?_⟩
  intro d A hd hA horders
  let Phi := fun a => (X ^ a - ∑ j ∈ range a, X ^ j : (ZMod d)[X])
  let O := fun P : (ZMod d)[X] => fun a : {a // a ∈ A} => P %ₘ Phi a.val
  let H := {y // y ∈ Set.range O}
  let g := fun a => Nat.gcd d (a - 1)
  let q := A.lcm g
  let Pw := fun {n : ℕ} (w : Fin n → Bool) =>
    ∑ i : Fin n, monomial i.val (if w i then 1 else 0 : ZMod d)
  have hqd : q ∣ d := Finset.lcm_dvd (fun a _ => Nat.gcd_dvd_left d (a - 1))
  have hdn : d ≠ 0 := by omega
  let : NeZero d := ⟨hdn⟩
  have heval : ∀ (a : ℕ) (ha : a ∈ A) (P : (ZMod d)[X]),
      (P %ₘ Phi a).eval₂ (ZMod.castHom (Nat.gcd_dvd_left d (a - 1)) (ZMod (g a))) 1 =
        ((P.eval 1).val : ZMod (g a)) := by
    intro a ha P
    let f := ZMod.castHom (Nat.gcd_dvd_left d (a - 1)) (ZMod (g a))
    have ha2 := horders a ha
    have hroot : (Phi a).eval₂ f 1 = 0 := by
      have hz : ((a - 1 : ℕ) : ZMod (g a)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_right d (a - 1))
      have hcast : (a : ZMod (g a)) = ((a - 1 : ℕ) : ZMod (g a)) + 1 := by
        have haeq : a = (a - 1) + 1 := by omega
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun x : ℕ => (x : ZMod (g a))) haeq
      simp [Phi, Polynomial.eval₂_sub, Polynomial.eval₂_finsetSum, hcast, hz]
    rw [Polynomial.eval₂_modByMonic_eq_self_of_root hroot, Polynomial.eval₂_at_one]
    exact ZMod.cast_eq_val _
  have hindependent : ∀ P Q : (ZMod d)[X], O P = O Q →
      ((P.eval 1).val : ZMod q) = ((Q.eval 1).val : ZMod q) := by
    intro P Q hPQ
    have hcoords : ∀ a ∈ A, Nat.ModEq (g a) (P.eval 1).val (Q.eval 1).val := by
      intro a ha
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      rw [← heval a ha P, ← heval a ha Q]
      exact congrArg (fun R : (ZMod d)[X] =>
        R.eval₂ (ZMod.castHom (Nat.gcd_dvd_left d (a - 1)) (ZMod (g a))) 1)
        (congrFun hPQ ⟨a, ha⟩)
    have hfold : ∀ S : Finset ℕ, (∀ a ∈ S, Nat.ModEq (g a) (P.eval 1).val (Q.eval 1).val) →
        Nat.ModEq (S.lcm g) (P.eval 1).val (Q.eval 1).val := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; exact Nat.modEq_one
      | @insert a S ha ih =>
        intro hs
        rw [Finset.lcm_insert]
        exact Nat.mod_lcm (hs a (by simp)) (ih (fun b hb => hs b (by simp [hb])))
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hfold A hcoords)
  let chi : H → ZMod q := fun y => ((Classical.choose y.property).eval 1).val
  have hchi : ∀ P : (ZMod d)[X], chi ⟨O P, ⟨P, rfl⟩⟩ = ((P.eval 1).val : ZMod q) := by
    intro P
    exact hindependent _ P (Classical.choose_spec (show O P ∈ Set.range O from ⟨P, rfl⟩))
  have hwordeval : ∀ n (w : Fin n → Bool), (Pw w).eval 1 = (wt w : ZMod d) := by
    intro n w
    simp [Pw, wt, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      Finset.sum_boole]
  have hwordchi : ∀ n (w : Fin n → Bool),
      chi ⟨O (Pw w), ⟨Pw w, rfl⟩⟩ = (wt w : ZMod q) := by
    intro n w
    rw [hchi, hwordeval]
    calc
      ((wt w : ZMod d).val : ZMod q) = (ZMod.castHom hqd (ZMod q)) (wt w : ZMod d) := by
        rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      _ = (wt w : ZMod q) := map_natCast (ZMod.castHom hqd (ZMod q)) (wt w)
  refine ⟨hqd, chi, hchi, hwordchi, ?_⟩
  intro y c hq hc hcq hy n w hw how
  have he : (⟨O (Pw w), ⟨Pw w, rfl⟩⟩ : H) = y := Subtype.ext how
  have hcharge : (wt w : ZMod q) = (c : ZMod q) := by rw [← hwordchi, he, hy]
  have hmod : wt w % q = c := by
    exact ((ZMod.natCast_eq_natCast_iff' _ _ q).mp hcharge).trans (Nat.mod_eq_of_lt hcq)
  have hcw : c ≤ wt w := by rw [← hmod]; exact Nat.mod_le _ _
  exact hinverse c n (hcw.trans (hcapacity n w hw))

end D5.S1.Words.AdmissibleWords.KBonacciHammingCapacity
