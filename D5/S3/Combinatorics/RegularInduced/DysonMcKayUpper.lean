/- GID: D5/S3/Combinatorics/RegularInduced/DysonMcKayUpper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RegularInduced/DysonMcKayUpper
   mirror-E: none(waiver:prime-component-budget-optimization)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Component budgets and triangle reserves bound every admissible avoiding union. -/

import Mathlib.Tactic
import D5.S3.Combinatorics.RegularInduced.DysonMcKayBags

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.RegularInduced.DysonMcKay

open DysonMcKayDefs

set_option maxHeartbeats 2000000 in
-- Finite allocation and integer optimization share one substantial declaration.
/-- Triangle reserves rule out the exceptional cycle configurations; the
remaining component budgets give the exact integer optimum in each prime class. -/
theorem upper_bound {p : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p)
    (comps : List (ℕ × ℕ)) (hadm : Admissible comps)
    (havoid : ¬ HasRegularInduced comps p) : order comps ≤ bound p := by
  classical
  have packet_cycle_allocation (comps : List (ℕ × ℕ)) (hadm : Admissible comps)
      {q k : ℕ} (hq : 0 < q) (J : Finset (Fin comps.length))
      (chosen : Fin comps.length → ℕ)
      (hJ : ∀ i ∈ J, 4 ≤ (comps.get i).1 ∧
        3 * chosen i = (comps.get i).1 * q ∧ 3 ≤ q ∧ q ≤ 3 * (comps.get i).2 ∧
        (3 ∣ (comps.get i).1 ∨ 3 ∣ q)) :
      let capacity : Fin comps.length → ℕ := fun i =>
        if i ∈ J then 0 else if (comps.get i).1 = 3 then
          if q ≤ 3 * (comps.get i).2 then 1 else 0
        else if q ≤ (comps.get i).2 then (comps.get i).1 / 2
        else if q ≤ 2 * (comps.get i).2 then (comps.get i).1 / 3 else 0
      k ≤ ∑ i, capacity i → HasRegularInduced comps ((∑ i ∈ J, chosen i) + k * q) := by
    classical
    intro capacity hk
    have allocate : ∀ {n : ℕ} (a : Fin n → ℕ) (k : ℕ), k ≤ ∑ i, a i →
        ∃ b : Fin n → ℕ, (∀ i, b i ≤ a i) ∧ (∑ i, b i) = k := by
      intro n
      induction n with
      | zero =>
        intro a k hk
        have hk₀ : k = 0 := by simpa using hk
        subst k
        exact ⟨fun _ => 0, fun i => Fin.elim0 i, by simp⟩
      | succ n ih =>
        intro a k hk
        rw [Fin.sum_univ_succ] at hk
        let first := min k (a 0)
        have hrest : k - first ≤ ∑ i : Fin n, a i.succ := by dsimp [first]; omega
        obtain ⟨b, hb, hs⟩ := ih (fun i => a i.succ) (k - first) hrest
        refine ⟨Fin.cons first b, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [first]
          · simpa using hb j
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, hs]
          dsimp [first]
          omega
    obtain ⟨b, hb, hs⟩ := allocate capacity k hk
    have hbJ (i : Fin comps.length) (hi : i ∈ J) : b i = 0 := by
      have he := hb i
      have hc : capacity i = 0 := by simp only [capacity, hi, ite_true]
      rw [hc] at he
      omega
    apply (regular_union_order_spectrum comps hadm _).mpr
    refine ⟨q, hq, fun i => if i ∈ J then chosen i else b i * q, ?_, ?_⟩
    · have he (i : Fin comps.length) :
          (if i ∈ J then chosen i else b i * q) =
            (if i ∈ J then chosen i else 0) + b i * q := by
        by_cases hi : i ∈ J
        · simp [hi, hbJ i hi]
        · simp [hi]
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_mul, hs]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    · intro i
      by_cases hiJ : i ∈ J
      · have hj := hJ i hiJ
        simp only [hiJ, ite_true, show ¬ (comps.get i).1 = 3 by omega, ite_false]
        exact Or.inr hj.2
      · simp only [hiJ, ite_false]
        have hr := (hadm _ (List.get_mem comps i)).1
        have hi := hb i
        have hcap : capacity i = (if (comps.get i).1 = 3 then
          if q ≤ 3 * (comps.get i).2 then 1 else 0
          else if q ≤ (comps.get i).2 then (comps.get i).1 / 2
          else if q ≤ 2 * (comps.get i).2 then (comps.get i).1 / 3 else 0) := by
          simp only [capacity, hiJ, ite_false]
        rw [hcap] at hi
        simp only [List.get_eq_getElem] at hr hi ⊢
        by_cases hr₃ : comps[i.val].1 = 3
        · simp only [hr₃, ite_true]
          by_cases hqs : q ≤ 3 * comps[i.val].2
          · have hb₁ : b i ≤ 1 := by simpa [hr₃, hqs] using hi
            by_cases hbi : b i = 0
            · exact Or.inl (by simp [hbi])
            · have hbi' : b i = 1 := by omega
              exact Or.inr ⟨by simp [hbi'], hqs⟩
          · have hb₀ : b i = 0 := by simpa [hr₃, hqs] using hi
            exact Or.inl (by simp [hb₀])
        · simp only [hr₃, ite_false]
          left
          refine ⟨b i, rfl, ?_, ?_, ?_⟩
          · split_ifs at hi <;> omega
          · intro hsq
            split_ifs at hi <;> omega
          · intro hbig
            have hb₀ : b i = 0 := by
              simpa [hr₃, show ¬ q ≤ comps[i.val].2 by omega,
                show ¬ q ≤ 2 * comps[i.val].2 by omega] using hi
            exact hb₀
  let r : Fin comps.length → ℕ := fun i => (comps.get i).1
  let s : Fin comps.length → ℕ := fun i => (comps.get i).2
  let a : Fin comps.length → ℕ := fun i => if r i = 3 then 1 else r i / 2
  let cap : ℕ → Fin comps.length → ℕ := fun q i =>
    if r i = 3 then if q ≤ 3 * s i then 1 else 0
    else if q ≤ s i then r i / 2 else if q ≤ 2 * s i then r i / 3 else 0
  let A := ∑ i, a i
  let T := ∑ i, cap 3 i
  let R := ∑ i, if r i = 3 then 2 else r i
  let S := (p - 1) / 2
  have had (i : Fin comps.length) : 3 ≤ r i ∧ 1 ≤ s i :=
    hadm _ (List.get_mem comps i)
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hSp : 2 * S = p - 1 := by dsimp [S]; omega
  have hS : 6 ≤ S := by dsimp [S]; omega
  have hpack (q k : ℕ) (hq : 0 < q) (hk : k ≤ ∑ i, cap q i) :
      HasRegularInduced comps (k * q) := by
    have h := packet_cycle_allocation comps hadm (k := k) hq ∅ (fun _ => 0) (by simp)
    simpa only [Finset.notMem_empty, ite_false, Finset.sum_empty, zero_add] using h hk
  have hcap₁ (i : Fin comps.length) : cap 1 i = a i := by
    have hs := (had i).2
    simp only [cap, a, show 1 ≤ s i by omega, show 1 ≤ 3 * s i by omega, ite_true]
  have hA : A ≤ p - 1 := by
    by_contra hn
    have hk : p ≤ ∑ i, cap 1 i := by simp only [hcap₁]; dsimp [A] at hn; omega
    have hh := hpack 1 p (by omega) hk
    simp only [mul_one] at hh
    exact havoid hh
  have hsbound (i : Fin comps.length) :
      (if r i = 3 then 3 * s i else 2 * s i) ≤ p - 1 := by
    by_contra hn
    have hcap : 1 ≤ cap p i := by
      have hri := (had i).1
      by_cases h3 : r i = 3
      · have hps : p ≤ 3 * s i := by simp only [h3, ite_true] at hn; omega
        simp only [cap, h3, hps, ite_true]
        exact le_rfl
      · simp only [h3, ite_false] at hn
        have hps : p ≤ 2 * s i := by omega
        simp only [cap, h3, hps, ite_false, ite_true]
        split_ifs <;> omega
    have hk : 1 ≤ ∑ i, cap p i :=
      hcap.trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i))
    have hh := hpack p 1 (by omega) hk
    simp only [one_mul] at hh
    exact havoid hh
  have hcaple (i : Fin comps.length) : cap 3 i ≤ a i := by
    have hr := (had i).1
    simp only [cap, a]
    split_ifs <;> omega
  have hn (i : Fin comps.length) :
      2 * (r i * s i) ≤ 5 * S * cap 3 i + 10 * a i := by
    have hr := (had i).1
    have hs := (had i).2
    have hb := hsbound i
    by_cases h3 : r i = 3
    · simp only [h3, ite_true] at hb
      have ht : cap 3 i = 1 := by simp only [cap, h3, show 3 ≤ 3 * s i by omega, ite_true]
      have ha : a i = 1 := by simp only [a, h3, ite_true]
      rw [ht, ha, h3]
      nlinarith
    · have hr₄ : 4 ≤ r i := by omega
      simp only [h3, ite_false] at hb
      have hsi : s i ≤ S := by omega
      have ha : a i = r i / 2 := by simp only [a, h3, ite_false]
      have hrlen : 2 * r i ≤ 5 * a i := by rw [ha]; omega
      by_cases hs₃ : 3 ≤ s i
      · have ht : cap 3 i = a i := by simp only [cap, a, h3, hs₃, ite_false, ite_true]
        rw [ht]
        nlinarith [Nat.mul_le_mul_right (s i) hrlen, Nat.mul_le_mul_left (5 * a i) hsi]
      · nlinarith [Nat.mul_le_mul_right 2 hrlen]
  have hN : order comps = ∑ i, r i * s i := by
    unfold order
    conv_lhs => rw [← List.ofFn_get comps, List.map_ofFn, List.sum_ofFn]
    rfl
  have hpacking : 2 * order comps ≤ 5 * S * T + 10 * A := by
    have hh := Finset.sum_le_sum (s := (univ : Finset (Fin comps.length))) (fun i _ => hn i)
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hN] using hh
  have hNR : order comps ≤ S * R := by
    have hl (i : Fin comps.length) : r i * s i ≤ S * (if r i = 3 then 2 else r i) := by
      have hb := hsbound i
      by_cases h3 : r i = 3
      · simp only [h3, ite_true] at hb ⊢
        omega
      · simp only [h3, ite_false] at hb ⊢
        have hs : s i ≤ S := by omega
        nlinarith
    have hh := Finset.sum_le_sum (s := (univ : Finset (Fin comps.length))) (fun i _ => hl i)
    simpa only [← Finset.mul_sum, hN] using hh
  have hprime₃ : p % 3 ≠ 0 := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h)
    omega
  have hres : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  let t := p / 12
  let B := if p % 12 = 1 then 27 * t else if p % 12 = 5 then 27 * t + 9
    else if p % 12 = 7 then 27 * t + 14 else 27 * t + 22
  have hpval : p = 12 * t + p % 12 := by dsimp [t]; omega
  have hB : bound p = S * B := by
    rcases hres with h | h | h | h
    · have hlin : 2 * B = 9 * S := by simp [B, h]; omega
      have he : 9 * (p - 1) ^ 2 = (S * B) * 8 := by
        rw [← hSp]
        nlinarith [congrArg (fun z : ℕ => z * S) hlin]
      simp only [bound, h, true_or, ite_true]
      rw [he, Nat.mul_div_cancel _ (by omega)]
    · have hlin : 2 * B = 9 * S := by simp [B, h]; omega
      have he : 9 * (p - 1) ^ 2 = (S * B) * 8 := by
        rw [← hSp]
        nlinarith [congrArg (fun z : ℕ => z * S) hlin]
      simp only [bound, h, or_true, ite_true]
      rw [he, Nat.mul_div_cancel _ (by omega)]
    · have hlin : 2 * B = 9 * S + 1 := by simp [B, h]; omega
      have hdiff : 9 * p - 7 = 18 * S + 2 := by omega
      have he : (p - 1) * (9 * p - 7) = (S * B) * 8 := by
        rw [← hSp, hdiff]
        nlinarith [congrArg (fun z : ℕ => z * S) hlin]
      simp only [bound, h, show ¬ (7 = 1 ∨ 7 = 5) by omega, ite_false, ite_true]
      rw [he, Nat.mul_div_cancel _ (by omega)]
    · have hlin : 2 * B + 1 = 9 * S := by simp [B, h]; omega
      have hdiff : 9 * p - 11 + 2 = 18 * S := by omega
      have he : (p - 1) * (9 * p - 11) = (S * B) * 8 := by
        rw [← hSp]
        nlinarith [congrArg (fun z : ℕ => z * S) hlin, congrArg (fun z : ℕ => z * S) hdiff]
      simp only [bound, h, show ¬ (11 = 1 ∨ 11 = 5) by omega,
        show ¬ (11 = 7) by omega, ite_false]
      rw [he, Nat.mul_div_cancel _ (by omega)]
  rw [hB]
  by_cases hlow : 3 * T < p + 4
  · have hT : 3 * T ≤ 2 * S + 4 := by omega
    have hNsmall : 6 * order comps ≤ 10 * S ^ 2 + 80 * S := by
      nlinarith [Nat.mul_le_mul_left (5 * S) hT, Nat.mul_le_mul_left 10 hA]
    have hSB : 2 * (S * B) + S ≥ 9 * S ^ 2 := by
      rcases hres with h | h | h | h
      all_goals
        have hlin : 9 * S ≤ 2 * B + 1 := by simp [B, h]; omega
        nlinarith [Nat.mul_le_mul_right S hlin]
    nlinarith [Nat.mul_le_mul_right S (show 88 ≤ 17 * S by omega)]
  · have hhigh : p + 4 ≤ 3 * T := by omega
    have hreserve (J : Finset (Fin comps.length))
        (hcycle : ∀ i ∈ J, 4 ≤ r i)
        (hlength : (∑ i ∈ J, r i) ≤ p)
        (hmod : (p - ∑ i ∈ J, r i) % 3 = 0)
        (hsupply : (p - ∑ i ∈ J, r i) / 3 + ∑ i ∈ J, cap 3 i ≤ T) : False := by
      have hj : ∀ i ∈ J, 4 ≤ (comps.get i).1 ∧
          3 * r i = (comps.get i).1 * 3 ∧ 3 ≤ 3 ∧ 3 ≤ 3 * (comps.get i).2 ∧
          (3 ∣ (comps.get i).1 ∨ 3 ∣ 3) := by
        intro i hi
        have hs : 1 ≤ (comps.get i).2 := (had i).2
        exact ⟨hcycle i hi, by dsimp [r]; omega, le_rfl, by omega,
          Or.inr (dvd_refl 3)⟩
      have hsplit : (∑ i, if i ∈ J then 0 else cap 3 i) +
          (∑ i ∈ J, cap 3 i) = T := by
        have he (i : Fin comps.length) :
            (if i ∈ J then 0 else cap 3 i) + (if i ∈ J then cap 3 i else 0) = cap 3 i := by
          split_ifs <;> simp
        have hh := congrArg (fun f : Fin comps.length → ℕ => ∑ i, f i) (funext he)
        rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hh
        simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using hh
      have hk : (p - ∑ i ∈ J, r i) / 3 ≤ ∑ i, if i ∈ J then 0 else cap 3 i := by omega
      have hh := packet_cycle_allocation comps hadm (q := 3) (by omega) J r hj hk
      have htotal : (∑ i ∈ J, r i) + (p - ∑ i ∈ J, r i) / 3 * 3 = p := by omega
      rw [htotal] at hh
      exact havoid hh
    have hexclude (u v : ℕ) (hu : 4 ≤ u) (hv : 4 ≤ v)
        (hpu : u ≤ p) (hpv : 2 * v ≤ p) (hmu : (p - u) % 3 = 0)
        (hmv : (p - 2 * v) % 3 = 0)
        (hsu : (p - u) / 3 + u / 2 ≤ T)
        (hsv : (p - 2 * v) / 3 + 2 * (v / 2) ≤ T) :
        (∀ i, r i ≠ u) ∧ (univ.filter fun i => r i = v).card ≤ 1 := by
      constructor
      · intro i hi
        apply hreserve {i}
        · intro j hj
          have : j = i := by simpa using hj
          subst j
          omega
        · simpa [hi] using hpu
        · simpa [hi] using hmu
        · have hc := hcaple i
          have ha : a i = u / 2 := by simp only [a, hi, show u ≠ 3 by omega, ite_false]
          simp only [sum_singleton, hi]
          rw [ha] at hc
          omega
      · apply Finset.card_le_one.mpr
        intro i hi j hj
        have hi' : r i = v := (mem_filter.mp hi).2
        have hj' : r j = v := (mem_filter.mp hj).2
        by_contra hne
        apply hreserve {i, j}
        · intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl <;> omega
        · simp [hne, hi', hj']; omega
        · simp [hne, hi', hj']; omega
        · have hci := hcaple i
          have hcj := hcaple j
          have hai : a i = v / 2 := by simp only [a, hi', show v ≠ 3 by omega, ite_false]
          have haj : a j = v / 2 := by simp only [a, hj', show v ≠ 3 by omega, ite_false]
          rw [hai] at hci
          rw [haj] at hcj
          simp only [sum_insert (show i ∉ ({j} : Finset (Fin comps.length)) from by
            simpa only [mem_singleton] using hne), sum_singleton, hi', hj']
          omega
    have hcorrection (i : Fin comps.length) :
        4 * (if r i = 3 then 2 else r i) ≤
          9 * a i + (if r i = 5 then 2 else if r i = 7 then 1 else 0) := by
      have hr := (had i).1
      simp only [a]
      split_ifs <;> omega
    have hRbase : 4 * R ≤ 9 * A +
        ∑ i, if r i = 5 then 2 else if r i = 7 then 1 else 0 := by
      have hh := Finset.sum_le_sum (s := (univ : Finset (Fin comps.length)))
        (fun i _ => hcorrection i)
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hh
    have hR : R ≤ B := by
      by_cases hp₁ : p % 3 = 1
      · obtain ⟨hn₇, hc₅⟩ := hexclude 7 5 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
        have hsum : (∑ i, if r i = 5 then 2 else if r i = 7 then 1 else 0) =
            2 * (univ.filter fun i => r i = 5).card := by
          simp only [hn₇, ite_false]
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
          omega
        have hR' : 4 * R ≤ 18 * S + 2 := by rw [hsum] at hRbase; omega
        rcases hres with h | h | h | h
        all_goals simp [B, h]; omega
      · have hp₂ : p % 3 = 2 := by omega
        have hp17 : 17 ≤ p := by omega
        obtain ⟨hn₅, hc₇⟩ := hexclude 5 7 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
        have hsum : (∑ i, if r i = 5 then 2 else if r i = 7 then 1 else 0) =
            (univ.filter fun i => r i = 7).card := by
          simp only [hn₅, ite_false]
          exact Finset.sum_boole _ _
        have hR' : 4 * R ≤ 18 * S + 1 := by rw [hsum] at hRbase; omega
        rcases hres with h | h | h | h
        all_goals simp [B, h]; omega
    exact hNR.trans (Nat.mul_le_mul_left S hR)

end D5.S3.Combinatorics.RegularInduced.DysonMcKay
