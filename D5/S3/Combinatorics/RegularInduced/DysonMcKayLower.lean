/- GID: D5/S3/Combinatorics/RegularInduced/DysonMcKayLower
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RegularInduced/DysonMcKayLower
   mirror-E: none(waiver:explicit-prime-extremal-constructions)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The four Dyson and McKay constructions attain the prime order bound. -/

import Mathlib.Tactic
import D5.S3.Combinatorics.RegularInduced.DysonMcKayBags

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.RegularInduced.DysonMcKay

open DysonMcKayDefs

set_option maxHeartbeats 1000000 in
/-- The prime constructions have the claimed orders and avoid every regular
induced subgraph of order `p`, including disconnected ones. -/
theorem attainment {p : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p) :
    ∃ comps : List (ℕ × ℕ), Admissible comps ∧ ¬ HasRegularInduced comps p ∧
      order comps = bound p := by
  classical
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp₃ : p % 3 ≠ 0 := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h)
    omega
  have hres : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  let S := (p - 1) / 2
  have hS : 6 ≤ S := by dsimp [S]; omega
  have hSp : 2 * S = p - 1 := by dsimp [S]; omega
  have hadm (r n : ℕ) (hr : 3 ≤ r) : Admissible ((r, S) :: List.replicate n (9, S)) := by
    intro c hc
    simp only [List.mem_cons, List.mem_replicate] at hc
    rcases hc with rfl | ⟨_, rfl⟩ <;> omega
  have havoid (r n : ℕ) (hr : r = 4 ∨ r = 5 ∨ r = 9)
      (hbudget : r / 2 + 4 * n = p - 1)
      (hresidue : r = 9 ∨ p % 3 ≠ r % 3) :
      ¬ HasRegularInduced ((r, S) :: List.replicate n (9, S)) p := by
    intro hh
    have hpgt : 2 * S < p := by omega
    have hr₄ : 4 ≤ r := by omega
    have hw := (regular_union_order_spectrum _ (hadm r n (by omega)) p).mp hh
    simp only [List.length_cons] at hw
    have hlen : (List.replicate n (9, S)).length = n := List.length_replicate
    obtain ⟨q, hq, m, hm, he⟩ := hw
    have hhead := he 0
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
      ] at hhead
    simp only [show r ≠ 3 by omega, ite_false] at hhead
    have htail (i : Fin (List.replicate n (9, S)).length) := he i.succ
    have htails : ∀ i : Fin (List.replicate n (9, S)).length,
        (∃ k : ℕ, m i.succ = k * q ∧ 2 * k ≤ 9 ∧
          (S < q → 3 * k ≤ 9) ∧ (2 * S < q → k = 0)) ∨
        (3 * m i.succ = 9 * q ∧ 3 ≤ q ∧ q ≤ 3 * S ∧ (3 ∣ 9 ∨ 3 ∣ q)) := by
      intro i
      simpa [List.get_eq_getElem] using htail i
    rw [Fin.sum_univ_succ] at hm
    have hheadle : m 0 ≤ p := by omega
    have htaille (i : Fin (List.replicate n (9, S)).length) : m i.succ ≤ p := by
      have hs := Finset.single_le_sum (fun j _ => Nat.zero_le (m j.succ)) (mem_univ i)
      omega
    have hq₁ : q ≠ 1 := by
      intro hq'
      have hb₀ : m 0 ≤ r / 2 := by
        rcases hhead with ⟨k, hk, hk₂, _, _⟩ | ⟨_, hq₃, _, _⟩
        · rw [hq'] at hk
          omega
        · omega
      have hbt : ∀ i : Fin (List.replicate n (9, S)).length, m i.succ ≤ 4 := by
        intro i
        rcases htails i with ⟨k, hk, hk₂, _, _⟩ | ⟨_, hq₃, _, _⟩
        · rw [hq'] at hk
          omega
        · omega
      have hs := Finset.sum_le_sum
        (s := (univ : Finset (Fin (List.replicate n (9, S)).length))) (fun i _ => hbt i)
      simp only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hs
      omega
    have htdiv (i : Fin (List.replicate n (9, S)).length) : q ∣ m i.succ := by
      rcases htails i with ⟨k, hk, _, _, _⟩ | ⟨hk, _, _, _⟩
      · exact ⟨k, by nlinarith⟩
      · exact ⟨3, by omega⟩
    have hsumdiv : q ∣ ∑ i : Fin (List.replicate n (9, S)).length, m i.succ :=
      Finset.dvd_sum fun i _ => htdiv i
    have hqne : q ≠ p := by
      intro hqp
      have hbig : 2 * S < q := hqp.symm ▸ hpgt
      have ht₀ : ∀ i : Fin (List.replicate n (9, S)).length, m i.succ = 0 := by
        intro i
        rcases htails i with ⟨k, hk, _, _, hk₀⟩ | ⟨hk, _, _, _⟩
        · have hk' := hk₀ hbig
          simp [hk'] at hk
          exact hk
        · have hi := htaille i
          omega
      have hh₀ : m 0 = 0 := by
        rcases hhead with ⟨k, hk, _, _, hk₀⟩ | ⟨hk, _, _, _⟩
        · have hk' := hk₀ hbig
          simp [hk'] at hk
          exact hk
        · have hmul := Nat.mul_le_mul_right q hr₄
          nlinarith
      simp only [ht₀, Finset.sum_const_zero, hh₀, zero_add] at hm
      omega
    have hnotdiv : ¬ q ∣ p := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with hd | hd
      · exact hq₁ hd
      · exact hqne hd
    rcases hhead with ⟨k, hk, _, _, _⟩ | ⟨hfull, _, _, hd⟩
    · have hd₀ : q ∣ m 0 := ⟨k, by nlinarith⟩
      exact hnotdiv (hm ▸ dvd_add hd₀ hsumdiv)
    · by_cases hr₉ : r = 9
      · have hd₀ : q ∣ m 0 := ⟨3, by rw [hr₉] at hfull; omega⟩
        exact hnotdiv (hm ▸ dvd_add hd₀ hsumdiv)
      · have hr₃ : ¬ 3 ∣ r := by rcases hr with hr | hr | hr <;> simp_all
        obtain ⟨z, hz⟩ := hd.resolve_left hr₃
        have hm₀ : m 0 = r * z := by rw [hz] at hfull; nlinarith
        have hzq : z ∣ q := ⟨3, by omega⟩
        have hzsum : z ∣ ∑ i : Fin (List.replicate n (9, S)).length, m i.succ :=
          dvd_trans hzq hsumdiv
        have hzhead : z ∣ m 0 := ⟨r, by nlinarith⟩
        have hzp : z ∣ p := hm ▸ dvd_add hzhead hzsum
        have hz₁ : z = 1 := by
          rcases (Nat.dvd_prime hp).mp hzp with hz' | hz'
          · exact hz'
          · have hmul := Nat.mul_le_mul_right p hr₄
            rw [hz'] at hm₀
            nlinarith
        have hmod : (∑ i : Fin (List.replicate n (9, S)).length, m i.succ) % 3 = 0 := by
          have hthree : 3 ∣ q := ⟨z, hz⟩
          exact Nat.mod_eq_zero_of_dvd (dvd_trans hthree hsumdiv)
        have hm₀' : m 0 = r := by simpa [hz₁] using hm₀
        have hneq : p % 3 ≠ r % 3 := hresidue.resolve_left hr₉
        omega
  have horder (r n : ℕ) : order ((r, S) :: List.replicate n (9, S)) =
      (r + 9 * n) * S := by simp [order, List.map_replicate, List.sum_replicate]; ring
  let t := p / 12
  have ht : p = 12 * t + p % 12 := by dsimp [t]; omega
  rcases hres with h | h | h | h
  · have htpos : 1 ≤ t := by omega
    let n := 3 * t - 1
    have hn : n + 1 = 3 * t := by dsimp [n]; omega
    refine ⟨(9, S) :: List.replicate n (9, S), hadm 9 n (by omega),
      havoid 9 n (by omega) (by omega) (Or.inl rfl), ?_⟩
    rw [horder]
    have hlin : 2 * (9 + 9 * n) = 9 * S := by omega
    have he : 9 * (p - 1) ^ 2 = ((9 + 9 * n) * S) * 8 := by
      rw [← hSp]
      nlinarith [congrArg (fun z : ℕ => z * S) hlin]
    simp only [bound, h, true_or, ite_true]
    rw [he, Nat.mul_div_cancel _ (by omega)]
  · let n := 3 * t
    have hn : n = 3 * t := rfl
    refine ⟨(9, S) :: List.replicate n (9, S), hadm 9 n (by omega),
      havoid 9 n (by omega) (by omega) (Or.inl rfl), ?_⟩
    rw [horder]
    have hlin : 2 * (9 + 9 * n) = 9 * S := by omega
    have he : 9 * (p - 1) ^ 2 = ((9 + 9 * n) * S) * 8 := by
      rw [← hSp]
      nlinarith [congrArg (fun z : ℕ => z * S) hlin]
    simp only [bound, h, or_true, ite_true]
    rw [he, Nat.mul_div_cancel _ (by omega)]
  · let n := 3 * t + 1
    have hn : n = 3 * t + 1 := rfl
    refine ⟨(5, S) :: List.replicate n (9, S), hadm 5 n (by omega),
      havoid 5 n (by omega) (by omega) (Or.inr (by omega)), ?_⟩
    rw [horder]
    have hlin : 2 * (5 + 9 * n) = 9 * S + 1 := by omega
    have hdiff : 9 * p - 7 = 18 * S + 2 := by omega
    have he : (p - 1) * (9 * p - 7) = ((5 + 9 * n) * S) * 8 := by
      rw [← hSp, hdiff]
      nlinarith [congrArg (fun z : ℕ => z * S) hlin]
    simp only [bound, h, show ¬ (7 = 1 ∨ 7 = 5) by omega, ite_false, ite_true]
    rw [he, Nat.mul_div_cancel _ (by omega)]
  · let n := 3 * t + 2
    have hn : n = 3 * t + 2 := rfl
    refine ⟨(4, S) :: List.replicate n (9, S), hadm 4 n (by omega),
      havoid 4 n (by omega) (by omega) (Or.inr (by omega)), ?_⟩
    rw [horder]
    have hlin : 2 * (4 + 9 * n) + 1 = 9 * S := by omega
    have hdiff : 9 * p - 11 + 2 = 18 * S := by omega
    have he : (p - 1) * (9 * p - 11) = ((4 + 9 * n) * S) * 8 := by
      rw [← hSp]
      nlinarith [congrArg (fun z : ℕ => z * S) hlin,
        congrArg (fun z : ℕ => z * S) hdiff]
    simp only [bound, h, show ¬ (11 = 1 ∨ 11 = 5) by omega,
      show ¬ (11 = 7) by omega, ite_false]
    rw [he, Nat.mul_div_cancel _ (by omega)]

end D5.S3.Combinatorics.RegularInduced.DysonMcKay
