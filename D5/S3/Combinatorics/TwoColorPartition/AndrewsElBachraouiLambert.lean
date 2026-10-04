/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiLambert
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiLambert
   mirror-E: none(waiver:odd-factor-coefficient-bijection)
   anchors: [mathlib/module/Mathlib.RingTheory.LaurentSeries,mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The shifted odd Lambert coefficient counts all proper nonunit odd divisors. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiLambert

open PowerSeries AndrewsElBachraouiDefs

/-- Factoring `2n+5` bijects the shifted Lambert summands with its nonendpoint divisors. -/
theorem lambert_divisor_coefficient (n : ℕ) :
    coeff n (∑ j ∈ Finset.range (n + 1),
      (X ^ (3 * j + 2) * geom (2 * j + 3) : PowerSeries ℤ)) + 2 =
        ((2 * n + 5).divisors.card : ℤ) := by
  classical
  let J := (Finset.range (n + 1)).filter fun j =>
    3 * j + 2 ≤ n ∧ 2 * j + 3 ∣ n - (3 * j + 2)
  let D := ((2 * n + 5).divisors.erase 1).erase (2 * n + 5)
  have hn : 2 * n + 5 ≠ 0 := by omega
  have hcoeff : coeff n (∑ j ∈ Finset.range (n + 1),
      (X ^ (3 * j + 2) * geom (2 * j + 3) : PowerSeries ℤ)) = (J.card : ℤ) := by
    rw [map_sum]
    simp only [coeff_X_pow_mul', geom, coeff_mk]
    calc
      _ = ∑ j ∈ Finset.range (n + 1),
          if 3 * j + 2 ≤ n ∧ 2 * j + 3 ∣ n - (3 * j + 2) then (1 : ℤ) else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp_all
      _ = (J.card : ℤ) := by simp [J, Finset.sum_boole]
  have hfactor (j : ℕ) (hj : j ∈ J) : ∃ t : ℕ,
      n = 3 * j + 2 + (2 * j + 3) * t := by
    obtain ⟨_, hle, hdvd⟩ := Finset.mem_filter.mp hj
    obtain ⟨t, ht⟩ := hdvd
    exact ⟨t, by omega⟩
  have hcard : J.card = D.card := by
    apply Finset.card_bij (fun j _ => 2 * j + 3)
    · intro j hj
      obtain ⟨t, ht⟩ := hfactor j hj
      have hp : (2 * j + 3) * (2 * t + 3) = 2 * n + 5 := by rw [ht]; ring
      have hdvd : 2 * j + 3 ∣ 2 * n + 5 := ⟨2 * t + 3, hp.symm⟩
      have hne : 2 * j + 3 ≠ 2 * n + 5 := by nlinarith
      simp only [D, Finset.mem_erase, Nat.mem_divisors]
      exact ⟨hne, by omega, hdvd, hn⟩
    · intro j hj l hl heq
      omega
    · intro d hd
      obtain ⟨hdM, hd1, hdvd, _⟩ := by
        simpa only [D, Finset.mem_erase, Nat.mem_divisors] using hd
      obtain ⟨r, hr⟩ := hdvd
      have hOdd : Odd (d * r) := by rw [← hr]; exact ⟨n + 2, by omega⟩
      obtain ⟨a, ha⟩ := (Nat.odd_mul.mp hOdd).1
      obtain ⟨b, hb⟩ := (Nat.odd_mul.mp hOdd).2
      have hdOdd : d % 2 = 1 := by omega
      have hrOdd : r % 2 = 1 := by omega
      have hd3 : 3 ≤ d := by omega
      have hr3 : 3 ≤ r := by
        have hrne : r ≠ 1 := by intro heq; simp [heq] at hr; omega
        omega
      let j := (d - 3) / 2
      let t := (r - 3) / 2
      have hdj : d = 2 * j + 3 := by dsimp [j]; omega
      have hrt : r = 2 * t + 3 := by dsimp [t]; omega
      have hnt : n = 3 * j + 2 + (2 * j + 3) * t := by
        rw [hdj, hrt] at hr
        nlinarith
      have hjn : j < n + 1 := by omega
      have hle : 3 * j + 2 ≤ n := by omega
      have hdiv : 2 * j + 3 ∣ n - (3 * j + 2) := by
        refine ⟨t, ?_⟩
        omega
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjn, hle, hdiv⟩, hdj.symm⟩
  have hMmem : 2 * n + 5 ∈ (2 * n + 5).divisors.erase 1 := by
    simp [Nat.mem_divisors]
  have h1mem : 1 ∈ (2 * n + 5).divisors := Nat.one_mem_divisors.mpr hn
  have hsize : D.card + 2 = (2 * n + 5).divisors.card := by
    have hfirst := Finset.card_erase_add_one h1mem
    have hsecond := Finset.card_erase_add_one hMmem
    dsimp [D]
    omega
  rw [hcoeff, hcard]
  exact_mod_cast hsize

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiLambert
