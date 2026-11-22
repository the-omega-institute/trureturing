/- GID: D5/S3/ArithSums/SpeziaA320043AllRowDivisorFormula
   generality: I
   mirror-B: D5/B/S3/ArithSums/SpeziaA320043AllRowDivisorFormula
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: For N ≥ 1, 12 a(N-1) = Σ_{m∣N} (m³φ(m) − m²E(m)) for the A320043 row sums a. -/

import D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-! The all-row divisor formula for the A320043 row sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.SpeziaA320043AllRowDivisorFormula

open Finset ArithmeticFunction D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation

/-- `E(m) = ∏_{q ∣ m prime} (1 - q)`, with `E(1) = 1`. -/
def E (m : ℕ) : ℤ := ∏ q ∈ m.primeFactors, (1 - (q : ℤ))

private theorem E_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) : E (p ^ k) = 1 - p := by
  rw [E, Nat.primeFactors_prime_pow (by omega) hp]; simp

private theorem E_one : E 1 = 1 := by simp [E]

private theorem pp_sum (p i : ℕ) (hp : p.Prime) :
    ∑ j ∈ range (i + 1), (p : ℤ) ^ j * E (p ^ (i - j)) = 1 := by
  rw [sum_range_succ, Nat.sub_self, pow_zero, E_one, mul_one]
  have h : ∀ j ∈ range i, (p : ℤ) ^ j * E (p ^ (i - j)) = -((p : ℤ) ^ j * ((p : ℤ) - 1)) := by
    intro j hj
    rw [E_prime_pow p (i - j) hp (by have := mem_range.mp hj; omega)]
    ring
  rw [sum_congr rfl h, sum_neg_distrib, ← sum_mul, geom_sum_mul]
  ring

private theorem E_conv (m : ℕ) (hm : 1 ≤ m) : ∑ d ∈ m.divisors, ((m / d : ℕ) : ℤ) * E d = 1 := by
  set ι : ArithmeticFunction ℤ := ↑(ArithmeticFunction.id : ArithmeticFunction ℕ) with hι
  set F : ArithmeticFunction ℤ :=
    ArithmeticFunction.prodPrimeFactors (fun p : ℕ => (1 - (p : ℤ))) with hF
  have hFapp : ∀ n, n ≠ 0 → F n = E n := fun n hn => by
    rw [hF, prodPrimeFactors_apply hn]; rfl
  have key :
      ι * F = (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ ((isMultiplicative_id.natCast).mul
      (IsMultiplicative.prodPrimeFactors _)) _ isMultiplicative_zeta.natCast]
    intro p i hp
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => ι a * F b), Nat.divisors_prime_pow hp,
      sum_map, natCoe_apply, zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
    push_cast
    rw [← pp_sum p i hp]
    apply sum_congr rfl
    intro j hj
    have hj' : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [Function.Embedding.coeFn_mk, hι, natCoe_apply, id_apply]
    rw [Nat.pow_div hj' hp.pos, hFapp _ (pow_ne_zero _ hp.ne_zero)]
    push_cast
    ring
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) key
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => ι a * F b), natCoe_apply,
    zeta_apply_ne (by omega)] at h
  push_cast at h
  rw [← h]
  apply sum_congr rfl
  intro d hd
  simp only [hι, natCoe_apply, id_apply]
  rw [hFapp d (Nat.pos_of_mem_divisors hd).ne']

/-- Grouping `1 ≤ k < N` by `g = gcd(k, N)`: `k = j · (N / m)` with `m = N / g ∣ N` and
`j = k / g` coprime to `m`, `1 ≤ j < m`. -/
private theorem group (N : ℕ) (hN : 1 ≤ N) (w : ℕ → ℕ → ℤ) :
    ∑ k ∈ Ico 1 N, w (N / Nat.gcd k N) (k / Nat.gcd k N) =
      ∑ m ∈ N.divisors, ∑ j ∈ (Ico 1 m).filter (fun j => Nat.Coprime j m), w m j := by
  rw [sum_sigma']
  refine sum_nbij' (fun k => ⟨N / Nat.gcd k N, k / Nat.gcd k N⟩)
    (fun x => x.2 * (N / x.1)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
    have hg : 0 < Nat.gcd k N := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgk : Nat.gcd k N ∣ k := Nat.gcd_dvd_left k N
    have hgN : Nat.gcd k N ∣ N := Nat.gcd_dvd_right k N
    simp only [mem_sigma, Nat.mem_divisors, mem_filter, mem_Ico]
    refine ⟨⟨Nat.div_dvd_of_dvd hgN, by omega⟩, ⟨?_, ?_⟩, Nat.coprime_div_gcd_div_gcd hg⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hgk) hg
    · exact Nat.div_lt_div_of_lt_of_dvd hgN hk2
  · intro x hx
    simp only [mem_sigma, Nat.mem_divisors, mem_filter, mem_Ico] at hx
    obtain ⟨⟨hdvd, -⟩, ⟨hj1, hj2⟩, -⟩ := hx
    obtain ⟨d, hd⟩ := hdvd
    have hm : 0 < x.1 := by omega
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · simp [h] at hd; omega
      · exact h
    simp only [mem_Ico]
    rw [hd, Nat.mul_div_cancel_left _ hm]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact Nat.mul_lt_mul_of_pos_right hj2 hd0
  · intro k hk
    obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
    have hgN : Nat.gcd k N ∣ N := Nat.gcd_dvd_right k N
    simp only
    rw [Nat.div_div_self hgN (by omega), Nat.div_mul_cancel (Nat.gcd_dvd_left k N)]
  · intro x hx
    simp only [mem_sigma, Nat.mem_divisors, mem_filter, mem_Ico] at hx
    obtain ⟨⟨hdvd, -⟩, ⟨hj1, hj2⟩, hcop⟩ := hx
    obtain ⟨d, hd⟩ := hdvd
    have hm : 0 < x.1 := by omega
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · simp [h] at hd; omega
      · exact h
    have hq : N / x.1 = d := by rw [hd, Nat.mul_div_cancel_left _ hm]
    have hg : Nat.gcd (x.2 * d) N = d := by
      rw [hd, mul_comm x.1 d, mul_comm x.2 d, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    simp only [hq, hg]
    have h1 : N / d = x.1 := by rw [hd, Nat.mul_div_cancel _ hd0]
    have h2 : x.2 * d / d = x.2 := Nat.mul_div_cancel _ hd0
    rw [h1, h2]
  · intro k hk
    rfl

/-- The coprime-weighted sums `S(m) = ∑_{1 ≤ j < m, (j, m) = 1} (m - j)^2 j`. -/
private def S (m : ℕ) : ℤ :=
  ∑ j ∈ (Ico 1 m).filter (fun j => Nat.Coprime j m), (((m - j) ^ 2 * j : ℕ) : ℤ)

private theorem term (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    Nat.gcd (N - k) k = Nat.gcd k N ∧
      (N - k) ^ 2 * k = Nat.gcd k N ^ 3 *
        ((N / Nat.gcd k N - k / Nat.gcd k N) ^ 2 * (k / Nat.gcd k N)) := by
  set g := Nat.gcd k N with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hN
  obtain ⟨j, hj⟩ := Nat.gcd_dvd_left k N
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right k N
  rw [← hg] at hj hm
  refine ⟨by rw [Nat.gcd_sub_self_left hk, Nat.gcd_comm], ?_⟩
  have h1 : k / g = j := by rw [hj, Nat.mul_div_cancel_left _ hg0]
  have h2 : N / g = m := by rw [hm, Nat.mul_div_cancel_left _ hg0]
  rw [h1, h2]
  have h3 : N - k = g * (m - j) := by rw [hm, hj, Nat.mul_sub]
  rw [h3, hj]
  ring

private theorem a_eq (N : ℕ) (hN : 1 ≤ N) : (a (N - 1) : ℤ) = ∑ m ∈ N.divisors, S m := by
  unfold S
  rw [← group N hN (fun m j => (((m - j) ^ 2 * j : ℕ) : ℤ))]
  unfold a
  have hI : Icc 1 (N - 1) = Ico 1 N := by
    rw [← Finset.Ico_add_one_right_eq_Icc, show N - 1 + 1 = N by omega]
  rw [show N - 1 + 1 = N by omega, hI, Nat.cast_sum]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_Ico.mp hk
  obtain ⟨hgcd, hprod⟩ := term N k (by omega) hk'.2.le
  rw [hgcd, hprod, Nat.mul_div_cancel_left _ (pow_pos (Nat.gcd_pos_of_pos_right _ (by omega)) 3)]

private theorem T_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Ico 1 N, (((N - k) ^ 2 * k : ℕ) : ℤ) = ∑ m ∈ N.divisors, ((N / m : ℕ) : ℤ) ^ 3 * S m := by
  unfold S
  simp_rw [mul_sum]
  rw [← group N hN (fun m j => ((N / m : ℕ) : ℤ) ^ 3 * (((m - j) ^ 2 * j : ℕ) : ℤ))]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_Ico.mp hk
  obtain ⟨-, hprod⟩ := term N k (by omega) hk'.2.le
  rw [hprod, Nat.div_div_self (Nat.gcd_dvd_right k N) (by omega)]
  push_cast
  ring

private theorem T_closed (N : ℕ) (hN : 1 ≤ N) :
    12 * ∑ k ∈ Ico 1 N, (((N - k) ^ 2 * k : ℕ) : ℤ) = (N : ℤ) ^ 4 - (N : ℤ) ^ 2 := by
  let F : ℕ → ℤ := fun k =>
    6 * (N : ℤ) ^ 2 * k * (k - 1) - 4 * N * k * (k - 1) * (2 * k - 1) + 3 * k ^ 2 * (k - 1) ^ 2
  have hstep : ∀ k ∈ Ico 1 N, 12 * (((N - k) ^ 2 * k : ℕ) : ℤ) = F (k + 1) - F k := by
    intro k hk
    have hk' := (mem_Ico.mp hk).2.le
    simp only [F, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk', Nat.cast_add, Nat.cast_one]
    ring
  rw [mul_sum, sum_congr rfl hstep, sum_Ico_eq_sum_range]
  simp_rw [show ∀ k, 1 + k + 1 = 1 + (k + 1) from fun k => by ring]
  rw [sum_range_sub (fun i => F (1 + i))]
  simp only [F, show 1 + (N - 1) = N by omega]
  push_cast
  ring

private theorem relB (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ m.divisors, ((m / d : ℕ) : ℤ) ^ 3 * ((d : ℤ) ^ 3 * (Nat.totient d) - (d : ℤ) ^ 2 * E d) =
      (m : ℤ) ^ 4 - (m : ℤ) ^ 2 := by
  have hterm : ∀ d ∈ m.divisors, ((m / d : ℕ) : ℤ) ^ 3 * ((d : ℤ) ^ 3 * (Nat.totient d) -
      (d : ℤ) ^ 2 * E d) = (m : ℤ) ^ 3 * (Nat.totient d) - (m : ℤ) ^ 2 *
      (((m / d : ℕ) : ℤ) * E d) := by
    intro d hd
    have hmd : ((m / d : ℕ) : ℤ) * d = m := by
      exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    rw [← hmd]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, ← mul_sum, E_conv m hm]
  have ht : ∑ d ∈ m.divisors, ((Nat.totient d : ℕ) : ℤ) = m := by
    exact_mod_cast Nat.sum_totient m
  rw [ht]
  ring

private theorem relA (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ m.divisors, ((m / d : ℕ) : ℤ) ^ 3 * (12 * S d) = (m : ℤ) ^ 4 - (m : ℤ) ^ 2 := by
  rw [← T_closed m hm, T_eq m hm, mul_sum]
  apply sum_congr rfl
  intro d _
  ring

private theorem S_closed (m : ℕ) (hm : 1 ≤ m) :
    12 * S m = (m : ℤ) ^ 3 * (Nat.totient m) - (m : ℤ) ^ 2 * E m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hA := relA m hm
    have hB := relB m hm
    have hmem := Nat.mem_divisors_self m (by omega)
    rw [← add_sum_erase _ _ hmem] at hA hB
    have hrest : ∑ d ∈ m.divisors.erase m, ((m / d : ℕ) : ℤ) ^ 3 * (12 * S d) =
        ∑ d ∈ m.divisors.erase m, ((m / d : ℕ) : ℤ) ^ 3 *
          ((d : ℤ) ^ 3 * (Nat.totient d) - (d : ℤ) ^ 2 * E d) := by
      apply sum_congr rfl
      intro d hd
      obtain ⟨hne, hdm⟩ := mem_erase.mp hd
      have hdvd := Nat.dvd_of_mem_divisors hdm
      have hd0 : 1 ≤ d := Nat.pos_of_mem_divisors hdm
      have hlt : d < m := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hne
      rw [ih d hlt hd0]
    rw [Nat.div_self (by omega)] at hA hB
    simp only [Nat.cast_one, one_pow, one_mul] at hA hB
    linarith

/-- Corollary 7: each quotient in `a(n)` is exact, and for every `N ≥ 1` (the source states
`N ≥ 2`; at `N = 1` both sides vanish),
`12 a(N - 1) = ∑_{m ∣ N} (m^3 φ(m) - m^2 E(m))`. -/
theorem result :
    (∀ n k : ℕ, Nat.gcd (n + 1 - k) k ^ 3 ∣ (n + 1 - k) ^ 2 * k) ∧
    ∀ N : ℕ, 1 ≤ N → 12 * (a (N - 1) : ℤ) =
      ∑ m ∈ N.divisors, ((m : ℤ) ^ 3 * (Nat.totient m) - (m : ℤ) ^ 2 * E m) := by
  refine ⟨fun n k => ?_, fun N hN => ?_⟩
  · rw [pow_succ]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left _ _) 2) (Nat.gcd_dvd_right _ _)
  · rw [a_eq N hN, mul_sum]
    apply sum_congr rfl
    intro m hm
    exact S_closed m (Nat.pos_of_mem_divisors hm)

end D5.S3.ArithSums.SpeziaA320043AllRowDivisorFormula
