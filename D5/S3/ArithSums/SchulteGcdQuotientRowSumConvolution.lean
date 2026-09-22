/- GID: D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution
   generality: G
   mirror-B: D5/B/S3/ArithSums/SchulteGcdQuotientRowSumConvolution
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Schulte's A350900 row sum is a convolution of n phi(n) and divisor phi sums. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace D5.S3.ArithSums.SchulteGcdQuotientRowSumConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Row sum of A350900: sum over i and k from 1 to n of
    gcd(i,n)/gcd(gcd(i,k),n), with every summand an exact quotient. -/
def rowSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
    Nat.gcd i n / Nat.gcd (Nat.gcd i k) n

/-- Schulte's row-sum identity: the Dirichlet convolution of n times phi(n)
    with the sum over divisors d of d times phi(d). -/
theorem result (n : ℕ) (hn : 0 < n) :
    rowSum n =
      ∑ d ∈ n.divisors, d * Nat.totient d *
        (∑ e ∈ (n / d).divisors, e * Nat.totient e) := by
  let sigmaPhi : ℕ → ℕ := fun m =>
    ∑ e ∈ m.divisors, e * Nat.totient e
  change rowSum n = ∑ d ∈ n.divisors, d * Nat.totient d * sigmaPhi (n / d)
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have inner_count (g : ℕ) (hgdiv : g ∣ n) (hg : 0 < g) :
      ∑ k ∈ Finset.range n, g / Nat.gcd g k =
        (n / g) * ∑ e ∈ g.divisors, e * Nat.totient e := by
    have sum_range_mul_of_periodic (f : ℕ → ℕ) (g q : ℕ)
        (hf : Function.Periodic f g) :
        ∑ k ∈ Finset.range (q * g), f k =
          q * ∑ k ∈ Finset.range g, f k := by
      induction q with
      | zero => simp
      | succ q ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, ih]
          have hblock : ∀ k, f (q * g + k) = f k := by
            intro k
            simpa [Nat.add_comm] using hf.nat_mul q k
          simp_rw [hblock, Nat.add_mul, Nat.one_mul]
    have one_period :
        ∑ k ∈ Finset.range g, g / Nat.gcd g k =
          ∑ e ∈ g.divisors, e * Nat.totient e := by
      have hMaps : ∀ k ∈ Finset.range g, Nat.gcd g k ∈ g.divisors := by
        intro k hk
        exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left g k, hg.ne'⟩
      calc
        (∑ k ∈ Finset.range g, g / Nat.gcd g k) =
            ∑ e ∈ g.divisors,
              ∑ k ∈ Finset.range g with Nat.gcd g k = e, g / e := by
                symm
                exact Finset.sum_fiberwise_of_maps_to' hMaps (fun e => g / e)
        _ = ∑ e ∈ g.divisors, Nat.totient (g / e) * (g / e) := by
              apply Finset.sum_congr rfl
              intro e he
              rw [Finset.sum_const, nsmul_eq_mul,
                ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors he)]
              simp only [Nat.cast_id]
        _ = ∑ e ∈ g.divisors, e * Nat.totient e := by
              rw [← Nat.sum_div_divisors g (fun e => e * Nat.totient e)]
              apply Finset.sum_congr rfl
              intro e he
              ac_rfl
    have hperiod : Function.Periodic (fun k => g / Nat.gcd g k) g := by
      exact (Nat.periodic_gcd g).comp (fun e => g / e)
    calc
      (∑ k ∈ Finset.range n, g / Nat.gcd g k) =
          ∑ k ∈ Finset.range ((n / g) * g), g / Nat.gcd g k := by
            rw [Nat.div_mul_cancel hgdiv]
      _ = (n / g) * ∑ k ∈ Finset.range g, g / Nat.gcd g k :=
            sum_range_mul_of_periodic (fun k => g / Nat.gcd g k) g (n / g) hperiod
      _ = (n / g) * ∑ e ∈ g.divisors, e * Nat.totient e := by rw [one_period]
  have sum_Icc_eq_sum_range (f : ℕ → ℕ) (hfn : f 0 = f n) :
      ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f k := by
    have hshift :
        ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
      rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by ext k; simp,
        Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]
    rw [hshift]
    have hfull :
        (∑ k ∈ Finset.range n, f (k + 1)) + f 0 =
          (∑ k ∈ Finset.range n, f k) + f n :=
      (Finset.sum_range_succ' f n).symm.trans (Finset.sum_range_succ f n)
    omega
  have rowSum_range :
      rowSum n = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
        Nat.gcd i n / Nat.gcd (Nat.gcd i k) n := by
    unfold rowSum
    calc
      (∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
          Nat.gcd i n / Nat.gcd (Nat.gcd i k) n) =
          ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range n,
            Nat.gcd i n / Nat.gcd (Nat.gcd i k) n := by
              apply Finset.sum_congr rfl
              intro i hi
              apply sum_Icc_eq_sum_range
              simp
      _ = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
            Nat.gcd i n / Nat.gcd (Nat.gcd i k) n := by
              apply sum_Icc_eq_sum_range
              apply Finset.sum_congr rfl
              intro k hk
              simp [Nat.gcd_comm]
  have hMaps : ∀ i ∈ Finset.range n, Nat.gcd n i ∈ n.divisors := by
    intro i hi
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n i, hn0⟩
  calc
    rowSum n = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
        Nat.gcd n i / Nat.gcd (Nat.gcd n i) k := by
          rw [rowSum_range]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          simp [Nat.gcd_comm, Nat.gcd_left_comm]
    _ = ∑ i ∈ Finset.range n,
        (n / Nat.gcd n i) * sigmaPhi (Nat.gcd n i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact inner_count (Nat.gcd n i) (Nat.gcd_dvd_left n i)
            (Nat.gcd_pos_of_pos_left i hn)
    _ = ∑ g ∈ n.divisors, ∑ i ∈ Finset.range n with Nat.gcd n i = g,
        (n / g) * sigmaPhi g := by
          symm
          exact Finset.sum_fiberwise_of_maps_to' hMaps
            (fun g => (n / g) * sigmaPhi g)
    _ = ∑ g ∈ n.divisors,
        Nat.totient (n / g) * ((n / g) * sigmaPhi g) := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [Finset.sum_const, nsmul_eq_mul,
            ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hg)]
          simp only [Nat.cast_id]
    _ = ∑ d ∈ n.divisors, d * Nat.totient d * sigmaPhi (n / d) := by
          rw [← Nat.sum_div_divisors n
            (fun d => d * Nat.totient d * sigmaPhi (n / d))]
          apply Finset.sum_congr rfl
          intro g hg
          rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hg) hn0]
          ac_rfl

end D5.S3.ArithSums.SchulteGcdQuotientRowSumConvolution
