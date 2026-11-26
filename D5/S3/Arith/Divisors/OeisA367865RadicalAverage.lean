/- GID: D5/S3/Arith/Divisors/OeisA367865RadicalAverage
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/OeisA367865RadicalAverage
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact rational radical-average identity for OEIS A367865. -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.FieldSimp

/-!
# OEIS A367865 radical-average identity

The escape audit remains unfinished. See https://github.com/the-omega-institute/trureturing/issues/34659.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction
open UniqueFactorizationMonoid

namespace D5.S3.Arith.Divisors.OeisA367865RadicalAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem radical_mul_gcd (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    UniqueFactorizationMonoid.radical (n * k) * Nat.gcd (UniqueFactorizationMonoid.radical n) k =
      UniqueFactorizationMonoid.radical n * UniqueFactorizationMonoid.radical k := by
  have hprod := Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul
    (UniqueFactorizationMonoid.radical n) k (fun p : ℕ => p)
  rw [← Nat.radical_eq_prod_primeFactors, ← Nat.radical_eq_prod_primeFactors,
    ← Nat.radical_eq_prod_primeFactors, ← Nat.radical_eq_prod_primeFactors] at hprod
  rw [UniqueFactorizationMonoid.radical_radical] at hprod
  have hsq : Squarefree (Nat.gcd (UniqueFactorizationMonoid.radical n) k) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
      (UniqueFactorizationMonoid.squarefree_radical)
  have hradg : UniqueFactorizationMonoid.radical
      (Nat.gcd (UniqueFactorizationMonoid.radical n) k) =
      Nat.gcd (UniqueFactorizationMonoid.radical n) k := by
    rw [Nat.radical_eq_prod_primeFactors]
    exact Nat.prod_primeFactors_of_squarefree hsq
  have hradmul : UniqueFactorizationMonoid.radical
      (UniqueFactorizationMonoid.radical n * k) =
      UniqueFactorizationMonoid.radical (n * k) := by
    apply UniqueFactorizationMonoid.radical_eq_iff_primeFactors_eq.mpr
    rw [UniqueFactorizationMonoid.primeFactors_mul_eq_union (by positivity) (by positivity),
      UniqueFactorizationMonoid.primeFactors_mul_eq_union (by positivity) (by positivity)]
    simp [UniqueFactorizationMonoid.primeFactors_radical]
  rw [hradg, hradmul] at hprod
  simpa [mul_comm, mul_left_comm, mul_assoc] using hprod

private theorem radical_quotient (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ((UniqueFactorizationMonoid.radical (n * k) : ℕ) : ℚ) /
        ((UniqueFactorizationMonoid.radical k : ℕ) : ℚ) =
      ((UniqueFactorizationMonoid.radical n /
        Nat.gcd (UniqueFactorizationMonoid.radical n) k : ℕ) : ℚ) := by
  have hg : Nat.gcd (UniqueFactorizationMonoid.radical n) k ∣
      UniqueFactorizationMonoid.radical n := Nat.gcd_dvd_left _ _
  have hradk : ((UniqueFactorizationMonoid.radical k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.radical_pos k))
  have hcastdiv :
      ((UniqueFactorizationMonoid.radical n /
        Nat.gcd (UniqueFactorizationMonoid.radical n) k : ℕ) : ℚ) =
        ((UniqueFactorizationMonoid.radical n : ℕ) : ℚ) /
          (Nat.gcd (UniqueFactorizationMonoid.radical n) k : ℚ) := by
    rw [Nat.cast_div hg]
    exact_mod_cast (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left k (Nat.radical_pos n)))
  rw [hcastdiv]
  field_simp [hradk]
  have hcast :
      ((UniqueFactorizationMonoid.radical (n * k) : ℕ) : ℚ) *
          (Nat.gcd (UniqueFactorizationMonoid.radical n) k : ℚ) =
        ((UniqueFactorizationMonoid.radical n : ℕ) : ℚ) *
          ((UniqueFactorizationMonoid.radical k : ℕ) : ℚ) := by
    exact_mod_cast (radical_mul_gcd n k hn hk)
  simpa [mul_comm] using hcast

private theorem gcd_sum (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range m,
      ((m / Nat.gcd m k : ℕ) : ℚ)) =
      ∑ d ∈ m.divisors, (d : ℚ) * (Nat.totient d : ℚ) := by
  have hMaps : ∀ k ∈ Finset.range m, Nat.gcd m k ∈ m.divisors := by
    intro k hk
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hm.ne'⟩
  calc
    (∑ k ∈ Finset.range m, ((m / Nat.gcd m k : ℕ) : ℚ)) =
        ∑ d ∈ m.divisors,
          ∑ k ∈ Finset.range m with Nat.gcd m k = d,
            ((m / d : ℕ) : ℚ) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to' hMaps (fun d => ((m / d : ℕ) : ℚ))
    _ = ∑ d ∈ m.divisors,
        ((Nat.totient (m / d) : ℕ) : ℚ) * ((m / d : ℕ) : ℚ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_const, nsmul_eq_mul,
        ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
    _ = ∑ d ∈ m.divisors, (d : ℚ) * (Nat.totient d : ℚ) := by
      rw [← Nat.sum_div_divisors m (fun d => (d : ℚ) * (Nat.totient d : ℚ))]
      apply Finset.sum_congr rfl
      intro d hd
      ring

private theorem radical_sum (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n,
      ((UniqueFactorizationMonoid.radical (n * k) : ℕ) : ℚ) /
        ((UniqueFactorizationMonoid.radical k : ℕ) : ℚ) =
      ((n : ℚ) / ((UniqueFactorizationMonoid.radical n : ℕ) : ℚ)) *
        ∑ d ∈ (UniqueFactorizationMonoid.radical n).divisors,
          (d : ℚ) * (Nat.totient d : ℚ) := by
  let m := UniqueFactorizationMonoid.radical n
  have hm : 0 < m := Nat.radical_pos n
  have hmn : m ∣ n := UniqueFactorizationMonoid.radical_dvd_self
  let q := n / m
  have hqm : q * m = n := Nat.div_mul_cancel hmn
  let f : ℕ → ℚ := fun k => ((m / Nat.gcd m k : ℕ) : ℚ)
  have hper : Function.Periodic f m := by
    exact (Nat.periodic_gcd m).comp (fun e => ((m / e : ℕ) : ℚ))
  have hzero : f 0 = f n := by
    rw [← hqm]
    exact (hper.nat_mul_eq q).symm
  have hsum :
      (∑ k ∈ Finset.range n, f k) =
        (n : ℚ) / m * ∑ k ∈ Finset.range m, f k := by
    calc
      (∑ k ∈ Finset.range n, f k) = ∑ k : Fin (q * m), f k := by
        rw [Fin.sum_univ_eq_sum_range, hqm]
      _ = ∑ ij : Fin q × Fin m, f ij.2 := by
        symm
        refine Fintype.sum_equiv finProdFinEquiv _ _ (fun ij => ?_)
        change f (ij.2 : ℕ) = f ((ij.2 : ℕ) + m * (ij.1 : ℕ))
        rw [Nat.mul_comm m]
        exact (hper.nat_mul (ij.1 : ℕ) ij.2).symm
      _ = (q : ℚ) * ∑ k ∈ Finset.range m, f k := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Fin.sum_univ_eq_sum_range]
      _ = (n : ℚ) / (m : ℚ) * ∑ k ∈ Finset.range m, f k := by
        rw [show (q : ℚ) = (n : ℚ) / (m : ℚ) from
          Nat.cast_div hmn (by exact_mod_cast hm.ne')]
  calc
    (∑ k ∈ Finset.Icc 1 n,
        ((UniqueFactorizationMonoid.radical (n * k) : ℕ) : ℚ) /
          ((UniqueFactorizationMonoid.radical k : ℕ) : ℚ)) =
        ∑ k ∈ Finset.Icc 1 n, f k := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [f, m]
          exact radical_quotient n k hn (Finset.mem_Icc.mp hk).1
    _ = ∑ k ∈ Finset.range n, f k := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hn,
        Finset.sum_range_eq_add_Ico f hn, hzero]
      exact add_comm _ _
    _ = (n : ℚ) / (m : ℚ) * ∑ k ∈ Finset.range m, f k := hsum
    _ = (n : ℚ) / (m : ℚ) *
        ∑ d ∈ m.divisors, (d : ℚ) * (Nat.totient d : ℚ) := by
          rw [gcd_sum m hm]


private theorem divisor_mobius_sq (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors,
      (d : ℚ) * (Nat.totient d : ℚ) *
        ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2) =
      ∑ d ∈ (UniqueFactorizationMonoid.radical n).divisors,
        (d : ℚ) * (Nat.totient d : ℚ) := by
  let m := UniqueFactorizationMonoid.radical n
  have hm : 0 < m := Nat.radical_pos n
  have hmn : m ∣ n := UniqueFactorizationMonoid.radical_dvd_self
  have hsub : m.divisors ⊆ n.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.mem_divisors.mp hd).1 hmn, hn.ne'⟩
  have hsqm : Squarefree m := UniqueFactorizationMonoid.squarefree_radical
  calc
    (∑ d ∈ n.divisors,
        (d : ℚ) * (Nat.totient d : ℚ) *
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2) =
        ∑ d ∈ m.divisors,
          (d : ℚ) * (Nat.totient d : ℚ) *
            ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2 := by
      symm
      apply Finset.sum_subset hsub
      intro d hd hnot
      have hsd : ¬ Squarefree d := by
        intro hsd
        have hdm : d ∣ m := by
          have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
          have hrd : UniqueFactorizationMonoid.radical d = d := by
            rw [Nat.radical_eq_prod_primeFactors]
            exact Nat.prod_primeFactors_of_squarefree hsd
          rw [← hrd]
          exact UniqueFactorizationMonoid.radical_dvd_radical hdn hn.ne'
        exact hnot (Nat.mem_divisors.mpr ⟨hdm, hm.ne'⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsd]
      norm_num
    _ = ∑ d ∈ m.divisors, (d : ℚ) * (Nat.totient d : ℚ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hsd := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1 hsqm
      have hsq : (((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2) = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsd
      rw [hsq, mul_one]

/-- OEIS A367865, including the case `n = 1`. -/
theorem result (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors,
      (d : ℚ) * (Nat.totient d : ℚ) *
        ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2) =
      ((UniqueFactorizationMonoid.radical n : ℕ) : ℚ) / (n : ℚ) *
        ∑ k ∈ Finset.Icc 1 n,
          ((UniqueFactorizationMonoid.radical (n * k) : ℕ) : ℚ) /
            ((UniqueFactorizationMonoid.radical k : ℕ) : ℚ) := by
  rw [divisor_mobius_sq n hn, radical_sum n hn]
  let m := UniqueFactorizationMonoid.radical n
  have hm : 0 < m := Nat.radical_pos n
  field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn.ne', show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne']

end D5.S3.Arith.Divisors.OeisA367865RadicalAverage
