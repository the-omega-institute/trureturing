/- GID: D5/S3/Arith/SortedDivisorPolynomialThreePrimes
   generality: G
   mirror-B: D5/B/S3/Arith/SortedDivisorPolynomialThreePrimes
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.PrimesCongruentOne, mathlib/module/Mathlib.LinearAlgebra.Lagrange, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: OEIS A167857 has a term with exactly three distinct prime divisors. -/

import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.SortedDivisorPolynomialThreePrimes

open Polynomial Finset

private def denominator (i : Fin 8) : ℤ :=
  ∏ j ∈ (univ : Finset (Fin 8)).erase i, ((i.val : ℤ) - j.val)

private noncomputable def numerator (i : Fin 8) : Polynomial ℤ :=
  ∏ j ∈ (univ : Finset (Fin 8)).erase i, (X - C (j.val : ℤ))

private theorem denominator_facts (i : Fin 8) :
    denominator i ∣ 5040 ∧ denominator i ≠ 0 := by
  exact (by decide : ∀ i : Fin 8, denominator i ∣ 5040 ∧ denominator i ≠ 0) i

private theorem rational_basis (i : Fin 8) :
    Lagrange.basis univ (fun j : Fin 8 => (j.val : ℚ)) i =
      C ((denominator i : ℚ)⁻¹) *
        (numerator i).map (Int.castRingHom ℚ) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, numerator, denominator,
    Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib,
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Int.coe_castRingHom, Int.cast_prod, Int.cast_sub, Int.cast_natCast]

private theorem integral_interpolation_eight (y : Fin 8 → ℤ)
    (hy : ∀ i, (5040 : ℤ) ∣ y i - 1) :
    ∃ f : Polynomial ℤ, ∀ i : Fin 8, f.eval (i.val : ℤ) = y i := by
  let c : Fin 8 → ℤ := fun i => (y i - 1) / denominator i
  let f : Polynomial ℤ := 1 + ∑ i : Fin 8, C (c i) * numerator i
  have hc (i : Fin 8) : c i * denominator i = y i - 1 :=
    Int.ediv_mul_cancel ((denominator_facts i).1.trans (hy i))
  have hm : f.map (Int.castRingHom ℚ) =
      1 + Lagrange.interpolate univ (fun i : Fin 8 => (i.val : ℚ))
        (fun i => ((y i : ℚ) - 1)) := by
    simp only [f, Polynomial.map_add, Polynomial.map_one, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom,
      Lagrange.interpolate_apply, rational_basis]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hd : (denominator i : ℚ) ≠ 0 := by
      exact_mod_cast (denominator_facts i).2
    have hci : (c i : ℚ) = ((y i : ℚ) - 1) * (denominator i : ℚ)⁻¹ := by
      have h := congrArg (fun z : ℤ => (z : ℚ)) (hc i)
      push_cast at h
      apply (eq_mul_inv_iff_mul_eq₀ hd).mpr
      exact h
    rw [hci, C_mul, mul_assoc]
  refine ⟨f, fun i => ?_⟩
  have hnodes : Set.InjOn (fun i : Fin 8 => (i.val : ℚ)) (univ : Finset (Fin 8)) := by
    intro i _ j _ h
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact_mod_cast h
  have h := Lagrange.eval_interpolate_at_node
    (fun i : Fin 8 => ((y i : ℚ) - 1)) hnodes (mem_univ i)
  have hf : ((f.eval (i.val : ℤ) : ℤ) : ℚ) = (y i : ℚ) := by
    calc
      ((f.eval (i.val : ℤ) : ℤ) : ℚ) =
          (f.map (Int.castRingHom ℚ)).eval (i.val : ℚ) := by
        simpa only [Int.coe_castRingHom] using
          (Polynomial.eval_natCast_map (Int.castRingHom ℚ) f i.val).symm
      _ = (y i : ℚ) := by
        rw [hm, Polynomial.eval_add, Polynomial.eval_one, h]
        ring
  exact_mod_cast hf

private theorem divisor_congruence {p q r d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpm : p ≡ 1 [MOD 5040]) (hqm : q ≡ 1 [MOD 5040])
    (hrm : r ≡ 1 [MOD 5040]) (hd : d ∣ p * q * r) :
    d ≡ 1 [MOD 5040] := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨x, z, hx, hz, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ha
  have hm {s t : ℕ} (hs : s.Prime) (ht : t ∣ s)
      (hsm : s ≡ 1 [MOD 5040]) : t ≡ 1 [MOD 5040] := by
    rcases (Nat.dvd_prime hs).mp ht with rfl | rfl
    · rfl
    · exact hsm
  simpa using ((hm hp hx hpm).mul (hm hq hz hqm)).mul (hm hr hb hrm)

/-- The original OEIS A167857 existence question, with the full increasing divisor
list of the same positive integer and the original zero-based inputs. -/
theorem result :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = 3 ∧
      ∃ f : Polynomial ℤ, ∀ (j : ℕ) (hj : j < n.divisors.card),
        f.eval (j : ℤ) =
          ((n.divisors.sort (· ≤ ·)).get
            ⟨j, by simpa only [Finset.length_sort] using hj⟩ : ℤ) := by
  obtain ⟨p, hp, _, hpm⟩ := Nat.exists_prime_gt_modEq_one 1 (by decide : 5040 ≠ 0)
  obtain ⟨q, hq, hpq, hqm⟩ := Nat.exists_prime_gt_modEq_one p (by decide : 5040 ≠ 0)
  obtain ⟨r, hr, hqr, hrm⟩ := Nat.exists_prime_gt_modEq_one q (by decide : 5040 ≠ 0)
  have hpne : p ≠ q := Nat.ne_of_lt hpq
  have hqne : q ≠ r := Nat.ne_of_lt hqr
  have hprne : p ≠ r := Nat.ne_of_lt (hpq.trans hqr)
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpne
  have hcopr : (p * q).Coprime r :=
    ((Nat.coprime_primes hp hr).mpr hprne).mul_left
      ((Nat.coprime_primes hq hr).mpr hqne)
  let n := p * q * r
  have hn : 0 < n := Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hcard : n.divisors.card = 8 := by
    rw [Nat.Coprime.card_divisors_mul hcopr, Nat.Coprime.card_divisors_mul hcop,
      hp.divisors, hq.divisors, hr.divisors]
    simp [hp.ne_one.symm, hq.ne_one.symm, hr.ne_one.symm]
  have hpf : n.primeFactors.card = 3 := by
    dsimp [n]
    rw [Nat.primeFactors_mul (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero,
      Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors,
      hr.primeFactors]
    simp [hpne, hqne, hprne]
  let ds := n.divisors.sort (· ≤ ·)
  have hlen : ds.length = 8 := by simpa only [ds, Finset.length_sort] using hcard
  let y : Fin 8 → ℤ := fun i => (ds.get ⟨i.val, by omega⟩ : ℤ)
  have hy (i : Fin 8) : (5040 : ℤ) ∣ y i - 1 := by
    have hd : ds.get ⟨i.val, by omega⟩ ∈ n.divisors :=
      (Finset.mem_sort (· ≤ ·)).mp (List.get_mem ds _)
    have hmod := divisor_congruence hp hq hr hpm hqm hrm (Nat.mem_divisors.mp hd).1
    exact Nat.modEq_iff_dvd.mp hmod.symm
  obtain ⟨f, hf⟩ := integral_interpolation_eight y hy
  refine ⟨n, hn, hpf, f, fun j hj => ?_⟩
  have hj8 : j < 8 := by omega
  exact hf ⟨j, hj8⟩

#print axioms result

end D5.S3.Arith.SortedDivisorPolynomialThreePrimes
