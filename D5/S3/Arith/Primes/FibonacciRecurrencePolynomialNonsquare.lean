/- GID: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialNonsquare
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRecurrencePolynomialNonsquare
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A dyadic analytic obstruction rules out all higher odd prime-power Fibonacci squares. -/

import D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialRoots
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialOddBridge
import D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Polynomial Finset PowerSeries
open scoped BigOperators PowerSeries Polynomial
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialRoots

open D5.S1.Scale
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialOddBridge
open D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold

open D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction

namespace D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare

set_option maxHeartbeats 4000000 in
/-- Large positive evaluations of the odd recurrence polynomial are nonsquares.
The odd-index Fibonacci quotients and higher prime-power layers inherit this
obstruction with their full positivity and index bounds. -/
theorem fibonacci_recurrence_polynomial_nonsquare : (∀ (r : ℕ), 119 ≤ r → ∀ (x : ℤ), 2 < x → 128 * (6 : ℤ)^r < x^2 - 4 →
      ¬ IsSquare ((fibonacciRecurrencePolynomial (2*r+1)).eval x)) ∧
    (∀ (r n : ℕ), 119 ≤ r → Odd n → 2*r+1 ≤ n → 0 < Nat.fib ((2*r+1)*n) / Nat.fib n ∧ ¬ IsSquare (Nat.fib ((2*r+1)*n) / Nat.fib n)) ∧
    (∀ (q k : ℕ), q.Prime → 239 ≤ q → 1 ≤ k → 0 < Nat.fib (q^(k+1)) / Nat.fib (q^k) ∧ ¬ IsSquare (Nat.fib (q^(k+1)) / Nat.fib (q^k))) := by
  have main (r : ℕ) (hr : 119 ≤ r) (x : ℤ) (hx : 2 < x)
      (hsize : 128 * (6 : ℤ)^r < x^2 - 4) :
      ¬ IsSquare ((fibonacciRecurrencePolynomial (2*r+1)).eval x) := by
    classical
    let formalA (lam : Fin r → ℝ) : ℂ⟦X⟧ := ∏ i : Fin r, (1 + PowerSeries.C (lam i : ℂ) * PowerSeries.X)
    let formalS (lam : Fin r → ℝ) : ℂ⟦X⟧ := (PowerSeries.binomialSeries ℂ (1/2 : ℂ)).subst (formalA lam - 1)
    have rootPair (r : ℕ) : ∃ lam : Fin r → ℝ, (∀ i, 0 ≤ lam i ∧ lam i < 4) ∧ (Polynomial.map (algebraMap ℤ ℂ)
              (fibonacciRecurrencePolynomial (2 * r + 1)) =
            ∏ i : Fin r, (Polynomial.X ^ 2 + Polynomial.C ((lam i : ℝ) : ℂ))) ∧
          (∀ z : ℂ, z ≠ 0 → (Polynomial.map (algebraMap ℤ ℂ) (fibonacciRecurrencePolynomial (2 * r + 1))).eval z =
              z ^ (2 * r) * ∏ i : Fin r, (1 + (lam i : ℂ) * (z⁻¹) ^ 2)) := by
      let q : ℕ := 2 * r + 1
      let theta (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)
      let c (k : ℕ) : ℂ := (Real.cos (theta k) : ℂ)
      let lamNat (k : ℕ) : ℝ := 4 * Real.cos (theta k) ^ 2
      let lam (i : Fin r) : ℝ := lamNat i.val
      let p : ℂ[X] := Polynomial.map (algebraMap ℤ ℂ)
        (fibonacciRecurrencePolynomial q)
      let rootFactor (k : ℕ) : ℂ[X] := Polynomial.X - Polynomial.C ((-2 * Complex.I) * c k)

      have hdegZ : (fibonacciRecurrencePolynomial q).natDegree = 2 * r := by
        simpa only [q] using
          (fibonacci_recurrence_polynomial_coefficients.1 (2 * r)).1
      have hleadZ : (fibonacciRecurrencePolynomial q).coeff (2 * r) = 1 := by
        simpa only [q] using
          (fibonacci_recurrence_polynomial_coefficients.1 (2 * r)).2
      have hmonicZ : (fibonacciRecurrencePolynomial q).Monic := monic_of_natDegree_le_of_coeff_eq_one (2 * r) hdegZ.le hleadZ
      have hmonic : p.Monic := hmonicZ.map (algebraMap ℤ ℂ)
      have hroots : p.roots = (Multiset.range (2 * r)).map (fun k : ℕ => (-2 * Complex.I) * c k) := by
        simpa only [p, q, c, theta, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using odd_recurrence_polynomial_root_multiset r
      have hcard : p.roots.card = p.natDegree := by
        rw [hroots, Multiset.card_map, Multiset.card_range]
        change 2 * r = (Polynomial.map (algebraMap ℤ ℂ) (fibonacciRecurrencePolynomial q)).natDegree
        rw [hmonicZ.natDegree_map, hdegZ]

      have hrootProd : p = ∏ k ∈ Finset.range (2 * r), rootFactor k := by
        have hp := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
          hmonic hcard
        calc
          p = (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod := hp.symm
          _ = ((Multiset.range (2 * r)).map rootFactor).prod := by
            rw [hroots]
            simp only [Multiset.map_map, Function.comp_apply]
            rfl
          _ = ∏ k ∈ Finset.range (2 * r), rootFactor k := rfl

      -- The second half, reversed, has index 2*r-1-i and angle pi-theta i.
      have hmirror (i : ℕ) (hi : i < r) : c (r + (r - 1 - i)) = -c i := by
        have hindex : r + (r - 1 - i) + 1 + (i + 1) = q := by
          dsimp [q]
          omega
        have hindexR : (((r + (r - 1 - i) + 1 : ℕ) : ℝ) + ((i + 1 : ℕ) : ℝ)) = (q : ℝ) := by
          exact_mod_cast hindex
        have hq : (q : ℝ) ≠ 0 := by
          have hqNat : q ≠ 0 := by dsimp [q]; omega
          exact_mod_cast hqNat
        have htheta : theta (r + (r - 1 - i)) = Real.pi - theta i := by
          dsimp [theta]
          field_simp [hq]
          nlinarith [congrArg (fun y : ℝ => y * Real.pi) hindexR]
        dsimp [c]
        rw [htheta, Real.cos_pi_sub]
        push_cast <;> rfl

      have hpair (i : ℕ) (hi : i < r) : rootFactor i * rootFactor (r + (r - 1 - i)) =
            Polynomial.X ^ 2 + Polynomial.C ((lamNat i : ℝ) : ℂ) := by
        have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
        dsimp [rootFactor]
        rw [hmirror i hi]
        have hquad (a : ℂ) :
            (Polynomial.X + Polynomial.C a) * (Polynomial.X - Polynomial.C a) = (Polynomial.X : ℂ[X]) ^ 2 - Polynomial.C (a ^ 2) := by
          rw [map_pow]
          ring
        have hsquare : (2 * Complex.I * c i) ^ 2 = -((lamNat i : ℝ) : ℂ) := by
          calc
            (2 * Complex.I * c i) ^ 2 = 4 * (Complex.I * Complex.I) * (c i) ^ 2 := by ring
            _ = -(4 * (c i) ^ 2) := by rw [hI]; ring
            _ = -((lamNat i : ℝ) : ℂ) := by simp [c, lamNat] <;> ring
        calc
          (Polynomial.X - Polynomial.C ((-2 * Complex.I) * c i)) * (Polynomial.X - Polynomial.C ((-2 * Complex.I) * (-c i))) =
            (Polynomial.X + Polynomial.C (2 * Complex.I * c i)) * (Polynomial.X - Polynomial.C (2 * Complex.I * c i)) := by
              have hneg : (-2 * Complex.I) * c i = -(2 * Complex.I * c i) := by ring
              have hpos : (-2 * Complex.I) * (-c i) = 2 * Complex.I * c i := by ring
              rw [hneg, hpos, map_neg]
              ring
          _ = Polynomial.X ^ 2 - Polynomial.C ((2 * Complex.I * c i) ^ 2) := hquad _
          _ = Polynomial.X ^ 2 + Polynomial.C ((lamNat i : ℝ) : ℂ) := by rw [hsquare, map_neg]; ring

      have hprodRange : p = ∏ i ∈ Finset.range r, (Polynomial.X ^ 2 + Polynomial.C ((lamNat i : ℝ) : ℂ)) := by
        calc
          p = ∏ k ∈ Finset.range (2 * r), rootFactor k := hrootProd
          _ = ∏ i ∈ Finset.range r, rootFactor i * rootFactor (r + (r - 1 - i)) := by
            rw [show 2 * r = r + r by omega, Finset.prod_range_add]
            rw [← Finset.prod_range_reflect (fun j => rootFactor (r + j)) r]
            rw [Finset.prod_mul_distrib]
          _ = ∏ i ∈ Finset.range r, (Polynomial.X ^ 2 + Polynomial.C ((lamNat i : ℝ) : ℂ)) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hpair i (Finset.mem_range.mp hi)
      have hprod : p = ∏ i : Fin r, (Polynomial.X ^ 2 + Polynomial.C ((lam i : ℝ) : ℂ)) := by
        exact hprodRange.trans
          (Finset.prod_range (fun i => (Polynomial.X : ℂ[X]) ^ 2 + Polynomial.C ((lamNat i : ℝ) : ℂ)))

      have hlam (i : Fin r) : 0 ≤ lam i ∧ lam i < 4 := by
        have hqpos : (0 : ℝ) < q := by positivity
        have hnum : 2 * (i.val + 1) < q := by dsimp [q]; omega
        have hnumR : (2 : ℝ) * (((i.val + 1 : ℕ) : ℝ)) < (q : ℝ) := by
          exact_mod_cast hnum
        have hthetaPos : 0 < theta i.val := by
          dsimp [theta]
          positivity
        have hthetaLt : theta i.val < Real.pi / 2 := by
          have hgap : 0 < ((q : ℝ) - 2 * (((i.val + 1 : ℕ) : ℝ))) * Real.pi := mul_pos (sub_pos.mpr hnumR) Real.pi_pos
          dsimp [theta]
          apply (div_lt_iff₀ hqpos).2
          nlinarith
        have hsin : 0 < Real.sin (theta i.val) := Real.sin_pos_of_pos_of_lt_pi hthetaPos
            (lt_trans hthetaLt (by nlinarith [Real.pi_pos]))
        have hsinSq : 0 < Real.sin (theta i.val) ^ 2 := sq_pos_of_pos hsin
        change 0 ≤ lamNat i.val ∧ lamNat i.val < 4
        constructor
        · dsimp [lamNat]
          positivity
        · dsimp [lamNat]
          nlinarith [Real.sin_sq_add_cos_sq (theta i.val)]

      have hreverse (z : ℂ) (hz : z ≠ 0) : p.eval z = z ^ (2 * r) * ∏ i : Fin r, (1 + (lam i : ℂ) * (z⁻¹) ^ 2) := by
        calc
          p.eval z = ∏ i : Fin r, (z ^ 2 + (lam i : ℂ)) := by
            rw [hprod, Polynomial.eval_prod]
            simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          _ = ∏ i : Fin r, (z ^ 2 * (1 + (lam i : ℂ) * (z⁻¹) ^ 2)) := by
            apply Finset.prod_congr rfl
            intro i hi
            field_simp [hz] <;> ring
          _ = z ^ (2 * r) * ∏ i : Fin r, (1 + (lam i : ℂ) * (z⁻¹) ^ 2) := by
            rw [Finset.prod_mul_distrib]
            simp [pow_mul]

      refine ⟨lam, hlam, ?_, ?_⟩
      · simpa only [p, q] using hprod
      · intro z hz
        simpa only [p, q] using hreverse z hz
    have integerPoly (r : ℕ) (hr : 1 ≤ r) (lam : Fin r → ℝ)
        (hprod : Polynomial.map (algebraMap ℤ ℂ) (fibonacciRecurrencePolynomial (2 * r + 1)) =
            ∏ i : Fin r, ((Polynomial.X : ℂ[X]) ^ 2 + Polynomial.C (lam i : ℂ))) :
        ∃ A : ℤ[X], A.map (algebraMap ℤ ℂ) = ∏ i : Fin r, (1 + Polynomial.C (lam i : ℂ) * Polynomial.X) ∧ A.coeff 0 = 1 ∧
          A.coeff 1 = (2 * r - 1 : ℤ) ∧
          Odd (2 * r - 1) := by
      let U : ℤ[X] := fibonacciRecurrencePolynomial (2 * r + 1)
      let A : ℤ[X] := (U.reverse).contract 2
      let phi : ℤ →+* ℂ := algebraMap ℤ ℂ

      have hdegree : U.natDegree = 2 * r := (fibonacci_recurrence_polynomial_coefficients.1 (2 * r)).1
      have hleading : U.coeff (2 * r) = 1 := (fibonacci_recurrence_polynomial_coefficients.1 (2 * r)).2
      have hmonic : U.Monic := monic_of_natDegree_le_of_coeff_eq_one (2 * r) hdegree.le hleading

      have hmapReverse : (U.reverse).map phi = (U.map phi).reverse := by
        simpa only [reverse, hmonic.natDegree_map] using
          (reflect_map phi U U.natDegree).symm

      have hreverseX2 : ((Polynomial.X : ℂ[X]) ^ 2).reverse = 1 := by
        simpa [Polynomial.reverse] using (reverse_X_pow_mul (1 : ℂ[X]) 2)
      have hreverseFactor (i : Fin r) : (((Polynomial.X : ℂ[X]) ^ 2 + Polynomial.C (lam i : ℂ)).reverse) =
            1 + Polynomial.C (lam i : ℂ) * Polynomial.X ^ 2 := by
        rw [reverse_add_C, natDegree_X_pow, hreverseX2]

      have hreverseProd (s : Finset (Fin r)) : (∏ i ∈ s, ((Polynomial.X : ℂ[X]) ^ 2 + Polynomial.C (lam i : ℂ))).reverse =
            ∏ i ∈ s, (1 + Polynomial.C (lam i : ℂ) * Polynomial.X ^ 2) := by
        classical
        induction s using Finset.induction_on with
        | empty => simp [Polynomial.reverse]
        | @insert i s his ih =>
            rw [Finset.prod_insert his, reverse_mul_of_domain, Finset.prod_insert his, hreverseFactor, ih]

      have hexpandFactor (i : Fin r) : Polynomial.expand ℂ 2 (1 + Polynomial.C (lam i : ℂ) * Polynomial.X) =
            1 + Polynomial.C (lam i : ℂ) * Polynomial.X ^ 2 := by
        simp only [map_add, map_mul, map_one, Polynomial.expand_C, Polynomial.expand_X]
      have hexpandProd : Polynomial.expand ℂ 2 (∏ i : Fin r, (1 + Polynomial.C (lam i : ℂ) * Polynomial.X)) =
            ∏ i : Fin r, (1 + Polynomial.C (lam i : ℂ) * Polynomial.X ^ 2) := by
        rw [map_prod]
        exact Finset.prod_congr rfl (fun i _ => hexpandFactor i)

      have hAmap : A.map phi = ∏ i : Fin r, (1 + Polynomial.C (lam i : ℂ) * Polynomial.X) := by
        calc
          A.map phi = ((U.map phi).reverse).contract 2 := by
            change ((U.reverse.contract 2).map phi) = _
            rw [map_contract (by decide : (2 : ℕ) ≠ 0), hmapReverse]
          _ = (Polynomial.expand ℂ 2 (∏ i : Fin r, (1 + Polynomial.C (lam i : ℂ) * Polynomial.X))).contract 2 := by
            rw [show U.map phi = ∏ i : Fin r, ((Polynomial.X : ℂ[X]) ^ 2 + Polynomial.C (lam i : ℂ)) from hprod]
            rw [hreverseProd Finset.univ, hexpandProd]
          _ = ∏ i : Fin r, (1 + Polynomial.C (lam i : ℂ) * Polynomial.X) := by
            rw [contract_expand 2 (by decide : (2 : ℕ) ≠ 0)]

      have hA0 : A.coeff 0 = 1 := by
        change (U.reverse.contract 2).coeff 0 = 1
        rw [coeff_contract (by decide : (2 : ℕ) ≠ 0), zero_mul, coeff_zero_reverse]
        exact hmonic.leadingCoeff
      have hA1 : A.coeff 1 = (2 * r - 1 : ℤ) := by
        change (U.reverse.contract 2).coeff 1 = (2 * r - 1 : ℤ)
        rw [coeff_contract (by decide : (2 : ℕ) ≠ 0), one_mul, coeff_reverse, hdegree, revAt_le (by omega : 2 ≤ 2 * r)]
        exact (fibonacci_recurrence_polynomial_coefficients.2.2 r hr).1
      exact ⟨A, hAmap, hA0, hA1, (fibonacci_recurrence_polynomial_coefficients.2.2 r hr).2⟩
    have scaledCoefficient (lam : (Fin r) → ℝ) (A : ℤ[X])
        (hA0 : A.coeff 0 = 1) (hA1 : Odd (A.coeff 1))
        (hAmap : Polynomial.map (algebraMap ℤ ℂ) A = ∏ i : (Fin r), ((1 + Polynomial.C (lam i : ℂ) * Polynomial.X) : ℂ[X]))
        (j : ℕ) (hj : 0 < j) :
        ∃ z : ℤ, Odd z ∧ (2 : ℂ)^(j + padicValNat 2 j.factorial) * PowerSeries.coeff j (formalS lam) = (z : ℂ) := by
      have dyadicCoefficient (Q : ℤ⟦X⟧) (hQ0 : PowerSeries.constantCoeff Q = 0)
          (hQ1 : Odd (PowerSeries.coeff 1 Q)) (j : ℕ) (hj : 0 < j) :
          ∃ z : ℤ, Odd z ∧ (2 : ℚ)^(j + padicValNat 2 j.factorial) * PowerSeries.coeff j
                ((PowerSeries.binomialSeries ℚ (1/2 : ℚ)).subst (Q.map (Int.castRingHom ℚ))) = (z : ℚ) := by
        have dyadicSum (j : ℕ) (hj : 0 < j) (c : ℕ → ℤ)
            (hc : Odd (c j))
         : ∃ z : ℤ, Odd z ∧ (2 : ℚ)^(j + padicValNat 2 j.factorial) * (∑ m ∈ Finset.range (j + 1),
                  Ring.choose (1/2 : ℚ) m * (c m : ℚ)) = (z : ℚ) := by
          have hval (n : ℕ) : padicValRat 2 (Ring.choose (1/2 : ℚ) n) = -((n : ℤ) + padicValNat 2 n.factorial) := by
            let oddPart : ℕ → ℤ := fun m =>
              ∏ k ∈ Finset.range m, (1 - 2 * (k : ℤ))
            have half_product (m : ℕ) : (2 : ℚ)^m * (m.factorial : ℚ) * Ring.choose (1/2 : ℚ) m = (oddPart m : ℚ) := by
              have hchoose : (m.factorial : ℚ) * Ring.choose (1/2 : ℚ) m = (descPochhammer ℤ m).smeval (1/2 : ℚ) := by
                simpa only [nsmul_eq_mul] using
                  (Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℚ) m).symm
              have hprod : ∀ j : ℕ, (descPochhammer ℤ j).smeval (1/2 : ℚ) = ∏ k ∈ Finset.range j, ((1/2 : ℚ) - k) := by
                intro j
                induction j with
                | zero => simp
                | succ j ih =>
                    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
                    congr 1
                    simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, nsmul_eq_mul,
                      pow_zero, mul_one, pow_one]
              rw [mul_assoc, hchoose, hprod]
              have htwo : (2 : ℚ)^m = ∏ _k ∈ Finset.range m, (2 : ℚ) := by simp
              rw [htwo, ← Finset.prod_mul_distrib]
              simp only [oddPart, Int.cast_prod, Int.cast_sub, Int.cast_one, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
              apply Finset.prod_congr rfl
              intro k hk
              ring
            have odd_part_not_dvd (m : ℕ) : ¬ (2 : ℤ) ∣ oddPart m := by
              induction m with
              | zero => norm_num [oddPart]
              | succ m ih =>
                  change ¬ (2 : ℤ) ∣ ∏ k ∈ Finset.range (m + 1), (1 - 2 * (k : ℤ))
                  rw [Finset.prod_range_succ]
                  have hfactor : ¬ (2 : ℤ) ∣ (1 - 2 * (m : ℤ)) := by omega
                  intro h
                  rcases (Int.prime_two.dvd_mul).mp h with h | h
                  · exact ih h
                  · exact hfactor h
            have hodd := odd_part_not_dvd n
            have hodd_ne : oddPart n ≠ 0 := by
              intro hz
              apply hodd
              rw [hz]
              exact dvd_zero 2
            have hchoose_ne : Ring.choose (1/2 : ℚ) n ≠ 0 := by
              intro hz
              have h := half_product n
              rw [hz, mul_zero] at h
              exact hodd_ne (Int.cast_eq_zero.mp h.symm)
            have hfactorial_ne : (n.factorial : ℚ) ≠ 0 := by
              exact_mod_cast Nat.factorial_ne_zero n
            have htwo : padicValRat 2 (2 : ℚ) = 1 := by
              change padicValRat 2 ((2 : ℕ) : ℚ) = 1
              exact padicValRat.self (by norm_num)
            have hval := congrArg (padicValRat 2) (half_product n)
            rw [padicValRat.mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) hfactorial_ne) hchoose_ne,
              padicValRat.mul (pow_ne_zero _ (by norm_num)) hfactorial_ne,
              padicValRat.pow, htwo] at hval
            simp only [padicValRat.of_nat, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hodd] at hval
            omega
          have hcat (n : ℕ) : Ring.choose (1/2 : ℚ) (n + 1) = (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) ∧
              ∃ z : ℤ, (2 : ℚ)^(2*n + 1) * Ring.choose (1/2 : ℚ) (n + 1) = (z : ℚ) := by
            let C : ℚ⟦X⟧ := catalanSeries.map (Nat.castRingHom ℚ)
            let T : ℚ⟦X⟧ := rescale (-1/4 : ℚ) C
            let S : ℚ⟦X⟧ := 1 + (PowerSeries.C (1/2 : ℚ)) * PowerSeries.X * T
            let B : ℚ⟦X⟧ := PowerSeries.binomialSeries ℚ (1/2 : ℚ)
            have hC : C^2 * PowerSeries.X + 1 = C := by
              have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
                catalanSeries_sq_mul_X_add_one
              simpa only [C, map_add, map_mul, map_pow, map_one, PowerSeries.map_X] using h
            have hT : T^2 * (PowerSeries.C (-1/4 : ℚ) * PowerSeries.X) + 1 = T := by
              have h := congrArg (rescale (-1/4 : ℚ)) hC
              simpa [T, rescale_X] using h
            have hhalf : (2 : ℚ⟦X⟧) * PowerSeries.C (1/2 : ℚ) = 1 := by
              have h : (2 : ℚ) * (1/2 : ℚ) = 1 := by norm_num
              simpa only [map_mul, map_ofNat, map_one] using
                congrArg (PowerSeries.C : ℚ →+* ℚ⟦X⟧) h
            have hquarter : (PowerSeries.C (1/2 : ℚ))^2 = -(PowerSeries.C (-1/4 : ℚ)) := by
              rw [← map_pow, ← map_neg]
              congr 1
              norm_num
            have hS : S^2 = 1 + PowerSeries.X := by
              dsimp [S]
              linear_combination -PowerSeries.X * hT + PowerSeries.X*T * hhalf + PowerSeries.X^2*T^2 * hquarter
            have hB : B^2 = 1 + PowerSeries.X := by
              calc
                B^2 = PowerSeries.binomialSeries ℚ ((1/2 : ℚ) + (1/2 : ℚ)) := by
                  simpa only [B, pow_two] using
                    (binomialSeries_add (A := ℚ) (1/2 : ℚ) (1/2 : ℚ)).symm
                _ = PowerSeries.binomialSeries ℚ (1 : ℚ) := by norm_num
                _ = (1 + PowerSeries.X)^1 := binomialSeries_nat 1
                _ = 1 + PowerSeries.X := pow_one _
            have hunit : IsUnit (S + B) := isUnit_iff_constantCoeff.mpr (by norm_num [S, B])
            have hdiff : S - B = 0 := by
              apply hunit.mul_right_cancel
              calc
                (S - B) * (S + B) = S^2 - B^2 := by ring
                _ = 0 := by rw [hS, hB]; ring
                _ = 0 * (S + B) := by ring
            have hSB : S = B := sub_eq_zero.mp hdiff
            have hc := congrArg (PowerSeries.coeff (n + 1)) hSB.symm
            have hbase : Ring.choose (1/2 : ℚ) (n + 1) = (1/2 : ℚ) * (-1/4 : ℚ)^n * (catalan n : ℚ) := by
              simpa [S, B, T, C, coeff_succ_X_mul, PowerSeries.coeff_C_mul, mul_assoc] using hc
            have hformula : Ring.choose (1/2 : ℚ) (n + 1) = (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) := by
              calc
                Ring.choose (1/2 : ℚ) (n + 1) = (1/2 : ℚ) * (-1/4 : ℚ)^n * (catalan n : ℚ) := hbase
                _ = (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) := by
                  rw [div_pow]
                  have hfour : (4 : ℚ)^n = (2 : ℚ)^(2*n) := by
                    norm_num [pow_mul]
                  rw [hfour, pow_add]
                  field_simp
            refine ⟨hformula, ?_⟩
            refine ⟨(-1 : ℤ)^n * (catalan n : ℤ), ?_⟩
            rw [hformula]
            field_simp
            norm_cast
          have hscaled : ∀ m, 0 < m → ∃ z : ℤ, Odd z ∧ (2 : ℚ)^(m + padicValNat 2 m.factorial) * Ring.choose (1/2 : ℚ) m = (z : ℚ) := by
            intro m hm
            obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
            have hformula := (hcat n).1
            have hval := hval (n+1)
            let j : ℕ := n + 1
            let e : ℕ := j + padicValNat 2 j.factorial
            let K : ℕ := 2*n + 1
            let k : ℕ := K - e
            have hj : j ≠ 0 := by dsimp [j]; omega
            have hvfac : padicValNat 2 j.factorial < j := padicValNat_factorial_lt_of_ne_zero 2 hj
            have heK : e ≤ K := by
              dsimp [j] at hvfac
              dsimp [e, K, j]
              omega
            have hke : e + k = K := by dsimp [k]; omega
            have hepos : 0 < e := by dsimp [e, j]; omega
            have hchoose_ne : Ring.choose (1/2 : ℚ) j ≠ 0 := by
              intro hz
              have hv := hval
              dsimp [j, e] at hv ⊢
              rw [hz, padicValRat.zero] at hv
              omega
            have hcne : catalan n ≠ 0 := by
              intro hz
              apply hchoose_ne
              rw [hformula, hz]
              simp
            have hcq : (catalan n : ℚ) ≠ 0 := by exact_mod_cast hcne
            have hsign : (-1 : ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
            have htwo : (2 : ℚ)^K ≠ 0 := pow_ne_zero _ (by norm_num)
            have hprod : Ring.choose (1/2 : ℚ) j * (2 : ℚ)^K = (-1 : ℚ)^n * (catalan n : ℚ) := by
              change Ring.choose (1/2 : ℚ) (n + 1) * (2 : ℚ)^(2*n + 1) = _
              rw [hformula]
              field_simp <;> ring
            have hsignVal : padicValRat 2 ((-1 : ℚ)^n) = 0 := by
              rw [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero]
            have htwoVal : padicValRat 2 (2 : ℚ) = 1 := by
              change padicValRat 2 ((2 : ℕ) : ℚ) = 1
              exact padicValRat.self (by norm_num)
            have hcv : padicValNat 2 (catalan n) = k := by
              have hv := congrArg (padicValRat 2) hprod
              rw [padicValRat.mul hchoose_ne htwo, padicValRat.mul hsign hcq, hsignVal, padicValRat.pow, htwoVal, padicValRat.of_nat,
                mul_one, zero_add] at hv
              dsimp [j] at hv
              rw [hval] at hv
              dsimp [K, e, j] at hv
              dsimp [k, K, e, j]
              omega
            have hdiv : 2^k ∣ catalan n := (padicValNat_dvd_iff_le (p := 2) hcne).2 (by rw [hcv])
            obtain ⟨u, hu⟩ := hdiv
            have hune : u ≠ 0 := by
              intro hzero
              apply hcne
              simp [hu, hzero]
            have huval : padicValNat 2 u = 0 := by
              have hv := congrArg (padicValNat 2) hu
              rw [hcv, padicValNat.mul (pow_ne_zero _ (by decide)) hune, padicValNat.prime_pow] at hv
              omega
            have huodd : Odd u := by
              apply Nat.not_even_iff_odd.mp
              intro hev
              have htwo_dvd : 2 ∣ u := Even.two_dvd hev
              have hvpos : 1 ≤ padicValNat 2 u := (padicValNat_dvd_iff_le (p := 2) hune).1 (by simpa using htwo_dvd)
              omega
            have huoddZ : Odd (u : ℤ) := by exact_mod_cast huodd
            have hzodd : Odd ((-1 : ℤ)^n * (u : ℤ)) := (show Odd (-1 : ℤ) by norm_num).pow.mul huoddZ
            refine ⟨(-1 : ℤ)^n * (u : ℤ), hzodd, ?_⟩
            change (2 : ℚ)^e * Ring.choose (1/2 : ℚ) j = _
            have hcu : (catalan n : ℚ) = (2 : ℚ)^k * (u : ℚ) := by
              exact_mod_cast hu
            rw [hformula, hcu]
            push_cast
            rw [show 2*n + 1 = e + k by simpa only [K] using hke.symm, pow_add]
            field_simp <;> ring
          classical
          let e : ℕ → ℕ := fun m => m + padicValNat 2 m.factorial
          have heStrict : StrictMono e := by
            intro m n hmn
            have hfac := Nat.factorial_dvd_factorial hmn.le
            have hval : padicValNat 2 m.factorial ≤ padicValNat 2 n.factorial :=
              (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero n)).1
                (dvd_trans (pow_padicValNat_dvd (p := 2) (n := m.factorial)) hfac)
            dsimp [e]
            omega
          have he0 : e 0 = 0 := by simp [e]
          have hepos : 0 < e j := by dsimp [e]; omega
          have hall : ∀ m, ∃ z : ℤ, (2 : ℚ)^(e m) * Ring.choose (1/2 : ℚ) m = (z : ℚ) ∧ (0 < m → Odd z) := by
            intro m
            by_cases hm : 0 < m
            · obtain ⟨z, hz, heq⟩ := hscaled m hm
              exact ⟨z, heq, fun _ => hz⟩
            · have hm0 : m = 0 := by omega
              subst m
              refine ⟨1, ?_, ?_⟩
              · simp [he0]
              · omega
          choose z hz hzodd using hall
          let d : ℕ → ℤ := fun m => (2 : ℤ)^(e j - e m) * z m * c m
          have hterm (m : ℕ) (hm : m ≤ j) : (2 : ℚ)^(e j) * (Ring.choose (1/2 : ℚ) m * (c m : ℚ)) = (d m : ℚ) := by
            have hem : e m ≤ e j := heStrict.monotone hm
            have he : e j = (e j - e m) + e m := by omega
            dsimp [d]
            push_cast
            conv_lhs => rw [he, pow_add]
            calc
              (2 : ℚ)^(e j - e m) * (2 : ℚ)^(e m) * (Ring.choose (1/2 : ℚ) m * (c m : ℚ)) = (2 : ℚ)^(e j - e m) *
                    ((2 : ℚ)^(e m) * Ring.choose (1/2 : ℚ) m) * (c m : ℚ) := by ring
              _ = _ := by rw [hz m]
          have hdEven (m : ℕ) (hm : m ∈ Finset.range j) : Even (d m) := by
            have hem : e m < e j := heStrict (Finset.mem_range.mp hm)
            have he : e j - e m = (e j - e m - 1) + 1 := by omega
            dsimp [d]
            rw [he, pow_succ]
            exact ((even_two.mul_left ((2 : ℤ)^(e j - e m - 1))).mul_right (z m)).mul_right (c m)
          have hdOdd : Odd (d j) := by
            simpa [d] using (hzodd j hj).mul hc
          have hsumEven : Even (∑ m ∈ Finset.range j, d m) := by
            exact Finset.even_sum d hdEven
          refine ⟨∑ m ∈ Finset.range (j+1), d m, ?_, ?_⟩
          · rw [Finset.sum_range_succ]
            exact hsumEven.add_odd hdOdd
          · change (2 : ℚ)^(e j) * _ = _
            rw [Finset.mul_sum]
            push_cast
            apply Finset.sum_congr rfl
            intro m hm
            exact hterm m (by have := Finset.mem_range.mp hm; omega)
        have coefficientSum (Q : ℤ⟦X⟧) (hQ0 : PowerSeries.constantCoeff Q = 0)
            (hQ1 : Odd (PowerSeries.coeff 1 Q)) :
            ∃ c : ℕ → ℕ → ℤ, (∀ j : ℕ, PowerSeries.coeff j ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (Q.map (Int.castRingHom ℚ))) =
                  ∑ m ∈ Finset.range (j + 1), Ring.choose (1 / 2 : ℚ) m * (c j m : ℚ)) ∧
              (∀ j : ℕ, c j j = (PowerSeries.coeff 1 Q) ^ j ∧ Odd (c j j)) := by
          let phi : ℤ →+* ℚ := Int.castRingHom ℚ
          let qQ : ℚ⟦X⟧ := Q.map phi
          let B : ℚ⟦X⟧ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst qQ
          let c (j m : ℕ) : ℤ := PowerSeries.coeff j (Q ^ m)

          have hqQ0 : PowerSeries.constantCoeff qQ = 0 := by
            change PowerSeries.constantCoeff (Q.map phi) = 0
            rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hQ0,
              map_zero]
          have hhas : PowerSeries.HasSubst qQ := PowerSeries.HasSubst.of_constantCoeff_zero' hqQ0

          have hcmap (j m : ℕ) : PowerSeries.coeff j (qQ ^ m) = (c j m : ℚ) := by
            change PowerSeries.coeff j ((PowerSeries.map phi Q) ^ m) = phi (PowerSeries.coeff j (Q ^ m))
            rw [← map_pow, PowerSeries.coeff_map]

          have hzero (j m : ℕ) (hjm : j < m) : c j m = 0 := by
            have horder : (m : ℕ∞) ≤ (Q ^ m).order := PowerSeries.le_order_pow_of_constantCoeff_eq_zero m hQ0
            have hcast : (j : ℕ∞) < (m : ℕ∞) := by exact_mod_cast hjm
            exact PowerSeries.coeff_of_lt_order j (hcast.trans_le horder)

          have hcoeff (j : ℕ) : PowerSeries.coeff j B = ∑ m ∈ Finset.range (j + 1), Ring.choose (1 / 2 : ℚ) m * (c j m : ℚ) := by
            let term : ℕ → ℚ := fun m => Ring.choose (1 / 2 : ℚ) m * (c j m : ℚ)
            have hterm (m : ℕ) : PowerSeries.coeff m (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) •
                    PowerSeries.coeff j (qQ ^ m) = term m := by
              simp only [PowerSeries.binomialSeries_coeff, hcmap, smul_eq_mul, mul_one] <;> rfl
            have hsupport : Function.support term ⊆ (Finset.range (j + 1) : Set ℕ) := by
              intro m hm
              by_contra hnot
              have hnm : ¬ m < j + 1 := by
                intro hmrange
                exact hnot (Finset.mem_coe.mpr (Finset.mem_range.mpr hmrange))
              have hjm : j < m := by omega
              have hterm0 : term m = 0 := by simp [term, hzero j m hjm]
              exact hm hterm0
            calc
              PowerSeries.coeff j B = finsum (fun m : ℕ => PowerSeries.coeff m (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) •
                      PowerSeries.coeff j (qQ ^ m)) :=
                PowerSeries.coeff_subst' hhas _ j
              _ = finsum term := by
                apply finsum_congr
                intro m
                exact hterm m
              _ = ∑ m ∈ Finset.range (j + 1), term m := finsum_eq_sum_of_support_subset term hsupport
              _ = ∑ m ∈ Finset.range (j + 1), Ring.choose (1 / 2 : ℚ) m * (c j m : ℚ) := rfl

          let T : ℤ⟦X⟧ := PowerSeries.mk (fun k => PowerSeries.coeff (k + 1) Q)
          have hshift : Q = PowerSeries.X * T := by
            simpa [T, hQ0] using PowerSeries.eq_X_mul_shift_add_const Q
          have hdiag (j : ℕ) : c j j = (PowerSeries.coeff 1 Q) ^ j := by
            calc
              c j j = PowerSeries.coeff j ((PowerSeries.X * T) ^ j) := by
                dsimp [c]
                rw [hshift]
              _ = PowerSeries.coeff j ((PowerSeries.X : ℤ⟦X⟧) ^ j * T ^ j) := by
                rw [mul_pow]
              _ = PowerSeries.coeff 0 (T ^ j) := by
                simpa only [zero_add] using PowerSeries.coeff_X_pow_mul (T ^ j) j 0
              _ = (PowerSeries.coeff 0 T) ^ j := by
                simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
              _ = (PowerSeries.coeff 1 Q) ^ j := by simp [T]
          refine ⟨c, ?_, ?_⟩
          · intro j
            simpa only [B, qQ, phi] using hcoeff j
          · intro j
            exact ⟨hdiag j, (hdiag j).symm ▸ hQ1.pow⟩
        obtain ⟨c, hcoeff, hdiag⟩ := coefficientSum Q hQ0 hQ1
        obtain ⟨z, hzOdd, heq⟩ := dyadicSum j hj (c j) (hdiag j).2
        refine ⟨z, hzOdd, ?_⟩
        rw [hcoeff j]
        exact heq
      have seriesIdentification (lam : (Fin r) → ℝ) (A : ℤ[X])
          (hA0 : A.coeff 0 = 1)
          (hAmap : Polynomial.map (algebraMap ℤ ℂ) A = ∏ i : (Fin r), ((1 + Polynomial.C (lam i : ℂ) * Polynomial.X) : ℂ[X])) :
          ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (((A : ℤ⟦X⟧) - 1).map (Int.castRingHom ℚ))).map
              (algebraMap ℚ ℂ) = formalS lam := by
        let Q : ℤ⟦X⟧ := (A : ℤ⟦X⟧) - 1
        let qQ : ℚ⟦X⟧ := Q.map (Int.castRingHom ℚ)
        have hQ0 : PowerSeries.constantCoeff Q = 0 := by
          simp [Q, hA0]
        have hqQ0 : PowerSeries.constantCoeff qQ = 0 := by
          change PowerSeries.constantCoeff (Q.map (Int.castRingHom ℚ)) = 0
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
            hQ0, map_zero]
        have hqSubst : PowerSeries.HasSubst qQ := PowerSeries.HasSubst.of_constantCoeff_zero' hqQ0

        have hAseries : ((Polynomial.map (algebraMap ℤ ℂ) A : ℂ[X]) : ℂ⟦X⟧) = formalA lam := by
          have h := congrArg
            (Polynomial.coeToPowerSeries.ringHom : ℂ[X] →+* ℂ⟦X⟧) hAmap
          rw [map_prod] at h
          simpa [formalA] using h

        have hQcomplex : Q.map (algebraMap ℤ ℂ) = formalA lam - 1 := by
          calc
            Q.map (algebraMap ℤ ℂ) = (A : ℤ⟦X⟧).map (algebraMap ℤ ℂ) - 1 := by simp [Q]
            _ = ((Polynomial.map (algebraMap ℤ ℂ) A : ℂ[X]) : ℂ⟦X⟧) - 1 := by
              rw [Polynomial.polynomial_map_coe]
            _ = formalA lam - 1 := by rw [hAseries]

        have hqQcomplex : qQ.map (algebraMap ℚ ℂ) = Q.map (algebraMap ℤ ℂ) := by
          ext n
          simp [qQ]

        have hbinomial : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).map (algebraMap ℚ ℂ) = PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) := by
          ext n
          simp only [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
          simp [Ring.map_choose]

        change ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst qQ).map
          (algebraMap ℚ ℂ) = formalS lam
        calc
          ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst qQ).map
              (algebraMap ℚ ℂ) = ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).map (algebraMap ℚ ℂ)).subst (qQ.map (algebraMap ℚ ℂ)) :=
            PowerSeries.map_subst hqSubst _
          _ = formalS lam := by
            rw [hbinomial, hqQcomplex, hQcomplex]
      let Q : ℤ⟦X⟧ := (A : ℤ⟦X⟧) - 1
      have hQ0 : PowerSeries.constantCoeff Q = 0 := by simp [Q, hA0]
      have hQ1 : Odd (PowerSeries.coeff 1 Q) := by simpa [Q] using hA1
      obtain ⟨z, hzOdd, heq⟩ := dyadicCoefficient Q hQ0 hQ1 j hj
      have hseries := seriesIdentification lam A hA0 hAmap
      have hcoeff := congrArg (PowerSeries.coeff j) hseries
      change algebraMap ℚ ℂ
          (PowerSeries.coeff j ((PowerSeries.binomialSeries ℚ (1/2 : ℚ)).subst (Q.map (Int.castRingHom ℚ)))) =
          PowerSeries.coeff j (formalS lam) at hcoeff
      have heqC : (2 : ℂ)^(j + padicValNat 2 j.factorial) * PowerSeries.coeff j (formalS lam) = (z : ℂ) := by
        have h := congrArg (algebraMap ℚ ℂ) heq
        simp only [map_mul, map_pow, map_ofNat] at h
        rw [show algebraMap ℚ ℂ (PowerSeries.coeff j ((PowerSeries.binomialSeries ℚ (1/2 : ℚ)).subst (Q.map (Int.castRingHom ℚ)))) =
            PowerSeries.coeff j (formalS lam) from hcoeff] at h
        simpa using h
      exact ⟨z, hzOdd, heqC⟩
    have integerRoot (r : ℕ) (hr : 119 ≤ r) (lam : Fin r → ℝ)
        (hlam : ∀ i, 0 ≤ lam i ∧ lam i < 4)
        (x M : ℤ) (hx : 2 < x)
        (hsize : 128 * (6 : ℤ)^r < x^2 - 4)
        (hreverse : ∀ z : ℂ, z ≠ 0 → (Polynomial.map (algebraMap ℤ ℂ) (fibonacciRecurrencePolynomial (2 * r + 1))).eval z = z ^ (2 * r) *
              ∏ i : Fin r, (1 + (lam i : ℂ) * (z⁻¹) ^ 2))
        (hsquare : (fibonacciRecurrencePolynomial (2 * r + 1)).eval x = M ^ 2) :
        ∃ N : ℤ, (x : ℂ)^r * (∏ i : Fin r, Complex.sqrt (1 + (lam i : ℂ) * ((x : ℂ)⁻¹) ^ 2)) = (N : ℂ) := by
      let P : ℤ[X] := fibonacciRecurrencePolynomial (2 * r + 1)
      let W : ℂ := (x : ℂ)^r * ∏ i : Fin r, Complex.sqrt (1 + (lam i : ℂ) * ((x : ℂ)⁻¹) ^ 2)
      have hx0 : x ≠ 0 := by omega
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
      have heval : (P.map (algebraMap ℤ ℂ)).eval (x : ℂ) = ((P.eval x : ℤ) : ℂ) := by
        simpa using
          (Polynomial.eval_map_apply (p := P) (f := algebraMap ℤ ℂ) x)
      have hroot : ((P.eval x : ℤ) : ℂ) = (x : ℂ) ^ (2 * r) * ∏ i : Fin r, (1 + (lam i : ℂ) * ((x : ℂ)⁻¹) ^ 2) := by
        calc
          ((P.eval x : ℤ) : ℂ) = (P.map (algebraMap ℤ ℂ)).eval (x : ℂ) := heval.symm
          _ = _ := by simpa only [P] using hreverse (x : ℂ) hxC

      have hsqrt (w : ℂ) : Complex.sqrt w * Complex.sqrt w = w := by
        calc
          _ = (w ^ (2⁻¹ : ℂ)) ^ (2 : ℕ) := by simp [Complex.sqrt, pow_two]
          _ = w ^ ((2⁻¹ : ℂ) * (2 : ℕ)) := (Complex.cpow_mul_nat w (2⁻¹ : ℂ) 2).symm
          _ = w := by norm_num
      have hprodSq : (∏ i : Fin r, Complex.sqrt (1 + (lam i : ℂ) * ((x : ℂ)⁻¹) ^ 2)) ^ 2 =
            ∏ i : Fin r, (1 + (lam i : ℂ) * ((x : ℂ)⁻¹) ^ 2) := by
        rw [pow_two, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        exact hsqrt _
      have hWsq : W ^ 2 = ((P.eval x : ℤ) : ℂ) := by
        calc
          W ^ 2 = (x : ℂ) ^ (2 * r) * ∏ i : Fin r, (1 + (lam i : ℂ) * ((x : ℂ)⁻¹) ^ 2) := by
            dsimp [W]
            rw [mul_pow, hprodSq, ← pow_mul, Nat.mul_comm r 2]
          _ = ((P.eval x : ℤ) : ℂ) := hroot.symm
      have hWMsq : W ^ 2 = (M : ℂ) ^ 2 := by
        calc
          W ^ 2 = ((P.eval x : ℤ) : ℂ) := hWsq
          _ = (M : ℂ) ^ 2 := by
            simpa only [P, Int.cast_pow] using
              congrArg (fun z : ℤ => (z : ℂ)) hsquare
      have hzero : (W - (M : ℂ)) * (W + (M : ℂ)) = 0 := by
        calc
          _ = W ^ 2 - (M : ℂ) ^ 2 := by ring
          _ = 0 := sub_eq_zero.mpr hWMsq
      rcases mul_eq_zero.mp hzero with hminus | hplus
      · refine ⟨M, ?_⟩
        change W = (M : ℂ)
        exact sub_eq_zero.mp hminus
      · refine ⟨-M, ?_⟩
        change W = ((-M : ℤ) : ℂ)
        simpa only [Int.cast_neg] using eq_neg_of_add_eq_zero_left hplus
    have analyticFacts (r : ℕ) (lam : Fin r → ℝ)
        (hlam : ∀ i, 0 ≤ lam i ∧ lam i < 4)
        (z : ℂ) (hz : ‖z‖ < (1 / 4 : ℝ)) :
        let formalA : (Fin r → ℝ) → ℂ⟦X⟧ := fun lam =>
          ∏ i : Fin r, (1 + PowerSeries.C (lam i : ℂ) * PowerSeries.X)
        let formalS : (Fin r → ℝ) → ℂ⟦X⟧ := fun lam =>
          (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)).subst (formalA lam - 1)
        (formalS lam).constantCoeff = 1 ∧ (∀ j : ℕ, ‖(formalS lam).coeff j‖ ≤ (Real.sqrt 2)^r * (4 : ℝ)^j) ∧
          HasSum (fun j : ℕ => (formalS lam).coeff j * z^j)
            (∏ i : Fin r, Complex.sqrt (1 + (lam i : ℂ) * z)) := by
      let formalA : ℂ⟦X⟧ := ∏ i : Fin r, (1 + PowerSeries.C (lam i : ℂ) * PowerSeries.X)
      let formalS : ℂ⟦X⟧ := (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)).subst (formalA - 1)
      let analyticS : ℂ → ℂ := fun w =>
        ∏ i : Fin r, Complex.sqrt (1 + (lam i : ℂ) * w)
      let taylorPS : (ℂ → ℂ) → ℂ⟦X⟧ := fun f =>
        PowerSeries.mk fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0
      change formalS.constantCoeff = 1 ∧ (∀ j : ℕ, ‖formalS.coeff j‖ ≤ (Real.sqrt 2)^r * (4 : ℝ)^j) ∧
        HasSum (fun j : ℕ => formalS.coeff j * z^j) (analyticS z)

      have formalA_const : formalA.constantCoeff = 1 := by
        simp [formalA]
      have formal_hasSubst : PowerSeries.HasSubst (formalA - 1) := PowerSeries.HasSubst.of_constantCoeff_zero'
          (by simp [formalA_const])
      have formal_square : formalS * formalS = formalA := by
        have hb : PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) * PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) = (1 + PowerSeries.X : ℂ⟦X⟧) := by
          rw [← PowerSeries.binomialSeries_add, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]
          simpa using (PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1)
        let B := formalA - 1
        have hB : PowerSeries.HasSubst B := formal_hasSubst
        calc
          formalS * formalS = (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) * PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)).subst B := by
            simpa [formalS, B] using
              (PowerSeries.subst_mul hB (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)) (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ))).symm
          _ = (1 + PowerSeries.X : ℂ⟦X⟧).subst B := by rw [hb]
          _ = formalA := by
            rw [PowerSeries.subst_add hB, PowerSeries.subst_X hB]
            rw [show (1 : ℂ⟦X⟧) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
            simp [B]

      have taylorPS_mul (f g : ℂ → ℂ)
          (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
          taylorPS (f * g) = taylorPS f * taylorPS g := by
        ext n
        simp only [taylorPS, PowerSeries.coeff_mk, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Nat.cast_choose _ (by grind)]
        field_simp [Nat.factorial_ne_zero]

      have analyticS_analyticAt : AnalyticAt ℂ analyticS 0 := by
        have hsqrt : AnalyticOnNhd ℂ Complex.sqrt Complex.slitPlane :=
          (Complex.analyticOnNhd_iff_differentiableOn Complex.isOpen_slitPlane).2
            Complex.differentiableOn_sqrt
        unfold analyticS
        apply Finset.analyticAt_fun_prod
        intro i _
        have harg : AnalyticAt ℂ (fun z : ℂ => 1 + (lam i : ℂ) * z) 0 := by fun_prop
        have hmem : 1 + (lam i : ℂ) * (0 : ℂ) ∈ Complex.slitPlane := by
          simp [Complex.mem_slitPlane_iff]
        simpa only [Function.comp_def] using
          (hsqrt _ hmem).comp (f := fun z : ℂ => 1 + (lam i : ℂ) * z) harg

      have taylorPS_square : taylorPS analyticS * taylorPS analyticS = formalA := by
        classical
        have hder (a : ℂ) (n : ℕ) : iteratedDeriv n (fun z : ℂ => 1 + a * z) 0 = if n = 0 then 1 else if n = 1 then a else 0 := by
          by_cases h0 : n = 0
          · subst n; simp
          · have hn : 0 < n := Nat.pos_of_ne_zero h0
            rw [iteratedDeriv_const_add (f := fun z : ℂ => a * z) (x := (0 : ℂ)) hn 1]
            rw [iteratedDeriv_const_mul_field (𝕜 := ℂ) a (fun z : ℂ => z), iteratedDeriv_fun_id_zero]
            split_ifs <;> simp_all
        have hlinear (a : ℂ) : taylorPS (fun z : ℂ => 1 + a * z) = (1 + PowerSeries.C a * PowerSeries.X : ℂ⟦X⟧) := by
          ext n
          simp only [taylorPS, PowerSeries.coeff_mk]
          rw [hder a n]
          by_cases h0 : n = 0
          · subst n; simp
          · by_cases h1 : n = 1
            · subst n; simp
            · simp [h0, h1, PowerSeries.coeff_X]
        have hprod (s : Finset (Fin r)) : taylorPS (fun z : ℂ => ∏ i ∈ s, (1 + (lam i : ℂ) * z)) =
              ∏ i ∈ s, (1 + PowerSeries.C (lam i : ℂ) * PowerSeries.X) := by
          induction s using Finset.induction_on with
          | empty =>
              ext n
              by_cases hn : n = 0
              · subst n; simp [taylorPS]
              · simp [taylorPS, iteratedDeriv_const, hn]
          | @insert i s his ih =>
              have hfi : AnalyticAt ℂ (fun z : ℂ => 1 + (lam i : ℂ) * z) 0 := by fun_prop
              have hfs : AnalyticAt ℂ
                  (fun z : ℂ => ∏ j ∈ s, (1 + (lam j : ℂ) * z)) 0 := by
                apply Finset.analyticAt_fun_prod
                intro j _
                fun_prop
              have heqfun : (fun z : ℂ => ∏ j ∈ insert i s, (1 + (lam j : ℂ) * z)) = (fun z : ℂ => 1 + (lam i : ℂ) * z) *
                      (fun z : ℂ => ∏ j ∈ s, (1 + (lam j : ℂ) * z)) := by
                funext z
                simp [Pi.mul_apply, Finset.prod_insert, his]
              rw [heqfun, taylorPS_mul _ _ hfi hfs, hlinear, ih]
              simp [Finset.prod_insert, his]
        have hsqrt (w : ℂ) : Complex.sqrt w * Complex.sqrt w = w := by
          calc
            _ = (w ^ (2⁻¹ : ℂ)) ^ (2 : ℕ) := by simp [Complex.sqrt, pow_two]
            _ = w ^ ((2⁻¹ : ℂ) * (2 : ℕ)) := (Complex.cpow_mul_nat w (2⁻¹ : ℂ) 2).symm
            _ = w := by norm_num
        have hsquare : analyticS * analyticS = (fun z : ℂ => ∏ i : Fin r, (1 + (lam i : ℂ) * z)) := by
          funext z
          simp only [Pi.mul_apply, analyticS, ← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i _
          exact hsqrt _
        calc
          taylorPS analyticS * taylorPS analyticS = taylorPS (analyticS * analyticS) :=
            (taylorPS_mul _ _ analyticS_analyticAt analyticS_analyticAt).symm
          _ = taylorPS (fun z : ℂ => ∏ i : Fin r, (1 + (lam i : ℂ) * z)) := by
            rw [hsquare]
          _ = formalA := by simpa [formalA] using hprod Finset.univ

      have formalS_const : formalS.constantCoeff = 1 := by
        have hA : MvPowerSeries.constantCoeff formalA = 1 := formalA_const
        unfold formalS
        change MvPowerSeries.constantCoeff _ = 1
        rw [PowerSeries.constantCoeff_subst formal_hasSubst, finsum_eq_single _ 0]
        · simp
        · intro j hj
          simp [map_pow, hA, zero_pow hj]
      have taylorPS_const : (taylorPS analyticS).constantCoeff = 1 := by
        simp [taylorPS, analyticS]
      have formal_coeff_eq_taylor (j : ℕ) : formalS.coeff j = (j.factorial : ℂ)⁻¹ * iteratedDeriv j analyticS 0 := by
        have hprod : (formalS - taylorPS analyticS) * (formalS + taylorPS analyticS) = 0 := by
          calc
            _ = formalS * formalS -
                taylorPS analyticS * taylorPS analyticS := by ring
            _ = 0 := by rw [formal_square, taylorPS_square, sub_self]
        have heq : formalS = taylorPS analyticS := by
          rcases mul_eq_zero.mp hprod with hminus | hplus
          · exact sub_eq_zero.mp hminus
          · have hc := congrArg PowerSeries.constantCoeff hplus
            simp [formalS_const, taylorPS_const] at hc
        simpa [taylorPS] using congrArg (PowerSeries.coeff j) heq

      have affine_re_pos (a : ℝ) (ha : 0 ≤ a ∧ a < 4)
          (z : ℂ) (hz : z ∈ Metric.closedBall 0 (1 / 4 : ℝ)) :
          0 < (1 + (a : ℂ) * z).re := by
        have hnorm : ‖z‖ ≤ (1 / 4 : ℝ) := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz
        have hre : -(1 / 4 : ℝ) ≤ z.re := by
          have := (abs_le.mp (Complex.abs_re_le_norm z)).1
          linarith
        have hprod : 0 ≤ a * (z.re + 1 / 4) := mul_nonneg ha.1 (by linarith)
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith
      have analyticS_diffContOnCl : DiffContOnCl ℂ analyticS (Metric.ball 0 (1 / 4 : ℝ)) := by
        have hsqrt : AnalyticOnNhd ℂ Complex.sqrt Complex.slitPlane :=
          (Complex.analyticOnNhd_iff_differentiableOn Complex.isOpen_slitPlane).2
            Complex.differentiableOn_sqrt
        apply DifferentiableOn.diffContOnCl_ball
          (U := Metric.closedBall 0 (1 / 4 : ℝ)) ?_ (Set.Subset.rfl)
        intro z hz
        have han : AnalyticAt ℂ analyticS z := by
          unfold analyticS
          apply Finset.analyticAt_fun_prod
          intro i _
          have harg : AnalyticAt ℂ (fun w : ℂ => 1 + (lam i : ℂ) * w) z := by fun_prop
          have hmem : 1 + (lam i : ℂ) * z ∈ Complex.slitPlane := by
            exact Complex.mem_slitPlane_iff.mpr
              (Or.inl (affine_re_pos (lam i) (hlam i) z hz))
          simpa only [Function.comp_def] using
            (hsqrt _ hmem).comp (f := fun z : ℂ => 1 + (lam i : ℂ) * z) harg
        exact han.differentiableAt.differentiableWithinAt
      have analyticS_boundary (z : ℂ)
          (hz : z ∈ Metric.sphere 0 (1 / 4 : ℝ)) :
          ‖analyticS z‖ ≤ (Real.sqrt 2)^r := by
        have hz' : ‖z‖ = (1 / 4 : ℝ) := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz
        unfold analyticS
        rw [norm_prod]
        calc
          ∏ i : Fin r, ‖Complex.sqrt (1 + (lam i : ℂ) * z)‖ ≤ ∏ _i : Fin r, Real.sqrt 2 := by
            apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            intro i _
            have hn : ‖1 + (lam i : ℂ) * z‖ ≤ 2 := by
              have ht := norm_add_le (1 : ℂ) ((lam i : ℂ) * z)
              rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlam i).1, hz'] at ht
              linarith [(hlam i).2]
            have hs : ‖Complex.sqrt (1 + (lam i : ℂ) * z)‖ = Real.sqrt ‖1 + (lam i : ℂ) * z‖ := by
              rw [Complex.sqrt]
              exact (Complex.norm_cpow_inv_nat (1 + (lam i : ℂ) * z) 2).trans
                (by rw [Real.sqrt_eq_rpow, one_div]; rfl)
            rw [hs]
            exact Real.sqrt_le_sqrt hn
          _ = (Real.sqrt 2)^r := by simp
      have coeff_bound (j : ℕ) : ‖formalS.coeff j‖ ≤ (Real.sqrt 2)^r * (4 : ℝ)^j := by
        rw [formal_coeff_eq_taylor j]
        have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          j (by norm_num : 0 < (1 / 4 : ℝ))
          analyticS_diffContOnCl analyticS_boundary
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        calc
          (j.factorial : ℝ)⁻¹ * ‖iteratedDeriv j analyticS 0‖ ≤ (j.factorial : ℝ)⁻¹ *
                ((j.factorial : ℝ) * (Real.sqrt 2)^r / (1 / 4 : ℝ)^j) :=
            mul_le_mul_of_nonneg_left hcauchy (inv_nonneg.mpr (Nat.cast_nonneg _))
          _ = (Real.sqrt 2)^r * (4 : ℝ)^j := by
            have hfac : (j.factorial : ℝ) ≠ 0 := by
              exact_mod_cast Nat.factorial_ne_zero j
            rw [div_pow, one_pow]
            field_simp
      have formal_hasSum (z : ℂ)
          (hz : z ∈ Metric.ball 0 (1 / 4 : ℝ)) :
          HasSum (fun j : ℕ => formalS.coeff j * z^j) (analyticS z) := by
        have ht := Complex.hasSum_taylorSeries_on_ball
          analyticS_diffContOnCl.differentiableOn hz
        apply ht.congr_fun
        intro j
        rw [formal_coeff_eq_taylor j]
        simp only [sub_zero, smul_eq_mul]
        ring

      refine ⟨formalS_const, coeff_bound, ?_⟩
      apply formal_hasSum z
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hr1 : 1 ≤ r := by omega
    obtain ⟨lam, hlam, hprod, hreverse⟩ := rootPair r
    obtain ⟨A, hAmap, hA0, hA1, hAodd⟩ := integerPoly r hr1 lam hprod
    have hcoef (j : ℕ) (hj : 0 < j) : ∃ z : ℤ, Odd z ∧ (2 : ℂ)^(j+padicValNat 2 j.factorial) *
          PowerSeries.coeff j (formalS lam) = (z : ℂ) :=
      scaledCoefficient lam A hA0 (by rw [hA1]; exact ⟨(r : ℤ)-1, by ring⟩) hAmap j hj
    let y : ℂ := ((x : ℂ)^2)⁻¹
    have hxR : (2 : ℝ) < x := by exact_mod_cast hx
    have hy : ‖y‖ < (1/4 : ℝ) := by
      have hxR0 : (0 : ℝ) < x := by linarith
      have hx2 : (4 : ℝ) < (x : ℝ)^2 := by nlinarith
      have hn : ‖y‖ = ((x : ℝ)^2)⁻¹ := by
        simp [y, norm_inv, norm_pow, Complex.norm_intCast, abs_of_pos hxR0]
      rw [hn]
      exact (inv_lt_comm₀ (by positivity) (by norm_num)).2 (by norm_num; exact hx2)
    obtain ⟨hs0, hsupper, hsum⟩ := analyticFacts r lam hlam y hy
    have hnot := dyadic_series_integer_obstruction (fun j => PowerSeries.coeff j (formalS lam)) r hr1 x hx
      (∏ i : Fin r, Complex.sqrt (1 + (lam i : ℂ)*y))
      (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hs0)
      (fun j hj => let ⟨z,hz,heq⟩ := hcoef j hj; ⟨z,hz,heq⟩)
      hsupper hsum
      (by exact_mod_cast hsize)
    intro hSquare
    obtain ⟨M,hM⟩ := hSquare.exists_sq
    obtain ⟨N,hN⟩ := integerRoot r hr lam hlam x M hx hsize hreverse hM
    apply hnot N
    simpa only [y, inv_pow] using hN
  have quotients
      (hmain : ∀ (r : ℕ), 119 ≤ r → ∀ (x : ℤ), 2 < x → 128 * (6 : ℤ) ^ r + 4 < x ^ 2 →
        ¬ IsSquare ((fibonacciRecurrencePolynomial (2 * r + 1)).eval x)) :
      (∀ (r n : ℕ), 119 ≤ r → Odd n → 2 * r + 1 ≤ n → 0 < Nat.fib ((2 * r + 1) * n) / Nat.fib n ∧
          ¬ IsSquare (Nat.fib ((2 * r + 1) * n) / Nat.fib n)) ∧
      (∀ (q k : ℕ), q.Prime → 239 ≤ q → 1 ≤ k → 0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
          ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))) := by
    have hoddLayer : ∀ (r n : ℕ), 119 ≤ r → Odd n → 2 * r + 1 ≤ n → 0 < Nat.fib ((2 * r + 1) * n) / Nat.fib n ∧
          ¬ IsSquare (Nat.fib ((2 * r + 1) * n) / Nat.fib n) := by
      intro r n hr hnodd hnlarge
      have hnpos : 0 < n := by omega
      have hdenpos : 0 < Nat.fib n := Nat.fib_pos.mpr hnpos
      have hnumpos : 0 < Nat.fib ((2 * r + 1) * n) := Nat.fib_pos.mpr (mul_pos (by omega) hnpos)
      have hdiv : Nat.fib n ∣ Nat.fib ((2 * r + 1) * n) := by
        apply Nat.fib_dvd
        refine ⟨2 * r + 1, ?_⟩
        ring
      have hmul : Nat.fib n * (Nat.fib ((2 * r + 1) * n) / Nat.fib n) = Nat.fib ((2 * r + 1) * n) := Nat.mul_div_cancel' hdiv
      have hbridge := (odd_fibonacci_recurrence_bridge n (2 * r + 1) hnodd).1
      have hdenne : (Nat.fib n : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hdenpos)
      have hquotient : ((Nat.fib ((2 * r + 1) * n) / Nat.fib n : ℕ) : ℤ) = (fibonacciRecurrencePolynomial (2 * r + 1)).eval
              (goldenLucas n) := by
        have hmulInt : (Nat.fib n : ℤ) * ((Nat.fib ((2 * r + 1) * n) / Nat.fib n : ℕ) : ℤ) = (Nat.fib ((2 * r + 1) * n) : ℤ) := by
          exact_mod_cast hmul
        exact mul_left_cancel₀ hdenne (hmulInt.trans hbridge.symm)
      have hbound := golden_lucas_nonsquare_threshold r n hr hnlarge
      have hLucasNonneg : 0 ≤ goldenLucas n := by
        cases n with
        | zero => omega
        | succ j =>
            simpa only [Nat.succ_eq_add_one, golden_lucas_succ_eq_fib_add_fib] using
              (add_nonneg (show (0 : ℤ) ≤ Nat.fib j by positivity) (show (0 : ℤ) ≤ Nat.fib (j + 2) by positivity))
      have hLucasGtTwo : 2 < goldenLucas n := by
        have hpow : 0 ≤ (6 : ℤ) ^ r := by positivity
        by_contra h
        have hle : goldenLucas n ≤ 2 := le_of_not_gt h
        have hsq : goldenLucas n ^ 2 ≤ 4 := by nlinarith
        nlinarith [hbound]
      have hnonsquare := hmain r hr (goldenLucas n) hLucasGtTwo hbound
      constructor
      · exact Nat.div_pos (Nat.le_of_dvd hnumpos hdiv) hdenpos
      · intro hsq
        apply hnonsquare
        rw [← hquotient]
        exact Int.isSquare_natCast_iff.mpr hsq
    refine ⟨hoddLayer, ?_⟩
    intro q k hqprime hqge hk
    have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
    let r := q / 2
    have hqform : 2 * r + 1 = q := by
      exact Nat.two_mul_div_two_add_one_of_odd hqodd
    have hr : 119 ≤ r := by omega
    have hnodd : Odd (q ^ k) := hqodd.pow
    have hnlarge : 2 * r + 1 ≤ q ^ k := by
      rw [hqform]
      exact Nat.le_self_pow (by omega) q
    have hresult := hoddLayer r (q ^ k) hr hnodd hnlarge
    have hindex : (2 * r + 1) * q ^ k = q ^ (k + 1) := by
      rw [hqform, pow_succ]
      ring
    simpa only [hindex] using hresult
  obtain ⟨hodd,hprime⟩ := quotients (fun r hr x hx hsize => main r hr x hx (by linarith))
  exact ⟨main,hodd,hprime⟩

#print axioms fibonacci_recurrence_polynomial_nonsquare

end D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
