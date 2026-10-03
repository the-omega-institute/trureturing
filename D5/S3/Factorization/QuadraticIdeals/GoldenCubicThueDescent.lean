/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueDescent
   generality: G
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicThueDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual two-prime cubic Thue descent, cyclic fields and integer finiteness. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimeNormField
import D5.S3.Arith.DiophantineApproximation.ThueEquation
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

open D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
open D5.S3.Arith.Primes.GoldenCubicBlockRanks
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial NumberField IsDedekindDomain

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueDescent

theorem golden_cubic_exact_thue_descent (j P Q : ℕ) (hj : 1 ≤ j) (hP : P.Prime) (hQ : Q.Prime) (hPQ : P ≠ Q) :
    (blockNorm ((goldenLucas (3 ^ j) - 1).toNat) = P ^ 2 * Q ^ 3 →
    ∃ pi gamma : EisensteinOrder,
      QuadraticAlgebra.norm pi = (P : ℤ) ∧
      QuadraticAlgebra.norm gamma = (Q : ℤ) ∧
      (Ideal.span {pi}).IsPrime ∧ IsCoprime pi (star pi) ∧
      Ideal.span {pi} = orientedIdeal ((goldenLucas (3 ^ j) - 1).toNat) ⊔
        Ideal.span {(P : EisensteinOrder)} ∧
      Ideal.span {gamma} = orientedIdeal ((goldenLucas (3 ^ j) - 1).toNat) ⊔
        Ideal.span {(Q : EisensteinOrder)} ∧
      (3 : EisensteinOrder) ∣ pi - 1 ∧
      (3 : EisensteinOrder) ∣ gamma - 1 ∧
      padicValNat P (Nat.fib (fibonacciRank P)) = 2 ∧
      padicValNat Q (Nat.fib (fibonacciRank Q)) = 3 ∧
      orientedFactor ((goldenLucas (3 ^ j) - 1).toNat) = pi ^ 2 * gamma ^ 3 ∧
      let a := pi.re; let b := pi.im; let u := gamma.re; let v := gamma.im
      let A := a ^ 2 - b ^ 2; let D := 2 * a * b - b ^ 2
      A*u^3 - 3*D*u^2*v + 3*(D-A)*u*v^2 + A*v^3 = -2 ∧
      D*(u^3-3*u*v^2+v^3) + (A-D)*(3*u*v*(u-v)) = goldenLucas (3^j)-1 ∧
      u^2-u*v+v^2 = (Q : ℤ) ∧
      (let p : ℚ[X] :=
        (⟨(A : ℚ), (-3*D : ℤ), (3*(D-A) : ℤ), (A : ℚ)⟩ : Cubic ℚ).toPoly;
        Irreducible p ∧ Module.finrank ℚ p.SplittingField = 3 ∧ IsCyclic p.Gal ∧
          NumberField.IsTotallyReal p.SplittingField ∧
          (⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℤ).discr = 81*(P : ℤ)^4) ∧
      {z : ℤ × ℤ | A*z.1^3 - 3*D*z.1^2*z.2 +
        3*(D-A)*z.1*z.2^2 + A*z.2^3 = -2}.Finite) ∧
      (∀ a b u v : ℤ,
        a^2-a*b+b^2 = (P : ℤ) → u^2-u*v+v^2 = (Q : ℤ) →
        (a^2-b^2)*u^3 - 3*(2*a*b-b^2)*u^2*v +
          3*((2*a*b-b^2)-(a^2-b^2))*u*v^2 + (a^2-b^2)*v^3 = -2 →
        (2*a*b-b^2)*(u^3-3*u*v^2+v^3) +
          ((a^2-b^2)-(2*a*b-b^2))*(3*u*v*(u-v)) + 1 = goldenLucas (3^j) →
        blockNorm ((goldenLucas (3 ^ j) - 1).toNat) = P ^ 2 * Q ^ 3) := by
  classical
  let x : ℤ := goldenLucas (3 ^ j)
  let b : ℕ := (x - 1).toNat
  let B : ℕ := blockNorm b
  have hxge : 4 ≤ x := by
    have hx72 : (x : ZMod 72) = 4 := (golden_cubic_lucas_block j hj).1
    have hdiv : (72 : ℤ) ∣ x - 4 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub 4 x 72).mp hx72.symm
    have hxpos : 0 < x := by
      have hn : 3 ^ j - 1 + 1 = 3 ^ j := by have := pow_pos (by decide : 0 < (3 : ℕ)) j; omega
      dsimp [x]
      rw [← hn, golden_lucas_succ_eq_fib_add_fib]
      have hpos : 0 < (Nat.fib (3 ^ j - 1 + 2) : ℤ) := by
        exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < 3 ^ j - 1 + 2))
      have hnonneg : 0 ≤ (Nat.fib (3 ^ j - 1) : ℤ) := Nat.cast_nonneg _
      omega
    obtain ⟨k, hk⟩ := hdiv
    omega
  have hbcast : (b : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
  have hBcast : (B : ℤ) = x ^ 2 + 3 := by
    simp only [B, blockNorm, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hbcast]
    ring
  constructor
  · intro hB
    have hB' : B = P ^ 2 * Q ^ 3 := hB
    have hsupport : B.primeFactors = {P, Q} := by
      rw [hB', Nat.primeFactors_mul (pow_ne_zero _ hP.ne_zero) (pow_ne_zero _ hQ.ne_zero),
        Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) hP,
        Nat.primeFactors_prime_pow (by decide : 3 ≠ 0) hQ]
      rfl
    have hPmem : P ∈ B.primeFactors := by rw [hsupport]; simp
    have hQmem : Q ∈ B.primeFactors := by rw [hsupport]; simp
    letI : Fact P.Prime := ⟨hP⟩
    letI : Fact Q.Prime := ⟨hQ⟩
    have hdepth (p : ℕ) (hp : p.Prime) (hpm : p ∈ B.primeFactors) :
        padicValNat p (Nat.fib (fibonacciRank p)) = padicValNat p B := by
      have hdvd : (p : ℤ) ∣ x ^ 2 + 3 := by
        rw [← hBcast]
        exact_mod_cast (Nat.dvd_of_mem_primeFactors hpm)
      rw [← (cubic_block_b_prime_rank j p hj hp hdvd).2.2, ← hBcast,
        padicValInt.of_nat]
    have hPdepth : padicValNat P (Nat.fib (fibonacciRank P)) = 2 := by
      rw [hdepth P hP hPmem, hB']
      exact padicValNat_mul_pow_left 2 3 hPQ
    have hQdepth : padicValNat Q (Nat.fib (fibonacciRank Q)) = 3 := by
      rw [hdepth Q hQ hQmem, hB']
      exact padicValNat_mul_pow_right 2 3 hPQ.symm
    obtain ⟨hetaId, hetaNorm, hetaNine, hetaCop, pi, hpi, heta⟩ :=
      golden_cubic_primary_product j hj
    rcases hpi P hPmem with ⟨hprimeP, _, hspanP, hnormP, hprimP, _⟩
    have hdivP : pi P ∣ orientedFactor b := by
      apply Ideal.mem_span_singleton.mp
      rw [hspanP]
      exact (le_sup_left : orientedIdeal b ≤ orientedIdeal b ⊔
        Ideal.span {(P : EisensteinOrder)})
        (Ideal.subset_span (Set.mem_singleton (orientedFactor b)))
    have hcopP : IsCoprime (pi P) (star (pi P)) :=
      IsCoprime.mono hdivP (map_dvd (starRingEnd EisensteinOrder) hdivP)
        ((Ideal.isCoprime_span_singleton_iff _ _).mp hetaCop)
    have hprimeP' : (Ideal.span {pi P}).IsPrime := hspanP.symm ▸ hprimeP
    rcases hpi Q hQmem with ⟨_, _, hspanQ, hnormQ, hprimQ, _⟩
    have hprod : orientedFactor b = pi P ^ 2 * pi Q ^ 3 := by
      change orientedFactor b = _ at heta
      rw [hsupport, Finset.prod_pair hPQ, hPdepth, hQdepth] at heta
      exact heta
    refine ⟨pi P, pi Q, hnormP, hnormQ, hprimeP', hcopP, hspanP, hspanQ,
      hprimP, hprimQ, hPdepth, hQdepth, hprod, ?_⟩
    have hsystem :
        let a := (pi P).re; let b := (pi P).im; let u := (pi Q).re; let v := (pi Q).im
        let A := a^2-b^2; let D := 2*a*b-b^2
        A*u^3-3*D*u^2*v+3*(D-A)*u*v^2+A*v^3 = -2 ∧
        D*(u^3-3*u*v^2+v^3)+(A-D)*(3*u*v*(u-v)) = goldenLucas (3^j)-1 ∧
        u^2-u*v+v^2 = (Q : ℤ) := by
      dsimp
      have hre := congrArg QuadraticAlgebra.re hprod
      have him := congrArg QuadraticAlgebra.im hprod
      have hnorm := hnormQ
      norm_num [orientedFactor, pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at hre him
      simp only [QuadraticAlgebra.norm_def] at hnorm
      rw [hbcast] at him
      constructor
      · linear_combination -hre
      constructor
      · linear_combination -him
      · nlinarith [hnorm]
    have hpi0 : pi P ≠ 0 := by
      intro hz
      have he := hnormP
      rw [hz] at he
      norm_num [QuadraticAlgebra.norm_def] at he
      have hPzero : P = 0 := by exact_mod_cast he.symm
      exact hP.ne_zero hPzero
    let A : ℤ := (pi P).re^2-(pi P).im^2
    let D : ℤ := 2*(pi P).re*(pi P).im-(pi P).im^2
    have hfield := GoldenCubicPrimeNormField.golden_cubic_prime_norm_field
      (pi P) P hpi0 hprimeP' hcopP hnormP
    have hnz := GoldenCubicPrimeNormField.prime_norm_cubic_no_integer_projective_zero
      (pi P) hpi0 hprimeP' hcopP
    have hA : A ≠ 0 := by
      simpa [A, D] using hnz 1 0 (Or.inl (by decide : (1 : ℤ) ≠ 0))
    have hirr : Irreducible
        ((⟨(A : ℚ), (-3*D : ℤ), (3*(D-A) : ℤ), (A : ℚ)⟩ : Cubic ℚ).toPoly) := hfield.1
    have hfinite : {z : ℤ × ℤ | A*z.1^3-3*D*z.1^2*z.2+
        3*(D-A)*z.1*z.2^2+A*z.2^3 = -2}.Finite := by
      classical
      let c : Cubic ℤ := ⟨A, -3*D, 3*(D-A), A⟩
      let g : ℤ[X] := c.toPoly
      let gq := g.map (Int.castRingHom ℚ)
      let gc := g.map (Int.castRingHom ℂ)
      have hdeg : g.natDegree = 3 := Polynomial.natDegree_eq_of_degree_eq_some
        (Cubic.degree_of_a_ne_zero hA)
      have hgq : gq = (⟨(A : ℚ), (-3*D : ℤ), (3*(D-A) : ℤ), (A : ℚ)⟩ : Cubic ℚ).toPoly := by
        change Polynomial.map (Int.castRingHom ℚ) c.toPoly = _
        rw [← Cubic.map_toPoly]
        rfl
      have hsep : gq.Separable := by rw [hgq]; exact hirr.separable
      have hmap : gc = gq.map (algebraMap ℚ ℂ) := by
        dsimp only [gc, gq]
        rw [Polynomial.map_map]
        congr 1
      have hsepC : gc.Separable := by rw [hmap]; exact hsep.map
      have hgcDegree : gc.natDegree = 3 := by
        dsimp only [gc]
        rw [natDegree_map_eq_of_injective (RingHom.injective_int _), hdeg]
      have hcard : gc.roots.toFinset.card = 3 := by
        rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsepC),
          ← (IsAlgClosed.splits gc).natDegree_eq_card_roots, hgcDegree]
      have hf := Polynomial.finite_setOf_eval_homogenize_eq
        (g := g) (d := 3) (by omega)
        (by change 3 ≤ gc.roots.toFinset.card + if g.natDegree = 3 then 0 else 1
            rw [hcard, hdeg]
            norm_num)
        (m := -2) (by decide : (-2 : ℤ) ≠ 0)
      convert hf using 1
      ext z
      simp only [Set.mem_setOf_eq]
      have heval : MvPolynomial.eval ![z.1,z.2] (g.homogenize 3) =
          A*z.1^3 - 3*D*z.1^2*z.2 + 3*(D-A)*z.1*z.2^2 + A*z.2^3 := by
        change MvPolynomial.eval ![z.1,z.2]
          ((Polynomial.C A * Polynomial.X^3 + Polynomial.C (-3*D) * Polynomial.X^2 +
            Polynomial.C (3*(D-A)) * Polynomial.X + Polynomial.C A).homogenize 3) = _
        simp only [Polynomial.homogenize_add, Polynomial.homogenize_C_mul,
          Polynomial.homogenize_X_pow (by decide : 3 ≤ 3),
          Polynomial.homogenize_X_pow (by decide : 2 ≤ 3),
          Polynomial.homogenize_X (by decide : 3 ≠ 0), Polynomial.homogenize_C]
        simp
        ring
      rw [heval]
    exact ⟨hsystem.1, hsystem.2.1, hsystem.2.2, hfield, hfinite⟩
  · intro a b u v hP hQ hf hg
    let f : ℤ := (a^2-b^2)*u^3 - 3*(2*a*b-b^2)*u^2*v +
      3*((2*a*b-b^2)-(a^2-b^2))*u*v^2 + (a^2-b^2)*v^3
    let g : ℤ := (2*a*b-b^2)*(u^3-3*u*v^2+v^3) +
      ((a^2-b^2)-(2*a*b-b^2))*(3*u*v*(u-v))
    have hnorm : f^2-f*g+g^2 = (a^2-a*b+b^2)^2*(u^2-u*v+v^2)^3 := by
      dsimp [f, g]
      ring
    change f = -2 at hf
    change g + 1 = goldenLucas (3^j) at hg
    rw [hP, hQ, hf] at hnorm
    have heq : goldenLucas (3^j)^2+3 = (P : ℤ)^2*(Q : ℤ)^3 := by
      rw [← hg]
      nlinarith only [hnorm]
    have hcast : (blockNorm ((goldenLucas (3 ^ j) - 1).toNat) : ℤ) =
        (P : ℤ)^2*(Q : ℤ)^3 := hBcast.trans heq
    exact_mod_cast hcast

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueDescent
