/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrimaryProduct
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicPrimaryProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact primary Eisenstein element factorization of the golden cubic block. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
import D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
import D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime
import D5.S3.Arith.Primes.GoldenCubicBlockRanks
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Tactic

open D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
open D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime
open D5.S3.Arith.Primes.GoldenCubicBlockRanks
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open NumberField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct

/-- The cubic Lucas block has an exact primary Eisenstein factorization. -/
theorem golden_cubic_primary_product (j : ℕ) (hj : 1 ≤ j) :
    let x : ℤ := goldenLucas (3 ^ j)
    let b : ℕ := (x - 1).toNat
    let B : ℕ := blockNorm b
    let eta : EisensteinOrder := orientedFactor b
    let lambda : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
    eta = QuadraticAlgebra.omega * ((x : EisensteinOrder) + lambda) ∧
    QuadraticAlgebra.norm eta = (B : ℤ) ∧
    (9 : EisensteinOrder) ∣ eta - (1 + lambda ^ 3) ∧
    IsCoprime (Ideal.span {eta}) (Ideal.span {star eta}) ∧
    ∃ pi : ℕ → EisensteinOrder,
      (∀ p ∈ B.primeFactors,
        let P : Ideal EisensteinOrder := orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
        P.IsPrime ∧
          (∀ Q : Ideal EisensteinOrder, Q.IsPrime →
            (p : EisensteinOrder) ∈ Q → eta ∈ Q → Q = P) ∧
          Ideal.span {pi p} = P ∧
          QuadraticAlgebra.norm (pi p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ pi p - 1 ∧
          p % 3 = 1) ∧
      eta = ∏ p ∈ B.primeFactors,
        (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p)) := by
  classical
  let x : ℤ := goldenLucas (3 ^ j)
  let b : ℕ := (x - 1).toNat
  let B : ℕ := blockNorm b
  let eta : EisensteinOrder := orientedFactor b
  let lambda : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
  change eta = QuadraticAlgebra.omega * ((x : EisensteinOrder) + lambda) ∧
    QuadraticAlgebra.norm eta = (B : ℤ) ∧
    (9 : EisensteinOrder) ∣ eta - (1 + lambda ^ 3) ∧
    IsCoprime (Ideal.span {eta}) (Ideal.span {star eta}) ∧
    ∃ pi : ℕ → EisensteinOrder,
      (∀ p ∈ B.primeFactors,
        let P : Ideal EisensteinOrder := orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
        P.IsPrime ∧
          (∀ Q : Ideal EisensteinOrder, Q.IsPrime →
            (p : EisensteinOrder) ∈ Q → eta ∈ Q → Q = P) ∧
          Ideal.span {pi p} = P ∧
          QuadraticAlgebra.norm (pi p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ pi p - 1 ∧
          p % 3 = 1) ∧
      eta = ∏ p ∈ B.primeFactors,
        (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p))
  have hp : 0 < 3 ^ j := pow_pos (by decide) j
  let n := 3 ^ j - 1
  have hn : n + 1 = 3 ^ j := by dsimp [n]; omega
  have hxpos : 0 < x := by
    change 0 < goldenLucas (3 ^ j)
    rw [← hn, golden_lucas_succ_eq_fib_add_fib]
    have hf : 0 < Nat.fib (n + 2) := Nat.fib_pos.mpr (by omega)
    have hn0 : 0 ≤ (Nat.fib n : ℤ) := Nat.cast_nonneg _
    have hf0 : 0 < (Nat.fib (n + 2) : ℤ) := by exact_mod_cast hf
    omega
  have hx72 : (x : ZMod 72) = 4 := (golden_cubic_lucas_block j hj).1
  have hdiv : (72 : ℤ) ∣ x - 4 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 4 x 72).mp (by simpa using hx72.symm)
  obtain ⟨k, hk⟩ := hdiv
  have hxge : 4 ≤ x := by omega
  have hbcast : (b : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
  have hbodd : Odd b := by
    rw [Nat.odd_iff]
    omega
  have hB : (B : ℤ) = x ^ 2 + 3 := by
    simp only [B, blockNorm, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hbcast]
    ring
  have hetaIdentity : eta = QuadraticAlgebra.omega * ((x : EisensteinOrder) + lambda) := by
    apply QuadraticAlgebra.ext
    · norm_num [eta, orientedFactor, lambda, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_mul, hbcast, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    · norm_num [eta, orientedFactor, lambda, QuadraticAlgebra.omega,
        QuadraticAlgebra.im_mul, hbcast, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      ring
  have hetaNorm : QuadraticAlgebra.norm eta = (B : ℤ) := by
    simp only [eta, orientedFactor, QuadraticAlgebra.norm_def]
    rw [hB, hbcast]
    ring
  have hetaNine : (9 : EisensteinOrder) ∣ eta - (1 + lambda ^ 3) := by
    have h9 : (9 : ℤ) ∣ x + 5 := by
      omega
    have hdiff : eta - (1 + lambda ^ 3) =
        ((x + 5 : ℤ) : EisensteinOrder) * QuadraticAlgebra.omega := by
      apply QuadraticAlgebra.ext
      · norm_num [eta, orientedFactor, lambda, QuadraticAlgebra.omega,
          QuadraticAlgebra.re_mul, QuadraticAlgebra.re_ofNat,
          QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_one,
          QuadraticAlgebra.im_one, hbcast, pow_succ] <;> ring
      · norm_num [eta, orientedFactor, lambda, QuadraticAlgebra.omega,
          QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat,
          QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_one,
          QuadraticAlgebra.im_one, hbcast, pow_succ] <;> ring
    obtain ⟨t, ht⟩ := h9
    refine ⟨(t : EisensteinOrder) * QuadraticAlgebra.omega, ?_⟩
    rw [hdiff, ht]
    push_cast
    ring
  have hetaCoprime : IsCoprime (Ideal.span {eta}) (Ideal.span {star eta}) := by
    simpa only [eta, orientedFactor, hbcast] using
      golden_eisenstein_conjugate_coprime j hj
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsPrincipalIdealRing (𝓞 (CyclotomicField 3 ℚ)) :=
    IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  let φ := Classical.choice eisenstein_cyclotomic_equiv_exists
  letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
  letI : IsPrincipalIdealRing EisensteinOrder :=
    IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
  have hPnorm (p : ℕ) (hpB : p ∣ B) :
      Ideal.absNorm (orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}) = p := by
    exact factor_norm b p hbodd hpB
  have hgen (p : ℕ) (hpB : p ∣ B) :
      ∃ g : EisensteinOrder,
        orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)} = Ideal.span {g} ∧
        QuadraticAlgebra.norm g = (p : ℤ) := by
    let P : Ideal EisensteinOrder := orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal P).principal
    have hn : Ideal.absNorm P = p := hPnorm p hpB
    have hnormabs : (Algebra.norm ℤ g).natAbs = p := by
      simpa only [hg, Ideal.absNorm_span_singleton] using hn
    have halg : Algebra.norm ℤ g = QuadraticAlgebra.norm g := by
      rw [Algebra.norm_apply]
      exact QuadraticAlgebra.det_toLinearMap_eq_norm g
    have hnonneg : 0 ≤ QuadraticAlgebra.norm g := by
      simp only [QuadraticAlgebra.norm_def]
      nlinarith [sq_nonneg (2 * g.re - g.im), sq_nonneg g.im]
    refine ⟨g, hg, ?_⟩
    rw [halg] at hnormabs
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hnormabs
    simpa only [Int.natCast_natAbs, abs_of_nonneg hnonneg] using hcast
  have hPprime (p : ℕ) (hp : p.Prime) (hpB : p ∣ B) :
      let P : Ideal EisensteinOrder :=
        orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
      P.IsPrime ∧
        ∀ Q : Ideal EisensteinOrder, Q.IsPrime →
          (p : EisensteinOrder) ∈ Q → eta ∈ Q → Q = P := by
    let P : Ideal EisensteinOrder := orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
    have hn : Ideal.absNorm P = p := hPnorm p hpB
    have hprimeNorm : Irreducible (Ideal.absNorm P) := by
      rw [hn]
      exact (Nat.irreducible_iff_nat_prime p).mpr hp
    have hP : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm hprimeNorm
    have hPneBot : P ≠ ⊥ := by
      intro hbot
      have hn0 : Ideal.absNorm P = 0 := by simp [hbot]
      rw [hn] at hn0
      exact hp.ne_zero hn0
    letI : P.IsPrime := hP
    have hmax : P.IsMaximal := IsPrime.to_maximal_ideal hPneBot
    change P.IsPrime ∧ ∀ Q : Ideal EisensteinOrder, Q.IsPrime →
      (p : EisensteinOrder) ∈ Q → eta ∈ Q → Q = P
    refine ⟨hP, ?_⟩
    intro Q hQ hQp hQeta
    have hPQ : P ≤ Q := by
      change Ideal.span {eta} ⊔ Ideal.span {(p : EisensteinOrder)} ≤ Q
      apply sup_le
      · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hQeta)
      · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hQp)
    exact (hmax.eq_of_le hQ.ne_top hPQ).symm
  have hBz : ((B : ℤ) : ZMod 3) = 1 := by
    have hx : x = 4 + 72 * k := by omega
    rw [hB, hx]
    push_cast
    have h72 : (72 : ZMod 3) = 0 := by
      calc
        (72 : ZMod 3) = (3 : ZMod 3) * 24 := by norm_num
        _ = 0 := by rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]; ring
    have h4 : (4 : ZMod 3) = 1 := by
      calc
        (4 : ZMod 3) = (3 : ZMod 3) + 1 := by ring
        _ = 1 := by rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]; ring
    rw [h72, zero_mul, add_zero, h4]
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]
    ring
  have hpNot3 (p : ℕ) (hpB : p ∣ B) : p ≠ 3 := by
    intro heq
    subst p
    have hcast : (B : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff B 3).mpr hpB
    have hbad : (1 : ZMod 3) = 0 := hBz.symm.trans (by exact_mod_cast hcast)
    exact one_ne_zero hbad
  have hPrimeMod3 (g : EisensteinOrder) (p : ℕ) (hp : p.Prime)
      (hp3 : p ≠ 3) (hn : QuadraticAlgebra.norm g = (p : ℤ)) : p % 3 = 1 := by
    have hsq : (((g.re + g.im : ℤ) : ZMod 3) ^ 2) = (p : ZMod 3) := by
      have hcast := congrArg (fun n : ℤ => (n : ZMod 3)) hn
      simp only [QuadraticAlgebra.norm_def] at hcast
      push_cast at hcast ⊢
      calc
        ((g.re : ZMod 3) + (g.im : ZMod 3)) ^ 2 =
            (g.re : ZMod 3) * (g.re : ZMod 3) -
            (g.re : ZMod 3) * (g.im : ZMod 3) +
            (g.im : ZMod 3) * (g.im : ZMod 3) := by
              have hthree : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
              calc
                _ = (g.re : ZMod 3) * (g.re : ZMod 3) -
                    (g.re : ZMod 3) * (g.im : ZMod 3) +
                    (g.im : ZMod 3) * (g.im : ZMod 3) +
                    3 * (g.re : ZMod 3) * (g.im : ZMod 3) := by ring
                _ = _ := by rw [hthree]; ring
        _ = (p : ZMod 3) := by linear_combination hcast
    have hcases (v : ZMod 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hpcast : (p : ZMod 3) = 1 := by
      rcases hcases ((g.re + g.im : ℤ) : ZMod 3) with hz | hz | hz
      · rw [hz, zero_pow (by decide : 2 ≠ 0)] at hsq
        have hdvd : 3 ∣ p := (ZMod.natCast_eq_zero_iff _ _).mp hsq.symm
        exact (hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd).symm).elim
      · simpa only [hz, one_pow] using hsq.symm
      · have h4 : (4 : ZMod 3) = 1 := by
          calc
            (4 : ZMod 3) = (3 : ZMod 3) + 1 := by ring
            _ = 1 := by rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]; ring
        have htwo : (2 : ZMod 3) ^ 2 = 1 := by
          calc
            (2 : ZMod 3) ^ 2 = 4 := by ring
            _ = 1 := h4
        simpa only [hz, htwo] using hsq.symm
    have hpmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hpmod with h0 | h1 | h2
    · have hdvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
      exact (hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd).symm).elim
    · exact h1
    · have hcast : (p : ZMod 3) = 2 := by simpa [h2] using (ZMod.natCast_mod p 3).symm
      have hbad : (1 : ZMod 3) = 2 := hpcast.symm.trans hcast
      have h12 : (1 : ZMod 3) ≠ 2 := by
        intro heq
        have hv := congrArg ZMod.val heq
        norm_num [ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod] at hv
      exact (h12 hbad).elim
  have hChoice (p : ℕ) : ∃ z : EisensteinOrder,
      p ∈ B.primeFactors →
        let P : Ideal EisensteinOrder :=
          orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
        P.IsPrime ∧
          (∀ Q : Ideal EisensteinOrder, Q.IsPrime →
            (p : EisensteinOrder) ∈ Q → eta ∈ Q → Q = P) ∧
          Ideal.span {z} = P ∧
          QuadraticAlgebra.norm z = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ z - 1 ∧
          p % 3 = 1 := by
    by_cases hpm : p ∈ B.primeFactors
    · have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
      have hpB : p ∣ B := Nat.dvd_of_mem_primeFactors hpm
      obtain ⟨g, hgspan, hgnorm⟩ := hgen p hpB
      have hp3 : p ≠ 3 := hpNot3 p hpB
      have hpmod : p % 3 = 1 := hPrimeMod3 g p hp hp3 hgnorm
      have hgnormz : ((QuadraticAlgebra.norm g : ℤ) : ZMod 3) = 1 := by
        rw [hgnorm]
        calc
          ((p : ℤ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by
            exact (ZMod.natCast_mod p 3).symm
          _ = 1 := by rw [hpmod]; rfl
      obtain ⟨u, hu, huNorm, hprimary⟩ := exists_primary_associate g hgnormz
      refine ⟨u * g, ?_⟩
      intro _
      have hprime := hPprime p hp hpB
      dsimp at hprime ⊢
      refine ⟨hprime.1, hprime.2, ?_, ?_, hprimary, hpmod⟩
      · rw [Ideal.span_singleton_mul_left_unit hu, ← hgspan]
      · rw [map_mul, huNorm, hgnorm, one_mul]
    · exact ⟨1, by intro h; exact (hpm h).elim⟩
  choose pi hpi using hChoice
  have hDepth (p : ℕ) (hpm : p ∈ B.primeFactors) :
      B.factorization p = padicValNat p (Nat.fib (fibonacciRank p)) := by
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hpB : p ∣ B := Nat.dvd_of_mem_primeFactors hpm
    have hpBZ : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
      change (p : ℤ) ∣ x ^ 2 + 3
      rw [← hB]
      exact_mod_cast hpB
    have hr := (cubic_block_b_prime_rank j p hj hp hpBZ).2.2
    calc
      B.factorization p = padicValNat p B := Nat.factorization_def B hp
      _ = padicValInt p (B : ℤ) := by rw [padicValInt.of_nat]
      _ = padicValNat p (Nat.fib (fibonacciRank p)) := by
        rw [hB]
        exact hr
  have hSpanProduct : Ideal.span {eta} =
      Ideal.span {∏ p ∈ B.primeFactors,
        (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p))} := by
    calc
      Ideal.span {eta} = ∏ p ∈ B.primeFactors,
          (orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}) ^
            B.factorization p := by
              simpa only [eta, orientedIdeal] using
                eisenstein_odd_ideal_factorization b hbodd
      _ = ∏ p ∈ B.primeFactors,
          (Ideal.span {pi p}) ^ padicValNat p (Nat.fib (fibonacciRank p)) := by
            apply Finset.prod_congr rfl
            intro p hp
            rcases hpi p hp with ⟨_, _, hspan, _, _, _⟩
            rw [hDepth p hp, hspan]
      _ = Ideal.span {∏ p ∈ B.primeFactors,
          (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p))} := by
            simp_rw [Ideal.span_singleton_pow]
            exact Ideal.prod_span_singleton B.primeFactors
              (fun p => (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p)))
  let q : EisensteinOrder →+* EisensteinOrder ⧸ Ideal.span {(3 : EisensteinOrder)} :=
    Ideal.Quotient.mk _
  have hEtaQ : q eta = 1 := by
    have hx : x = 4 + 72 * k := by omega
    have hb3 : (3 : ℤ) ∣ (b : ℤ) := by
      rw [hbcast, hx]
      refine ⟨1 + 24 * k, ?_⟩
      ring
    have hcoords : (3 : ℤ) ∣ (eta - 1).re ∧ (3 : ℤ) ∣ (eta - 1).im := by
      constructor
      · change (3 : ℤ) ∣ -3
        norm_num
      · change (3 : ℤ) ∣ (b : ℤ)
        exact hb3
    have hdvd : (3 : EisensteinOrder) ∣ eta - 1 :=
      (QuadraticAlgebra.algebraMap_dvd_iff).mpr hcoords
    have hm : eta - 1 ∈ Ideal.span {(3 : EisensteinOrder)} :=
      Ideal.mem_span_singleton.mpr hdvd
    have hq0 : q (eta - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_sub, map_one, sub_eq_zero] using hq0
  have hProdQ : q (∏ p ∈ B.primeFactors,
      (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p))) = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro p hpm
    rw [map_pow]
    have hprimary : (3 : EisensteinOrder) ∣ pi p - 1 := by
      rcases hpi p hpm with ⟨_, _, _, _, hprimary, _⟩
      exact hprimary
    have hm : pi p - 1 ∈ Ideal.span {(3 : EisensteinOrder)} :=
      Ideal.mem_span_singleton.mpr hprimary
    have hq0 : q (pi p - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have hq1 : q (pi p) = 1 := by
      simpa only [map_sub, map_one, sub_eq_zero] using hq0
    rw [hq1, one_pow]
  have hUnitPrimary (u : EisensteinOrder) (hu : IsUnit u)
      (hprimary : (3 : EisensteinOrder) ∣ u - 1) : u = 1 := by
    have hcoords : (3 : ℤ) ∣ u.re - 1 ∧ (3 : ℤ) ∣ u.im := by
      have h := (QuadraticAlgebra.algebraMap_dvd_iff
        (r := (3 : ℤ)) (z := u - 1)).mp hprimary
      simpa only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, sub_zero] using h
    have hnormunit : IsUnit (QuadraticAlgebra.norm u) :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    have hnormnonneg : 0 ≤ QuadraticAlgebra.norm u := by
      simp only [QuadraticAlgebra.norm_def]
      nlinarith [sq_nonneg (2 * u.re - u.im), sq_nonneg u.im]
    have hnorm : QuadraticAlgebra.norm u = 1 := by
      have habs := Int.isUnit_iff_abs_eq.mp hnormunit
      simpa [abs_of_nonneg hnormnonneg] using habs
    have hbSqFour : 3 * u.im ^ 2 ≤ 4 := by
      simp only [QuadraticAlgebra.norm_def] at hnorm
      nlinarith [sq_nonneg (2 * u.re - u.im)]
    have hbSq : u.im ^ 2 ≤ 1 := by omega
    have hbBounds : -1 ≤ u.im ∧ u.im ≤ 1 := by
      constructor <;> nlinarith
    obtain ⟨k, hk⟩ := hcoords.2
    have hb : u.im = 0 := by omega
    have haSq : u.re ^ 2 = 1 := by
      simpa only [QuadraticAlgebra.norm_def, hb, mul_zero, zero_mul,
        sub_zero, add_zero, pow_two] using hnorm
    have haBounds : -1 ≤ u.re ∧ u.re ≤ 1 := by
      constructor <;> nlinarith
    obtain ⟨m, hm⟩ := hcoords.1
    have ha : u.re = 1 := by omega
    apply QuadraticAlgebra.ext
    · simpa only [QuadraticAlgebra.re_one] using ha
    · simpa only [QuadraticAlgebra.im_one] using hb
  refine ⟨hetaIdentity, hetaNorm, hetaNine, hetaCoprime, ?_⟩
  refine ⟨pi, fun p hp => hpi p hp, ?_⟩
  have ha : Associated
      (∏ p ∈ B.primeFactors,
        (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p))) eta :=
    (Ideal.span_singleton_eq_span_singleton.mp hSpanProduct).symm
  obtain ⟨u, hu⟩ := ha
  have hqu : q (u : EisensteinOrder) = 1 := by
    have h := congrArg q hu
    simpa only [map_mul, hProdQ, one_mul, hEtaQ] using h
  have huPrimary : (3 : EisensteinOrder) ∣ (u : EisensteinOrder) - 1 := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((u : EisensteinOrder) - 1) = 0
    rw [map_sub, hqu, map_one, sub_self]
  have hu1 : (u : EisensteinOrder) = 1 :=
    hUnitPrimary u u.isUnit huPrimary
  simpa only [hu1, mul_one] using hu.symm

#print axioms golden_cubic_primary_product

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
