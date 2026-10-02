/- GID: D5/S3/Factorization/Galois/GoldenCubicCompleteUnitObstruction
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCompleteUnitObstruction
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The actual conjugate-complete golden cubic radical field has full degree and excludes a cube root of the cubic cyclotomic unit. -/

import D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
import D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
import Mathlib.RingTheory.Coprime.Basic
import D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
import D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Norm.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import D5.S3.Factorization.Galois.CubicRadicalTowerDegree
import D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial
open D5.S1.Scale
open D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
open NumberField IsDedekindDomain
open scoped WithZero

namespace D5.S3.Factorization.Galois.GoldenCubicCompleteUnitObstruction

set_option maxHeartbeats 800000

/-- The actual earlier primary factors, their conjugates, and two and three generate
an extension of the full prescribed degree, in which the cubic cyclotomic unit
remains noncube. The selected primary factors retain their actual oriented products. -/
theorem golden_cubic_complete_degree_and_unit_obstruction (j : ℕ) :
    let K := CyclotomicField 3 ℚ
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
    let L := AlgebraicClosure K
    let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 K := Classical.choice eisenstein_cyclotomic_equiv_exists
    let B : ℕ → ℕ := fun i => blockNorm ((goldenLucas (3 ^ i) - 1).toNat)
    let S : Finset ℕ := (Finset.Ico 1 j).biUnion (fun i => (B i).primeFactors)
    let I := ({p : ℕ // p ∈ S} × Bool) ⊕ Fin 2
    ∃ π : ℕ → EisensteinOrder, ∃ root : I → L,
      (∀ p ∈ S,
        (Ideal.span {π p}).IsPrime ∧ QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
        (3 : EisensteinOrder) ∣ π p - 1 ∧ p % 3 = 1 ∧
        IsCoprime (π p) (star (π p))) ∧
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
        IsCoprime (π p) (π q) ∧ IsCoprime (π p) (star (π q)) ∧
        IsCoprime (star (π p)) (π q) ∧ IsCoprime (star (π p)) (star (π q))) ∧
      (∀ i, 1 ≤ i → i < j →
        orientedFactor ((goldenLucas (3 ^ i) - 1).toNat) =
          ∏ p ∈ (B i).primeFactors,
            π p ^ padicValNat p (Nat.fib (fibonacciRank p))) ∧
      (∀ v : I, root v ^ 3 = algebraMap K L
        ((Sum.elim (fun w => φ (if w.2 then star (π w.1.val) else π w.1.val))
          (fun k => if k.val = 0 then (2 : 𝓞 K) else 3) v) : K)) ∧
      Module.finrank K (IntermediateField.adjoin K (Set.range root)) =
        3 ^ (2 * S.card + 2) ∧
      (∀ x : IntermediateField.adjoin K (Set.range root),
        x ^ 3 ≠ algebraMap K (IntermediateField.adjoin K (Set.range root))
          (IsCyclotomicExtension.zeta 3 ℚ K)) ∧
      IsGalois K (IntermediateField.adjoin K (Set.range root)) ∧
      ∃ e : ((IntermediateField.adjoin K (Set.range root)) ≃ₐ[K]
          (IntermediateField.adjoin K (Set.range root))) ≃*
          (I → Multiplicative (ZMod 3)),
        ∀ σ : (IntermediateField.adjoin K (Set.range root)) ≃ₐ[K]
            (IntermediateField.adjoin K (Set.range root)), ∀ i : I,
          σ (⟨root i, IntermediateField.subset_adjoin K (Set.range root) ⟨i, rfl⟩⟩ :
              IntermediateField.adjoin K (Set.range root)) =
            algebraMap K (IntermediateField.adjoin K (Set.range root))
              (IsCyclotomicExtension.zeta 3 ℚ K) ^
              (Multiplicative.toAdd (e σ i)).val *
                (⟨root i, IntermediateField.subset_adjoin K (Set.range root) ⟨i, rfl⟩⟩ :
                  IntermediateField.adjoin K (Set.range root)) := by
  classical
  have full_support_selection (j : ℕ) :
      let B : ℕ → ℕ := fun i => blockNorm ((goldenLucas (3 ^ i) - 1).toNat)
      let S : Finset ℕ := (Finset.Ico 1 j).biUnion (fun i => (B i).primeFactors)
      ∃ π : ℕ → EisensteinOrder,
        (∀ p ∈ S,
          (Ideal.span {π p}).IsPrime ∧
          QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ π p - 1 ∧
          p % 3 = 1 ∧
          IsCoprime (π p) (star (π p))) ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
          IsCoprime (π p) (π q) ∧ IsCoprime (π p) (star (π q)) ∧
          IsCoprime (star (π p)) (π q) ∧ IsCoprime (star (π p)) (star (π q))) ∧
        (∀ i, 1 ≤ i → i < j →
          orientedFactor ((goldenLucas (3 ^ i) - 1).toNat) =
            ∏ p ∈ (B i).primeFactors,
              π p ^ padicValNat p (Nat.fib (fibonacciRank p))) := by
    classical
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    let φ := Classical.choice eisenstein_cyclotomic_equiv_exists
    letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
    let b : ℕ → ℕ := fun i => (goldenLucas (3 ^ i) - 1).toNat
    let B : ℕ → ℕ := fun i => blockNorm (b i)
    let η : ℕ → EisensteinOrder := fun i => orientedFactor (b i)
    let S : Finset ℕ := (Finset.Ico 1 j).biUnion (fun i => (B i).primeFactors)
    have hB (i : ℕ) (hi : 1 ≤ i) : B i = (goldenLucas (3 ^ i) ^ 2 + 3).natAbs := by
      let x : ℤ := goldenLucas (3 ^ i)
      have hp : 0 < 3 ^ i := pow_pos (by decide) i
      let n := 3 ^ i - 1
      have hn : n + 1 = 3 ^ i := by dsimp [n]; omega
      have hxpos : 0 < x := by
        change 0 < goldenLucas (3 ^ i)
        rw [← hn, golden_lucas_succ_eq_fib_add_fib]
        have hf : 0 < Nat.fib (n + 2) := Nat.fib_pos.mpr (by omega)
        have hf0 : 0 < (Nat.fib (n + 2) : ℤ) := by exact_mod_cast hf
        have hn0 : 0 ≤ (Nat.fib n : ℤ) := Nat.cast_nonneg _
        omega
      have hbcast : (b i : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
      have hcast : (B i : ℤ) = x ^ 2 + 3 := by
        simp only [B, blockNorm, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [hbcast]
        ring
      have h := congrArg Int.natAbs hcast
      simpa only [Int.natAbs_natCast, x] using h
    have hdisjoint (i k p : ℕ) (hi : 1 ≤ i) (hk : 1 ≤ k)
        (hpi : p ∈ (B i).primeFactors) (hpk : p ∈ (B k).primeFactors) : i = k := by
      by_contra hik
      have hcop := cubic_block_native_power_periods.2.1 i k hi hk hik
      change (goldenLucas (3 ^ i) ^ 2 + 3).natAbs.Coprime
        (goldenLucas (3 ^ k) ^ 2 + 3).natAbs at hcop
      rw [← hB i hi, ← hB k hk] at hcop
      have hd : p ∣ (B i).gcd (B k) :=
        Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpi) (Nat.dvd_of_mem_primeFactors hpk)
      rw [hcop.gcd_eq_one] at hd
      exact (Nat.prime_of_mem_primeFactors hpi).not_dvd_one hd
    let f : ℕ → ℕ → EisensteinOrder := fun i =>
      if hi : 1 ≤ i then
        Classical.choose (golden_cubic_primary_product i hi).2.2.2.2
      else fun _ => 1
    have hf (i : ℕ) (hi : 1 ≤ i) :=
      Classical.choose_spec (golden_cubic_primary_product i hi).2.2.2.2
    let layer (p : {p : ℕ // p ∈ S}) : ℕ :=
      Classical.choose (Finset.mem_biUnion.mp p.property)
    have hlayer (p : {p : ℕ // p ∈ S}) :
        layer p ∈ Finset.Ico 1 j ∧ p.val ∈ (B (layer p)).primeFactors :=
      Classical.choose_spec (Finset.mem_biUnion.mp p.property)
    let π : ℕ → EisensteinOrder := fun p =>
      if hp : p ∈ S then f (layer ⟨p, hp⟩) p else 1
    have hselect (i p : ℕ) (hi : 1 ≤ i) (hij : i < j)
        (hp : p ∈ (B i).primeFactors) : π p = f i p := by
      have hpS : p ∈ S := Finset.mem_biUnion.mpr ⟨i, Finset.mem_Ico.mpr ⟨hi, hij⟩, hp⟩
      have hl := hlayer ⟨p, hpS⟩
      have hieq : layer ⟨p, hpS⟩ = i :=
        hdisjoint _ _ p (Finset.mem_Ico.mp hl.1).1 hi hl.2 hp
      simp only [π, dif_pos hpS, hieq]
    have hdatum (p : ℕ) (hp : p ∈ S) :
        (Ideal.span {π p}).IsPrime ∧
        QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
        (3 : EisensteinOrder) ∣ π p - 1 ∧ p % 3 = 1 ∧
        IsCoprime (π p) (star (π p)) := by
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨hi1, hij⟩ := Finset.mem_Ico.mp hi
      have hfi := hf i hi1
      change _ ∧ _ at hfi
      have hsel := hselect i p hi1 hij hpi
      have hfip := hfi.1 p hpi
      simp only [f, dif_pos hi1] at hsel
      rw [hsel]
      obtain ⟨hprime, huniq, hspan, hnorm, hprimary, hpmod⟩ := hfip
      have hdiv : (Classical.choose (golden_cubic_primary_product i hi1).2.2.2.2) p ∣ η i := by
        apply Ideal.mem_span_singleton.mp
        rw [hspan]
        exact (le_sup_left : orientedIdeal (b i) ≤ orientedIdeal (b i) ⊔
          Ideal.span {(p : EisensteinOrder)}) (Ideal.subset_span (Set.mem_singleton _))
      have hstarDiv := map_dvd (starRingEnd EisensteinOrder) hdiv
      have hcop : IsCoprime (η i) (star (η i)) :=
        (Ideal.isCoprime_span_singleton_iff _ _).mp
          (golden_cubic_primary_product i hi1).2.2.2.1
      exact ⟨hspan.symm ▸ hprime, hnorm, hprimary, hpmod,
        IsCoprime.mono hdiv hstarDiv hcop⟩
    change ∃ π : ℕ → EisensteinOrder, _
    refine ⟨π, hdatum, ?_, ?_⟩
    · intro p hp q hq hpq
      have hnP : π p * star (π p) = (p : EisensteinOrder) := by
        rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, (hdatum p hp).2.1]
        rfl
      have hnQ : π q * star (π q) = (q : EisensteinOrder) := by
        rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, (hdatum q hq).2.1]
        rfl
      have hdP : π p ∣ (p : EisensteinOrder) := ⟨star (π p), hnP.symm⟩
      have hdQ : π q ∣ (q : EisensteinOrder) := ⟨star (π q), hnQ.symm⟩
      have hdsP : star (π p) ∣ (p : EisensteinOrder) := ⟨π p, by rw [mul_comm]; exact hnP.symm⟩
      have hdsQ : star (π q) ∣ (q : EisensteinOrder) := ⟨π q, by rw [mul_comm]; exact hnQ.symm⟩
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨k, hk, hqk⟩ := Finset.mem_biUnion.mp hq
      have hNat : p.Coprime q :=
        (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpi)
          (Nat.prime_of_mem_primeFactors hqk)).mpr hpq
      have hCop : IsCoprime (p : EisensteinOrder) (q : EisensteinOrder) := by
        simpa only [Int.cast_natCast] using (hNat.isCoprime.intCast (R := EisensteinOrder))
      exact ⟨IsCoprime.mono hdP hdQ hCop, IsCoprime.mono hdP hdsQ hCop,
        IsCoprime.mono hdsP hdQ hCop, IsCoprime.mono hdsP hdsQ hCop⟩
    · intro i hi hij
      have hfi := hf i hi
      convert hfi.2 using 1
      apply Finset.prod_congr rfl
      intro p hp
      rw [hselect i p hi hij hp]
      simp only [f, dif_pos hi]

  have actual_two_row :
      let K := CyclotomicField 3 ℚ
      let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 K := Classical.choice eisenstein_cyclotomic_equiv_exists
      ∃ V : HeightOneSpectrum (𝓞 K),
        V.asIdeal = Ideal.span {(2 : 𝓞 K)} ∧
        WithZero.log (V.valuation K (2 : K)) = -1 ∧
        V.valuation K (3 : K) = 1 ∧
        ∀ p : ℕ, p.Prime → p % 3 = 1 → ∀ a : EisensteinOrder,
          QuadraticAlgebra.norm a = (p : ℤ) → V.valuation K (φ a : K) = 1 := by
    let K := CyclotomicField 3 ℚ
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
    let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 K := Classical.choice eisenstein_cyclotomic_equiv_exists
    letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
    have h2E0 : (2 : EisensteinOrder) ≠ 0 := by
      intro h
      have hi := congrArg QuadraticAlgebra.re h
      norm_num [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.re_zero] at hi
    have h2O0 : (2 : 𝓞 K) ≠ 0 := by norm_num
    have h2Eprime : (Ideal.span {(2 : EisensteinOrder)}).IsPrime :=
      (inert_eisenstein_quotient_frobenius 2 (by decide)).1.isPrime
    have hφ2 : φ (2 : EisensteinOrder) = (2 : 𝓞 K) := map_ofNat φ.toRingHom 2
    have h2prime : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
      apply (Ideal.span_singleton_prime h2O0).mpr
      rw [← hφ2]
      exact (MulEquiv.prime_iff φ).mpr ((Ideal.span_singleton_prime h2E0).mp h2Eprime)
    let V : HeightOneSpectrum (𝓞 K) := {
      asIdeal := Ideal.span {(2 : 𝓞 K)}
      isPrime := h2prime
      ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact h2O0
    }
    letI : V.asIdeal.IsPrime := h2prime
    have h2Mem : (2 : 𝓞 K) ∈ V.asIdeal := Ideal.subset_span (Set.mem_singleton _)
    refine ⟨V, rfl, ?_, ?_, ?_⟩
    · have hcoe : ((2 : 𝓞 K) : K) = (2 : K) := by
        rw [RingOfIntegers.coe_eq_algebraMap]
        exact map_ofNat (algebraMap (𝓞 K) K) 2
      rw [← hcoe, HeightOneSpectrum.valuation_of_algebraMap, V.intValuation_singleton h2O0 rfl]
      rfl
    · have hcoe : ((3 : 𝓞 K) : K) = (3 : K) := by
        rw [RingOfIntegers.coe_eq_algebraMap]
        exact map_ofNat (algebraMap (𝓞 K) K) 3
      rw [← hcoe]
      apply (V.valuation_eq_one_iff_notMem (K := K)).mpr
      exact Ideal.IsPrime.notMem_of_isCoprime_of_mem
        (show IsCoprime (2 : 𝓞 K) 3 from ⟨-1, 1, by ring⟩) h2Mem
    · intro p hp hpmod a hnorm
      apply (V.valuation_eq_one_iff_notMem (K := K)).mpr
      have hn : a * star a = (p : EisensteinOrder) := by
        rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hnorm]
        rfl
      have hd : a ∣ (p : EisensteinOrder) := ⟨star a, hn.symm⟩
      have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hpmod
      have hNat : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
      have hcopNat : IsCoprime (p : EisensteinOrder) 2 := by
        obtain ⟨r, s, hrs⟩ := hNat.isCoprime
        refine ⟨(r : EisensteinOrder), (s : EisensteinOrder), ?_⟩
        exact_mod_cast hrs
      have hcop : IsCoprime (φ (2 : EisensteinOrder)) (φ a) :=
        (IsCoprime.mono hd dvd_rfl hcopNat).symm.map φ.toRingHom
      rw [hφ2] at hcop
      exact Ideal.IsPrime.notMem_of_isCoprime_of_mem hcop h2Mem

  have lambda_prime_and_square :
      let lam : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
      (Ideal.span {lam}).IsPrime ∧ lam ^ 2 = -(3 : EisensteinOrder) := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    letI : IsPrincipalIdealRing (𝓞 (CyclotomicField 3 ℚ)) :=
      IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
    let φ := Classical.choice eisenstein_cyclotomic_equiv_exists
    letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
    letI : IsPrincipalIdealRing EisensteinOrder :=
      IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
    let lam : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
    have hlam0 : lam ≠ 0 := by
      intro h
      have hi := congrArg QuadraticAlgebra.im h
      norm_num [lam, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at hi
    have hnorm : Algebra.norm ℤ lam = 3 := by
      rw [Algebra.norm_apply]
      change (DistribSMul.toLinearMap ℤ EisensteinOrder lam).det = 3
      rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
      norm_num [lam, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    have hPrime : Prime lam := by
      apply Ideal.prime_of_irreducible_absNorm_span hlam0
      rw [Ideal.absNorm_span_singleton, hnorm]
      change Irreducible (3 : ℕ)
      exact Nat.irreducible_iff_prime.mpr (Nat.prime_iff.mp Nat.prime_three)
    refine ⟨(Ideal.span_singleton_prime hlam0).mpr hPrime, ?_⟩
    apply QuadraticAlgebra.ext
    · norm_num [lam, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    · norm_num [lam, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

  have actual_three_row :
      let K := CyclotomicField 3 ℚ
      let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 K := Classical.choice eisenstein_cyclotomic_equiv_exists
      let lam : 𝓞 K := φ (1 + 2 * QuadraticAlgebra.omega)
      ∃ V : HeightOneSpectrum (𝓞 K),
        V.asIdeal = Ideal.span {lam} ∧
        WithZero.log (V.valuation K (3 : K)) = -2 ∧
        V.valuation K (2 : K) = 1 ∧
        ∀ x : EisensteinOrder, (3 : EisensteinOrder) ∣ x - 1 →
          V.valuation K (φ x : K) = 1 := by
    let K := CyclotomicField 3 ℚ
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
    let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 K := Classical.choice eisenstein_cyclotomic_equiv_exists
    letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
    let lamE : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
    let lam : 𝓞 K := φ lamE
    obtain ⟨hPrimeE, hSqE⟩ := lambda_prime_and_square
    have hE0 : lamE ≠ 0 := by
      intro h
      have hi := congrArg QuadraticAlgebra.im h
      norm_num [lamE, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_ofNat,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at hi
    have h0 : lam ≠ 0 := by
      simpa only [lam, map_zero] using φ.injective.ne hE0
    have hPrime : (Ideal.span {lam}).IsPrime := by
      apply (Ideal.span_singleton_prime h0).mpr
      exact (MulEquiv.prime_iff φ).mpr ((Ideal.span_singleton_prime hE0).mp hPrimeE)
    have hφ3 : φ (3 : EisensteinOrder) = (3 : 𝓞 K) := map_ofNat φ.toRingHom 3
    have hSq : lam ^ 2 = -(3 : 𝓞 K) := by
      simpa only [lam, lamE, map_pow, map_neg, hφ3] using congrArg φ hSqE
    let V : HeightOneSpectrum (𝓞 K) := {
      asIdeal := Ideal.span {lam}
      isPrime := hPrime
      ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0
    }
    letI : V.asIdeal.IsPrime := hPrime
    have hThreeMem : (3 : 𝓞 K) ∈ V.asIdeal := by
      have h := V.asIdeal.pow_mem_of_mem (Ideal.subset_span (Set.mem_singleton lam)) 2 (by decide)
      rw [hSq] at h
      exact V.asIdeal.neg_mem_iff.mp h
    have hLogLam : WithZero.log (V.valuation K (lam : K)) = -1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap,
        V.intValuation_singleton h0 rfl]
      rfl
    have hLog3 : WithZero.log (V.valuation K (3 : K)) = -2 := by
      have hSqK : (lam : K) ^ 2 = -(3 : K) := by
        exact congrArg (fun t : 𝓞 K => (t : K)) hSq
      have h := congrArg (fun t : K => WithZero.log (V.valuation K t)) hSqK
      rw [map_pow, WithZero.log_pow, Valuation.map_neg, hLogLam] at h
      norm_num at h
      exact h.symm
    have hTwoNotMem : (2 : 𝓞 K) ∉ V.asIdeal :=
      Ideal.IsPrime.notMem_of_isCoprime_of_mem
        (show IsCoprime (3 : 𝓞 K) 2 from ⟨1, -1, by ring⟩) hThreeMem
    refine ⟨V, rfl, hLog3,
      (V.valuation_eq_one_iff_notMem (K := K)).mpr hTwoNotMem, ?_⟩
    intro x hx
    apply (V.valuation_eq_one_iff_notMem (K := K)).mpr
    intro hxMem
    change φ x ∈ V.asIdeal at hxMem
    have hxDiv : (3 : 𝓞 K) ∣ φ x - 1 := by
      have hd := map_dvd φ.toRingHom hx
      change φ (3 : EisensteinOrder) ∣ φ (x - 1) at hd
      rw [hφ3, map_sub, map_one] at hd
      exact hd
    have hxMinus : φ x - 1 ∈ V.asIdeal := V.asIdeal.mem_of_dvd hxDiv hThreeMem
    have hOne : (1 : 𝓞 K) ∈ V.asIdeal := by
      simpa only [sub_sub_cancel] using V.asIdeal.sub_mem hxMem hxMinus
    exact hPrime.one_notMem hOne

  classical
  let K := CyclotomicField 3 ℚ
  let L := AlgebraicClosure K
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
  let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 K := Classical.choice eisenstein_cyclotomic_equiv_exists
  letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
  let B : ℕ → ℕ := fun i => blockNorm ((goldenLucas (3 ^ i) - 1).toNat)
  let S : Finset ℕ := (Finset.Ico 1 j).biUnion (fun i => (B i).primeFactors)
  obtain ⟨π, hπ, hcross, hfactor⟩ := full_support_selection j
  let δ := {p : ℕ // p ∈ S} × Bool
  let a : δ → EisensteinOrder := fun v => if v.2 then star (π v.1.val) else π v.1.val
  have haNorm (v : δ) : QuadraticAlgebra.norm (a v) = (v.1.val : ℤ) := by
    cases hb : v.2 <;> simpa only [a, hb, Bool.false_eq_true, ↓reduceIte,
      QuadraticAlgebra.norm_star] using (hπ v.1.val v.1.property).2.1
  have ha0 (v : δ) : a v ≠ 0 := by
    intro hz
    have hnorm := haNorm v
    rw [hz] at hnorm
    have hp0 : v.1.val ≠ 0 := by
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp v.1.property
      exact (Nat.prime_of_mem_primeFactors hpi).ne_zero
    apply hp0
    simpa only [QuadraticAlgebra.norm_zero, Nat.cast_eq_zero] using hnorm.symm
  have haPrime (v : δ) : (Ideal.span {a v}).IsPrime := by
    apply (Ideal.span_singleton_prime (ha0 v)).mpr
    have hpp : Prime (π v.1.val) := by
      have hπ0 : π v.1.val ≠ 0 := by
        have hn := (hπ v.1.val v.1.property).2.1
        intro hz
        rw [hz, QuadraticAlgebra.norm_zero] at hn
        obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp v.1.property
        have hp0 := (Nat.prime_of_mem_primeFactors hpi).ne_zero
        apply hp0
        exact_mod_cast hn.symm
      exact (Ideal.span_singleton_prime hπ0).mp (hπ v.1.val v.1.property).1
    cases hb : v.2
    · simpa only [a, hb, Bool.false_eq_true, ↓reduceIte] using hpp
    · simp only [a, hb, ↓reduceIte]
      change Prime ((starRingAut : RingAut EisensteinOrder) (π v.1.val))
      exact (MulEquiv.prime_iff (starRingAut : RingAut EisensteinOrder)).mpr hpp
  have haCop (u v : δ) (hne : u ≠ v) : IsCoprime (a u) (a v) := by
    rcases u with ⟨p, b⟩
    rcases v with ⟨q, c⟩
    by_cases hp : p = q
    · subst q
      cases b <;> cases c
      · exact False.elim (hne rfl)
      · simpa only [a, Bool.false_eq_true, ↓reduceIte] using (hπ p.val p.property).2.2.2.2
      · simpa only [a, Bool.false_eq_true, ↓reduceIte] using ((hπ p.val p.property).2.2.2.2).symm
      · exact False.elim (hne rfl)
    · have hpval : p.val ≠ q.val := fun h => hp (Subtype.ext h)
      have h := hcross p.val p.property q.val q.property hpval
      cases b <;> cases c
      · simpa only [a, Bool.false_eq_true, ↓reduceIte] using h.1
      · simpa only [a, Bool.false_eq_true, ↓reduceIte] using h.2.1
      · simpa only [a, Bool.false_eq_true, ↓reduceIte] using h.2.2.1
      · simpa only [a, Bool.false_eq_true, ↓reduceIte] using h.2.2.2
  have hφa0 (v : δ) : φ (a v) ≠ 0 := by
    simpa only [map_zero] using φ.injective.ne (ha0 v)
  have hφprime (v : δ) : (Ideal.span {φ (a v)}).IsPrime := by
    apply (Ideal.span_singleton_prime (hφa0 v)).mpr
    exact (MulEquiv.prime_iff φ).mpr ((Ideal.span_singleton_prime (ha0 v)).mp (haPrime v))

  have hpPrime (u : δ) : u.1.val.Prime := by
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp u.1.property
    exact Nat.prime_of_mem_primeFactors hpi
  have haPrimary (u : δ) : (3 : EisensteinOrder) ∣ a u - 1 := by
    have hp := (hπ u.1.val u.1.property).2.2.1
    cases hb : u.2
    · simpa only [a, hb, Bool.false_eq_true, ↓reduceIte] using hp
    · have hs := map_dvd (starRingEnd EisensteinOrder) hp
      change star (3 : EisensteinOrder) ∣ star (π u.1.val - 1) at hs
      simpa only [a, hb, ↓reduceIte, star_ofNat, star_sub, star_one] using hs
  let V (u : δ) : HeightOneSpectrum (𝓞 K) := {
    asIdeal := Ideal.span {φ (a u)}
    isPrime := hφprime u
    ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hφa0 u
  }
  have hVsupp (u v : δ) (hne : u ≠ v) :
      (V u).valuation K (φ (a v) : K) = 1 := by
    letI : (V u).asIdeal.IsPrime := hφprime u
    apply ((V u).valuation_eq_one_iff_notMem (K := K)).mpr
    exact Ideal.IsPrime.notMem_of_isCoprime_of_mem
      ((haCop u v hne).map φ.toRingHom)
      (Ideal.subset_span (Set.mem_singleton _))
  have hVsmall (u : δ) (ell : ℕ) (hell : ell.Prime) (huell : u.1.val ≠ ell) :
      (V u).valuation K (ell : K) = 1 := by
    letI : (V u).asIdeal.IsPrime := hφprime u
    have hcoe : ((ell : 𝓞 K) : K) = (ell : K) := by norm_cast
    rw [← hcoe]
    apply ((V u).valuation_eq_one_iff_notMem (K := K)).mpr
    have hn : a u * star (a u) = (u.1.val : EisensteinOrder) := by
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, haNorm u]
      rfl
    have hd : a u ∣ (u.1.val : EisensteinOrder) := ⟨star (a u), hn.symm⟩
    have hNat : u.1.val.Coprime ell := (Nat.coprime_primes (hpPrime u) hell).mpr huell
    have hcopN : IsCoprime (u.1.val : EisensteinOrder) (ell : EisensteinOrder) := by
      obtain ⟨r, s, hrs⟩ := hNat.isCoprime
      refine ⟨(r : EisensteinOrder), (s : EisensteinOrder), ?_⟩
      exact_mod_cast hrs
    have hcop : IsCoprime (φ (a u)) (φ (ell : EisensteinOrder)) :=
      (IsCoprime.mono hd dvd_rfl hcopN).map φ.toRingHom
    have hφell : φ (ell : EisensteinOrder) = (ell : 𝓞 K) := map_natCast φ.toRingHom ell
    rw [hφell] at hcop
    exact Ideal.IsPrime.notMem_of_isCoprime_of_mem hcop
      (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨V2, hV2ideal, hV2log, hV2three, hV2supp⟩ := actual_two_row
  obtain ⟨V3, hV3ideal, hV3log, hV3two, hV3supp⟩ := actual_three_row
  let I := δ ⊕ Fin 2
  let rad : I → 𝓞 K := Sum.elim (fun u => φ (a u))
    (fun k => if k.val = 0 then 2 else 3)
  let ν : I → Valuation K (WithZero (Multiplicative ℤ)) :=
    Sum.elim (fun u => (V u).valuation K)
      (fun k => if k.val = 0 then V2.valuation K else V3.valuation K)
  have hrad (i : I) : (rad i : K) ≠ 0 := by
    cases i with
    | inl u => exact RingOfIntegers.coe_injective.ne (hφa0 u)
    | inr k => fin_cases k <;> norm_num [rad]
  have hdiag (i : I) : ¬ (3 : ℤ) ∣ WithZero.log (ν i (rad i : K)) := by
    cases i with
    | inl u =>
      change ¬ (3 : ℤ) ∣ WithZero.log ((V u).valuation K (φ (a u) : K))
      have hlog : WithZero.log ((V u).valuation K (φ (a u) : K)) = -1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap,
          (V u).intValuation_singleton (hφa0 u) rfl]
        rfl
      rw [hlog]
      norm_num
    | inr k =>
      fin_cases k
      · change ¬ (3 : ℤ) ∣ WithZero.log (V2.valuation K (2 : K))
        rw [hV2log]
        norm_num
      · change ¬ (3 : ℤ) ∣ WithZero.log (V3.valuation K (3 : K))
        rw [hV3log]
        norm_num
  have hoff (i k : I) (hik : i ≠ k) : ν i (rad k : K) = 1 := by
    cases i with
    | inl u =>
      cases k with
      | inl v => exact hVsupp u v (fun h => hik (congrArg Sum.inl h))
      | inr k =>
        have hpmod := (hπ u.1.val u.1.property).2.2.2.1
        fin_cases k
        · change (V u).valuation K (2 : K) = 1
          apply hVsmall u 2 Nat.prime_two
          intro h
          rw [h] at hpmod
          norm_num at hpmod
        · change (V u).valuation K (3 : K) = 1
          apply hVsmall u 3 Nat.prime_three
          intro h
          rw [h] at hpmod
          norm_num at hpmod
    | inr i =>
      cases k with
      | inl u =>
        fin_cases i
        · change V2.valuation K (φ (a u) : K) = 1
          exact hV2supp u.1.val (hpPrime u) (hπ u.1.val u.1.property).2.2.2.1 (a u) (haNorm u)
        · change V3.valuation K (φ (a u) : K) = 1
          exact hV3supp (a u) (haPrimary u)
      | inr k =>
        fin_cases i <;> fin_cases k
        · exact False.elim (hik rfl)
        · exact hV2three
        · exact hV3two
        · exact False.elim (hik rfl)
  let root : I → L := fun i => Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (algebraMap K L (rad i : K)) (by decide : 0 < 3))
  have hroot (i : I) : root i ^ 3 = algebraMap K L (rad i : K) :=
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (algebraMap K L (rad i : K)) (by decide : 0 < 3))
  let ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
  have hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hp := hζ.pow_eq_one
    rw [hz] at hp
    norm_num at hp
  have hζnoncube : ¬ ∃ x : K, x ^ 3 = ζ := by
    rintro ⟨x, hx⟩
    have hnot : x ^ 3 ≠ 1 := by
      rw [hx]
      exact hζ.ne_one (by decide)
    have h9 : x ^ 9 = 1 := by
      calc
        x ^ 9 = (x ^ 3) ^ 3 := by ring
        _ = ζ ^ 3 := by rw [hx]
        _ = 1 := hζ.pow_eq_one
    have horder : orderOf x = 9 := by
      have h := orderOf_eq_prime_pow (p := 3) (n := 1)
        (by simpa only [pow_one] using hnot)
        (by simpa only [show (3 : ℕ) ^ (1 + 1) = 9 by decide] using h9)
      norm_num at h
      exact h
    have hroot9 : IsPrimitiveRoot x 9 := IsPrimitiveRoot.iff_orderOf.mpr horder
    have hdiv : 9 ∣ 2 * 3 := hroot9.dvd_of_isCyclotomicExtension 3 (by decide)
    norm_num at hdiv
  have hζval (i : I) : WithZero.log (ν i ζ) = 0 := by
    have h := congrArg WithZero.log (congrArg (ν i) hζ.pow_eq_one)
    simp only [map_pow, map_one, WithZero.log_pow, nsmul_eq_mul,
      WithZero.log_one] at h
    have h3 : (3 : ℤ) * WithZero.log (ν i ζ) = 0 := by simpa using h
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  have hdeg :=
    D5.S3.Factorization.Galois.CubicRadicalTowerDegree.finite_valuation_degree_and_unit_noncube ζ hζ
    (fun i : I => (rad i : K)) root hroot hrad ν hdiag hoff
    ζ hζ0 hζnoncube hζval
  have hradNoncube (i : I) (c : K) : c ^ 3 ≠ (rad i : K) := by
    intro hc
    have hv := congrArg (ν i) hc
    have hlog := congrArg WithZero.log hv
    simp only [map_pow, WithZero.log_pow, nsmul_eq_mul] at hlog
    have hdiv : (3 : ℤ) ∣ WithZero.log (ν i (rad i : K)) :=
      ⟨WithZero.log (ν i c), hlog.symm⟩
    exact hdiag i hdiv
  have hdegree : Module.finrank K (IntermediateField.adjoin K (Set.range root)) =
      3 ^ Fintype.card I := by
    simpa only [I, δ, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_bool, Fintype.card_fin, mul_comm] using hdeg.1
  let radK : I → K := fun i => (rad i : K)
  have hcoordinates :
    IsGalois K (IntermediateField.adjoin K (Set.range root)) ∧
      ∃ e : ((IntermediateField.adjoin K (Set.range root)) ≃ₐ[K] (IntermediateField.adjoin K (Set.range root))) ≃*
          (I → Multiplicative (ZMod 3)),
        ∀ σ : (IntermediateField.adjoin K (Set.range root)) ≃ₐ[K] (IntermediateField.adjoin K (Set.range root)), ∀ i : I,
          σ (⟨root i, IntermediateField.subset_adjoin K (Set.range root) ⟨i, rfl⟩⟩ : IntermediateField.adjoin K (Set.range root)) = algebraMap K (IntermediateField.adjoin K (Set.range root)) ζ ^
            (Multiplicative.toAdd (e σ i)).val * (⟨root i, IntermediateField.subset_adjoin K (Set.range root) ⟨i, rfl⟩⟩ : IntermediateField.adjoin K (Set.range root)) := by
    have single_radical_splitting
        {L' : Type} [Field L'] [Algebra K L']
        (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (a : K) (α : L')
        (hα : α ^ 3 = algebraMap K L' a)
        (H : Irreducible (X ^ 3 - C a)) :
        IsSplittingField K (IntermediateField.adjoin K {α}) (X ^ 3 - C a) := by
      have hζ' : (primitiveRoots 3 K).Nonempty :=
        ⟨ζ, (mem_primitiveRoots (by decide : 0 < 3)).mpr hζ⟩
      have hpoly : aeval α (X ^ 3 - C a) = 0 := by simp [hα]
      have hint : IsIntegral K α :=
        ⟨X ^ 3 - C a, monic_X_pow_sub_C _ (by decide : 3 ≠ 0), hpoly⟩
      have hmin : X ^ 3 - C a = minpoly K α :=
        minpoly.eq_of_irreducible_of_monic H hpoly
          (monic_X_pow_sub_C _ (by decide : 3 ≠ 0))
      letI : Fact (Irreducible (X ^ 3 - C a)) := ⟨H⟩
      letI : IsSplittingField K (AdjoinRoot (X ^ 3 - C a)) (X ^ 3 - C a) :=
        isSplittingField_AdjoinRoot_X_pow_sub_C hζ' H
      let equiv : AdjoinRoot (X ^ 3 - C a) ≃ₐ[K] IntermediateField.adjoin K {α} :=
        (AdjoinRoot.algEquivOfEq K _ _ hmin).trans
          (IntermediateField.adjoinRootEquivAdjoin K hint)
      exact IsSplittingField.of_algEquiv (IntermediateField.adjoin K {α}) (X ^ 3 - C a) equiv

    -- Coordinates are restrictions to the actual one-radical subfields, then pinned Kummer coordinates.

    classical
    let M := IntermediateField.adjoin K (Set.range root)
    let β : I → M := fun i => ⟨root i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
    let p : I → K[X] := fun i => X ^ 3 - C (radK i)
    have hirr (i : I) : Irreducible (p i) :=
      (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_three).mpr (hradNoncube i)
    let t : I → IntermediateField K L := fun i => IntermediateField.adjoin K {root i}
    letI : ∀ i, IsSplittingField K (t i) (p i) := fun i =>
      single_radical_splitting ζ hζ (radK i) (root i) (hroot i) (hirr i)
    letI : ∀ i, Normal K (t i) := fun i => Normal.of_isSplittingField (p i)
    have hsup : (⨆ i, t i) = M := by
      apply le_antisymm
      · apply iSup_le
        intro i
        apply IntermediateField.adjoin_le_iff.mpr
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
      · apply IntermediateField.adjoin_le_iff.mpr
        rintro x ⟨i, rfl⟩
        exact (le_iSup t i) (IntermediateField.mem_adjoin_simple_self K (root i))
    letI : Normal K M := hsup ▸ inferInstance
    letI : IsGalois K M := {
      to_isSeparable := inferInstance
      to_normal := inferInstance
    }
    letI : FiniteDimensional K M := Module.finite_of_finrank_pos (by rw [hdegree]; positivity)
    let F : I → IntermediateField K M := fun i => IntermediateField.adjoin K {β i}
    have hβ (i : I) : β i ^ 3 = algebraMap K M (radK i) := by
      apply Subtype.ext
      exact hroot i
    letI : ∀ i, IsSplittingField K (F i) (p i) := fun i =>
      single_radical_splitting ζ hζ (radK i) (β i) (hβ i) (hirr i)
    letI : ∀ i, Normal K (F i) := fun i => Normal.of_isSplittingField (p i)
    let coordinate : (M ≃ₐ[K] M) →* (I → Multiplicative (ZMod 3)) :=
      MonoidHom.pi (fun i => (autEquivZmod (hirr i) (F i) hζ).toMonoidHom.comp
        (AlgEquiv.restrictNormalHom (F i)))
    have hinj : Function.Injective coordinate := by
      intro σ τ hστ
      apply AlgEquiv.coe_toAlgHom_injective
      apply IntermediateField.adjoin_algHom_ext K
      intro x hx
      rcases hx with ⟨i, rfl⟩
      have hi := congrFun hστ i
      change autEquivZmod (hirr i) (F i) hζ (σ.restrictNormal (F i)) =
        autEquivZmod (hirr i) (F i) hζ (τ.restrictNormal (F i)) at hi
      have hr := (autEquivZmod (hirr i) (F i) hζ).injective hi
      have h := congrArg (fun f : F i ≃ₐ[K] F i => (f (IntermediateField.AdjoinSimple.gen K (β i)) : M)) hr
      simpa only [AlgEquiv.restrictNormal_apply, IntermediateField.AdjoinSimple.coe_gen,
        β, AlgEquiv.coe_toAlgHom] using h
    have hcard : Nat.card (M ≃ₐ[K] M) = Nat.card (I → Multiplicative (ZMod 3)) := by
      rw [IsGalois.card_aut_eq_finrank]
      change Module.finrank K (IntermediateField.adjoin K (Set.range root)) = _
      rw [hdegree]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_multiplicative, ZMod.card]
    have hbij : Function.Bijective coordinate :=
      (Nat.bijective_iff_injective_and_card coordinate).mpr ⟨hinj, hcard⟩
    let e := MulEquiv.ofBijective coordinate hbij
    change IsGalois K M ∧ ∃ e : (M ≃ₐ[K] M) ≃* (I → Multiplicative (ZMod 3)), _
    refine ⟨inferInstance, e, ?_⟩
    intro σ i
    let m : ℕ := (Multiplicative.toAdd (coordinate σ i)).val
    have hα : (IntermediateField.AdjoinSimple.gen K (β i)) ^ 3 =
        algebraMap K (F i) (radK i) := by
      apply Subtype.ext
      exact hβ i
    have h := autEquivZmod_symm_apply_natCast (hirr i) (F i) hα hζ m
    have hcast : Multiplicative.ofAdd (m : ZMod 3) = coordinate σ i := by
      simp only [m, ZMod.natCast_zmod_val]
      rfl
    rw [hcast] at h
    change (autEquivZmod (hirr i) (F i) hζ).symm
        ((autEquivZmod (hirr i) (F i) hζ) (σ.restrictNormal (F i)))
          (IntermediateField.AdjoinSimple.gen K (β i)) = _ at h
    rw [MulEquiv.symm_apply_apply] at h
    have hh := congrArg (fun y : F i => (y : M)) h
    rw [IntermediateField.coe_smul, AlgEquiv.restrictNormal_apply] at hh
    change σ (β i) = algebraMap K M ζ ^ m * β i
    simpa only [IntermediateField.AdjoinSimple.coe_gen, Algebra.smul_def, map_pow, β] using hh
  obtain ⟨hgal, e, he⟩ := hcoordinates
  change ∃ π : ℕ → EisensteinOrder, ∃ root : I → L, _
  refine ⟨π, root, hπ, hcross, hfactor, ?_, ?_, ?_, hgal, ⟨e, he⟩⟩
  · intro v
    cases v with
    | inl u => exact hroot (Sum.inl u)
    | inr k =>
      fin_cases k
      · exact hroot (Sum.inr 0)
      · have h := hroot (Sum.inr 1)
        change root (Sum.inr 1) ^ 3 = algebraMap K L ((3 : 𝓞 K) : K) at h
        have hcoe : ((3 : 𝓞 K) : K) = (3 : K) := by
          rw [RingOfIntegers.coe_eq_algebraMap]
          exact map_ofNat (algebraMap (𝓞 K) K) 3
        rw [hcoe] at h
        exact h
  · simpa only [I, δ, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_bool, Fintype.card_fin, mul_comm] using hdeg.1
  · exact hdeg.2

end D5.S3.Factorization.Galois.GoldenCubicCompleteUnitObstruction
