/- GID: D5/S3/Factorization/Galois/GoldenCubicCommonCompletionAndGalois
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCommonCompletionAndGalois
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact local ramification, Galois, and different computations for the actual common golden cubic fields. -/

/-
Completion-map constructions adapt Tau Ceti's Apache-2.0 source
TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean at revision
33c2099c678ea391f7ea3e0ddaf945a76a625e5d.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026tamedifferent.md.
-/
import Mathlib.RingTheory.Radical.Basic
import Mathlib.Data.Nat.Squarefree
import D5.S3.Factorization.Dedekind.TameDifferent
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import D5.S1.Scale.GoldenCubicBlockCongruences
import D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial
open D5.S1.Scale
open D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower

open D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
open NumberField IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Valued WithZeroTopology Pointwise
open UniqueFactorizationMonoid NumberField.InfinitePlace

namespace D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants


universe u v w

set_option maxHeartbeats 200000
theorem actual_common_cubic_three_completion_collapses (J : ℕ) :
    ∃ hK : NumberField ComplexBase, ∃ hN : NumberField (complexTower J),
    letI := hK
    letI := hN
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ComplexBase))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J))),
      v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) →
      w.asIdeal.LiesOver v.asIdeal →
      ∃ f : v.adicCompletion ComplexBase →+* w.adicCompletion (complexTower J),
        (∀ x : ComplexBase,
          f (algebraMap ComplexBase (v.adicCompletion ComplexBase) x) =
            algebraMap (complexTower J) (w.adicCompletion (complexTower J))
              (algebraMap ComplexBase (complexTower J) x)) ∧
        Continuous f ∧ Function.Surjective f := by
  have one_add_nine_int_is_three_adic_cube (a : ℤ) :
      ∃ r : ℤ_[3], r ^ 3 = ((1 + 9 * a : ℤ) : ℤ_[3]) := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let q : ℤ[X] := X + C 3 * X ^ 2 + C 3 * X ^ 3 - C a
    have hqeval : q.aeval (a : ℤ_[3]) = ((3 * a ^ 2 + 3 * a ^ 3 : ℤ) : ℤ_[3]) := by
      simp [q, map_ofNat] <;> ring
    have hqder : q.derivative.aeval (a : ℤ_[3]) =
        ((1 + 6 * a + 9 * a ^ 2 : ℤ) : ℤ_[3]) := by
      simp [q, map_ofNat] <;> ring
    have hdunit : IsCoprime (1 + 6 * a + 9 * a ^ 2) (3 : ℤ) := by
      refine ⟨1, -(2 * a + 3 * a ^ 2), ?_⟩
      ring
    have hdNorm : ‖((1 + 6 * a + 9 * a ^ 2 : ℤ) : ℤ_[3])‖ = 1 :=
      PadicInt.norm_intCast_eq_one_iff.mpr hdunit
    have hnorm : ‖q.aeval (a : ℤ_[3])‖ < ‖q.derivative.aeval (a : ℤ_[3])‖ ^ 2 := by
      rw [hqeval, hqder, hdNorm, one_pow]
      apply PadicInt.norm_intCast_lt_one_iff.mpr
      exact ⟨a ^ 2 + a ^ 3, by ring⟩
    obtain ⟨z, hz, hclose, hnormz, huniq⟩ := hensels_lemma hnorm
    have hzEq : z + 3 * z ^ 2 + 3 * z ^ 3 - (a : ℤ_[3]) = 0 := by
      simpa [q, map_ofNat] using hz
    refine ⟨1 + 3 * z, ?_⟩
    push_cast
    linear_combination 9 * hzEq
  have actual_golden_block_three_adic_cube (j : ℕ) (hj : 1 ≤ j) :
      ∃ r : ℤ_[3], r ^ 3 = (block j : ℤ_[3]) := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let b : ℤ := goldenLucas (3 ^ j) ^ 2 + 3
    have hmod : (b : ZMod 9) = 1 := (golden_cubic_lucas_block j hj).2.2.1
    have hdiv : (9 : ℤ) ∣ b - 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (b - 1) 9).mp (by simp [hmod])
    obtain ⟨a, ha⟩ := hdiv
    have hb : b = 1 + 9 * a := by linarith
    obtain ⟨r, hr⟩ := one_add_nine_int_is_three_adic_cube a
    refine ⟨r, ?_⟩
    have hcast : (block j : ℤ) = b := by
      have hnonneg : 0 ≤ goldenLucas (3 ^ j) ^ 2 + 3 := by positivity
      simp [block, b, abs_of_nonneg hnonneg]
    have hcastP : (block j : ℤ_[3]) = (b : ℤ_[3]) := by
      exact_mod_cast hcast
    rw [hcastP, hb]
    exact hr

  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K := ComplexBase
  let N := complexTower J
  letI : Algebra ℚ K := K.algebra'
  have hω : IsPrimitiveRoot omega 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      3 ℚ ℂ K hω).2 rfl
  have hKdegree : Module.finrank ℚ K = 2 := by
    have h := IsCyclotomicExtension.finrank K
      (cyclotomic.irreducible_rat (by decide : 0 < 3))
    norm_num at h ⊢
    exact h
  letI : FiniteDimensional ℚ K :=
    FiniteDimensional.of_finrank_pos (by rw [hKdegree]; decide)
  letI : FiniteDimensional K N := FiniteDimensional.of_finrank_pos (by
    rw [golden_cubic_block_positive_root_tower_degree J]; positivity)
  letI : FiniteDimensional ℚ N := Module.Finite.trans K N
  letI : NumberField K := ⟨⟩
  letI : NumberField N := ⟨⟩
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro v w hv hw
  letI : v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) := hv
  letI : w.asIdeal.LiesOver v.asIdeal := hw
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨3, Nat.prime_three⟩
  have hv0 : v0.asIdeal = Ideal.span {(3 : ℤ)} := by
    change (Ideal.span {(3 : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
    simp [Ideal.map_span]
  letI : v.asIdeal.LiesOver v0.asIdeal := hv0.symm ▸ hv
  let Qv := v0.adicCompletion ℚ
  let Kv := v.adicCompletion K
  let Nw := w.adicCompletion N
  letI : CharZero Kv := Algebra.charZero_of_charZero K Kv
  letI : CharZero Nw := Algebra.charZero_of_charZero N Nw
  letI : FaithfulSMul ℤ (𝓞 K) :=
    FaithfulSMul.of_field_isFractionRing ℤ (𝓞 K) ℚ K
  letI : FaithfulSMul (𝓞 K) (𝓞 N) :=
    FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 N) K N
  have hucQK := uniformContinuous_algebraMap_liesOver (K := ℚ) (L := K) v0 v
  have hucKN := uniformContinuous_algebraMap_liesOver (K := K) (L := N) v w
  let fQK : Qv →+* Kv :=
    (adicCompletion.equiv K v).symm.toRingHom.comp <|
      (UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v0.valuation ℚ)) (WithVal (v.valuation K)))
        hucQK.continuous).comp (adicCompletion.equiv ℚ v0).toRingHom
  let fKN : Kv →+* Nw :=
    (adicCompletion.equiv N w).symm.toRingHom.comp <|
      (UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation N)))
        hucKN.continuous).comp (adicCompletion.equiv K v).toRingHom
  have hQK (x : ℚ) : fQK (algebraMap ℚ Qv x) =
      algebraMap K Kv (algebraMap ℚ K x) := by
    apply adicCompletion.ext
    change UniformSpace.Completion.map
      (algebraMap (WithVal (v0.valuation ℚ)) (WithVal (v.valuation K)))
      (UniformSpace.Completion.coeRingHom ((WithVal.equiv (v0.valuation ℚ)).symm x)) =
      UniformSpace.Completion.coeRingHom
        ((WithVal.equiv (v.valuation K)).symm (algebraMap ℚ K x))
    exact (UniformSpace.Completion.map_coe hucQK
      ((WithVal.equiv (v0.valuation ℚ)).symm x)).trans
      (congrArg (UniformSpace.Completion.coeRingHom (α := WithVal (v.valuation K))) (by
        rw [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]
        rfl))
  have hKN (x : K) : fKN (algebraMap K Kv x) =
      algebraMap N Nw (algebraMap K N x) := by
    apply adicCompletion.ext
    change UniformSpace.Completion.map
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation N)))
      (UniformSpace.Completion.coeRingHom ((WithVal.equiv (v.valuation K)).symm x)) =
      UniformSpace.Completion.coeRingHom
        ((WithVal.equiv (w.valuation N)).symm (algebraMap K N x))
    exact (UniformSpace.Completion.map_coe hucKN
      ((WithVal.equiv (v.valuation K)).symm x)).trans
      (congrArg (UniformSpace.Completion.coeRingHom (α := WithVal (w.valuation N))) (by
        rw [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]
        rfl))
  have hcont : Continuous fKN := by
    have h : (fKN : Kv → Nw) = adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map
          (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation N))) ∘
          adicCompletion.toCompletion := by
      funext x
      have hx : (fKN x).toCompletion = UniformSpace.Completion.map
          (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation N)))
          x.toCompletion := rfl
      rw [Function.comp_apply, Function.comp_apply, ← hx,
        adicCompletion.ofCompletion_toCompletion]
    rw [h]
    exact (adicCompletion.continuous_ofCompletion N w).comp
      (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v))
  let fAlg : Kv →ₐ[K] Nw := { fKN with commutes' := hKN }
  letI : Algebra Kv Nw := fKN.toAlgebra
  letI : IsScalarTower K Kv Nw := IsScalarTower.of_algHom fAlg
  letI : ContinuousSMul Kv Nw := by
    apply continuousSMul_of_algebraMap
    exact hcont
  let eQ : ℚ_[3] ≃A[ℚ] Qv := Padic.adicCompletionEquiv ℤ ⟨3, Nat.prime_three⟩
  let ζ : K := ⟨omega, IntermediateField.subset_adjoin ℚ {omega} (Set.mem_singleton omega)⟩
  have hζ : IsPrimitiveRoot ζ 3 := by
    apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap K ℂ)
      (hf := (algebraMap K ℂ).injective)
    exact hω
  let ζM : Nw := algebraMap N Nw (algebraMap K N ζ)
  have hζM : IsPrimitiveRoot ζM 3 :=
    (hζ.map_of_injective (algebraMap K N).injective).map_of_injective
      (algebraMap N Nw).injective
  have hblock0 (j : ℕ) : block j ≠ 0 := by
    change (goldenLucas (3 ^ j) ^ 2 + 3).natAbs ≠ 0
    have hp : 0 < goldenLucas (3 ^ j) ^ 2 + (3 : ℤ) := by positivity
    exact Int.natAbs_ne_zero.mpr hp.ne'
  have hrootcube (j : ℕ) : positiveRoot j ^ 3 = (block j : ℂ) := by
    change (((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 = (block j : ℂ)
    rw [← Complex.ofReal_pow]
    simpa using congrArg (fun x : ℝ => (x : ℂ))
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j))
        (by decide : (3 : ℕ) ≠ 0))
  let internalS : Set N := {x | (x : ℂ) ∈ D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J}
  have hImageS : N.val '' internalS = D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, IntermediateField.subset_adjoin K (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J) hx⟩, hx, rfl⟩
  have hgenS : IntermediateField.adjoin K internalS = ⊤ := by
    apply IntermediateField.map_injective N.val
    rw [IntermediateField.adjoin_map, hImageS, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    rfl
  have hAlgGen : Algebra.adjoin K internalS = ⊤ := by
    have h := congrArg IntermediateField.toSubalgebra hgenS
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x hx => (IsIntegral.of_finite K x).isAlgebraic)] at h
    exact h
  have hgenerator (t : N) (ht : t ∈ internalS) : algebraMap N Nw t ∈ fKN.range := by
    obtain ⟨j, hj, hjJ, htj⟩ := ht
    obtain ⟨r, hr⟩ := actual_golden_block_three_adic_cube j hj
    have hrQ : (r : ℚ_[3]) ^ 3 = (block j : ℚ_[3]) := by
      simpa only [PadicInt.coe_pow, PadicInt.coe_natCast] using
        congrArg (fun x : ℤ_[3] => (x : ℚ_[3])) hr
    let a : Kv := fQK (eQ (r : ℚ_[3]))
    have ha : a ^ 3 = (block j : Kv) := by
      change (fQK (eQ (r : ℚ_[3]))) ^ 3 = _
      rw [← map_pow, ← map_pow, hrQ]
      simp
    have ha0 : a ≠ 0 := by
      intro h
      have hb : (block j : Kv) = 0 := by simpa [h] using ha.symm
      exact (Nat.cast_ne_zero.mpr (hblock0 j)) hb
    have ht : t ^ 3 = (block j : N) := by
      apply Subtype.ext
      simpa [htj] using hrootcube j
    have hratio : (algebraMap N Nw t / fKN a) ^ 3 = 1 := by
      rw [div_pow, ← map_pow, ht, ← map_pow, ha]
      have hfcast : fKN (block j : Kv) = (block j : Nw) := map_natCast fKN (block j)
      rw [map_natCast, hfcast]
      exact div_self (show (block j : Nw) ≠ 0 from Nat.cast_ne_zero.mpr (hblock0 j))
    obtain ⟨k, hk, heq⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one
      (R := Nw) (ζ := ζM) (ξ := algebraMap N Nw t / fKN a) hζM hratio
    change ∃ x : Kv, fKN x = algebraMap N Nw t
    let z : Kv := algebraMap K Kv ζ
    have hz : fKN z = ζM := hKN ζ
    have hmul : fKN (z ^ k * a) = ζM ^ k * fKN a := by
      exact (fKN.map_mul (z ^ k) a).trans
        (congrArg (fun y : Nw => y * fKN a)
          ((fKN.map_pow z k).trans (congrArg (fun y : Nw => y ^ k) hz)))
    refine Exists.intro (z ^ k * a) ?_
    calc
      fKN (z ^ k * a) = ζM ^ k * fKN a := hmul
      _ = algebraMap N Nw t := by
        rw [heq]
        exact div_mul_cancel₀ _ (by
          simpa only [map_zero] using fKN.injective.ne ha0)
  have hglobal (x : N) : algebraMap N Nw x ∈ fKN.range := by
    have hx : x ∈ Algebra.adjoin K internalS := by
      rw [hAlgGen]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hgenerator x hx
    | algebraMap r => exact ⟨algebraMap K Kv r, hKN r⟩
    | add x y hx hy hx' hy' =>
        rw [map_add]
        exact fKN.range.add_mem hx' hy'
    | mul x y hx hy hx' hy' =>
        rw [map_mul]
        exact fKN.range.mul_mem hx' hy'
  let lin : Kv →ₗ[Kv] Nw := Algebra.linearMap Kv Nw
  have hdense : DenseRange lin := by
    apply (w.denseRange_algebraMap N).mono
    rintro _ ⟨x, rfl⟩
    exact hglobal x
  have hclosed : IsClosed (Set.range lin) := by
    rw [← lin.coe_range]
    exact lin.range.closed_of_finiteDimensional
  have hsurj : Function.Surjective fKN := by
    change Function.Surjective lin
    rw [← Set.range_eq_univ, ← hclosed.closure_eq]
    exact hdense.closure_range
  exact ⟨fKN, hKN, hcont, hsurj⟩

set_option maxHeartbeats 200000
theorem actual_common_cubic_three_completion_and_ramification (J : ℕ) :
    ∃ hK : NumberField ComplexBase, ∃ hN : NumberField (complexTower J),
    letI := hK
    letI := hN
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ComplexBase))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J))),
      v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) →
      w.asIdeal.LiesOver v.asIdeal →
      ∃ f : v.adicCompletion ComplexBase →+* w.adicCompletion (complexTower J),
        (∀ x : ComplexBase,
          f (algebraMap ComplexBase (v.adicCompletion ComplexBase) x) =
            algebraMap (complexTower J) (w.adicCompletion (complexTower J))
              (algebraMap ComplexBase (complexTower J) x)) ∧
        Continuous f ∧ Function.Surjective f ∧
        w.asIdeal.ramificationIdx (𝓞 ComplexBase) = 1 := by
  classical
  obtain ⟨hK, hN, hcomplete⟩ := actual_common_cubic_three_completion_collapses J
  refine ⟨hK, hN, ?_⟩
  letI := hK
  letI := hN
  intro v w hv hw
  let K := ComplexBase
  let N := complexTower J
  let Kv := v.adicCompletion K
  let Nw := w.adicCompletion N
  letI : w.asIdeal.LiesOver v.asIdeal := hw
  letI : FaithfulSMul (𝓞 K) (𝓞 N) :=
    FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 N) K N
  obtain ⟨f, hfK, hfcont, hfsurj⟩ := hcomplete v w hv hw
  let iK : K →+* Kv := algebraMap K Kv
  let iN : N →+* Nw := algebraMap N Nw
  let e : ℕ := v.asIdeal.ramificationIdx' w.asIdeal
  have heIndex : e = w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot
  have hvalK (x : K) : Valued.v (iK x) = v.valuation K x := by
    change Valued.v (x : Kv) = _
    exact adicCompletion.valued_coe K v x
  have hvalN (x : N) : Valued.v (iN x) = w.valuation N x := by
    change Valued.v (x : Nw) = _
    exact adicCompletion.valued_coe N w x
  have hcontK : Continuous (Valued.v : Kv → WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)
  have hcontN : Continuous (Valued.v : Nw → WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective N)
  have hvalCompletion (x : Kv) : Valued.v (f x) = Valued.v x ^ e := by
    have hEq := (v.denseRange_algebraMap K).equalizer
      (hcontN.comp hfcont) (hcontK.pow e) (by
        funext a
        simp only [Function.comp_apply]
        rw [hfK a]
        change Valued.v (iN (algebraMap K N a)) = Valued.v (iK a) ^ e
        rw [hvalN, hvalK]
        exact (valuation_liesOver (K := K) N v w a).symm)
    exact congrFun hEq x
  obtain ⟨y, hy⟩ := w.valuedAdicCompletion_surjective N (WithZero.exp (1 : ℤ))
  obtain ⟨x, hx⟩ := hfsurj y
  have hpower := hvalCompletion x
  rw [hx, hy] at hpower
  have hlog := congrArg WithZero.log hpower
  simp only [WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at hlog
  have heDiv : (e : ℤ) ∣ 1 := ⟨WithZero.log (Valued.v x), hlog⟩
  have heDivNat : e ∣ 1 := by exact_mod_cast heDiv
  have heOne : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    heIndex.symm.trans (Nat.dvd_one.mp heDivNat)
  exact ⟨f, hfK, hfcont, hfsurj, heOne⟩

theorem actual_common_cubic_three_residue_degree_one (J : ℕ) :
    ∃ hK : NumberField ComplexBase, ∃ hN : NumberField (complexTower J),
    letI := hK
    letI := hN
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ComplexBase))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J))),
      v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) →
      w.asIdeal.LiesOver v.asIdeal → w.asIdeal.inertiaDeg (𝓞 ComplexBase) = 1 := by
  classical
  obtain ⟨hK, hN, hcomplete⟩ := actual_common_cubic_three_completion_and_ramification J
  refine ⟨hK, hN, ?_⟩
  letI := hK
  letI := hN
  intro v w hv hw
  let K := ComplexBase
  let N := complexTower J
  let Kv := v.adicCompletion K
  let Nw := w.adicCompletion N
  letI : w.asIdeal.LiesOver v.asIdeal := hw
  letI : v.asIdeal.IsPrime := v.isPrime
  letI : w.asIdeal.IsPrime := w.isPrime
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  letI : FaithfulSMul (𝓞 K) (𝓞 N) :=
    FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 N) K N
  obtain ⟨f, hfK, hfcont, hfsurj, he⟩ := hcomplete v w hv hw
  let iK : K →+* Kv := algebraMap K Kv
  let iN : N →+* Nw := algebraMap N Nw
  have hvalK (x : K) : Valued.v (iK x) = v.valuation K x := by
    change Valued.v (x : Kv) = _
    exact adicCompletion.valued_coe K v x
  have hvalN (x : N) : Valued.v (iN x) = w.valuation N x := by
    change Valued.v (x : Nw) = _
    exact adicCompletion.valued_coe N w x
  have hcontK : Continuous (Valued.v : Kv → WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)
  have hcontN : Continuous (Valued.v : Nw → WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective N)
  have hval (x : Kv) : Valued.v (f x) = Valued.v x := by
    have hEq := (v.denseRange_algebraMap K).equalizer
      (hcontN.comp hfcont) hcontK (by
        funext a
        simp only [Function.comp_apply]
        rw [hfK a]
        change Valued.v (iN (algebraMap K N a)) = Valued.v (iK a)
        rw [hvalN, hvalK]
        have h := valuation_liesOver (K := K) N v w a
        rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, he, pow_one] at h
        exact h.symm)
    exact congrFun hEq x
  letI : Field ((𝓞 K) ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field ((𝓞 N) ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  have hres : Function.Surjective
      (algebraMap ((𝓞 K) ⧸ v.asIdeal) ((𝓞 N) ⧸ w.asIdeal)) := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, hy⟩ := hfsurj (iN (b : N))
    have hyInt : Valued.v y ≤ 1 := by
      rw [← hval, hy, hvalN]
      exact w.valuation_le_one b
    let U : Set Kv := {x | Valued.v (x - y) < 1}
    have hU : IsOpen U :=
      WithZeroTopology.isOpen_Iio.preimage (hcontK.comp (continuous_sub_right y))
    have hyU : y ∈ U := by
      change Valued.v (y - y) < (1 : WithZero (Multiplicative ℤ))
      rw [sub_self, Valuation.map_zero]
      exact zero_lt_one
    obtain ⟨a, ha⟩ := (v.denseRange_algebraMap K).exists_mem_open hU ⟨y, hyU⟩
    have haClose : Valued.v (iK a - y) < 1 := ha
    have haInt : v.valuation K a ≤ 1 := by
      rw [← hvalK]
      rw [← sub_add_cancel (iK a) y]
      exact Valuation.map_add_le _ haClose.le hyInt
    obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer haInt (1 : (WithZero (Multiplicative ℤ))ˣ)
    have hrClose : Valued.v (iK (algebraMap (𝓞 K) K r) - iK a) < 1 := by
      rw [← iK.map_sub, hvalK]
      exact hr
    have hry : Valued.v (iK (algebraMap (𝓞 K) K r) - y) < 1 := by
      rw [← sub_add_sub_cancel _ (iK a)]
      exact Valuation.map_add_lt _ hrClose haClose
    refine ⟨Ideal.Quotient.mk v.asIdeal r, ?_⟩
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
    apply Ideal.Quotient.eq.mpr
    apply (w.valuation_lt_one_iff_mem (K := N) _).mp
    have h := hval (iK (algebraMap (𝓞 K) K r) - y)
    rw [f.map_sub, hfK, hy] at h
    have hrMap : algebraMap K N (algebraMap (𝓞 K) K r) =
        (algebraMap (𝓞 K) (𝓞 N) r : N) :=
      (IsScalarTower.algebraMap_apply (𝓞 K) K N r).symm.trans
        (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 N) N r)
    change Valued.v (iN (algebraMap K N (algebraMap (𝓞 K) K r)) - iN (b : N)) = _ at h
    rw [hrMap, ← iN.map_sub, hvalN] at h
    exact h.trans_lt hry
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    ⟨(algebraMap ((𝓞 K) ⧸ v.asIdeal) ((𝓞 N) ⧸ w.asIdeal)).injective, hres⟩

set_option maxHeartbeats 200000
theorem actual_common_cubic_q_galois_and_conjugation (J : ℕ) :
    IsGalois ℚ (complexTower J) ∧
    ∃ c : complexTower J ≃ₐ[ℚ] complexTower J,
      (∀ x, (c x : ℂ) = star (x : ℂ)) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
      ∀ σ : complexTower J ≃ₐ[ComplexBase] complexTower J,
        c * σ.restrictScalars ℚ * c = (σ.restrictScalars ℚ)⁻¹ := by
  classical
  let K := ComplexBase
  let N := complexTower J
  let QN := (complexTower J).restrictScalars ℚ
  let S : Set ℂ := {omega} ∪
    D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J
  have hN : QN = IntermediateField.adjoin ℚ S :=
    IntermediateField.adjoin_adjoin_left ℚ {omega}
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
  have homegaN : omega ∈ N := by
    change omega ∈ QN
    exact hN.symm ▸ IntermediateField.subset_adjoin ℚ S (Or.inl (Set.mem_singleton omega))
  have hrootN (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ J) : positiveRoot j ∈ N := by
    change positiveRoot j ∈ QN
    exact hN.symm ▸ IntermediateField.subset_adjoin ℚ S (Or.inr ⟨j, hj, hjJ, rfl⟩)
  have hω : IsPrimitiveRoot omega 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hω0 : omega ≠ 0 := hω.ne_zero (by decide)
  have hconjω : star omega = omega⁻¹ :=
    (Complex.inv_eq_conj (hω.norm'_eq_one (by decide))).symm
  have hblock0 (j : ℕ) : (block j : ℂ) ≠ 0 := by
    have hpos : 0 < goldenLucas (3 ^ j) ^ 2 + (3 : ℤ) := by positivity
    have hn : block j ≠ 0 := by
      change (goldenLucas (3 ^ j) ^ 2 + 3).natAbs ≠ 0
      exact Int.natAbs_ne_zero.mpr hpos.ne'
    exact Nat.cast_ne_zero.mpr hn
  have hrootcube (j : ℕ) : positiveRoot j ^ 3 = (block j : ℂ) := by
    change (((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 = (block j : ℂ)
    rw [← Complex.ofReal_pow]
    simpa using congrArg (fun x : ℝ => (x : ℂ))
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j))
        (by decide : (3 : ℕ) ≠ 0))
  have hroot0 (j : ℕ) : positiveRoot j ≠ 0 := by
    intro h
    exact hblock0 j (by rw [← hrootcube j, h]; simp)
  let z : N := ⟨omega, homegaN⟩
  have hz : IsPrimitiveRoot z 3 := by
    apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap N ℂ)
      (hf := (algebraMap N ℂ).injective)
    exact hω
  have hz0 : z ≠ 0 := hz.ne_zero (by decide)
  let rad : Option (Fin J) → ℚ := fun i =>
    match i with
    | none => 1
    | some i => block (i.val + 1)
  let root : Option (Fin J) → N := fun i =>
    match i with
    | none => 1
    | some i => ⟨positiveRoot (i.val + 1), hrootN _ (by omega) (by omega)⟩
  let p : Option (Fin J) → ℚ[X] := fun i => X ^ 3 - C (rad i)
  let P : ℚ[X] := ∏ i : Option (Fin J), p i
  have hcube (i : Option (Fin J)) : root i ^ 3 = algebraMap ℚ N (rad i) := by
    cases i with
    | none => simp [root, rad]
    | some i =>
      apply Subtype.ext
      simpa [root, rad] using hrootcube (i.val + 1)
  have hp0 (i : Option (Fin J)) : p i ≠ 0 := X_pow_sub_C_ne_zero (by decide) _
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)
  have hsplit (i : Option (Fin J)) : ((p i).map (algebraMap ℚ N)).Splits := by
    simpa only [p, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C] using
      (X_pow_sub_C_splits_of_isPrimitiveRoot hz (hcube i))
  have hPsplit : (P.map (algebraMap ℚ N)).Splits := by
    rw [Polynomial.map_prod]
    exact Polynomial.Splits.prod (fun i _ => hsplit i)
  letI : Module.IsTorsionFree ℚ N := DivisionSemiring.to_moduleIsTorsionFree
  have hproot (i : Option (Fin J)) (t : N) (ht : aeval t (p i) = 0) :
      t ∈ P.rootSet N := by
    rw [mem_rootSet_of_ne hP0]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) ht
  let incl : N →ₐ[ℚ] ℂ := N.val.toRingHom.toRatAlgHom
  have hInclRange : incl.fieldRange = QN := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact t.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hgen : IntermediateField.adjoin ℚ (P.rootSet N) = ⊤ := by
    apply IntermediateField.map_injective incl
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, hInclRange]
    change IntermediateField.adjoin ℚ (Subtype.val '' P.rootSet N) = QN
    apply le_antisymm
    · exact IntermediateField.adjoin_le_iff.mpr
        (by rintro x ⟨t, ht, rfl⟩; exact t.property)
    · apply hN.le.trans
      apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      apply IntermediateField.subset_adjoin
      rcases hx with hx | ⟨j, hj, hjJ, rfl⟩
      · rcases Set.mem_singleton_iff.mp hx with rfl
        refine ⟨z, hproot none z ?_, rfl⟩
        simp [p, rad, hz.pow_eq_one]
      · let i : Fin J := ⟨j - 1, by omega⟩
        let t : N := ⟨positiveRoot j, hrootN j hj hjJ⟩
        have hi : i.val + 1 = j := by dsimp [i]; omega
        refine ⟨t, hproot (some i) t ?_, rfl⟩
        have ht : t ^ 3 = (block j : N) := by
          apply Subtype.ext
          simpa [t] using hrootcube j
        simp [p, rad, hi, ht]
  letI : IsSplittingField ℚ N P :=
    isSplittingField_iff_intermediateField.mpr ⟨hPsplit, hgen⟩
  letI : Normal ℚ N := Normal.of_isSplittingField P
  letI : IsGalois ℚ N := {
    to_isSeparable := inferInstance
    to_normal := inferInstance
  }
  have hclosed (x : ℂ) (hx : x ∈ N) : star x ∈ N := by
    change x ∈ QN at hx
    change star x ∈ QN
    rw [hN] at hx ⊢
    exact IntermediateField.adjoin_induction ℚ (s := S)
      (p := fun x _ => star x ∈ IntermediateField.adjoin ℚ S)
      (by
        intro x hx
        rcases hx with hx | ⟨j, hj, hjJ, rfl⟩
        · rcases Set.mem_singleton_iff.mp hx with rfl
          rw [hconjω]
          exact inv_mem (IntermediateField.subset_adjoin ℚ S
            (Or.inl (Set.mem_singleton omega)))
        · simpa [positiveRoot] using
            IntermediateField.subset_adjoin ℚ S (Or.inr ⟨j, hj, hjJ, rfl⟩))
      (by
        intro r
        simpa using IntermediateField.algebraMap_mem (IntermediateField.adjoin ℚ S) r)
      (by intro x y hx hy hxr hyr; rw [star_add]; exact add_mem hxr hyr)
      (by intro x hx hxr; rw [star_inv₀]; exact inv_mem hxr)
      (by intro x y hx hy hxr hyr; rw [star_mul]; exact mul_mem hyr hxr) hx
  let c : N ≃ₐ[ℚ] N := {
    toFun := fun x => ⟨star (x : ℂ), hclosed x.val x.property⟩
    invFun := fun x => ⟨star (x : ℂ), hclosed x.val x.property⟩
    left_inv := by intro x; apply Subtype.ext; exact star_star (x : ℂ)
    right_inv := by intro x; apply Subtype.ext; exact star_star (x : ℂ)
    map_mul' := by intro x y; apply Subtype.ext; simp
    map_add' := by intro x y; apply Subtype.ext; simp
    commutes' := by intro r; apply Subtype.ext; simp
  }
  have hcz : c z = z⁻¹ := by
    apply Subtype.ext
    exact hconjω
  have hc2 : c ^ 2 = 1 := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact star_star (x : ℂ)
  have hcne : c ≠ 1 := by
    intro h
    have hzz : z⁻¹ = z := hcz.symm.trans (by rw [h]; rfl)
    have hp : z ^ 2 = 1 := by
      calc
        _ = z⁻¹ * z := by rw [pow_two, hzz]
        _ = 1 := inv_mul_cancel₀ hz0
    exact hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) hp
  let internalS : Set N := {x | (x : ℂ) ∈ S}
  have hImageS : incl '' internalS = S := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      have hxN : x ∈ N := by
        change x ∈ QN
        exact hN.symm ▸ IntermediateField.subset_adjoin ℚ S hx
      exact ⟨⟨x, hxN⟩, hx, rfl⟩
  have hgenS : IntermediateField.adjoin ℚ internalS = ⊤ := by
    apply IntermediateField.map_injective incl
    rw [IntermediateField.adjoin_map, hImageS, ← AlgHom.fieldRange_eq_map, hInclRange, ← hN]
  have hAlgGen : Algebra.adjoin ℚ internalS = ⊤ := by
    have h := congrArg IntermediateField.toSubalgebra hgenS
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x hx => (Normal.isIntegral (inferInstance : Normal ℚ N) x).isAlgebraic)] at h
    exact h
  have haction (σ : N ≃ₐ[K] N) :
      c * σ.restrictScalars ℚ * c = (σ.restrictScalars ℚ)⁻¹ := by
    let zk : K := ⟨omega, IntermediateField.subset_adjoin ℚ {omega}
      (Set.mem_singleton omega)⟩
    have hsigmaZ : σ z = z := σ.commutes zk
    have hinverseZ : σ.symm z = z := σ.symm.commutes zk
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top hAlgGen
    intro x hx
    rcases hx with hx | ⟨j, hj, hjJ, hx⟩
    · have hxz : x = z := Subtype.ext (Set.mem_singleton_iff.mp hx)
      subst x
      change c (σ (c z)) = σ.symm z
      rw [hcz, map_inv₀, hsigmaZ, map_inv₀, hcz, inv_inv, hinverseZ]
    · let t : N := ⟨positiveRoot j, hrootN j hj hjJ⟩
      have hxt : x = t := Subtype.ext hx
      subst x
      have htcube : t ^ 3 = (block j : N) := by
        apply Subtype.ext
        simpa [t] using hrootcube j
      have ht0 : t ≠ 0 := by
        intro h
        exact hroot0 j (congrArg Subtype.val h)
      have hct : c t = t := by apply Subtype.ext; simp [c, t, positiveRoot]
      have hσcube : σ t ^ 3 = (block j : N) := by rw [← map_pow, htcube, map_natCast]
      have hr : (σ t / t) ^ 3 = 1 := by
        rw [div_pow, hσcube, htcube, div_self]
        exact Nat.cast_ne_zero.mpr (by
          intro h
          exact hblock0 j (by rw [h]; simp))
      obtain ⟨m, hm, heq⟩ := hz.eq_pow_of_pow_eq_one hr
      have hrot : σ t = z ^ m * t := by
        calc
          _ = (σ t / t) * t := (div_mul_cancel₀ _ ht0).symm
          _ = _ := by rw [heq]
      have hinv : σ.symm t = z⁻¹ ^ m * t := by
        apply σ.injective
        rw [AlgEquiv.apply_symm_apply, map_mul, map_pow, map_inv₀,
          hsigmaZ, hrot]
        simp only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, one_mul]
      change c (σ (c t)) = σ.symm t
      rw [hct, hrot, map_mul, map_pow, hcz, hct, hinv]
  exact ⟨inferInstance, c, (fun _ => rfl), hc2, hcne, haction⟩

set_option maxHeartbeats 200000
theorem actual_common_cubic_conjugation_self_normalizing (J : ℕ) :
    ∃ c : complexTower J ≃ₐ[ℚ] complexTower J,
      (∀ x, (c x : ℂ) = star (x : ℂ)) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
      Subgroup.normalizer (Subgroup.zpowers c : Set _) = Subgroup.zpowers c := by
  classical
  let K := ComplexBase
  let N := complexTower J
  have hω : IsPrimitiveRoot omega 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      3 ℚ ℂ K hω).2 rfl
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have hKdegree : Module.finrank ℚ K = 2 := by
    have h := IsCyclotomicExtension.finrank K
      (cyclotomic.irreducible_rat (by decide : 0 < 3))
    norm_num at h ⊢
    exact h
  letI : FiniteDimensional ℚ K :=
    FiniteDimensional.of_finrank_pos (by rw [hKdegree]; decide)
  letI : FiniteDimensional K N :=
    FiniteDimensional.of_finrank_pos (by
      rw [golden_cubic_block_positive_root_tower_degree J]; positivity)
  letI : FiniteDimensional ℚ N := Module.Finite.trans K N
  obtain ⟨hgalQ, c, hccoe, hc2, hcne, hcinv⟩ :=
    actual_common_cubic_q_galois_and_conjugation J
  letI : IsGalois ℚ N := hgalQ
  let H := N ≃ₐ[K] N
  let G := N ≃ₐ[ℚ] N
  let B := K ≃ₐ[ℚ] K
  let f : H →* G := {
    toFun := fun σ => σ.restrictScalars ℚ
    map_one' := AlgEquiv.ext (fun _ => rfl)
    map_mul' := fun _ _ => AlgEquiv.ext (fun _ => rfl)
  }
  let r : G →* B := AlgEquiv.restrictNormalHom K
  have hfinj : Function.Injective f := by
    intro σ τ h
    exact AlgEquiv.ext (fun x => congrArg (fun t : G => t x) h)
  have hker : f.range = r.ker := by
    ext σ
    constructor
    · rintro ⟨τ, rfl⟩
      change r (f τ) = 1
      apply AlgEquiv.ext
      intro x
      apply (algebraMap K N).injective
      change algebraMap K N ((τ.restrictScalars ℚ).restrictNormal K x) =
        algebraMap K N x
      rw [AlgEquiv.restrictNormal_commutes]
      exact τ.commutes x
    · intro h
      change r σ = 1 at h
      refine ⟨{ σ with commutes' := fun x => ?_ }, AlgEquiv.ext (fun _ => rfl)⟩
      exact (σ.restrictNormal_commutes K x).symm.trans
        (congrArg (algebraMap K N) (AlgEquiv.ext_iff.mp h x))
  let S : GroupExtension H G B := {
    inl := f
    rightHom := r
    inl_injective := hfinj
    range_inl_eq_ker_rightHom := hker
    rightHom_surjective := AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K) (E := N)
  }
  have hBcard : Nat.card B = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hKdegree]
  let ζ : K := ⟨omega, IntermediateField.subset_adjoin ℚ {omega}
    (Set.mem_singleton omega)⟩
  let z : N := algebraMap K N ζ
  have hz : IsPrimitiveRoot z 3 := by
    apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap N ℂ)
      (hf := (algebraMap N ℂ).injective)
    exact hω
  have hz0 : z ≠ 0 := hz.ne_zero (by decide)
  have hcz : c z = z⁻¹ := by
    apply Subtype.ext
    rw [hccoe]
    exact (Complex.inv_eq_conj (hω.norm'_eq_one (by decide))).symm
  have hrcne : r c ≠ 1 := by
    intro h
    have hfix : c z = z := by
      have hh : algebraMap K N (r c ζ) = c z :=
        c.restrictNormal_commutes K ζ
      rw [h] at hh
      exact hh.symm
    have hinv : z⁻¹ = z := hcz.symm.trans hfix
    have hpow : z ^ 2 = 1 := by
      calc
        _ = z⁻¹ * z := by rw [pow_two, hinv]
        _ = 1 := inv_mul_cancel₀ hz0
    exact hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) hpow
  letI : IsGalois K N := IsGalois.tower_top_of_isGalois ℚ K N
  have hHcard : Nat.card H = 3 ^ J := by
    rw [IsGalois.card_aut_eq_finrank]
    exact golden_cubic_block_positive_root_tower_degree J
  have hHodd : (Nat.card H).Coprime 2 := by
    rw [hHcard]
    exact Nat.Coprime.pow_left J (by decide : Nat.Coprime 3 2)
  have hconj : ∀ a : H, c * S.inl a * c = S.inl a⁻¹ := fun a => hcinv a
  have hNorm : Subgroup.normalizer (Subgroup.zpowers c : Set _) = Subgroup.zpowers c := by
    let C := Subgroup.zpowers c
    have hcne : c ≠ 1 := by intro h; exact hrcne (by rw [h, map_one])
    have hcorder : orderOf c = 2 := by
      apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
      refine ⟨hc2, ?_⟩
      intro m hm hpos
      have hm1 : m = 1 := by omega
      simpa [hm1] using hcne
    have hCcases (x : G) (hx : x ∈ C) : x = 1 ∨ x = c := by
      have h := (mem_zpowers_iff_mem_range_orderOf (x := c) (y := x)).mp hx
      rw [hcorder] at h
      rcases Finset.mem_image.mp h with ⟨k, hk, hpow⟩
      have hk2 : k < 2 := Finset.mem_range.mp hk
      interval_cases k <;> simp_all
    have hBcases (b : B) : b = 1 ∨ b = S.rightHom c := by
      by_cases hb : b = 1
      · exact Or.inl hb
      · obtain ⟨b0, hb0, huniq⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hBcard
        exact Or.inr ((huniq b hb).trans (huniq (S.rightHom c) hrcne).symm)
    have hkernel (g : G) (hg : S.rightHom g = 1) (hgc : g * c = c * g) : g = 1 := by
      have hgr : g ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom]
        exact hg
      obtain ⟨a, rfl⟩ := hgr
      have haInv : a = a⁻¹ := by
        apply S.inl_injective
        have h := hconj a
        rw [← hgc, mul_assoc, ← pow_two, hc2, mul_one] at h
        exact h
      have ha2 : a ^ 2 = 1 := by
        calc
          a ^ 2 = a * a⁻¹ := (pow_two a).trans (congrArg (fun t => a * t) haInv)
          _ = 1 := mul_inv_cancel a
      have ha1 : a = 1 := by
        apply (powCoprime hHodd).injective
        change a ^ 2 = (1 : H) ^ 2
        simpa only [one_pow] using ha2
      rw [ha1, map_one]
    apply le_antisymm
    · intro g hg
      have hmem : g * c * g⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp hg c).mp (Subgroup.mem_zpowers c)
      have hgc : g * c = c * g := by
        rcases hCcases _ hmem with h | h
        · have hc1 : c = 1 := by
            have h' := congrArg (fun x : G => g⁻¹ * x * g) h
            simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_inv_cancel, mul_one,
              one_mul] using h'
          exact (hcne hc1).elim
        · have h' := congrArg (fun x : G => x * g) h
          simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'
      rcases hBcases (S.rightHom g) with hb | hb
      · rw [hkernel g hb hgc]
        exact C.one_mem
      · have hker : S.rightHom (g * c) = 1 := by
          rw [map_mul, hb, ← map_mul, ← pow_two, hc2, map_one]
        have hcomm : (g * c) * c = c * (g * c) := by
          calc
            (g * c) * c = g := by rw [mul_assoc, ← pow_two, hc2, mul_one]
            _ = (c * g) * c := by rw [← hgc, mul_assoc, ← pow_two, hc2, mul_one]
            _ = c * (g * c) := mul_assoc c g c
        have hprod := hkernel (g * c) hker hcomm
        have hgeq : g = c := by
          have h' := congrArg (fun x : G => x * c) hprod
          simpa only [mul_assoc, ← pow_two, hc2, mul_one, one_mul] using h'
        rw [hgeq]
        exact Subgroup.mem_zpowers c
    · exact Subgroup.le_normalizer
  exact ⟨c, hccoe, hc2, hcne, hNorm⟩
end D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants

#print axioms D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants.actual_common_cubic_q_galois_and_conjugation
