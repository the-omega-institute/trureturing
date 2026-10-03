/- GID: D5/S3/Factorization/Galois/GoldenCubicCommonInertiaAndSignature
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCommonInertiaAndSignature
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

import D5.S3.Factorization.Galois.GoldenCubicCommonCompletionAndGalois

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
theorem actual_common_cubic_three_prime_orbits (J : ℕ) :
    ∃ hN : NumberField (complexTower J), letI := hN
    ∃ c : complexTower J ≃ₐ[ℚ] complexTower J,
      (∀ x, (c x : ℂ) = star (x : ℂ)) ∧
      ((Ideal.span {(3 : ℤ)}).primesOver (𝓞 (complexTower J))).ncard = 3 ^ J ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J)),
        w.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) →
        w.asIdeal.ramificationIdx ℤ = 2 ∧ w.asIdeal.inertiaDeg ℤ = 1) ∧
      ∃! P : (Ideal.span {(3 : ℤ)}).primesOver (𝓞 (complexTower J)), c • P.val = P.val := by

  classical
  let K := ComplexBase
  let N := complexTower J
  obtain ⟨hK, hN, hcomplete⟩ := actual_common_cubic_three_completion_and_ramification J
  obtain ⟨hK', hN', hres⟩ := actual_common_cubic_three_residue_degree_one J
  letI := hK
  letI := hN
  have hω : IsPrimitiveRoot omega 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      3 ℚ ℂ K hω).2 rfl
  have hKdegree : Module.finrank ℚ K = 2 := by
    have h := IsCyclotomicExtension.finrank K
      (cyclotomic.irreducible_rat (by decide : 0 < 3))
    norm_num at h ⊢
    exact h
  letI : FiniteDimensional K N := FiniteDimensional.of_finrank_pos (by
    rw [golden_cubic_block_positive_root_tower_degree J]; positivity)
  obtain ⟨hgalQ, c0, hc0, hc02, hc0ne, hcinv⟩ :=
    actual_common_cubic_q_galois_and_conjugation J
  letI : IsGalois ℚ N := hgalQ
  obtain ⟨c, hccoe, hc2, hcne, hnorm⟩ :=
    actual_common_cubic_conjugation_self_normalizing J
  let G := N ≃ₐ[ℚ] N
  let H : Subgroup G := Subgroup.zpowers c
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨3, Nat.prime_three⟩
  have hv0 : v0.asIdeal = Ideal.span {(3 : ℤ)} := by
    change (Ideal.span {(3 : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
    simp [Ideal.map_span]
  let p := v0.asIdeal
  letI : p.IsPrime := v0.isPrime
  letI : p.IsMaximal := v0.isPrime.isMaximal v0.ne_bot
  letI : Finite (ℤ ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient v0.ne_bot
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  have hlocal (w : IsDedekindDomain.HeightOneSpectrum (𝓞 N))
      (hw : w.asIdeal.LiesOver p) :
      w.asIdeal.ramificationIdx ℤ = 2 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
    letI : w.asIdeal.LiesOver p := hw
    let v := w.under (𝓞 K)
    letI : w.asIdeal.LiesOver v.asIdeal := Ideal.over_under _
    letI : v.asIdeal.LiesOver p := Ideal.LiesOver.tower_bot w.asIdeal v.asIdeal p
    letI : v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) := hv0 ▸ inferInstance
    obtain ⟨f, hf, hcont, hsurj, he⟩ := hcomplete v w inferInstance inferInstance
    have hfres := hres v w inferInstance inferInstance
    have heK := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime 3 K v.asIdeal
    have hfK := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 3 K v.asIdeal
    constructor
    · rw [Ideal.ramificationIdx_tower v.asIdeal w.asIdeal, heK, he]
    · rw [Ideal.inertiaDeg_tower v.asIdeal w.asIdeal, hfK, hfres]
  have hlocalIdeal (P : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver p] :
      P.ramificationIdx ℤ = 2 ∧ P.inertiaDeg ℤ = 1 :=
    hlocal ⟨P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v0.ne_bot P⟩ inferInstance
  have hcardG : Nat.card G = 2 * 3 ^ J := by
    rw [IsGalois.card_aut_eq_finrank]
    calc
      Module.finrank ℚ N = Module.finrank ℚ K * Module.finrank K N :=
        (Module.finrank_mul_finrank ℚ K N).symm
      _ = 2 * 3 ^ J := by rw [hKdegree, golden_cubic_block_positive_root_tower_degree J]
  obtain ⟨P0, hP0max, hP0over⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) p
  letI : P0.IsMaximal := hP0max
  letI : P0.IsPrime := hP0max.isPrime
  letI : P0.LiesOver p := hP0over
  have hcount : (p.primesOver (𝓞 N)).ncard = 3 ^ J := by
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 N) G
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P0 G,
      Ideal.inertiaDegIn_eq_inertiaDeg p P0 G,
      (hlocalIdeal P0).1, (hlocalIdeal P0).2, hcardG] at h
    omega
  have hstabcard (P : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver p] :
      Nat.card (MulAction.stabilizer G P) = 2 := by
    rw [Ideal.card_stabilizer_eq (G := G) p P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
      Ideal.inertiaDegIn_eq_inertiaDeg p P G,
      (hlocalIdeal P).1, (hlocalIdeal P).2]
  have hcorder : orderOf c = 2 := by
    apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
    refine ⟨hc2, ?_⟩
    intro m hm hpos
    have hm1 : m = 1 := by omega
    simpa [hm1] using hcne
  have hHcard : Nat.card H = 2 := by rw [Nat.card_zpowers, hcorder]
  letI primeAction : MulAction G (p.primesOver (𝓞 N)) := {
    smul := fun σ Q => ⟨σ • Q.val, Q.property.1.smul σ, Q.property.2.smul σ⟩
    one_smul := fun Q => Subtype.ext (one_smul G Q.val)
    mul_smul := fun σ τ Q => Subtype.ext (mul_smul σ τ Q.val)
  }
  letI : MulAction H (p.primesOver (𝓞 N)) :=
    MulAction.compHom (p.primesOver (𝓞 N)) H.subtype
  have hHgroup : IsPGroup 2 H := IsPGroup.of_card (show Nat.card H = 2 ^ 1 by simpa using hHcard)
  have hnotdvd : ¬ 2 ∣ Nat.card (p.primesOver (𝓞 N)) := by
    rw [Nat.card_coe_set_eq, hcount]
    intro h
    exact (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h)
  obtain ⟨P, hP⟩ := hHgroup.nonempty_fixed_point_of_prime_not_dvd_card
    (p.primesOver (𝓞 N)) hnotdvd
  have hPfixed : c • P = P := hP ⟨c, Subgroup.mem_zpowers c⟩
  have hstabeq (Q : p.primesOver (𝓞 N)) (hQ : c • Q = Q) :
      MulAction.stabilizer G Q.val = H := by
    letI : Q.val.IsPrime := Q.property.1
    letI : Q.val.LiesOver p := Q.property.2
    have hle : H ≤ MulAction.stabilizer G Q.val :=
      Subgroup.zpowers_le.mpr (congrArg Subtype.val hQ)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hstabcard, hHcard])).symm
  have huniq (Q : p.primesOver (𝓞 N)) (hQ : c • Q = Q) : Q = P := by
    letI : P.val.IsPrime := P.property.1
    letI : P.val.LiesOver p := P.property.2
    letI : Q.val.IsPrime := Q.property.1
    letI : Q.val.LiesOver p := Q.property.2
    obtain ⟨g, hgval⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P.val Q.val G
    have hg : g • P = Q := Subtype.ext hgval
    have hconj : H.map (MulAut.conj g).toMonoidHom = H := by
      calc
        H.map (MulAut.conj g).toMonoidHom =
            (MulAction.stabilizer G P.val).map (MulAut.conj g).toMonoidHom :=
          congrArg (fun T : Subgroup G => T.map (MulAut.conj g).toMonoidHom)
            (hstabeq P hPfixed).symm
        _ = MulAction.stabilizer G (g • P.val) :=
          (MulAction.stabilizer_smul_eq_stabilizer_map_conj g P.val).symm
        _ = MulAction.stabilizer G Q.val := congrArg (MulAction.stabilizer G) hgval
        _ = H := hstabeq Q hQ
    have hgnorm : g ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj
    have hnormH : Subgroup.normalizer (H : Set G) = H := hnorm
    have hgH : g ∈ H := by rwa [hnormH] at hgnorm
    have hgp : g • P = P := hP ⟨g, hgH⟩
    exact hg.symm.trans hgp
  refine ⟨hN, c, hccoe, ?_, ?_, ?_⟩
  · simpa only [p, hv0] using hcount
  · intro w hw
    have hw' : w.asIdeal.LiesOver p := by
      change w.asIdeal.LiesOver v0.asIdeal
      rwa [hv0]
    exact hlocal w hw'
  · have hfinal : ∃! Q : p.primesOver (𝓞 N), c • Q.val = Q.val := by
      refine ⟨P, congrArg Subtype.val hPfixed, ?_⟩
      intro Q hQ
      exact huniq Q (Subtype.ext hQ)
    change ∃! Q : v0.asIdeal.primesOver (𝓞 N), c • Q.val = Q.val at hfinal
    rw [hv0] at hfinal
    exact hfinal

set_option maxHeartbeats 800000
theorem actual_common_cubic_inertia_unit_coordinates
    (J p : ℕ) [NumberField (complexTower J)] (hp : p.Prime) (hp3 : p ≠ 3)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J)))
    (hw : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    (σ : complexTower J ≃ₐ[ℚ] complexTower J)
    (hσ : σ ∈ w.asIdeal.inertia (complexTower J ≃ₐ[ℚ] complexTower J)) :
    (∀ z : complexTower J, (z : ℂ) = omega → σ z = z) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ J →
      ¬ p ∣ (block j / Nat.floorRoot 3 (block j) ^ 3) →
      ∀ t : complexTower J, (t : ℂ) = positiveRoot j → σ t = t := by
  classical
  let N := complexTower J
  let P := w.asIdeal
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hw
  letI : P.IsPrime := w.isPrime
  let O := 𝓞 N
  let κ := O ⧸ P
  let q : O →+* κ := Ideal.Quotient.mk P
  change ∀ x : O, σ • x - x ∈ P at hσ
  have hnotmem (b : ℤ) (hb : ¬ (p : ℤ) ∣ b) : (b : O) ∉ P := by
    intro h
    apply hb
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) b).mpr
    simpa using h
  have hthree : (3 : κ) ≠ 0 := by
    intro h
    apply hnotmem 3 (by
      intro hdiv
      have hdiv' : p ∣ 3 := by exact_mod_cast hdiv
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdiv'))
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (map_natCast q 3).trans h
  let ζK : ComplexBase := ⟨omega,
    IntermediateField.subset_adjoin ℚ {omega} (Set.mem_singleton omega)⟩
  let ζ : N := algebraMap ComplexBase N ζK
  have hζ : IsPrimitiveRoot ζ 3 := by
    apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap N ℂ)
      (hf := (algebraMap N ℂ).injective)
    exact Complex.isPrimitiveRoot_exp 3 (by decide)
  let zI : O := hζ.toInteger
  have hzI : (zI : N) = ζ := rfl
  have hzIprim : IsPrimitiveRoot zI 3 := hζ.toInteger_isPrimitiveRoot
  have hzIpoly : zI ^ 2 + zI + 1 = 0 := by
    have h := hzIprim.geom_sum_eq_zero (by decide)
    norm_num [Finset.sum_range_succ] at h
    linear_combination h
  have hred3 : (q zI) ^ 3 = 1 := by
    rw [← map_pow, hzIprim.pow_eq_one, map_one]
  have hredne : q zI ≠ 1 := by
    intro h
    have hpoly := congrArg q hzIpoly
    simp only [map_add, map_pow, map_one, map_zero, h] at hpoly
    exact hthree (by norm_num at hpoly ⊢; exact hpoly)
  have hredprimitive : IsPrimitiveRoot (q zI) 3 := by
    apply IsPrimitiveRoot.mk_of_lt _ (by decide) hred3
    intro k hk hk3
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · simpa using hredne
    · intro h2
      apply hredne
      have h := hred3
      rw [pow_succ, h2, one_mul] at h
      exact h
  have hfixUnitCube (x : O) (b : ℤ) (hb : ¬ (p : ℤ) ∣ b)
      (hxcube : x ^ 3 = (b : O)) : σ (x : N) = (x : N) := by
    have hqx0 : q x ≠ 0 := by
      intro h
      have hq := congrArg q hxcube
      rw [map_pow, h, zero_pow (by decide), map_intCast] at hq
      exact hnotmem b hb (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hq.symm))
    have hx0 : (x : N) ≠ 0 := by
      intro h
      have hx : x = 0 := RingOfIntegers.ext h
      exact hqx0 (by rw [hx, map_zero])
    have hxcubeN : (x : N) ^ 3 = (b : N) := by
      simpa only [map_pow, map_intCast] using congrArg (algebraMap O N) hxcube
    have hratio : (σ (x : N) / (x : N)) ^ 3 = 1 := by
      rw [div_pow, ← map_pow, hxcubeN, map_intCast]
      exact div_self (by
        intro hb0
        exact (pow_ne_zero 3 hx0) (hxcubeN.trans hb0))
    obtain ⟨k, hk, hpow⟩ := hζ.eq_pow_of_pow_eq_one hratio
    have hσx : σ (x : N) = ζ ^ k * (x : N) := by
      rw [hpow]
      exact (div_mul_cancel₀ _ hx0).symm
    have hσcoe : algebraMap O N (σ • x) = σ (algebraMap O N x) := by
      have h := smul_distrib_smul σ x (1 : N)
      simpa only [Algebra.smul_def, mul_one, smul_one, AlgEquiv.smul_def] using h.symm
    have hσxO : σ • x = zI ^ k * x := by
      apply RingOfIntegers.ext
      change algebraMap O N (σ • x) = algebraMap O N (zI ^ k * x)
      rw [hσcoe, map_mul, map_pow]
      rw [← RingOfIntegers.coe_eq_algebraMap x,
        ← RingOfIntegers.coe_eq_algebraMap zI, hzI]
      exact hσx
    have hres : q (σ • x) = q x := by
      exact Ideal.Quotient.eq.mpr (hσ x)
    rw [hσxO, map_mul, map_pow] at hres
    have hredpow : (q zI) ^ k = 1 :=
      mul_right_cancel₀ hqx0 (by simpa using hres)
    have hk0 : k = 0 := Nat.eq_zero_of_dvd_of_lt
      (hredprimitive.dvd_of_pow_eq_one k hredpow) hk
    simpa [hk0] using hσx
  constructor
  · intro z hz
    have hzζ : z = ζ := by
      apply Subtype.ext
      exact hz
    rw [hzζ]
    exact hfixUnitCube zI 1 (by
      intro h
      have hpdiv : p ∣ 1 := by exact_mod_cast h
      exact hp.ne_one (Nat.dvd_one.mp hpdiv))
      (by simpa only [Int.cast_one] using hzIprim.pow_eq_one)
  · intro j hj hjJ hpunit t ht
    have hblock0 : block j ≠ 0 := by
      change (goldenLucas (3 ^ j) ^ 2 + 3).natAbs ≠ 0
      have hp : 0 < goldenLucas (3 ^ j) ^ 2 + (3 : ℤ) := by positivity
      exact Int.natAbs_ne_zero.mpr hp.ne'
    let c : ℕ := Nat.floorRoot 3 (block j)
    let d : ℕ := block j / c ^ 3
    have hc0 : c ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by decide, hblock0⟩
    have hfactor : block j = d * c ^ 3 :=
      (Nat.div_mul_cancel (show c ^ 3 ∣ block j from Nat.floorRoot_pow_dvd)).symm
    have ht3 : t ^ 3 = (block j : N) := by
      apply Subtype.ext
      change (t : ℂ) ^ 3 = _
      rw [ht]
      change (((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 = (block j : ℂ)
      rw [← Complex.ofReal_pow]
      simpa using congrArg (fun x : ℝ => (x : ℂ))
        (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j)) (by decide : (3 : ℕ) ≠ 0))
    let x : N := t / (c : N)
    have hxcube : x ^ 3 = (d : N) := by
      change (t / (c : N)) ^ 3 = _
      rw [div_pow, ht3, hfactor]
      push_cast
      exact mul_div_cancel_right₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hc0))
    have hxint : IsIntegral ℤ x :=
      IsIntegral.of_pow (by decide : 0 < 3)
        (hxcube ▸ (show IsIntegral ℤ (d : N) from isIntegral_algebraMap))
    let xI : O := ⟨x, hxint⟩
    have hxcubeO : xI ^ 3 = (d : O) := by
      apply RingOfIntegers.ext
      exact hxcube
    have hpunitInt : ¬ (p : ℤ) ∣ (d : ℤ) := by
      change ¬ p ∣ d at hpunit
      exact_mod_cast hpunit
    have hfix := hfixUnitCube xI d hpunitInt hxcubeO
    have hfixX : σ x = x := hfix
    have hxrecover : x * (c : N) = t := div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hc0)
    calc
      σ t = σ (x * (c : N)) := congrArg σ hxrecover.symm
      _ = σ x * (c : N) := by rw [map_mul, map_natCast]
      _ = t := by rw [hfixX, hxrecover]

set_option maxHeartbeats 800000
theorem actual_common_cubic_inertia_card_le_three
    (J j p : ℕ) [NumberField (complexTower J)]
    (hj : 1 ≤ j) (hjJ : j ≤ J) (hp : p.Prime) (hp3 : p ≠ 3)
    (hpj : p ∣ block j)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J)))
    (hw : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) :
    Nat.card (w.asIdeal.inertia (complexTower J ≃ₐ[ℚ] complexTower J)) ≤ 3 := by
  classical
  let N := complexTower J
  let QN := (complexTower J).restrictScalars ℚ
  let S : Set ℂ := {omega} ∪
    D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J
  have hN : QN = IntermediateField.adjoin ℚ S :=
    IntermediateField.adjoin_adjoin_left ℚ {omega}
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
  let incl : N →ₐ[ℚ] ℂ := N.val.toRingHom.toRatAlgHom
  have hInclRange : incl.fieldRange = QN := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact t.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
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
      (fun x hx => (IsIntegral.of_finite ℚ x).isAlgebraic)] at h
    exact h
  let θ : N := ⟨positiveRoot j,
    IntermediateField.subset_adjoin ComplexBase
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
      ⟨j, hj, hjJ, rfl⟩⟩
  have hθcube : θ ^ 3 = (block j : N) := by
    apply Subtype.ext
    change (((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 = (block j : ℂ)
    rw [← Complex.ofReal_pow]
    simpa using congrArg (fun x : ℝ => (x : ℂ))
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j))
        (by decide : (3 : ℕ) ≠ 0))
  let I := w.asIdeal.inertia (N ≃ₐ[ℚ] N)
  let T := (Polynomial.nthRoots 3 (block j : N)).toFinset
  let f : I → ↥T := fun σ => ⟨σ.val θ, by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_nthRoots (by decide : 0 < 3)).mpr
    rw [← map_pow, hθcube, map_natCast]⟩
  have hinj : Function.Injective f := by
    intro σ τ hστ
    have hθ : σ.val θ = τ.val θ := congrArg Subtype.val hστ
    have hσ := actual_common_cubic_inertia_unit_coordinates J p hp hp3 w hw σ.val σ.property
    have hτ := actual_common_cubic_inertia_unit_coordinates J p hp hp3 w hw τ.val τ.property
    apply Subtype.ext
    have hMaps : σ.val.toAlgHom = τ.val.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hAlgGen
      intro z hz
      rcases hz with hz | hz
      · have hzω : (z : ℂ) = omega := Set.mem_singleton_iff.mp hz
        exact (hσ.1 z hzω).trans (hτ.1 z hzω).symm
      · obtain ⟨i, hi, hiJ, hzi⟩ := hz
        by_cases hij : i = j
        · subst i
          have hzt : z = θ := Subtype.ext hzi
          exact ((congrArg σ.val hzt).trans hθ).trans (congrArg τ.val hzt).symm
        · have hpuniti : ¬ p ∣ block i := by
            intro hpi
            have hc : (block i).Coprime (block j) :=
              D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods.2.1 i j hi hj hij
            have hg := Nat.dvd_gcd hpi hpj
            rw [hc.gcd_eq_one] at hg
            exact hp.ne_one (Nat.dvd_one.mp hg)
          have hpdi : ¬ p ∣ block i / Nat.floorRoot 3 (block i) ^ 3 := by
            intro hpd
            exact hpuniti (hpd.trans (Nat.div_dvd_of_dvd Nat.floorRoot_pow_dvd))
          exact (hσ.2 i hi hiJ hpdi z hzi).trans (hτ.2 i hi hiJ hpdi z hzi).symm
    exact AlgEquiv.ext fun x => DFunLike.congr_fun hMaps x
  letI : Fintype I := Fintype.ofFinite I
  calc
    Nat.card I = Fintype.card I := Nat.card_eq_fintype_card
    _ ≤ Fintype.card ↥T := Fintype.card_le_of_injective f hinj
    _ = T.card := Fintype.card_coe T
    _ ≤ (Polynomial.nthRoots 3 (block j : N)).card := Multiset.toFinset_card_le (Polynomial.nthRoots 3 (block j : N))
    _ ≤ 3 := Polynomial.card_nthRoots 3 (block j : N)

set_option maxHeartbeats 200000
theorem actual_common_cubic_rational_degree_and_signature (J : ℕ) :
    let F := IntermediateField.adjoin ℚ
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
    Module.finrank ℚ (complexTower J) = 2 * 3 ^ J ∧
      Module.finrank ℚ F = 3 ^ J ∧
      ∃ hF : NumberField F,
        @nrRealPlaces F _ hF = 1 ∧
        @nrComplexPlaces F _ hF = (3 ^ J - 1) / 2 := by
  classical
  let F := IntermediateField.adjoin ℚ
    (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
  let K := ComplexBase
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
  letI : FiniteDimensional K (complexTower J) :=
    FiniteDimensional.of_finrank_pos (by
      rw [golden_cubic_block_positive_root_tower_degree J]; positivity)
  letI : FiniteDimensional ℚ (complexTower J) := Module.Finite.trans K (complexTower J)
  letI : Module.Free ℚ K := Module.Free.of_divisionRing ℚ K
  letI : Module.Free K (complexTower J) := Module.Free.of_divisionRing K (complexTower J)
  letI : Module.Free ℚ (complexTower J) := Module.Free.of_divisionRing ℚ (complexTower J)
  have hNdegree : Module.finrank ℚ (complexTower J) = 2 * 3 ^ J := by
    rw [← Module.finrank_mul_finrank ℚ K (complexTower J), hKdegree,
      golden_cubic_block_positive_root_tower_degree J]
  have hrootcube (j : ℕ) : positiveRoot j ^ 3 = (block j : ℂ) := by
    change (((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 = (block j : ℂ)
    rw [← Complex.ofReal_pow]
    simpa using congrArg (fun x : ℝ => (x : ℂ))
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j))
        (by decide : (3 : ℕ) ≠ 0))
  have hrootsFinite :
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J).Finite := by
    apply (Set.finite_range (fun i : Fin J => positiveRoot (i.val + 1))).subset
    rintro z ⟨j, hj, hjJ, rfl⟩
    refine ⟨⟨j - 1, by omega⟩, ?_⟩
    simpa [Nat.sub_add_cancel hj]
  letI := hrootsFinite.fintype
  letI : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro z ⟨j, hj, hjJ, rfl⟩
      refine ⟨X ^ 3 - C (block j : ℚ), monic_X_pow_sub_C (block j : ℚ) (by decide), ?_⟩
      simpa using sub_eq_zero.mpr (hrootcube j))
  letI : NumberField F := {
    to_charZero := inferInstance
    to_finiteDimensional := inferInstance
  }
  let incl : F →+* ℂ := (IntermediateField.val F).toRingHom
  have hreal (x : F) : star (x : ℂ) = (x : ℂ) := by
    rcases x with ⟨x, hx⟩
    exact IntermediateField.adjoin_induction ℚ
      (p := fun z _ => star z = z)
      (by rintro z ⟨j, hj, hjJ, rfl⟩; simp [positiveRoot])
      (by intro r; simp)
      (by intro x y hx hy hxr hyr; simp [map_add, hxr, hyr])
      (by intro x hx hxr; simp [map_inv₀, hxr])
      (by intro x y hx hy hxr hyr; simp [map_mul, hxr, hyr]) hx
  have hincl : ComplexEmbedding.IsReal incl := by
    apply ComplexEmbedding.isReal_iff.mpr
    ext x
    exact hreal x
  have homega_not_real : star omega ≠ omega := by
    intro hrealω
    have hωim : omega.im = 0 := Complex.conj_eq_iff_im.mp hrealω
    have hco : ((omega.re : ℝ) : ℂ) = omega := by
      apply Complex.ext <;> simp [hωim]
    have hp : omega.re ^ 3 = (1 : ℝ) := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_pow, hco, hω.pow_eq_one, Complex.ofReal_one]
    have hr : omega.re = 1 :=
      (by decide : Odd 3).pow_injective (by simpa using hp)
    apply hω.ne_one (by decide)
    rw [← hco, hr, Complex.ofReal_one]
  have homega_not_F : omega ∉ F := by
    intro hx
    exact homega_not_real (hreal ⟨omega, hx⟩)
  let H : IntermediateField ℚ ℂ := K ⊓ F
  letI : Module.Free ℚ H := Module.Free.of_divisionRing ℚ H
  letI : FiniteDimensional ℚ H := FiniteDimensional.of_injective
    (IntermediateField.inclusion (show H ≤ K from inf_le_left)).toLinearMap
    (IntermediateField.inclusion_injective (show H ≤ K from inf_le_left))
  have hdiv : Module.finrank ℚ H ∣ 2 := by
    rw [← hKdegree]
    exact IntermediateField.finrank_dvd_of_le_right (show H ≤ K from inf_le_left)
  have hHdegree : Module.finrank ℚ H = 1 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv with h | h
    · exact h
    · have hHK : H = K := IntermediateField.eq_of_le_of_finrank_eq
        (show H ≤ K from inf_le_left) (h.trans hKdegree.symm)
      have hωK : omega ∈ K :=
        IntermediateField.subset_adjoin ℚ {omega} (Set.mem_singleton omega)
      have hωH : omega ∈ H := hHK.symm ▸ hωK
      exact (homega_not_F hωH.2).elim
  have hInf : K ⊓ F = ⊥ := IntermediateField.finrank_eq_one_iff.mp hHdegree
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have hld : K.LinearDisjoint F := IntermediateField.LinearDisjoint.of_inf_eq_bot hInf
  have hsupdegree : Module.finrank ℚ ↥(K ⊔ F) = 2 * 3 ^ J := by
    rw [← IntermediateField.restrictScalars_adjoin_eq_sup ℚ K
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)]
    exact hNdegree
  have hFdegree : Module.finrank ℚ F = 3 ^ J := by
    have h := hld.finrank_sup
    rw [hKdegree, hsupdegree] at h
    omega
  have hunique (φ : F →+* ℂ) (hφ : ComplexEmbedding.IsReal φ) : φ = incl := by
    have hAlg : φ.toRatAlgHom = incl.toRatAlgHom := by
      apply IntermediateField.adjoin_algHom_ext ℚ
      rintro z ⟨j, hj, hjJ, rfl⟩
      let t : F := ⟨positiveRoot j, IntermediateField.subset_adjoin ℚ
        (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
        ⟨j, hj, hjJ, rfl⟩⟩
      have htcube : t ^ 3 = (block j : F) := by
        apply Subtype.ext
        simpa [t] using hrootcube j
      have hφcube : hφ.embedding t ^ 3 = (block j : ℝ) := by
        rw [← map_pow, htcube, map_natCast]
      have hdesign : ((block j : ℝ) ^ ((3 : ℝ)⁻¹)) ^ 3 = (block j : ℝ) :=
        Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j)) (by decide)
      have htimage : hφ.embedding t = (block j : ℝ) ^ ((3 : ℝ)⁻¹) :=
        (by decide : Odd 3).pow_injective (hφcube.trans hdesign.symm)
      change φ t = (t : ℂ)
      rw [← hφ.coe_embedding_apply, htimage]
      rfl
    exact congrArg AlgHom.toRingHom hAlg
  let realIncl : {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} := ⟨incl, hincl⟩
  have hsub : Subsingleton {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} := by
    refine ⟨fun x y => Subtype.ext ((hunique x.val x.property).trans
      (hunique y.val y.property).symm)⟩
  letI := hsub
  letI : Nonempty {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} := ⟨realIncl⟩
  have hrealCount : nrRealPlaces F = 1 := by
    rw [← card_real_embeddings F]
    exact Fintype.card_eq_one_of_forall_eq (i := realIncl) (fun _ => Subsingleton.elim _ _)
  have hcomplexCount : nrComplexPlaces F = (3 ^ J - 1) / 2 := by
    have h := card_add_two_mul_card_eq_rank F
    rw [hrealCount, hFdegree] at h
    omega
  exact ⟨hNdegree, hFdegree, inferInstance, hrealCount, hcomplexCount⟩
end D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants

#print axioms D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants.actual_common_cubic_rational_degree_and_signature
