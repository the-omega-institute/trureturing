/- GID: D5/S3/Factorization/Galois/GoldenCubicBlockCommonDiscriminants
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicBlockCommonDiscriminants
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual golden cubic fields have explicit signatures, inversion Galois action and exact different-derived discriminants. -/

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

import D5.S3.Factorization.Galois.GoldenCubicCommonDifferentSupport

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

set_option maxHeartbeats 800000

/-- The actual common golden cubic fields have the prescribed Galois structure,
signature, discriminants and root discriminant. -/
theorem golden_cubic_block_common_field_discriminants (J : ℕ) (hJ : 1 ≤ J) :
    let N := complexTower J
    let F := IntermediateField.adjoin ℚ
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
    let R := ∏ j ∈ Finset.Icc 1 J,
      radical (block j / Nat.floorRoot 3 (block j) ^ 3)
    ∃ hN : NumberField N, letI := hN
    ∃ hF : NumberField F, letI := hF
      Module.finrank ℚ N = 2 * 3 ^ J ∧
      Module.finrank ℚ F = 3 ^ J ∧
      nrRealPlaces F = 1 ∧ nrComplexPlaces F = (3 ^ J - 1) / 2 ∧
      (∀ x : F, star (x : ℂ) = (x : ℂ)) ∧
      ¬ NumberField.IsTotallyReal F ∧
      (NumberField.discr N).natAbs = 3 ^ (3 ^ J) * R ^ (4 * 3 ^ (J - 1)) ∧
      (NumberField.discr F).natAbs = 3 ^ ((3 ^ J - 1) / 2) * R ^ (2 * 3 ^ (J - 1)) ∧
      NumberField.rootDiscr N = Real.sqrt 3 * (R : ℝ) ^ (2 / 3 : ℝ) ∧
      IsGalois ℚ N ∧
      (∃ c : N ≃ₐ[ℚ] N,
        (∀ x, (c x : ℂ) = star (x : ℂ)) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
        (∀ σ : N ≃ₐ[ComplexBase] N,
          c * σ.restrictScalars ℚ * c = (σ.restrictScalars ℚ)⁻¹) ∧
        let E : IntermediateField ℚ N := FixedPoints.intermediateField (Subgroup.zpowers c)
        Nonempty (F ≃ₐ[ℚ] E) ∧ Module.finrank E N = 2) ∧
      ∃ φ : Multiplicative (ZMod 2) →* MulAut (Fin J → Multiplicative (ZMod 3)),
        (∀ x, φ (Multiplicative.ofAdd (1 : ZMod 2)) x = x⁻¹) ∧
        Nonempty ((Fin J → Multiplicative (ZMod 3)) ⋊[φ]
          Multiplicative (ZMod 2) ≃* (N ≃ₐ[ℚ] N)) := by
  classical
  let N := complexTower J
  let F := IntermediateField.adjoin ℚ
    (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
  let R := ∏ j ∈ Finset.Icc 1 J,
    radical (block j / Nat.floorRoot 3 (block j) ^ 3)
  obtain ⟨hK, hN, hcomplete⟩ := actual_common_cubic_three_completion_collapses J
  letI := hN
  obtain ⟨hNdegree, hFdegree, hF, hsignature⟩ :=
    actual_common_cubic_rational_degree_and_signature J
  letI := hF
  have actual_common_cubic_normal_discriminant_check (J : ℕ) (hJ : 1 ≤ J) [NumberField (complexTower J)] :
      let R := ∏ j ∈ Finset.Icc 1 J,
        radical (block j / Nat.floorRoot 3 (block j) ^ 3)
      (NumberField.discr (complexTower J)).natAbs =
        3 ^ (3 ^ J) * R ^ (4 * 3 ^ (J - 1)) := by
    classical
    let K := ComplexBase
    let N := complexTower J
    let R := ∏ j ∈ Finset.Icc 1 J,
      radical (block j / Nat.floorRoot 3 (block j) ^ 3)
    change (NumberField.discr N).natAbs =
      3 ^ (3 ^ J) * R ^ (4 * 3 ^ (J - 1))
    obtain ⟨hK, hN, hcomplete⟩ := actual_common_cubic_three_completion_and_ramification J
    letI := hK
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
    have hdegree : Module.finrank ℚ N = 2 * 3 ^ J := by
      calc
        Module.finrank ℚ N = Module.finrank ℚ K * Module.finrank K N :=
          (Module.finrank_mul_finrank ℚ K N).symm
        _ = 2 * 3 ^ J := by rw [hKdegree, golden_cubic_block_positive_root_tower_degree J]
    have hnorm := congrArg Ideal.absNorm (actual_common_cubic_absolute_different_sixth_power J)
    change ((differentIdeal ℤ (𝓞 N)) ^ 6).absNorm =
      ((Ideal.span {(3 : 𝓞 N)}) ^ 3 * (Ideal.span {(R : 𝓞 N)}) ^ 4).absNorm at hnorm
    rw [map_pow, map_mul, map_pow, map_pow,
      NumberField.absNorm_differentIdeal N (𝓞 N)] at hnorm
    change (NumberField.discr N).natAbs ^ 6 =
      (Ideal.span {((3 : ℕ) : 𝓞 N)}).absNorm ^ 3 *
        (Ideal.span {(R : 𝓞 N)}).absNorm ^ 4 at hnorm
    simp only [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hdegree] at hnorm
    have hpowJ : 3 ^ J = 3 * 3 ^ (J - 1) := by
      calc
        3 ^ J = 3 ^ ((J - 1) + 1) := by congr 1; omega
        _ = 3 * 3 ^ (J - 1) := by rw [pow_succ]; ring
    apply Nat.pow_left_injective (by decide : (6 : ℕ) ≠ 0)
    change (NumberField.discr N).natAbs ^ 6 = (3 ^ (3 ^ J) * R ^ (4 * 3 ^ (J - 1))) ^ 6
    rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [← pow_mul, ← pow_mul] at hnorm
    calc
      (NumberField.discr N).natAbs ^ 6 =
          3 ^ ((2 * 3 ^ J) * 3) * R ^ ((2 * 3 ^ J) * 4) := hnorm
      _ = 3 ^ (3 ^ J * 6) * R ^ ((4 * 3 ^ (J - 1)) * 6) := by
        congr 1
        · congr 1
          ring
        · congr 1
          rw [hpowJ]
          ring
  have actual_common_cubic_quadratic_unramified_away_three
      (J : ℕ) [NumberField (complexTower J)]
      (c : complexTower J ≃ₐ[ℚ] complexTower J) (hc2 : c ^ 2 = 1) (hcne : c ≠ 1) :
      let H := Subgroup.zpowers c
      let E : IntermediateField ℚ (complexTower J) := FixedPoints.intermediateField H
      ∀ (p : ℕ) (_ : p.Prime) (_ : p ≠ 3)
        (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J))),
        w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
        w.asIdeal.ramificationIdx (𝓞 E) = 1 := by
    classical
    let N := complexTower J
    let G := N ≃ₐ[ℚ] N
    let H : Subgroup G := Subgroup.zpowers c
    let E : IntermediateField ℚ N := FixedPoints.intermediateField H
    letI : IsGalois ℚ N := (actual_common_cubic_q_galois_and_conjugation J).1
    letI : IsGaloisGroup H E N := inferInstance
    letI : IsGaloisGroup H (𝓞 E) (𝓞 N) :=
      IsGaloisGroup.of_isFractionRing H (𝓞 E) (𝓞 N) E N
    have hcorder : orderOf c = 2 := by
      apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
      refine ⟨hc2, ?_⟩
      intro m hm hpos
      have hm1 : m = 1 := by omega
      simpa [hm1] using hcne
    have hHcard : Nat.card H = 2 := by rw [Nat.card_zpowers, hcorder]
    change ∀ (p : ℕ) (_ : p.Prime) (_ : p ≠ 3)
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 N)),
      w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) → w.asIdeal.ramificationIdx (𝓞 E) = 1
    intro p hp hp3 w hw
    letI : w.asIdeal.IsPrime := w.isPrime
    letI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
    let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, hp⟩
    have hv0 : v0.asIdeal = Ideal.span {(p : ℤ)} := by
      change (Ideal.span {(p : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
      simp [Ideal.map_span]
    letI : w.asIdeal.LiesOver v0.asIdeal := hv0.symm ▸ hw
    letI : v0.asIdeal.IsPrime := v0.isPrime
    letI : v0.asIdeal.IsMaximal := v0.isPrime.isMaximal v0.ne_bot
    letI : Finite (ℤ ⧸ v0.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v0.ne_bot
    letI : Field (ℤ ⧸ v0.asIdeal) := Ideal.Quotient.field v0.asIdeal
    have hcardI : Nat.card (w.asIdeal.inertia G) = w.asIdeal.ramificationIdx ℤ := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) v0.asIdeal w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx v0.asIdeal w.asIdeal G]
    have hecases : w.asIdeal.ramificationIdx ℤ = 1 ∨
        w.asIdeal.ramificationIdx ℤ = 3 := by
      by_cases hmod : ∀ j : ℕ, 1 ≤ j → j ≤ J → 3 ∣ (block j).factorization p
      · exact Or.inl (actual_common_cubic_unramified_outside_support J p hp hp3 hmod w hw)
      · push_neg at hmod
        obtain ⟨j, hj, hjJ, hmod⟩ := hmod
        have hpj : p ∣ block j := by
          by_contra h
          rw [Nat.factorization_eq_zero_of_not_dvd h] at hmod
          exact hmod (dvd_zero 3)
        have hle := actual_common_cubic_inertia_card_le_three J j p hj hjJ hp hp3 hpj w hw
        rw [hcardI] at hle
        have hdiv := actual_common_cubic_ramification_three_divides J j p hj hjJ hp hmod w hw
        exact Or.inr (Nat.le_antisymm hle
          (Nat.le_of_dvd (Ideal.ramificationIdx_pos w.asIdeal ℤ) hdiv))
    have hcoprime : Nat.Coprime (Nat.card (w.asIdeal.inertia G)) (Nat.card H) := by
      rw [hcardI, hHcard]
      rcases hecases with h | h <;> rw [h] <;> norm_num
    have hinf : w.asIdeal.inertia G ⊓ H = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcoprime)
    have hmap : (w.asIdeal.inertia H).map H.subtype = ⊥ := by
      rw [AddSubgroup.inertia_map_subtype w.asIdeal.toAddSubgroup H, hinf]
    have hcardRel : Nat.card (w.asIdeal.inertia H) = 1 := by
      rw [← Subgroup.card_subtype H (w.asIdeal.inertia H), hmap]
      simp
    let v := w.under (𝓞 E)
    letI : w.asIdeal.LiesOver v.asIdeal := Ideal.over_under _
    letI : v.asIdeal.IsPrime := v.isPrime
    letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    letI : Finite ((𝓞 E) ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Field ((𝓞 E) ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have hcardRelEq : Nat.card (w.asIdeal.inertia H) =
        w.asIdeal.ramificationIdx (𝓞 E) := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) v.asIdeal w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal H]
    exact hcardRelEq.symm.trans hcardRel
  have actual_common_cubic_quadratic_three_ramification
      (J : ℕ) [NumberField (complexTower J)]
      (c : complexTower J ≃ₐ[ℚ] complexTower J) (hc2 : c ^ 2 = 1) (hcne : c ≠ 1) :
      let H := Subgroup.zpowers c
      let E : IntermediateField ℚ (complexTower J) := FixedPoints.intermediateField H
      ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J))),
        w.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) →
        (w.asIdeal.ramificationIdx (𝓞 E) = 2 ↔ c • w.asIdeal = w.asIdeal) ∧
        (w.asIdeal.ramificationIdx (𝓞 E) = 1 ↔ c • w.asIdeal ≠ w.asIdeal) := by
    classical
    let N := complexTower J
    let G := N ≃ₐ[ℚ] N
    let H : Subgroup G := Subgroup.zpowers c
    let E : IntermediateField ℚ N := FixedPoints.intermediateField H
    letI : IsGalois ℚ N := (actual_common_cubic_q_galois_and_conjugation J).1
    letI : IsGaloisGroup H E N := inferInstance
    letI : IsGaloisGroup H (𝓞 E) (𝓞 N) :=
      IsGaloisGroup.of_isFractionRing H (𝓞 E) (𝓞 N) E N
    obtain ⟨hN, c', hc'coe, hcount, hlocal, huniq⟩ := actual_common_cubic_three_prime_orbits J
    have hcorder : orderOf c = 2 := by
      apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
      refine ⟨hc2, ?_⟩
      intro m hm hpos
      have hm1 : m = 1 := by omega
      simpa [hm1] using hcne
    have hHcard : Nat.card H = 2 := by rw [Nat.card_zpowers, hcorder]
    change ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 N)),
      w.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) →
      (w.asIdeal.ramificationIdx (𝓞 E) = 2 ↔ c • w.asIdeal = w.asIdeal) ∧
      (w.asIdeal.ramificationIdx (𝓞 E) = 1 ↔ c • w.asIdeal ≠ w.asIdeal)
    intro w hw
    let P := w.asIdeal
    letI : P.IsPrime := w.isPrime
    letI : P.IsMaximal := w.isPrime.isMaximal w.ne_bot
    let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨3, Nat.prime_three⟩
    have hv0 : v0.asIdeal = Ideal.span {(3 : ℤ)} := by
      change (Ideal.span {(3 : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
      simp [Ideal.map_span]
    letI : P.LiesOver v0.asIdeal := hv0.symm ▸ hw
    letI : v0.asIdeal.IsPrime := v0.isPrime
    letI : v0.asIdeal.IsMaximal := v0.isPrime.isMaximal v0.ne_bot
    letI : Finite (ℤ ⧸ v0.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v0.ne_bot
    letI : Field (ℤ ⧸ v0.asIdeal) := Ideal.Quotient.field v0.asIdeal
    have heAbs : P.ramificationIdx ℤ = 2 := (hlocal w hw).1
    have hfAbs : P.inertiaDeg ℤ = 1 := (hlocal w hw).2
    have hcardI : Nat.card (P.inertia G) = 2 := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) v0.asIdeal P,
        Ideal.ramificationIdxIn_eq_ramificationIdx v0.asIdeal P G, heAbs]
    have hcardD : Nat.card (MulAction.stabilizer G P) = 2 := by
      rw [Ideal.card_stabilizer_eq (G := G) v0.asIdeal P,
        Ideal.ramificationIdxIn_eq_ramificationIdx v0.asIdeal P G,
        Ideal.inertiaDegIn_eq_inertiaDeg v0.asIdeal P G, heAbs, hfAbs]
    have hIeqD : P.inertia G = MulAction.stabilizer G P :=
      Subgroup.eq_of_le_of_card_ge (Ideal.inertia_le_stabilizer P) (by rw [hcardI, hcardD])
    have hmap : (P.inertia H).map H.subtype = P.inertia G ⊓ H :=
      AddSubgroup.inertia_map_subtype P.toAddSubgroup H
    let v := w.under (𝓞 E)
    letI : P.LiesOver v.asIdeal := Ideal.over_under _
    letI : v.asIdeal.IsPrime := v.isPrime
    letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    letI : Finite ((𝓞 E) ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Field ((𝓞 E) ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have hcardRelEq : Nat.card (P.inertia H) = P.ramificationIdx (𝓞 E) := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) v.asIdeal P,
        Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P H]
    have hcardRelIntersection : P.ramificationIdx (𝓞 E) = Nat.card ↥(P.inertia G ⊓ H) := by
      rw [← hcardRelEq, ← Subgroup.card_subtype H (P.inertia H), hmap]
    have hecalc : P.ramificationIdx (𝓞 E) = if c • P = P then 2 else 1 := by
      rw [hcardRelIntersection]
      by_cases hfix : c • P = P
      · rw [if_pos hfix]
        have hle : H ≤ P.inertia G := by
          rw [hIeqD]
          exact Subgroup.zpowers_le.mpr hfix
        rw [inf_eq_right.mpr hle, hHcard]
      · rw [if_neg hfix]
        have hdiv : Nat.card ↥(P.inertia G ⊓ H) ∣ 2 := by
          rw [← hHcard]
          exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
        · exact h
        · have heq : P.inertia G ⊓ H = H :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hHcard, h])
          have hcI : c ∈ P.inertia G :=
            (show c ∈ P.inertia G ⊓ H from heq.symm ▸ Subgroup.mem_zpowers c).1
          exact (hfix (Ideal.inertia_le_stabilizer P hcI)).elim
    change (P.ramificationIdx (𝓞 E) = 2 ↔ c • P = P) ∧
      (P.ramificationIdx (𝓞 E) = 1 ↔ c • P ≠ P)
    constructor <;> rw [hecalc] <;> by_cases hfix : c • P = P <;> simp [hfix]
  have actual_common_cubic_quadratic_different_norm (J : ℕ) :
      ∃ hN : NumberField (complexTower J), letI := hN
      ∃ c : complexTower J ≃ₐ[ℚ] complexTower J,
        (∀ x, (c x : ℂ) = star (x : ℂ)) ∧
        let H := Subgroup.zpowers c
        let E : IntermediateField ℚ (complexTower J) := FixedPoints.intermediateField H
        (differentIdeal (𝓞 E) (𝓞 (complexTower J))).absNorm = 3 := by
    classical
    let N := complexTower J
    obtain ⟨hN, c, hccoe, hcount, hlocal, Pstar, hstarfix, hstaruniq⟩ :=
      actual_common_cubic_three_prime_orbits J
    letI := hN
    let G := N ≃ₐ[ℚ] N
    let H : Subgroup G := Subgroup.zpowers c
    let E : IntermediateField ℚ N := FixedPoints.intermediateField H
    let D := differentIdeal (𝓞 E) (𝓞 N)
    letI : IsGalois ℚ N := (actual_common_cubic_q_galois_and_conjugation J).1
    letI : FaithfulSMul (𝓞 E) (𝓞 N) :=
      FaithfulSMul.of_field_isFractionRing (𝓞 E) (𝓞 N) E N
    obtain ⟨c0, hccoe0, hc02, hc0ne, hnorm⟩ :=
      actual_common_cubic_conjugation_self_normalizing J
    have hcc0 : c = c0 := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (hccoe x).trans (hccoe0 x).symm
    have hc2 : c ^ 2 = 1 := hcc0.symm ▸ hc02
    have hcne : c ≠ 1 := hcc0.symm ▸ hc0ne
    have hDne : D ≠ ⊥ := differentIdeal_ne_bot
    have hnotrel (w : IsDedekindDomain.HeightOneSpectrum (𝓞 N))
        (he : w.asIdeal.ramificationIdx (𝓞 E) = 1) : ¬ w.asIdeal ∣ D := by
      let P := w.asIdeal
      let v := w.under (𝓞 E)
      letI : P.IsPrime := w.isPrime
      letI : P.IsMaximal := w.isPrime.isMaximal w.ne_bot
      letI : P.LiesOver v.asIdeal := Ideal.over_under _
      letI : v.asIdeal.IsPrime := v.isPrime
      letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
      letI : Finite ((𝓞 E) ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      letI : Field ((𝓞 E) ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
      letI : Field ((𝓞 N) ⧸ P) := Ideal.Quotient.field P
      letI : Algebra.IsSeparable ((𝓞 E) ⧸ v.asIdeal) ((𝓞 N) ⧸ P) := inferInstance
      have hpMap : Ideal.map (algebraMap (𝓞 E) (𝓞 N)) v.asIdeal ≠ ⊥ :=
        (Ideal.map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 N))).not.mpr v.ne_bot
      obtain ⟨Q, hsup, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hpMap P
      rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        v.asIdeal P hpMap, he, pow_one] at hfactor
      exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable (𝓞 E) P Q
        (Ideal.isCoprime_iff_sup_eq.mpr hsup) hfactor.symm
    letI : Pstar.val.IsPrime := Pstar.property.1
    letI : Pstar.val.LiesOver (Ideal.span {(3 : ℤ)}) := Pstar.property.2
    let wstar : IsDedekindDomain.HeightOneSpectrum (𝓞 N) :=
      ⟨Pstar.val, Pstar.property.1,
        Ideal.ne_bot_of_liesOver_of_ne_bot
          (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (3 : ℤ) ≠ 0)) Pstar.val⟩
    have hmultStar : multiplicity Pstar.val D = 1 := by
      let P := Pstar.val
      let v := wstar.under (𝓞 E)
      letI : P.IsMaximal := wstar.isPrime.isMaximal wstar.ne_bot
      letI : P.LiesOver v.asIdeal := Ideal.over_under _
      letI : v.asIdeal.IsPrime := v.isPrime
      letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
      letI : v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) :=
        Ideal.LiesOver.tower_bot P v.asIdeal (Ideal.span {(3 : ℤ)})
      letI : Finite ((𝓞 E) ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      letI : Field ((𝓞 E) ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
      letI : Field ((𝓞 N) ⧸ P) := Ideal.Quotient.field P
      have he : P.ramificationIdx (𝓞 E) = 2 :=
        (actual_common_cubic_quadratic_three_ramification J c hc2 hcne wstar
          Pstar.property.2).1.mpr hstarfix
      have htwo : (2 : (𝓞 E) ⧸ v.asIdeal) ≠ 0 := by
        intro h
        have hq : Ideal.Quotient.mk v.asIdeal (2 : 𝓞 E) = 0 :=
          (map_natCast (Ideal.Quotient.mk v.asIdeal) 2).trans h
        have h2v := Ideal.Quotient.eq_zero_iff_mem.mp hq
        have h3v : (3 : 𝓞 E) ∈ v.asIdeal :=
          (inferInstance : v.asIdeal.LiesOver (Ideal.span {(3 : ℤ)})).1.le
            (Ideal.mem_span_singleton_self (3 : ℤ))
        have h1v := v.asIdeal.sub_mem (v.asIdeal.add_mem h2v h2v) h3v
        norm_num at h1v
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one v.asIdeal).mpr h1v)
      have hpMap : Ideal.map (algebraMap (𝓞 E) (𝓞 N)) v.asIdeal ≠ ⊥ :=
        (Ideal.map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 N))).not.mpr v.ne_bot
      obtain ⟨Q, hsup, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hpMap P
      rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        v.asIdeal P hpMap, he] at hfactor
      have hPQ : IsCoprime (P ^ 2) Q := (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
      have hsep : Algebra.IsSeparable ((𝓞 E) ⧸ v.asIdeal) ((𝓞 N) ⧸ P) := inferInstance
      have hnot : ¬ P ^ 2 ∣ D := by
        rw [D5.S3.Factorization.Dedekind.TameDifferent.prime_power_divides_different_iff
          (𝓞 E) v.ne_bot P Q hPQ hfactor.symm]
        exact not_or.mpr ⟨not_not.mpr hsep, htwo⟩
      have hlower : P ^ 1 ∣ D := by
        simpa only [Nat.reduceSub] using
          (pow_sub_one_dvd_differentIdeal (𝓞 E) P 2 v.ne_bot ⟨Q, hfactor⟩)
      exact multiplicity_eq_of_emultiplicity_eq_some
        (emultiplicity_eq_coe.mpr ⟨hlower, hnot⟩)
    have hfactorOnly : ∀ P ∈ normalizedFactors D, P = Pstar.val := by
      intro P hP
      have hprime := prime_of_normalized_factor P hP
      letI : P.IsPrime := Ideal.isPrime_of_prime hprime
      letI : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
      let w : IsDedekindDomain.HeightOneSpectrum (𝓞 N) :=
        ⟨P, inferInstance, hprime.ne_zero⟩
      have hPd : P ∣ D := dvd_of_mem_normalizedFactors hP
      obtain ⟨p, n, hn, hpmem, hp, hnormP⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      have hpover : P.LiesOver (Ideal.span {(p : ℤ)}) :=
        (Ideal.liesOver_span_iff (inferInstance : P.IsPrime).ne_top
          (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa only [map_natCast] using hpmem)
      by_cases hp3 : p = 3
      · subst p
        let Q : (Ideal.span {(3 : ℤ)}).primesOver (𝓞 N) := ⟨P, inferInstance, hpover⟩
        by_cases hfix : c • P = P
        · exact congrArg Subtype.val (hstaruniq Q hfix)
        · have he := (actual_common_cubic_quadratic_three_ramification J c hc2 hcne w hpover).2.mpr hfix
          exact (hnotrel w he hPd).elim
      · have he := actual_common_cubic_quadratic_unramified_away_three J c hc2 hcne p hp hp3 w hpover
        exact (hnotrel w he hPd).elim
    have hreplicate : normalizedFactors D =
        Multiset.replicate (normalizedFactors D).card Pstar.val :=
      Multiset.eq_replicate_of_mem hfactorOnly
    have hcountStar : (normalizedFactors D).count Pstar.val = 1 := by
      have h := multiplicity_eq_count_normalizedFactors wstar.irreducible hDne
      simpa only [normalize_eq] using h.symm.trans hmultStar
    have hcardFactors : (normalizedFactors D).card = 1 := by
      rw [hreplicate, Multiset.count_replicate_self] at hcountStar
      exact hcountStar
    have hDeq : D = Pstar.val := by
      rw [← Ideal.prod_normalizedFactors_eq_self hDne, hreplicate, hcardFactors]
      simp
    have hnormStar := Ideal.pow_inertiaDeg 3 Pstar.val
    rw [(hlocal wstar Pstar.property.2).2, pow_one] at hnormStar
    refine ⟨hN, c, hccoe, ?_⟩
    change D.absNorm = 3
    rw [hDeq]
    exact hnormStar.symm
  have actual_common_cubic_real_field_fixed_field
      (J : ℕ) [NumberField (complexTower J)]
      (c : complexTower J ≃ₐ[ℚ] complexTower J)
      (hccoe : ∀ x, (c x : ℂ) = star (x : ℂ))
      (hc2 : c ^ 2 = 1) (hcne : c ≠ 1) :
      let F := IntermediateField.adjoin ℚ (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
      let H := Subgroup.zpowers c
      let E : IntermediateField ℚ (complexTower J) := FixedPoints.intermediateField H
      Nonempty (F ≃ₐ[ℚ] E) ∧ Module.finrank E (complexTower J) = 2 := by
    classical
    let N := complexTower J
    let F := IntermediateField.adjoin ℚ (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
    let G := N ≃ₐ[ℚ] N
    let H : Subgroup G := Subgroup.zpowers c
    let E : IntermediateField ℚ N := FixedPoints.intermediateField H
    obtain ⟨hNdegree, hFdegree, hF, hsig⟩ :=
      actual_common_cubic_rational_degree_and_signature J
    letI := hF
    obtain ⟨hgalQ, c0, hc0, hc02, hc0ne, hcinv⟩ :=
      actual_common_cubic_q_galois_and_conjugation J
    letI : IsGalois ℚ N := hgalQ
    have hcorder : orderOf c = 2 := by
      apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
      refine ⟨hc2, ?_⟩
      intro m hm hpos
      have hm1 : m = 1 := by omega
      simpa [hm1] using hcne
    have hHcard : Nat.card H = 2 := by rw [Nat.card_zpowers, hcorder]
    have hrelative : Module.finrank E N = 2 := by
      rw [IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup G ℚ N H, hHcard]
    have hEdegree : Module.finrank ℚ E = 3 ^ J := by
      have h := Module.finrank_mul_finrank ℚ E N
      rw [hrelative, hNdegree] at h
      omega
    have hFle : F ≤ N.restrictScalars ℚ := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro x hx
      exact IntermediateField.subset_adjoin ComplexBase ((D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)) hx
    let inclRing : F →+* N := {
      toFun := fun x => ⟨x.val, hFle x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
    }
    let incl : F →ₐ[ℚ] N := inclRing.toRatAlgHom
    have hreal (x : F) : star (x : ℂ) = (x : ℂ) := by
      rcases x with ⟨x, hx⟩
      exact IntermediateField.adjoin_induction ℚ
        (p := fun z _ => star z = z)
        (by rintro z ⟨j, hj, hjJ, rfl⟩; simp [positiveRoot])
        (by intro r; simp)
        (by intro x y hx hy hxr hyr; simp [map_add, hxr, hyr])
        (by intro x hx hxr; simp [map_inv₀, hxr])
        (by intro x y hx hy hxr hyr; simp [map_mul, hxr, hyr]) hx
    have hle : incl.fieldRange ≤ E := by
      rintro x ⟨a, rfl⟩
      apply FixedPoints.mem_intermediateField_iff.mpr
      have hcfix : c (incl a) = incl a := by
        apply Subtype.ext
        exact (hccoe (incl a)).trans (hreal a)
      have hHfix : H ≤ MulAction.stabilizer G (incl a) :=
        Subgroup.zpowers_le.mpr hcfix
      intro σ
      exact hHfix σ.property
    have hrangedegree : Module.finrank ℚ incl.fieldRange = 3 ^ J :=
      incl.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans hFdegree
    have hrangeeq : incl.fieldRange = E :=
      IntermediateField.eq_of_le_of_finrank_eq hle (hrangedegree.trans hEdegree.symm)
    have equiv : F ≃ₐ[ℚ] E :=
      incl.equivFieldRange.trans (IntermediateField.equivOfEq hrangeeq)
    exact ⟨⟨equiv⟩, hrelative⟩
  have actual_real_discriminant (J : ℕ) (hJ : 1 ≤ J) :
      let F := IntermediateField.adjoin ℚ
        (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
      ∃ hF : NumberField F, letI := hF
      let R := ∏ j ∈ Finset.Icc 1 J,
        radical (block j / Nat.floorRoot 3 (block j) ^ 3)
      (NumberField.discr F).natAbs =
        3 ^ ((3 ^ J - 1) / 2) * R ^ (2 * 3 ^ (J - 1)) := by
    classical
    let N := complexTower J
    let F := IntermediateField.adjoin ℚ
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
    let R := ∏ j ∈ Finset.Icc 1 J,
      radical (block j / Nat.floorRoot 3 (block j) ^ 3)
    change ∃ hF : NumberField F, letI := hF;
      (NumberField.discr F).natAbs =
        3 ^ ((3 ^ J - 1) / 2) * R ^ (2 * 3 ^ (J - 1))
    obtain ⟨hNdegree, hFdegree, hF, hsig⟩ :=
      actual_common_cubic_rational_degree_and_signature J
    letI := hF
    obtain ⟨hN, c, hccoe, hDnorm⟩ := actual_common_cubic_quadratic_different_norm J
    letI := hN
    obtain ⟨c0, hccoe0, hc02, hc0ne, hnorm⟩ :=
      actual_common_cubic_conjugation_self_normalizing J
    have hcc0 : c = c0 := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (hccoe x).trans (hccoe0 x).symm
    have hc2 : c ^ 2 = 1 := hcc0.symm ▸ hc02
    have hcne : c ≠ 1 := hcc0.symm ▸ hc0ne
    let H := Subgroup.zpowers c
    let E : IntermediateField ℚ N := FixedPoints.intermediateField H
    obtain ⟨⟨eFE⟩, hrelative⟩ :=
      actual_common_cubic_real_field_fixed_field J c hccoe hc2 hcne
    change (differentIdeal (𝓞 E) (𝓞 N)).absNorm = 3 at hDnorm
    have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      E (𝓞 E) N (𝓞 N)
    have hdiscFE : NumberField.discr F = NumberField.discr E :=
      NumberField.discr_eq_discr_of_algEquiv F eFE
    rw [hDnorm, hrelative, ← hdiscFE] at htower
    have hNdisc := actual_common_cubic_normal_discriminant_check J hJ
    change (NumberField.discr N).natAbs = 3 ^ (3 ^ J) * R ^ (4 * 3 ^ (J - 1)) at hNdisc
    have hodd : 3 ^ J % 2 = 1 := by simp [Nat.pow_mod]
    have hexp : 1 + ((3 ^ J - 1) / 2) * 2 = 3 ^ J := by omega
    have hcalc : 3 * (3 ^ ((3 ^ J - 1) / 2) * R ^ (2 * 3 ^ (J - 1))) ^ 2 =
        3 ^ (3 ^ J) * R ^ (4 * 3 ^ (J - 1)) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      have h3 : 3 * 3 ^ (((3 ^ J - 1) / 2) * 2) = 3 ^ (3 ^ J) := by
        rw [← pow_succ']
        congr 1
        omega
      have hRexp : (2 * 3 ^ (J - 1)) * 2 = 4 * 3 ^ (J - 1) := by ring
      rw [← mul_assoc, h3, hRexp]
    have hsquares : (NumberField.discr F).natAbs ^ 2 =
        (3 ^ ((3 ^ J - 1) / 2) * R ^ (2 * 3 ^ (J - 1))) ^ 2 := by
      apply Nat.mul_left_cancel (by decide : 0 < (3 : ℕ))
      exact htower.symm.trans (hNdisc.trans hcalc.symm)
    refine ⟨hF, ?_⟩
    change (NumberField.discr F).natAbs =
      3 ^ ((3 ^ J - 1) / 2) * R ^ (2 * 3 ^ (J - 1))
    exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hsquares
  have actual_root_discriminant (J : ℕ) (hJ : 1 ≤ J) [NumberField (complexTower J)] :
      let R := ∏ j ∈ Finset.Icc 1 J,
        radical (block j / Nat.floorRoot 3 (block j) ^ 3)
      NumberField.rootDiscr (complexTower J) =
        Real.sqrt 3 * (R : ℝ) ^ (2 / 3 : ℝ) := by
    classical
    let N := complexTower J
    let R := ∏ j ∈ Finset.Icc 1 J,
      radical (block j / Nat.floorRoot 3 (block j) ^ 3)
    change NumberField.rootDiscr N = Real.sqrt 3 * (R : ℝ) ^ (2 / 3 : ℝ)
    have hdegree := (actual_common_cubic_rational_degree_and_signature J).1
    change Module.finrank ℚ N = 2 * 3 ^ J at hdegree
    have hdisc := actual_common_cubic_normal_discriminant_check J hJ
    change (NumberField.discr N).natAbs = 3 ^ (3 ^ J) * R ^ (4 * 3 ^ (J - 1)) at hdisc
    have hdiscR : |(NumberField.discr N : ℝ)| =
        (3 : ℝ) ^ (3 ^ J) * (R : ℝ) ^ (4 * 3 ^ (J - 1)) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) hdisc
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_natAbs, Int.cast_abs] using h
    rw [NumberField.rootDiscr_def, hdegree, Int.cast_abs, hdiscR]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 3),
      ← Real.rpow_natCast_mul (Nat.cast_nonneg R), Real.sqrt_eq_rpow]
    have hpow : (3 : ℝ) ^ J = 3 * (3 : ℝ) ^ (J - 1) := by
      calc
        (3 : ℝ) ^ J = 3 ^ ((J - 1) + 1) := by congr 1; omega
        _ = 3 * 3 ^ (J - 1) := by rw [pow_succ]; ring
    have hpos : (3 : ℝ) ^ J ≠ 0 := by positivity
    have hpos' : (3 : ℝ) ^ (J - 1) ≠ 0 := by positivity
    congr 1
    · congr 1
      push_cast
      field_simp [hpos] <;> ring
    · congr 1
      push_cast
      rw [hpow]
      field_simp [hpos'] <;> ring
  have hNdisc := actual_common_cubic_normal_discriminant_check J hJ
  obtain ⟨hF', hFdisc⟩ := actual_real_discriminant J hJ
  have hrd := actual_root_discriminant J hJ
  have hreal (x : F) : star (x : ℂ) = (x : ℂ) := by
    rcases x with ⟨x, hx⟩
    exact IntermediateField.adjoin_induction ℚ
      (p := fun z _ => star z = z)
      (by rintro z ⟨j, hj, hjJ, rfl⟩; simp [positiveRoot])
      (by intro r; simp)
      (by intro x y hx hy hxr hyr; simp [map_add, hxr, hyr])
      (by intro x hx hxr; simp [map_inv₀, hxr])
      (by intro x y hx hy hxr hyr; simp [map_mul, hxr, hyr]) hx
  have hnotreal : ¬ NumberField.IsTotallyReal F := by
    intro h
    have hz : nrComplexPlaces F = 0 := NumberField.nrComplexPlaces_eq_zero_iff.mpr h
    rw [hsignature.2] at hz
    have hpowJ : 3 ^ J = 3 * 3 ^ (J - 1) := by
      calc
        3 ^ J = 3 ^ ((J - 1) + 1) := by congr 1; omega
        _ = 3 * 3 ^ (J - 1) := by rw [pow_succ]; ring
    have hpositive : 0 < 3 ^ (J - 1) := by positivity
    omega
  obtain ⟨hgal, c, hccoe, hc2, hcne, hcinv⟩ :=
    actual_common_cubic_q_galois_and_conjugation J
  have hfixed := actual_common_cubic_real_field_fixed_field J c hccoe hc2 hcne
  have hsemidirect := actual_common_cubic_semidirect J
  refine ⟨hN, hF, hNdegree, hFdegree, hsignature.1, hsignature.2,
    hreal, hnotreal, hNdisc, hFdisc, hrd, hgal, ?_, hsemidirect⟩
  exact ⟨c, hccoe, hc2, hcne, hcinv, hfixed⟩
end D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants

#print axioms D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants.golden_cubic_block_common_field_discriminants
