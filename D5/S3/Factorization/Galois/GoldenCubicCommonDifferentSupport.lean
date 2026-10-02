/- GID: D5/S3/Factorization/Galois/GoldenCubicCommonDifferentSupport
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCommonDifferentSupport
   mirror-E: none(waiver:algebraically-proved)
   anchors: [lit/tauceti2026tamedifferent]
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

import D5.S3.Factorization.Galois.GoldenCubicCommonInertiaAndSignature

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial
open D5.S1.Scale
open D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower

open D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
open NumberField IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Valued WithZeroTopology Pointwise
open UniqueFactorizationMonoid NumberField.InfinitePlace
open private base_not_cube from D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower

namespace D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants

set_option maxHeartbeats 800000 in
theorem actual_common_cubic_semidirect (J : ℕ) :
    ∃ φ : Multiplicative (ZMod 2) →* MulAut (Fin J → Multiplicative (ZMod 3)),
      (∀ x, φ (Multiplicative.ofAdd (1 : ZMod 2)) x = x⁻¹) ∧
      Nonempty ((Fin J → Multiplicative (ZMod 3)) ⋊[φ]
        Multiplicative (ZMod 2) ≃* (complexTower J ≃ₐ[ℚ] complexTower J)) := by
  have actual_common_cubic_full_coordinates (J : ℕ) :
      ∃ beta : Fin J → complexTower J,
        (∀ i, (beta i : ℂ) = positiveRoot (i.val + 1)) ∧
        ∃ e : (complexTower J ≃ₐ[ComplexBase] complexTower J) ≃*
            (Fin J → Multiplicative (ZMod 3)),
          ∀ σ i,
            σ (beta i) =
              algebraMap ComplexBase (complexTower J)
                (⟨omega, IntermediateField.subset_adjoin ℚ {omega}
                  (Set.mem_singleton omega)⟩ : ComplexBase) ^
                    (Multiplicative.toAdd (e σ i)).val * beta i := by
    classical
    let K := ComplexBase
    have hω : IsPrimitiveRoot omega 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ Base :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    letI : IsCyclotomicExtension {3} ℚ K :=
      (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
        3 ℚ ℂ K hω).2 rfl
    let baseEquiv : Base ≃ₐ[ℚ] K := IsCyclotomicExtension.algEquiv {3} ℚ Base K
    let ζ : K := ⟨omega,
      IntermediateField.subset_adjoin ℚ {omega} (Set.mem_singleton omega)⟩
    have hζ : IsPrimitiveRoot ζ 3 := by
      apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap K ℂ)
        (hf := (algebraMap K ℂ).injective)
      exact hω
    let rad : Fin J → K := fun i => block (i.val + 1)
    let roots : Fin J → ℂ := fun i => positiveRoot (i.val + 1)
    have hcube (i : Fin J) : roots i ^ 3 = algebraMap K ℂ (rad i) := by
      change (((block (i.val + 1) : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 =
        (block (i.val + 1) : ℂ)
      rw [← Complex.ofReal_pow]
      simpa using congrArg (fun x : ℝ => (x : ℂ))
        (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block (i.val + 1)))
          (by decide : (3 : ℕ) ≠ 0))
    have hnotcube (i : Fin J) (t : K) : t ^ 3 ≠ rad i := by
      intro ht
      have hb : (block (i.val + 1) : ℤ) =
          goldenLucas (3 ^ (i.val + 1)) ^ 2 + 3 := by
        have hnonneg : 0 ≤ goldenLucas (3 ^ (i.val + 1)) ^ 2 + 3 := by positivity
        simp [block, abs_of_nonneg hnonneg]
      have hnc : ¬ ∃ z : ℤ, z ^ 3 = (block (i.val + 1) : ℤ) := by
        rw [hb]
        exact D5.S3.Factorization.GoldenCubicBlockNoncube.golden_cubic_block_not_cube
          (i.val + 1) (by omega)
      apply base_not_cube (block (i.val + 1)) hnc
      refine ⟨baseEquiv.symm t, ?_⟩
      have h := congrArg baseEquiv.symm ht
      simpa only [map_pow, rad, map_natCast] using h
    have hrange : Set.range roots =
        D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val + 1, by omega, by omega, rfl⟩
      · rintro ⟨j, hj, hjJ, rfl⟩
        refine ⟨⟨j - 1, by omega⟩, ?_⟩
        dsimp [roots]
        rw [Nat.sub_add_cancel hj]
    have hdegree : Module.finrank K (IntermediateField.adjoin K (Set.range roots)) =
        3 ^ Fintype.card (Fin J) := by
      rw [hrange, Fintype.card_fin]
      exact golden_cubic_block_positive_root_tower_degree J
    have hcoordinates :
      IsGalois K (IntermediateField.adjoin K (Set.range roots)) ∧
      ∃ e : ((IntermediateField.adjoin K (Set.range roots)) ≃ₐ[K] (IntermediateField.adjoin K (Set.range roots))) ≃*
          (Fin J → Multiplicative (ZMod 3)),
        ∀ σ : (IntermediateField.adjoin K (Set.range roots)) ≃ₐ[K] (IntermediateField.adjoin K (Set.range roots)), ∀ i : Fin J,
          σ (⟨roots i, IntermediateField.subset_adjoin K (Set.range roots) ⟨i, rfl⟩⟩ : IntermediateField.adjoin K (Set.range roots)) = algebraMap K (IntermediateField.adjoin K (Set.range roots)) ζ ^
            (Multiplicative.toAdd (e σ i)).val * (⟨roots i, IntermediateField.subset_adjoin K (Set.range roots) ⟨i, rfl⟩⟩ : IntermediateField.adjoin K (Set.range roots)) := by
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
      let M := IntermediateField.adjoin K (Set.range roots)
      let β : Fin J → M := fun i => ⟨roots i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
      let p : Fin J → K[X] := fun i => X ^ 3 - C (rad i)
      have hirr (i : Fin J) : Irreducible (p i) :=
        (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_three).mpr (hnotcube i)
      let t : Fin J → IntermediateField K ℂ := fun i => IntermediateField.adjoin K {roots i}
      letI : ∀ i, IsSplittingField K (t i) (p i) := fun i =>
        single_radical_splitting ζ hζ (rad i) (roots i) (hcube i) (hirr i)
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
          exact (le_iSup t i) (IntermediateField.mem_adjoin_simple_self K (roots i))
      letI : Normal K M := hsup ▸ inferInstance
      letI : IsGalois K M := {
        to_isSeparable := inferInstance
        to_normal := inferInstance
      }
      letI : FiniteDimensional K M := Module.finite_of_finrank_pos (by rw [hdegree]; positivity)
      let F : Fin J → IntermediateField K M := fun i => IntermediateField.adjoin K {β i}
      have hβ (i : Fin J) : β i ^ 3 = algebraMap K M (rad i) := by
        apply Subtype.ext
        exact hcube i
      letI : ∀ i, IsSplittingField K (F i) (p i) := fun i =>
        single_radical_splitting ζ hζ (rad i) (β i) (hβ i) (hirr i)
      letI : ∀ i, Normal K (F i) := fun i => Normal.of_isSplittingField (p i)
      let coordinate : (M ≃ₐ[K] M) →* (Fin J → Multiplicative (ZMod 3)) :=
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
      have hcard : Nat.card (M ≃ₐ[K] M) = Nat.card (Fin J → Multiplicative (ZMod 3)) := by
        rw [IsGalois.card_aut_eq_finrank]
        change Module.finrank K (IntermediateField.adjoin K (Set.range roots)) = _
        rw [hdegree]
        simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_multiplicative, ZMod.card]
      have hbij : Function.Bijective coordinate :=
        (Nat.bijective_iff_injective_and_card coordinate).mpr ⟨hinj, hcard⟩
      let e := MulEquiv.ofBijective coordinate hbij
      change IsGalois K M ∧ ∃ e : (M ≃ₐ[K] M) ≃* (Fin J → Multiplicative (ZMod 3)), _
      refine ⟨inferInstance, e, ?_⟩
      intro σ i
      let m : ℕ := (Multiplicative.toAdd (coordinate σ i)).val
      have hα : (IntermediateField.AdjoinSimple.gen K (β i)) ^ 3 =
          algebraMap K (F i) (rad i) := by
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
    obtain ⟨_hgal, e, he⟩ := hcoordinates
    have hM : IntermediateField.adjoin K (Set.range roots) = complexTower J := by
      rw [hrange]
      rfl
    have hcoords : ∃ beta : Fin J → complexTower J,
        (∀ i, (beta i : ℂ) = positiveRoot (i.val + 1)) ∧
        ∃ e : (complexTower J ≃ₐ[K] complexTower J) ≃*
            (Fin J → Multiplicative (ZMod 3)),
          ∀ σ i, σ (beta i) = algebraMap K (complexTower J) ζ ^
            (Multiplicative.toAdd (e σ i)).val * beta i := by
      have h : ∃ beta : Fin J → IntermediateField.adjoin K (Set.range roots),
          (∀ i, (beta i : ℂ) = positiveRoot (i.val + 1)) ∧
          ∃ e : (IntermediateField.adjoin K (Set.range roots) ≃ₐ[K]
              IntermediateField.adjoin K (Set.range roots)) ≃*
              (Fin J → Multiplicative (ZMod 3)),
            ∀ σ i, σ (beta i) =
              algebraMap K (IntermediateField.adjoin K (Set.range roots)) ζ ^
                (Multiplicative.toAdd (e σ i)).val * beta i :=
        ⟨(fun i => ⟨roots i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩),
          (fun i => rfl), e, he⟩
      exact hM ▸ h
    exact hcoords
  have index_two_split_inversion
      {A E B : Type} [Group A] [Group E] [Group B] [Finite E] [Finite B]
      (S : GroupExtension A E B) (hB : Nat.card B = 2)
      (c : E) (hc2 : c ^ 2 = 1) (hcB : S.rightHom c ≠ 1)
      (hconj : ∀ a, c * S.inl a * c = S.inl a⁻¹) :
      ∃ φ : B →* MulAut A,
        (∀ a, φ (S.rightHom c) a = a⁻¹) ∧ Nonempty (A ⋊[φ] B ≃* E) := by
    classical
    let C := Subgroup.zpowers c
    have hcne : c ≠ 1 := by intro h; exact hcB (by rw [h, map_one])
    have hcorder : orderOf c = 2 := by
      apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
      refine ⟨hc2, ?_⟩
      intro m hm hpos
      have hm1 : m = 1 := by omega
      simpa [hm1] using hcne
    have hCcard : Nat.card C = 2 := by
      rw [Nat.card_zpowers, hcorder]
    let r : C →* B := S.rightHom.comp C.subtype
    have hCcases (x : C) : (x : E) = 1 ∨ (x : E) = c := by
      have hx := (mem_zpowers_iff_mem_range_orderOf (x := c) (y := (x : E))).mp x.property
      rw [hcorder] at hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, hpow⟩
      have hk2 : k < 2 := Finset.mem_range.mp hk
      interval_cases k <;> simp_all
    have hker (x : C) (hx : r x = 1) : x = 1 := by
      rcases hCcases x with h | h
      · exact Subtype.ext h
      · have : S.rightHom c = 1 := by simpa [r, h] using hx
        exact (hcB this).elim
    have hrinj : Function.Injective r := by
      intro x y hxy
      have h : r (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      have hh := hker _ h
      exact mul_inv_eq_one.mp hh
    have hrbij : Function.Bijective r :=
      (Nat.bijective_iff_injective_and_card r).mpr ⟨hrinj, hCcard.trans hB.symm⟩
    let e : C ≃* B := MulEquiv.ofBijective r hrbij
    let s : S.Splitting := {
      toMonoidHom := C.subtype.comp e.symm.toMonoidHom
      rightInverse_rightHom := by
        intro b
        exact e.apply_symm_apply b
    }
    have hsc : s (S.rightHom c) = c := by
      let cc : C := ⟨c, Subgroup.mem_zpowers c⟩
      have hec : e cc = S.rightHom c := rfl
      have h := congrArg (fun x : C => (x : E)) (e.symm_apply_apply cc)
      change (e.symm (S.rightHom c) : E) = c
      simpa only [hec, cc] using h
    have hcinv : c⁻¹ = c := by
      apply mul_left_cancel (a := c)
      rw [mul_inv_cancel, ← pow_two, hc2]
    refine ⟨s.conjAct, ?_, ⟨s.semidirectProductMulEquiv⟩⟩
    intro a
    apply S.inl_injective
    change S.inl (S.conjAct (s (S.rightHom c)) a) = S.inl a⁻¹
    rw [GroupExtension.inl_conjAct_comm, hsc, hcinv]
    exact hconj a

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
  obtain ⟨φB, hφB, ⟨eBsem⟩⟩ := index_two_split_inversion S hBcard c hc2 hrcne
    (fun σ => hcinv σ)
  obtain ⟨beta, hbeta, ecoord, hcoords⟩ := actual_common_cubic_full_coordinates J
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let e2 : Multiplicative (ZMod 2) ≃* B :=
    zmodMulEquivOfGenerator (fun b => mem_zpowers_of_prime_card hBcard hrcne) hBcard
  have he2 : e2 (Multiplicative.ofAdd (1 : ZMod 2)) = r c :=
    zmodMulEquivOfGenerator_apply_ofAdd_one _ _
  let φ : Multiplicative (ZMod 2) →* MulAut (Fin J → Multiplicative (ZMod 3)) :=
    (MulAut.congr ecoord).toMonoidHom.comp (φB.comp e2.toMonoidHom)
  have hφ : ∀ x, φ (Multiplicative.ofAdd (1 : ZMod 2)) x = x⁻¹ := by
    intro x
    change ecoord (φB (e2 (Multiplicative.ofAdd (1 : ZMod 2))) (ecoord.symm x)) = x⁻¹
    rw [he2, hφB, map_inv, MulEquiv.apply_symm_apply]
  have echange : H ⋊[φB] B ≃*
      (Fin J → Multiplicative (ZMod 3)) ⋊[φ] Multiplicative (ZMod 2) :=
    SemidirectProduct.congr' ecoord e2.symm
  exact ⟨φ, hφ, ⟨echange.symm.trans eBsem⟩⟩

theorem actual_common_cubic_ramification_three_divides
    (J j p : ℕ) [NumberField (complexTower J)]
    (hj : 1 ≤ j) (hjJ : j ≤ J) (hp : p.Prime)
    (hmod : ¬ 3 ∣ (block j).factorization p)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J)))
    (hw : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) :
    3 ∣ w.asIdeal.ramificationIdx ℤ := by
  classical
  let N := complexTower J
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, hp⟩
  have hv0 : v0.asIdeal = Ideal.span {(p : ℤ)} := by
    change (Ideal.span {(p : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
    simp [Ideal.map_span]
  letI : w.asIdeal.LiesOver v0.asIdeal := hv0.symm ▸ hw
  letI : FaithfulSMul ℤ (𝓞 N) := FaithfulSMul.of_field_isFractionRing ℤ (𝓞 N) ℚ N
  have hB0 : block j ≠ 0 := by
    change (goldenLucas (3 ^ j) ^ 2 + 3).natAbs ≠ 0
    have hp : 0 < goldenLucas (3 ^ j) ^ 2 + (3 : ℤ) := by positivity
    exact Int.natAbs_ne_zero.mpr hp.ne'
  have hBint : (block j : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hB0
  have hmult : multiplicity v0.asIdeal (Ideal.span {(block j : ℤ)}) =
      (block j).factorization p := by
    rw [hv0]
    calc
      multiplicity (Ideal.span {(p : ℤ)}) (Ideal.span {(block j : ℤ)}) =
          multiplicity (p : ℤ) (block j : ℤ) := by
        apply multiplicity_eq_of_emultiplicity_eq
        apply emultiplicity_eq_emultiplicity_iff.mpr
        intro n
        rw [Ideal.span_singleton_pow, Ideal.dvd_iff_le,
          Ideal.span_singleton_le_span_singleton]
      _ = multiplicity p (block j) := Int.natCast_multiplicity p (block j)
      _ = (block j).factorization p := Nat.multiplicity_eq_factorization hp hB0
  have hbase : v0.valuation ℚ (block j : ℚ) =
      WithZero.exp (-(block j).factorization p : ℤ) := by
    change v0.valuation ℚ (algebraMap ℤ ℚ (block j : ℤ)) = _
    rw [valuation_of_algebraMap, v0.intValuation_eq_exp_neg_multiplicity hBint, hmult]
  let θ : N := ⟨positiveRoot j,
    IntermediateField.subset_adjoin ComplexBase
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
      ⟨j, hj, hjJ, rfl⟩⟩
  have hθcube : θ ^ 3 = (block j : N) := by
    apply Subtype.ext
    change (((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 = (block j : ℂ)
    rw [← Complex.ofReal_pow]
    simpa using congrArg (fun x : ℝ => (x : ℂ))
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j)) (by decide : (3 : ℕ) ≠ 0))
  let e := v0.asIdeal.ramificationIdx' w.asIdeal
  have hval := valuation_liesOver (K := ℚ) (L := N) v0 w (block j : ℚ)
  change v0.valuation ℚ (block j : ℚ) ^ e = w.valuation N (block j : N) at hval
  rw [hbase] at hval
  have hcubeval : (w.valuation N θ) ^ 3 = w.valuation N (block j : N) := by
    rw [← map_pow, hθcube]
  have hlog := congrArg WithZero.log (hcubeval.trans hval.symm)
  simp only [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hdiv : (3 : ℤ) ∣ (e : ℤ) * ((block j).factorization p : ℤ) := by
    refine ⟨- WithZero.log (w.valuation N θ), ?_⟩
    linear_combination hlog
  have hdivN : 3 ∣ e * (block j).factorization p := by exact_mod_cast hdiv
  have he : 3 ∣ e := (Nat.prime_three.dvd_mul.mp hdivN).resolve_right hmod
  have hp0 : v0.asIdeal ≠ ⊥ := v0.ne_bot
  rwa [show e = w.asIdeal.ramificationIdx ℤ from
    Ideal.ramificationIdx'_eq_ramificationIdx v0.asIdeal w.asIdeal hp0] at he
theorem actual_common_cubic_unramified_outside_support
    (J p : ℕ) [NumberField (complexTower J)] (hp : p.Prime) (hp3 : p ≠ 3)
    (hmod : ∀ j : ℕ, 1 ≤ j → j ≤ J → 3 ∣ (block j).factorization p)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J)))
    (hw : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) :
    w.asIdeal.ramificationIdx ℤ = 1 := by
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
  letI : IsGalois ℚ N := (actual_common_cubic_q_galois_and_conjugation J).1
  have hunit (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ J) :
      ¬ p ∣ block j / Nat.floorRoot 3 (block j) ^ 3 := by
    have hB0 : block j ≠ 0 := by
      change (goldenLucas (3 ^ j) ^ 2 + 3).natAbs ≠ 0
      have hp : 0 < goldenLucas (3 ^ j) ^ 2 + (3 : ℤ) := by positivity
      exact Int.natAbs_ne_zero.mpr hp.ne'
    let c := Nat.floorRoot 3 (block j)
    let d := block j / c ^ 3
    have hfactor : block j = d * c ^ 3 :=
      (Nat.div_mul_cancel (show c ^ 3 ∣ block j from Nat.floorRoot_pow_dvd)).symm
    have hd0 : d ≠ 0 := by
      intro h
      exact hB0 (by rw [hfactor, h, zero_mul])
    have hdFac : d.factorization p = 0 := by
      dsimp only [d, c]
      rw [Nat.factorization_div Nat.floorRoot_pow_dvd,
        Nat.factorization_pow, Nat.factorization_floorRoot]
      change (block j).factorization p - 3 * ((block j).factorization p / 3) = 0
      have hm := hmod j hj hjJ
      have hrem := Nat.mod_eq_zero_of_dvd hm
      omega
    intro hpd
    have hpos := hp.factorization_pos_of_dvd hd0 hpd
    omega
  let I := w.asIdeal.inertia (N ≃ₐ[ℚ] N)
  have hidentity (σ : I) : σ.val = 1 := by
    have hσ := actual_common_cubic_inertia_unit_coordinates J p hp hp3 w hw σ.val σ.property
    have hMaps : σ.val.toAlgHom = (1 : N ≃ₐ[ℚ] N).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hAlgGen
      intro z hz
      rcases hz with hz | hz
      · exact hσ.1 _ (Set.mem_singleton_iff.mp hz)
      · obtain ⟨j, hj, hjJ, hzi⟩ := hz
        exact hσ.2 j hj hjJ (hunit j hj hjJ) _ hzi
    exact AlgEquiv.ext fun x => DFunLike.congr_fun hMaps x
  letI : Subsingleton I := ⟨fun σ τ => Subtype.ext
    ((hidentity σ).trans (hidentity τ).symm)⟩
  have hcard : Nat.card I = 1 := Nat.card_unique
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, hp⟩
  have hv0 : v0.asIdeal = Ideal.span {(p : ℤ)} := by
    change (Ideal.span {(p : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
    simp [Ideal.map_span]
  letI : w.asIdeal.LiesOver v0.asIdeal := hv0.symm ▸ hw
  letI : v0.asIdeal.IsPrime := v0.isPrime
  letI : w.asIdeal.IsPrime := w.isPrime
  letI : Finite (ℤ ⧸ v0.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v0.ne_bot
  have hecard : Nat.card I = w.asIdeal.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[ℚ] N) v0.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx v0.asIdeal w.asIdeal (N ≃ₐ[ℚ] N)]
  exact hecard.symm.trans hcard
private theorem actual_supported_different_exact_check
    (J j p : ℕ) [NumberField (complexTower J)]
    (hj : 1 ≤ j) (hjJ : j ≤ J) (hp : p.Prime) (hp3 : p ≠ 3)
    (hmod : ¬ 3 ∣ (block j).factorization p)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J)))
    (hw : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) :
    multiplicity w.asIdeal (differentIdeal ℤ (𝓞 (complexTower J))) = 2 := by
  classical
  let N := complexTower J
  let P := w.asIdeal
  letI : IsGalois ℚ N := (actual_common_cubic_q_galois_and_conjugation J).1
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, hp⟩
  have hv0 : v0.asIdeal = Ideal.span {(p : ℤ)} := by
    change (Ideal.span {(p : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
    simp [Ideal.map_span]
  letI : P.LiesOver v0.asIdeal := hv0.symm ▸ hw
  letI : v0.asIdeal.IsPrime := v0.isPrime
  letI : P.IsPrime := w.isPrime
  letI : v0.asIdeal.IsMaximal := v0.isPrime.isMaximal v0.ne_bot
  letI : P.IsMaximal := w.isPrime.isMaximal w.ne_bot
  letI : Finite (ℤ ⧸ v0.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v0.ne_bot
  letI : Field (ℤ ⧸ v0.asIdeal) := Ideal.Quotient.field v0.asIdeal
  letI : Field ((𝓞 N) ⧸ P) := Ideal.Quotient.field P
  have hecard : Nat.card (P.inertia (N ≃ₐ[ℚ] N)) = P.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[ℚ] N) v0.asIdeal P,
      Ideal.ramificationIdxIn_eq_ramificationIdx v0.asIdeal P (N ≃ₐ[ℚ] N)]
  have hpj : p ∣ block j := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_dvd h] at hmod
    exact hmod (dvd_zero 3)
  have hle := actual_common_cubic_inertia_card_le_three J j p hj hjJ hp hp3 hpj w hw
  rw [hecard] at hle
  have hdiv := actual_common_cubic_ramification_three_divides J j p hj hjJ hp hmod w hw
  have he : P.ramificationIdx ℤ = 3 := Nat.le_antisymm hle
    (Nat.le_of_dvd (Ideal.ramificationIdx_pos P ℤ) hdiv)
  have hthree : (3 : ℤ ⧸ v0.asIdeal) ≠ 0 := by
    intro h
    have hq : Ideal.Quotient.mk v0.asIdeal (3 : ℤ) = 0 :=
      (map_natCast (Ideal.Quotient.mk v0.asIdeal) 3).trans h
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hq
    rw [hv0] at hmem
    have hdvd : (p : ℤ) ∣ 3 := Ideal.mem_span_singleton.mp hmem
    have hdvdN : p ∣ 3 := by exact_mod_cast hdvd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvdN)
  have hpMap : Ideal.map (algebraMap ℤ (𝓞 N)) v0.asIdeal ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 N))).not.mpr v0.ne_bot
  obtain ⟨Q, hsup, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hpMap P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    v0.asIdeal P hpMap, he] at hfactor
  have hPQ : IsCoprime (P ^ 3) Q := (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  have hsep : Algebra.IsSeparable (ℤ ⧸ v0.asIdeal) ((𝓞 N) ⧸ P) := inferInstance
  have hnot : ¬ P ^ 3 ∣ differentIdeal ℤ (𝓞 N) := by
    rw [D5.S3.Factorization.Dedekind.TameDifferent.prime_power_divides_different_iff
      ℤ v0.ne_bot P Q hPQ hfactor.symm]
    exact not_or.mpr ⟨not_not.mpr hsep, hthree⟩
  have hlower : P ^ 2 ∣ differentIdeal ℤ (𝓞 N) := by
    simpa only [Nat.reduceSub] using
      (pow_sub_one_dvd_differentIdeal ℤ P 3 v0.ne_bot ⟨Q, hfactor⟩)
  exact multiplicity_eq_of_emultiplicity_eq_some
    (emultiplicity_eq_coe.mpr ⟨hlower, hnot⟩)
private theorem actual_common_cubic_three_absolute_different
    (J : ℕ) [NumberField (complexTower J)]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (complexTower J)))
    (hw : w.asIdeal.LiesOver (Ideal.span {(3 : ℤ)})) :
    multiplicity w.asIdeal (differentIdeal ℤ (𝓞 (complexTower J))) = 1 := by
  classical
  let N := complexTower J
  let P := w.asIdeal
  obtain ⟨hN, c, hccoe, hcount, hlocal, huniq⟩ := actual_common_cubic_three_prime_orbits J
  letI : IsGalois ℚ N := (actual_common_cubic_q_galois_and_conjugation J).1
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨3, Nat.prime_three⟩
  have hv0 : v0.asIdeal = Ideal.span {(3 : ℤ)} := by
    change (Ideal.span {(3 : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
    simp [Ideal.map_span]
  letI : P.LiesOver v0.asIdeal := hv0.symm ▸ hw
  letI : v0.asIdeal.IsPrime := v0.isPrime
  letI : P.IsPrime := w.isPrime
  letI : v0.asIdeal.IsMaximal := v0.isPrime.isMaximal v0.ne_bot
  letI : P.IsMaximal := w.isPrime.isMaximal w.ne_bot
  letI : Finite (ℤ ⧸ v0.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v0.ne_bot
  letI : Field (ℤ ⧸ v0.asIdeal) := Ideal.Quotient.field v0.asIdeal
  letI : Field ((𝓞 N) ⧸ P) := Ideal.Quotient.field P
  have he : P.ramificationIdx ℤ = 2 := (hlocal w hw).1
  have htwo : (2 : ℤ ⧸ v0.asIdeal) ≠ 0 := by
    intro h
    have hq : Ideal.Quotient.mk v0.asIdeal (2 : ℤ) = 0 :=
      (map_natCast (Ideal.Quotient.mk v0.asIdeal) 2).trans h
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hq
    rw [hv0] at hmem
    have hdvd : (3 : ℤ) ∣ 2 := Ideal.mem_span_singleton.mp hmem
    norm_num at hdvd
  have hpMap : Ideal.map (algebraMap ℤ (𝓞 N)) v0.asIdeal ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 N))).not.mpr v0.ne_bot
  obtain ⟨Q, hsup, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hpMap P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    v0.asIdeal P hpMap, he] at hfactor
  have hPQ : IsCoprime (P ^ 2) Q := (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  have hsep : Algebra.IsSeparable (ℤ ⧸ v0.asIdeal) ((𝓞 N) ⧸ P) := inferInstance
  have hnot : ¬ P ^ 2 ∣ differentIdeal ℤ (𝓞 N) := by
    rw [D5.S3.Factorization.Dedekind.TameDifferent.prime_power_divides_different_iff
      ℤ v0.ne_bot P Q hPQ hfactor.symm]
    exact not_or.mpr ⟨not_not.mpr hsep, htwo⟩
  have hlower : P ^ 1 ∣ differentIdeal ℤ (𝓞 N) := by
    simpa only [Nat.reduceSub] using
      (pow_sub_one_dvd_differentIdeal ℤ P 2 v0.ne_bot ⟨Q, hfactor⟩)
  exact multiplicity_eq_of_emultiplicity_eq_some
    (emultiplicity_eq_coe.mpr ⟨hlower, hnot⟩)
theorem actual_common_cubic_absolute_different_sixth_power
    (J : ℕ) [NumberField (complexTower J)] :
    let R := ∏ j ∈ Finset.Icc 1 J,
      radical (block j / Nat.floorRoot 3 (block j) ^ 3)
    (differentIdeal ℤ (𝓞 (complexTower J))) ^ 6 =
      (Ideal.span {(3 : 𝓞 (complexTower J))}) ^ 3 *
        (Ideal.span {(R : 𝓞 (complexTower J))}) ^ 4 := by
  classical
  let N := complexTower J
  let R := ∏ j ∈ Finset.Icc 1 J,
    radical (block j / Nat.floorRoot 3 (block j) ^ 3)
  let D := differentIdeal ℤ (𝓞 N)
  let A3 : Ideal (𝓞 N) := Ideal.span {(3 : 𝓞 N)}
  let AR : Ideal (𝓞 N) := Ideal.span {(R : 𝓞 N)}
  have hRfacts : Squarefree R ∧ ¬ 3 ∣ R ∧
      (∀ p : ℕ, p.Prime → (p ∣ R ↔
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ ¬ 3 ∣ (block j).factorization p)) := by
    classical
    let d := fun j => block j / Nat.floorRoot 3 (block j) ^ 3
    let r := fun j => radical (d j)
    let R := ∏ j ∈ Finset.Icc 1 J, r j
    have hbne (j : ℕ) : block j ≠ 0 := by
      change (goldenLucas (3 ^ j) ^ 2 + 3).natAbs ≠ 0
      apply Int.natAbs_ne_zero.mpr
      have h := sq_nonneg (goldenLucas (3 ^ j))
      nlinarith
    have hdne (j : ℕ) : d j ≠ 0 := by
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (hbne j))
        (Nat.floorRoot_pow_dvd (n := 3) (a := block j)))
        (pow_pos (Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨by decide, hbne j⟩)) 3)).ne'
    have hdFactor (j p : ℕ) : (d j).factorization p = (block j).factorization p % 3 := by
      dsimp only [d]
      rw [Nat.factorization_div (Nat.floorRoot_pow_dvd (n := 3) (a := block j)),
        Nat.factorization_pow, Nat.factorization_floorRoot]
      simp only [Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
      omega
    have hrBlock (j : ℕ) : r j ∣ block j :=
      dvd_trans radical_dvd_self (Nat.div_dvd_of_dvd
        (Nat.floorRoot_pow_dvd (n := 3) (a := block j)))
    have hrSupport (j p : ℕ) (hp : p.Prime) : p ∣ r j ↔ ¬ 3 ∣ (block j).factorization p := by
      rw [dvd_radical_iff_of_irreducible hp.prime.irreducible (hdne j)]
      have hzero : (d j).factorization p = 0 ↔ ¬ p ∣ d j := by
        simp only [Nat.factorization_eq_zero_iff, hp, hdne j, not_true_eq_false,
          or_false, false_or]
      have hnonzero : p ∣ d j ↔ (d j).factorization p ≠ 0 := by
        simpa only [not_not] using (not_congr hzero).symm
      rw [hnonzero, hdFactor, Nat.dvd_iff_mod_eq_zero]
    have hpair : Set.Pairwise (Finset.Icc 1 J : Set ℕ) (fun i j => IsRelPrime (r i) (r j)) := by
      intro i hi j hj hij
      apply Nat.coprime_iff_isRelPrime.mp
      exact Nat.Coprime.of_dvd (hrBlock i) (hrBlock j)
        (D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods.2.1
          i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij)
    have hsq : Squarefree R := Finset.squarefree_prod_of_pairwise_isCoprime hpair
      (fun j hj => squarefree_radical)
    have hsupport (p : ℕ) (hp : p.Prime) : p ∣ R ↔
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ ¬ 3 ∣ (block j).factorization p := by
      rw [hp.prime.dvd_finsetProd_iff r]
      simp only [Finset.mem_Icc, hrSupport _ _ hp, and_assoc]
    have hblock3 (j : ℕ) (hj : 1 ≤ j) : ¬ 3 ∣ block j := by
      intro hdiv
      have hbcast : (block j : ℤ) = goldenLucas (3 ^ j) ^ 2 + 3 := by
        simp [block, abs_of_nonneg (by positivity : 0 ≤ goldenLucas (3 ^ j) ^ 2 + 3)]
      have hdivI : (3 : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
        rw [← hbcast]
        exact Int.natCast_dvd.mpr hdiv
      have hzmod := (golden_cubic_lucas_block j hj).2.2.1
      have hmod9 : (goldenLucas (3 ^ j) ^ 2 + 3) % 9 = 1 :=
        (ZMod.intCast_eq_intCast_iff' _ 1 9).mp hzmod
      have hmod3 := Int.emod_eq_zero_of_dvd hdivI
      omega
    have hnot3 : ¬ 3 ∣ R := by
      intro h
      obtain ⟨j, hj, hjJ, hmod⟩ := (hsupport 3 Nat.prime_three).mp h
      rw [Nat.factorization_eq_zero_of_not_dvd (hblock3 j hj)] at hmod
      exact hmod (dvd_zero 3)
    exact ⟨hsq, hnot3, hsupport⟩
  obtain ⟨hRsq, hR3, hRsupport⟩ := hRfacts
  have hRne : R ≠ 0 := hRsq.ne_zero
  have hDne : D ≠ ⊥ := differentIdeal_ne_bot
  have hA3ne : A3 ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hARne : AR ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hRne)
  have hrightne : A3 ^ 3 * AR ^ 4 ≠ 0 := mul_ne_zero (pow_ne_zero _ hA3ne) (pow_ne_zero _ hARne)
  have hleftne : D ^ 6 ≠ 0 := pow_ne_zero _ hDne
  have hequal (P : Ideal (𝓞 N)) (hPprime : Prime P) :
      emultiplicity P (D ^ 6) = emultiplicity P (A3 ^ 3 * AR ^ 4) := by
    letI : P.IsPrime := Ideal.isPrime_of_prime hPprime
    letI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPprime.ne_zero
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 N) := ⟨P, inferInstance, hPprime.ne_zero⟩
    obtain ⟨p, n, hn, hpP, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have hPover : P.LiesOver (Ideal.span {(p : ℤ)}) :=
      (Ideal.liesOver_span_iff (inferInstance : P.IsPrime).ne_top
        (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa only [map_natCast] using hpP)
    letI := hPover
    let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, hp⟩
    have hv0 : v0.asIdeal = Ideal.span {(p : ℤ)} := by
      change (Ideal.span {(p : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
      simp [Ideal.map_span]
    letI : P.LiesOver v0.asIdeal := hv0.symm ▸ hPover
    letI : v0.asIdeal.IsPrime := v0.isPrime
    letI : v0.asIdeal.IsMaximal := v0.isPrime.isMaximal v0.ne_bot
    letI : Field (ℤ ⧸ v0.asIdeal) := Ideal.Quotient.field v0.asIdeal
    letI : Finite (ℤ ⧸ v0.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v0.ne_bot
    letI : Field ((𝓞 N) ⧸ P) := Ideal.Quotient.field P
    have hspan (a : ℕ) (ha : a ≠ 0) :
        emultiplicity P (Ideal.span {(a : 𝓞 N)}) =
          (P.ramificationIdx ℤ : ℕ∞) * (a.factorization p : ℕ∞) := by
      have haI : (Ideal.span {(a : ℤ)} : Ideal ℤ) ≠ ⊥ :=
        Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr ha)
      have hvprime : Irreducible v0.asIdeal := by
        rw [hv0]
        exact (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp hp)).irreducible
      have hmap := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
        haI hvprime hPprime.irreducible hPprime.ne_zero
      rw [Ideal.map_span, Set.image_singleton, map_natCast,
        Ideal.ramificationIdx'_eq_ramificationIdx v0.asIdeal P v0.ne_bot, hv0,
        Ideal.emultiplicity_eq_emultiplicity_span, Int.natCast_emultiplicity,
        (Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.pos_of_ne_zero ha⟩).emultiplicity_eq_multiplicity,
        Nat.multiplicity_eq_factorization hp ha] at hmap
      exact hmap
    have hDmult : emultiplicity P D = (multiplicity P D : ℕ∞) :=
      (FiniteMultiplicity.of_prime_left hPprime hDne).emultiplicity_eq_multiplicity
    rw [emultiplicity_pow hPprime, emultiplicity_mul hPprime,
      emultiplicity_pow hPprime, emultiplicity_pow hPprime]
    change (6 : ℕ∞) * emultiplicity P D =
      (3 : ℕ∞) * emultiplicity P (Ideal.span {((3 : ℕ) : 𝓞 N)}) +
        (4 : ℕ∞) * emultiplicity P (Ideal.span {(R : 𝓞 N)})
    rw [hspan 3 (by decide), hspan R hRne, hDmult]
    by_cases hp3 : p = 3
    · subst p
      obtain ⟨hN, c, hccoe, hcount, hlocal, huniq⟩ := actual_common_cubic_three_prime_orbits J
      have he : P.ramificationIdx ℤ = 2 := (hlocal w hPover).1
      have hm : multiplicity P D = 1 := actual_common_cubic_three_absolute_different J w hPover
      have hRfact : R.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hR3
      rw [he, hm, hRfact]
      norm_num
    · have h3fact : (3 : ℕ).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun h => hp3
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))
      rw [h3fact]
      by_cases hpR : p ∣ R
      · obtain ⟨j, hj, hjJ, hmod⟩ := (hRsupport p hp).mp hpR
        have hpj : p ∣ block j := by
          by_contra h
          rw [Nat.factorization_eq_zero_of_not_dvd h] at hmod
          exact hmod (dvd_zero 3)
        have hle := actual_common_cubic_inertia_card_le_three J j p hj hjJ hp hp3 hpj w hPover
        have hdiv := actual_common_cubic_ramification_three_divides J j p hj hjJ hp hmod w hPover
        have hcard : Nat.card (P.inertia (N ≃ₐ[ℚ] N)) = P.ramificationIdx ℤ := by
          letI : IsGalois ℚ N := (actual_common_cubic_q_galois_and_conjugation J).1
          rw [Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[ℚ] N) v0.asIdeal P,
            Ideal.ramificationIdxIn_eq_ramificationIdx v0.asIdeal P (N ≃ₐ[ℚ] N)]
        rw [hcard] at hle
        have he : P.ramificationIdx ℤ = 3 := Nat.le_antisymm hle
          (Nat.le_of_dvd (Ideal.ramificationIdx_pos P ℤ) hdiv)
        have hm : multiplicity P D = 2 := actual_supported_different_exact_check J j p
          hj hjJ hp hp3 hmod w hPover
        have hRfact : R.factorization p = 1 := Nat.factorization_eq_one_of_squarefree hRsq hp hpR
        rw [he, hm, hRfact]
        norm_num
      · have hRfact : R.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpR
        have hnoSupport : ∀ j : ℕ, 1 ≤ j → j ≤ J → 3 ∣ (block j).factorization p := by
          intro j hj hjJ
          by_contra h
          exact hpR ((hRsupport p hp).mpr ⟨j, hj, hjJ, h⟩)
        have he : P.ramificationIdx ℤ = 1 :=
          actual_common_cubic_unramified_outside_support J p hp hp3 hnoSupport w hPover
        have hpMap : Ideal.map (algebraMap ℤ (𝓞 N)) v0.asIdeal ≠ ⊥ :=
          (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 N))).not.mpr v0.ne_bot
        obtain ⟨Q, hsup, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hpMap P
        rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
          v0.asIdeal P hpMap, he, pow_one] at hfactor
        have hnot : ¬ P ∣ D := not_dvd_differentIdeal_of_isCoprime_of_isSeparable
          ℤ P Q (Ideal.isCoprime_iff_sup_eq.mpr hsup) hfactor.symm
        have hm : multiplicity P D = 0 := multiplicity_eq_of_dvd_of_not_dvd (one_dvd D) (by simpa only [Nat.zero_add, pow_one] using hnot)
        rw [hm, hRfact]
        simp
  apply associated_iff_eq.mp
  apply dvd_dvd_iff_associated.mp
  constructor
  · rw [dvd_iff_emultiplicity_le hleftne]
    intro P hP
    exact (hequal P hP).le
  · rw [dvd_iff_emultiplicity_le hrightne]
    intro P hP
    exact (hequal P hP).symm.le
end D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants

#print axioms D5.S3.Factorization.Galois.GoldenCubicBlockCommonDiscriminants.actual_common_cubic_absolute_different_sixth_power
