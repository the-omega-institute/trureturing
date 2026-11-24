/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterPositiveDegree
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterPositiveEmbedding

/-! Ordered spanning and the finite diagonal denominator exhaust the native
positive BRST root spaces once the positive Serre map is injective. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 150000
set_option synthInstance.maxSize 512

noncomputable section

open scoped Classical BigOperators DirectSum

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open MonsterPositiveCocycle MonsterPositiveStringPresentation
local notation "monsterMultiplicity" => ActualLeechOrbifoldMonsterDenominator.multiplicity
open OrderedLieMonomials WeightedFreeAlgebraEulerSeries

local notation "SG" => stringGrade monsterRealOrder
local notation "PG" => presentationGrade monsterRealOrder
local notation "A" => StringLie monsterRealOrder
local notation "W" => realMomentumGrade
local notation "φ" => monsterPositiveToRealBRST

private def stringGradeMap (p : Weight) : SG p →ₗ[ℝ] W (monsterNativeMomentum p) :=
  ((monsterPositiveToRealBRST.toLinearMap.comp (stringMap monsterRealOrder).toLinearMap).comp (SG p).subtype).codRestrict _
    (fun x => monsterPositiveToRealBRST_mem_grade
      (stringMap_mem_presentationGrade monsterRealOrder x.property))

private theorem stringGradeMap_injective (hinj : Function.Injective φ) (p : Weight) :
    Function.Injective (stringGradeMap p) := by
  intro x y h
  apply Subtype.ext
  exact stringMap_injective monsterRealOrder (hinj (congrArg Subtype.val h))

private theorem stringGrade_finite (hinj : Function.Injective φ) (p : Weight) :
    FiniteDimensional ℝ (SG p) := by
  let : FiniteDimensional ℝ (W (monsterNativeMomentum p)) :=
    realMomentumWeightSpace_finiteDimensional _
  exact FiniteDimensional.of_injective _ (stringGradeMap_injective hinj p)

private abbrev StringBasisIndex :=
  Σ p : Weight, Fin (Module.finrank ℝ (SG p))

private def stringPieceBasis (hinj : Function.Injective φ) (p : Weight) :
    Module.Basis (Fin (Module.finrank ℝ (SG p))) ℝ (SG p) :=
  letI := stringGrade_finite hinj p
  Module.finBasis ℝ _

private def stringBasis (hinj : Function.Injective φ) : Module.Basis StringBasisIndex ℝ A :=
  (DirectSum.Decomposition.isInternal SG).collectedBasis (stringPieceBasis hinj)

private def weightTotal (p : Weight) : ℕ := (p.1 + p.2).toNat

private def basisDegree (i : StringBasisIndex) : ℕ := weightTotal i.1

private theorem stringBasisIndex_positive (i : StringBasisIndex) :
    0 < i.1.1 ∧ 0 < i.1.2 := by
  by_contra h
  have hz := stringGrade_eq_bot_of_outside monsterRealOrder i.1 h
  have hi := i.2.isLt
  have hdim : Module.finrank ℝ (SG i.1) = 0 := by rw [hz, finrank_bot]
  omega

private theorem basisDegree_pos (i : StringBasisIndex) : 0 < basisDegree i := by
  have := stringBasisIndex_positive i
  unfold basisDegree weightTotal
  omega

private def basisIndexSlice (s : ℕ → Prop) :
    {i : StringBasisIndex // s (basisDegree i)} ≃
      Σ p : {p : Weight // (0 < p.1 ∧ 0 < p.2) ∧ s (weightTotal p)},
        Fin (Module.finrank ℝ (SG p.val)) :=
  (Equiv.subtypeEquiv (Equiv.refl StringBasisIndex)
    (fun i => (and_iff_right (stringBasisIndex_positive i)).symm)).trans
    (Equiv.subtypeSigmaEquiv _ _)

private theorem finite_basisDegree_cutoff (d : ℕ) : Finite {i : StringBasisIndex // basisDegree i ≤ d} := by
  let f : {p : Weight // (0 < p.1 ∧ 0 < p.2) ∧ weightTotal p ≤ d} → Fin (d + 1) × Fin (d + 1) :=
    fun p =>
      have h := p.property
      have hsum : (p.1.1 + p.1.2).toNat ≤ d := h.2
      (⟨p.1.1.toNat, by omega⟩, ⟨p.1.2.toNat, by omega⟩)
  let : Finite {p : Weight // (0 < p.1 ∧ 0 < p.2) ∧ weightTotal p ≤ d} :=
    Finite.of_injective f (by
      intro p q h
      have h₁ := congrArg (fun x : Fin (d + 1) × Fin (d + 1) => x.1.val) h
      have h₂ := congrArg (fun x : Fin (d + 1) × Fin (d + 1) => x.2.val) h
      change p.1.1.toNat = q.1.1.toNat at h₁
      change p.1.2.toNat = q.1.2.toNat at h₂
      have hp := p.property.1
      have hq := q.property.1
      exact Subtype.ext (Prod.ext (by omega) (by omega)))
  exact Finite.of_injective (basisIndexSlice (· ≤ d)) (basisIndexSlice (· ≤ d)).injective

private def paperWeight (p : ℕ × ℕ) : Weight := (p.1, p.2)

private def imaginaryPairEquiv (d : ℕ) :
    {p : Weight // (0 < p.1 ∧ 0 < p.2) ∧ weightTotal p = d} ≃ monsterImaginaryPairs d where
  toFun p := ⟨(p.1.1.toNat, p.1.2.toNat), by
    rw [mem_monsterImaginaryPairs]
    have h := p.property.1
    have hd := p.property.2
    unfold weightTotal at hd
    change p.1.1.toNat + p.1.2.toNat = d ∧ 0 < p.1.1.toNat ∧ 0 < p.1.2.toNat
    omega⟩
  invFun p := ⟨paperWeight p.val, by
    have h := (mem_monsterImaginaryPairs d p.val).mp p.property
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change 0 < (p.val.1 : ℤ)
      exact_mod_cast h.2.1
    · change 0 < (p.val.2 : ℤ)
      exact_mod_cast h.2.2
    · change ((p.val.1 : ℤ) + (p.val.2 : ℤ)).toNat = d
      rw [← Nat.cast_add, Int.toNat_natCast, h.1]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · have h := p.property.1.1
      change (p.1.1.toNat : ℤ) = p.1.1
      omega
    · have h := p.property.1.2
      change (p.1.2.toNat : ℤ) = p.1.2
      omega
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (Int.toNat_natCast _) (Int.toNat_natCast _)

private def stringMultiplicity (d : ℕ) : ℕ :=
  ∑ x ∈ monsterImaginaryPairs d, Module.finrank ℝ (SG (paperWeight x))

private theorem stringGrade_finrank_le (hinj : Function.Injective φ) (p : ℕ × ℕ)
    (hp : 0 < p.1) :
    Module.finrank ℝ (SG (paperWeight p)) ≤ monsterMultiplicity p.1 p.2 := by
  let : FiniteDimensional ℝ (W (monsterNativeMomentum (paperWeight p))) :=
    realMomentumWeightSpace_finiteDimensional _
  have hdim : Module.finrank ℝ (W (monsterNativeMomentum (paperWeight p))) =
      monsterMultiplicity p.1 p.2 := monsterImaginaryGrade_finrank p.1 p.2 hp
  rw [← hdim]
  exact (stringGradeMap (paperWeight p)).finrank_le_finrank_of_injective
    (stringGradeMap_injective hinj _)

private theorem stringMultiplicity_le (hinj : Function.Injective φ) :
    stringMultiplicity ≤ monsterNativeImaginaryMultiplicity := by
  intro d
  exact Finset.sum_le_sum fun p hp =>
    stringGrade_finrank_le hinj p ((mem_monsterImaginaryPairs d p).mp hp).2.1

private theorem finrank_basisWeightSpace_eq_stringMultiplicity (hinj : Function.Injective φ) (d : ℕ) :
    Module.finrank ℝ (basisWeightSpace (stringBasis hinj) basisDegree d) = stringMultiplicity d := by
  let e := (basisIndexSlice (· = d)).trans
    (Equiv.sigmaCongrLeft' (imaginaryPairEquiv d))
  let : Fintype {i : StringBasisIndex // basisDegree i = d} := Fintype.ofEquiv _ e.symm
  change Module.finrank ℝ (Submodule.span ℝ (Set.range
    (⇑(stringBasis hinj) ∘ (Subtype.val : {i : StringBasisIndex // basisDegree i = d} → _)))) = _
  rw [finrank_span_eq_card ((stringBasis hinj).linearIndependent.comp Subtype.val Subtype.val_injective),
    ← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_sigma]
  simp only [Nat.card_fin, stringMultiplicity]
  change (∑ x : monsterImaginaryPairs d, Module.finrank ℝ (SG (paperWeight x.val))) = _
  exact Finset.sum_coe_sort (monsterImaginaryPairs d)
    (fun x => Module.finrank ℝ (SG (paperWeight x)))

private theorem basisDegree_bracket (hinj : Function.Injective φ) :
    BracketHomogeneous (stringBasis hinj) basisDegree := by
  rintro i j ⟨p, k⟩ hk
  have hmem : ⁅stringBasis hinj i, stringBasis hinj j⁆ ∈ SG (i.1 + j.1) :=
    stringGrade_bracket monsterRealOrder
      (DirectSum.IsInternal.collectedBasis_mem _ _ i)
      (DirectSum.IsInternal.collectedBasis_mem _ _ j)
  have hp : i.1 + j.1 = p := by
    by_contra h
    exact hk (DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ h hmem)
  subst p
  have hi := stringBasisIndex_positive i
  have hj := stringBasisIndex_positive j
  change ((i.1.1 + j.1.1) + (i.1.2 + j.1.2)).toNat =
    (i.1.1 + i.1.2).toNat + (j.1.1 + j.1.2).toNat
  omega

private theorem basisDegree_of_token (hinj : Function.Injective φ) (w : MonsterStringToken)
    (i : StringBasisIndex) (hi : (stringBasis hinj).repr (FreeLieAlgebra.of ℝ w) i ≠ 0) :
    basisDegree i = monsterStringDegree w := by
  obtain ⟨p, j⟩ := i
  have hp : tokenWeight monsterRealOrder w = p := by
    by_contra h
    exact hi (DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ h
      (token_mem_stringGrade monsterRealOrder w))
  subst p
  have h := monsterStringDegree_eq_coordinates w
  change ((tokenWeight monsterRealOrder w).1 + (tokenWeight monsterRealOrder w).2).toNat = _
  omega

private theorem stringMultiplicity_eq_native (hinj : Function.Injective φ) :
    stringMultiplicity = monsterNativeImaginaryMultiplicity := by
  let : LinearOrder StringBasisIndex := IsWellOrder.linearOrder WellOrderingRel
  apply multiplicities_eq_of_freeAlgebra_euler_sandwich_of_denominator ℝ ℤ
    monsterStringDegree monsterStringDegree_pos finite_monsterStringDegree_cutoff
    (Nat.eq_zero_of_le_zero (by simpa using stringMultiplicity_le hinj 0))
    monsterNativeImaginaryMultiplicity_zero (stringMultiplicity_le hinj) ?_
    monsterNative_truncatedEulerDenominator
  intro d
  let : Finite {i : StringBasisIndex // basisDegree i ≤ d} := finite_basisDegree_cutoff d
  simpa only [finrank_basisWeightSpace_eq_stringMultiplicity hinj] using
    finrank_freeAlgebraWeightSpace_le_eulerCoeff (stringBasis hinj) basisDegree
      (basisDegree_bracket hinj) monsterStringDegree (basisDegree_of_token hinj) basisDegree_pos d

private theorem stringGradeMap_surjective (hinj : Function.Injective φ) (p : ℕ × ℕ)
    (hp : 0 < p.1 ∧ 0 < p.2) : Function.Surjective (stringGradeMap (paperWeight p)) := by
  let d := p.1 + p.2
  have hmem : p ∈ monsterImaginaryPairs d := (mem_monsterImaginaryPairs d p).mpr ⟨rfl, hp⟩
  have hle (q : ℕ × ℕ) (hq : q ∈ monsterImaginaryPairs d) :
      Module.finrank ℝ (SG (paperWeight q)) ≤ monsterMultiplicity q.1 q.2 :=
    stringGrade_finrank_le hinj q ((mem_monsterImaginaryPairs d q).mp hq).2.1
  have heq := congrFun (stringMultiplicity_eq_native hinj) d
  have hdim := (Finset.sum_eq_sum_iff_of_le hle).mp heq p hmem
  let : FiniteDimensional ℝ (SG (paperWeight p)) := stringGrade_finite hinj _
  let : FiniteDimensional ℝ (W (monsterNativeMomentum (paperWeight p))) :=
    realMomentumWeightSpace_finiteDimensional _
  have hnative : Module.finrank ℝ (W (monsterNativeMomentum (paperWeight p))) =
      monsterMultiplicity p.1 p.2 := monsterImaginaryGrade_finrank p.1 p.2 hp.1
  rw [← hnative] at hdim
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (stringGradeMap_injective hinj _)

/-- The actual positive Serre map is surjective onto every positive native root space.
Its one premise is the injectivity of that same homomorphism. -/
private theorem monsterPositiveToRealBRSTGrade_surjective_of_injective (hinj : Function.Injective φ)
    (p : Weight) (hp : 0 < p.1) : Function.Surjective (monsterPositiveToRealBRSTGrade p) := by
  by_cases hr : p = realRoot
  · subst p
    intro x
    obtain ⟨r, hr⟩ := monsterPositiveRealGrade_span x
    refine ⟨⟨r • generator monsterRealOrder none,
      (PG realRoot).smul_mem r (real_mem_presentationGrade monsterRealOrder)⟩, ?_⟩
    apply Subtype.ext
    change φ (r • generator monsterRealOrder none) = x.val
    rw [map_smul, monsterPositiveToRealBRST_generator]
    exact hr
  · by_cases hn : 0 < p.2
    · let q : ℕ × ℕ := (p.1.toNat, p.2.toNat)
      have hq : 0 < q.1 ∧ 0 < q.2 := by dsimp [q]; omega
      have he : paperWeight q = p := by
        apply Prod.ext <;> dsimp [paperWeight, q] <;> omega
      rw [← he]
      intro x
      obtain ⟨y, hy⟩ := stringGradeMap_surjective hinj q hq x
      exact ⟨⟨stringMap monsterRealOrder y, stringMap_mem_presentationGrade monsterRealOrder y.property⟩, hy⟩
    · intro x
      refine ⟨0, ?_⟩
      rw [map_zero]
      apply Subtype.ext
      have hle : W (monsterNativeMomentum p) ≤ ⊥ :=
        le_of_eq (monsterNativeGrade_eq_bot_of_outside p hp hr hn)
      exact ((Submodule.mem_bot ℝ).mp (hle x.property)).symm

/-- Every positive native BRST root vector is the image of a vector of the same
paper weight under the actual positive Serre homomorphism. -/
theorem monsterPositiveToRealBRSTGrade_surjective (p : Weight) (hp : 0 < p.1) :
    Function.Surjective (monsterPositiveToRealBRSTGrade p) :=
  monsterPositiveToRealBRSTGrade_surjective_of_injective monsterPositiveToRealBRST_injective p hp

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
