/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterNegativeEmbedding
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterNegativeEmbedding
   mirror-E: none(waiver:native-real-BRST)
   anchors: []
   utility: none
   digest: Inject the negative Monster Serre presentation using native charge reversal. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterRankTwoComparison
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealChargeReversal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

noncomputable section

open scoped Classical DirectSum

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open MonsterPositiveCocycle MonsterPositiveStringPresentation MonsterPositivePresentationInjectivity
open MonsterPresentationBracketScalar (presentation_lieSpan_eq_top)
open RealRootBracket (monsterSimpleMomentum)

local notation "J" => MonsterRealImaginaryIndex
local notation "P" => PositivePresentation monsterRealOrder
local notation "G" => presentationGrade monsterRealOrder
local notation "L" => momentumRealLie
local notation "W" => realMomentumGrade
local notation "N" => RealPositiveMomentumSum

private theorem negative_simple_ne_zero : monsterRealNegativeGenerator none ≠ 0 := by
  intro hz
  have hf : monsterRealSimpleF = 0 := Subtype.ext hz
  have hpair := monsterRealSimple_pair
  rw [hf, map_zero] at hpair
  exact zero_ne_one hpair

private theorem negative_injOn_span {ι : Type*} (v : ι → P)
    (hv : LinearIndependent ℝ (monsterNegativeToRealBRST ∘ v)) :
    Set.InjOn monsterNegativeToRealBRST (Submodule.span ℝ (Set.range v) : Set P) := by
  intro x hx y hy hxy
  rw [SetLike.mem_coe, ← Finsupp.range_linearCombination] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  apply congrArg (Finsupp.linearCombination ℝ v)
  apply hv
  change monsterNegativeToRealBRST.toLinearMap (Finsupp.linearCombination ℝ v a) =
    monsterNegativeToRealBRST.toLinearMap (Finsupp.linearCombination ℝ v b) at hxy
  rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination] at hxy
  exact hxy

private theorem negative_injOn_first (n : ℤ) :
    Set.InjOn monsterNegativeToRealBRST (G (1, n) : Set P) := by
  by_cases hreal : n = -1
  · subst n
    change Set.InjOn monsterNegativeToRealBRST (G realRoot : Set P)
    rw [presentationGrade_real monsterRealOrder]
    intro x hx y hy hxy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [map_smul, monsterNegativeToRealBRST_generator] at hxy
    have h : (a - b) • monsterRealNegativeGenerator none = 0 := by rw [sub_smul, hxy, sub_self]
    rw [sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right negative_simple_ne_zero)]
  by_cases hn : 0 < n
  · let m : ℕ+ := ⟨n.toNat, by omega⟩
    have hm : ((m : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn.le
    rw [← hm, presentationGrade_first monsterRealOrder _ (by omega)]
    have hspan : {x : P | ∃ j : J, ((monsterRealOrder j : ℕ) : ℤ) = (m : ℕ) ∧
        x = generator monsterRealOrder (some j)} =
        Set.range (fun i => generator monsterRealOrder (some (⟨m, i⟩ : J))) := by
      ext x
      constructor
      · rintro ⟨⟨k, i⟩, hk, rfl⟩
        have hkm : k = m := PNat.coe_injective (Int.ofNat.inj hk)
        subst k
        exact Set.mem_range_self i
      · rintro ⟨i, rfl⟩
        exact ⟨⟨m, i⟩, rfl, rfl⟩
    rw [hspan]
    apply negative_injOn_span
    change LinearIndependent ℝ (fun i =>
      monsterNegativeToRealBRST (generator monsterRealOrder (some (⟨m, i⟩ : J))))
    simp only [monsterNegativeToRealBRST_generator]
    exact (monsterRealNegativeBasis m).linearIndependent.map_injOn
      (W (-monsterSimpleMomentum m)).subtype Subtype.val_injective.injOn
  · rw [presentationGrade_eq_bot_of_outside monsterRealOrder (1, n)
      (by simpa [realRoot] using hreal) (by simpa using hn)]
    intro x hx y hy _
    exact (Submodule.mem_bot ℝ).mp hx |>.trans ((Submodule.mem_bot ℝ).mp hy).symm

private def reversedNegative : P →ₗ⁅ℝ⁆ L :=
  realChargeReversalLieEquiv.toLieHom.comp monsterNegativeToRealBRST

private theorem reversedNegative_mem_grade (p : Weight) (x : G p) :
    reversedNegative x ∈ W (monsterNativeMomentum p) := by
  have h := realChargeReversalLieEquiv_mem_weightSpace
    (monsterNegativeToRealBRST_mem_grade x.property)
  change realChargeReversalLieEquiv (monsterNegativeToRealBRST x) ∈
    realMomentumWeightSpace (monsterNativeMomentum p)
  simpa only [neg_neg] using h

private theorem reversedNegative_mem_positive (x : P) :
    reversedNegative x ∈ realPositiveMomentumLie := by
  have h : LieSubalgebra.lieSpan ℝ P (Set.range (generator monsterRealOrder)) ≤
      realPositiveMomentumLie.comap reversedNegative := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨a, rfl⟩
    have hmem : generator monsterRealOrder a ∈ G (monsterRealSimpleWeight a) := by
      cases a with
      | none => exact real_mem_presentationGrade monsterRealOrder
      | some j => exact imaginary_mem_presentationGrade monsterRealOrder j
    have hpos : 0 < (monsterRealSimpleWeight a).1 := by
      cases a <;> simp [monsterRealSimpleWeight, realRoot, imaginaryRoot]
    let p := nativePositiveMomentum (monsterRealSimpleWeight a) hpos
    change reversedNegative (generator monsterRealOrder a) ∈ realPositiveMomentumIncl.range
    exact ⟨realPositiveMomentumLof p
      ⟨_, reversedNegative_mem_grade (monsterRealSimpleWeight a) ⟨_, hmem⟩⟩,
      realPositiveMomentumIncl_lof p _⟩
  rw [presentation_lieSpan_eq_top monsterRealOrder] at h
  exact h (LieSubalgebra.mem_top x)

private def reversedNegativeFactorLinear : P →ₗ[ℝ] N :=
  realPositiveMomentumEquiv.symm.toLinearMap.comp
    (reversedNegative.toLinearMap.codRestrict realPositiveMomentumLie.toSubmodule
      reversedNegative_mem_positive)

private theorem incl_reversedNegativeFactorLinear (x : P) :
    realPositiveMomentumIncl (reversedNegativeFactorLinear x) = reversedNegative x := by
  let y : realPositiveMomentumLie := ⟨reversedNegative x, reversedNegative_mem_positive x⟩
  change (realPositiveMomentumEquiv (realPositiveMomentumEquiv.symm y) : L) = _
  rw [LinearEquiv.apply_symm_apply]

private def reversedNegativeFactor : P →ₗ⁅ℝ⁆ N where
  toLinearMap := reversedNegativeFactorLinear
  map_lie' := by
    intro x y
    apply realPositiveMomentumIncl_injective
    change realPositiveMomentumIncl (reversedNegativeFactorLinear ⁅x, y⁆) =
      realPositiveMomentumIncl ⁅reversedNegativeFactorLinear x, reversedNegativeFactorLinear y⁆
    simp only [realPositiveMomentumIncl_lie, incl_reversedNegativeFactorLinear, LieHom.map_lie]

private theorem reversedNegativeFactor_preservesGrades :
    PreservesGrades reversedNegativeFactor := by
  intro p hp x
  let r := nativePositiveMomentum p hp
  let y : W r.1 := ⟨_, reversedNegative_mem_grade p x⟩
  refine ⟨y, realPositiveMomentumIncl_injective ?_⟩
  change realPositiveMomentumIncl (reversedNegativeFactorLinear x) =
    realPositiveMomentumIncl (realPositiveMomentumLof r y)
  rw [incl_reversedNegativeFactorLinear, realPositiveMomentumIncl_lof]

/-- The BPZ-dual negative Serre map is injective. Charge reversal transports
it into the positive native algebra, where the graded tensor argument applies. -/
theorem monsterNegativeToRealBRST_injective :
    Function.Injective monsterNegativeToRealBRST := by
  have hbase : ∀ (p : Weight), p.1 = 1 →
      Function.Injective (fun x : G p => reversedNegativeFactor x) := by
    rintro ⟨m, n⟩ hm
    change m = 1 at hm
    subst m
    intro x y hxy
    have h := congrArg realPositiveMomentumIncl hxy
    change realPositiveMomentumIncl (reversedNegativeFactorLinear x) =
      realPositiveMomentumIncl (reversedNegativeFactorLinear y) at h
    rw [incl_reversedNegativeFactorLinear, incl_reversedNegativeFactorLinear] at h
    exact Subtype.ext (negative_injOn_first n x.property y.property
      (realChargeReversalLieEquiv.injective h))
  have hinj := positivePresentation_to_native_injective reversedNegativeFactor
    reversedNegativeFactor_preservesGrades hbase
  intro x y hxy
  apply hinj
  apply realPositiveMomentumIncl_injective
  change realPositiveMomentumIncl (reversedNegativeFactorLinear x) =
    realPositiveMomentumIncl (reversedNegativeFactorLinear y)
  rw [incl_reversedNegativeFactorLinear, incl_reversedNegativeFactorLinear]
  exact congrArg realChargeReversalLieEquiv hxy

/-- The full actual rank-two evaluation is injective. -/
theorem monsterRankTwoToRealBRST_injective :
    Function.Injective monsterRankTwoToRealBRST :=
  monsterRankTwoToRealBRST_injective_of_negative monsterNegativeToRealBRST_injective

/-- A positive native grade and its opposite have the same finite dimension
by charge reversal. Positive grade surjectivity therefore implies negative grade surjectivity. -/
theorem monsterNegativeToRealBRSTGrade_surjective_of_positive (p : Weight)
    (hPos : Function.Surjective (monsterPositiveToRealBRSTGrade p)) :
    Function.Surjective (monsterNegativeToRealBRSTGrade p) := by
  let : FiniteDimensional ℝ (W (monsterNativeMomentum p)) :=
    realMomentumWeightSpace_finiteDimensional _
  let : FiniteDimensional ℝ (W (-monsterNativeMomentum p)) :=
    realMomentumWeightSpace_finiteDimensional _
  let e := LinearEquiv.ofBijective (monsterPositiveToRealBRSTGrade p)
    ⟨monsterPositiveToRealBRSTGrade_injective p, hPos⟩
  let : FiniteDimensional ℝ (G p) := FiniteDimensional.of_injective
    (monsterPositiveToRealBRSTGrade p) (monsterPositiveToRealBRSTGrade_injective p)
  have hdim := (LinearEquiv.finrank_eq e).trans
    (LinearEquiv.finrank_eq (realChargeReversalWeightSpaceEquiv (monsterNativeMomentum p)))
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
  intro x y h
  exact Subtype.ext (monsterNegativeToRealBRST_injective (congrArg Subtype.val h))

/-- Only the positive native grade surjectivity is needed for full surjectivity. -/
theorem monsterRankTwoToRealBRST_surjective_of_positive
    (hPos : ∀ p : Weight, 0 < p.1 → Function.Surjective (monsterPositiveToRealBRSTGrade p)) :
    Function.Surjective monsterRankTwoToRealBRST :=
  monsterRankTwoToRealBRST_surjective hPos
    (fun p hp => monsterNegativeToRealBRSTGrade_surjective_of_positive p (hPos p hp))

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
