/- GID: D5/S3/VertexAlgebra/BRST/MonsterPositivePresentationInjectivity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/MonsterPositivePresentationInjectivity
   mirror-E: none(waiver:algebraic-positive-presentation)
   anchors: []
   utility: none
   digest: The finite BPZ split and the presentation bracket scalar prove graded injectivity. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPositiveTensorBracket
import D5.S3.VertexAlgebra.BRST.MonsterPresentationBracketScalar
import Mathlib.RingTheory.Flat.Basic

/-!
Equations (17)–(18) of the direct-presentation derivation dated 2026-11-24.
Both split tensors obey the same bracket identity in the corresponding coordinates.
The scalar identity detects a homogeneous kernel element once the comparison map
is injective on the tensor of all smaller positive first-coordinate pieces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Classical DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.MonsterPositivePresentationInjectivity

open MonsterPositiveCocycle MonsterPositiveStringPresentation MonsterPresentationBracketScalar
open ActualLeechOrbifoldBRST.RelativeBracket

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] realPositiveMomentumLieRing realPositiveMomentumLieAlgebra

/-- The native momentum in ordered null coordinates for a presentation bidegree. -/
def nativeMomentum (p : Weight) : Fin 2 → ℤ := ![p.1, -p.2]

private theorem nativeMomentum_injective : Function.Injective nativeMomentum := by
  intro p q h
  apply Prod.ext
  · simpa [nativeMomentum] using congrFun h (0 : Fin 2)
  · simpa [nativeMomentum] using congrFun h (1 : Fin 2)

/-- A positive presentation bidegree as an index of the native direct sum. -/
def nativePositiveMomentum (p : Weight) (hp : 0 < p.1) : RealPositiveMomentum :=
  ⟨nativeMomentum p, by simpa [nativeMomentum] using hp⟩

private theorem nativeCoefficient_eq_weightForm (p q : Weight) :
    realPositiveTensorCartanCoefficient (nativeMomentum p) (nativeMomentum q) =
      weightForm p q := by
  simp [realPositiveTensorCartanCoefficient, nativeMomentum, weightForm, add_comm]

variable {J : Type*} {order : J → ℕ+}

local notation "P" => PositivePresentation order
local notation "grade" => presentationGrade order
local notation "N" => RealPositiveMomentumSum
local notation "ΔP" => gradedPresentationDelta order
local notation "ΔN" => realPositiveSplitTensor
local notation "TN" => (N ⊗[ℝ] N)

/-- A grade-preserving map sends each positive presentation weight to its corresponding
single native momentum summand. The other presentation weights are zero. -/
def PreservesGrades (F : P →ₗ⁅ℝ⁆ N) : Prop :=
  ∀ (p : Weight) (hp : 0 < p.1) (x : grade p),
    ∃ y, F x = realPositiveMomentumLof (nativePositiveMomentum p hp) y

private theorem grade_eq_bot_of_first_nonpos {p : Weight} (hp : ¬ 0 < p.1) :
    grade p = ⊥ :=
  presentationGrade_eq_bot_of_outside order p
    (fun h => hp (h.symm ▸ (show 0 < realRoot.1 by decide)))
    (fun h => hp h.1)

private theorem tensor_ad_apply {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (x : L) (t : L ⊗[ℝ] L) :
    (TensorProduct.map (LieAlgebra.ad ℝ L x) LinearMap.id +
      TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ L x) :
        L ⊗[ℝ] L →ₗ[ℝ] L ⊗[ℝ] L) t = ⁅x, t⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp
  | add a b ha hb => rw [map_add, lie_add, ha, hb]

private theorem native_ad_eq_lie (x : N) (t : TN) :
    realPositiveTensorAd x t = ⁅x, t⁆ :=
  tensor_ad_apply x t

private theorem tensorMap_lie {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [LieRing M] [LieAlgebra ℝ M] (f : L →ₗ⁅ℝ⁆ M) (x : L) (t : L ⊗[ℝ] L) :
    TensorProduct.map f.toLinearMap f.toLinearMap ⁅x, t⁆ =
      ⁅f x, TensorProduct.map f.toLinearMap f.toLinearMap t⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [TensorProduct.LieModule.lie_tmul_right, map_add, TensorProduct.map_tmul,
        LieHom.coe_toLinearMap, LieHom.map_lie]
  | add a b ha hb => rw [lie_add, map_add, map_add, lie_add, ha, hb]

private theorem native_split_bracket_of_lof {p q : Weight} {u v : N}
    (hp : 0 < p.1) (hq : 0 < q.1)
    (hu : ∃ a, u = realPositiveMomentumLof (nativePositiveMomentum p hp) a)
    (hv : ∃ b, v = realPositiveMomentumLof (nativePositiveMomentum q hq) b) :
    ΔN ⁅u, v⁆ = ⁅u, ΔN v⁆ - ⁅v, ΔN u⁆ +
      weightForm p q • (u ⊗ₜ[ℝ] v - v ⊗ₜ[ℝ] u) := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  let r := nativePositiveMomentum p hp
  let s := nativePositiveMomentum q hq
  have hcoef : realPositiveTensorCartanCoefficient r.1 s.1 = weightForm p q :=
    nativeCoefficient_eq_weightForm p q
  simpa only [hcoef, native_ad_eq_lie] using realPositiveSplitTensor_lie r s a b

private theorem native_split_bracket_of_mem (F : P →ₗ⁅ℝ⁆ N) (hF : PreservesGrades F)
    {p q : Weight} {x y : P} (hx : x ∈ grade p) (hy : y ∈ grade q) :
    ΔN ⁅F x, F y⁆ =
      ⁅F x, ΔN (F y)⁆ - ⁅F y, ΔN (F x)⁆ +
        weightForm p q • (F x ⊗ₜ[ℝ] F y - F y ⊗ₜ[ℝ] F x) := by
  by_cases hp : 0 < p.1
  · by_cases hq : 0 < q.1
    · exact native_split_bracket_of_lof hp hq (hF p hp ⟨x, hx⟩) (hF q hq ⟨y, hy⟩)
    · rw [grade_eq_bot_of_first_nonpos hq, Submodule.mem_bot] at hy
      simp [hy]
  · rw [grade_eq_bot_of_first_nonpos hp, Submodule.mem_bot] at hx
    simp [hx]

/-- The linear difference of the two ways to map into the native tensor product. -/
private def splitDifference (f : P →ₗ⁅ℝ⁆ N) : P →ₗ[ℝ] TN :=
  (TensorProduct.map f.toLinearMap f.toLinearMap).comp ΔP -
    realPositiveSplitTensor.comp f.toLinearMap

private theorem splitDifference_lie_of_mem (F : P →ₗ⁅ℝ⁆ N)
    (hF : PreservesGrades (order := order) F)
    {p q : Weight} {x y : P} (hx : x ∈ grade p) (hy : y ∈ grade q) :
    splitDifference (order := order) F ⁅x, y⁆ =
      ⁅F x, splitDifference (order := order) F y⁆ - ⁅F y, splitDifference (order := order) F x⁆ := by
  simp only [splitDifference, LinearMap.sub_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieHom.map_lie, gradedPresentationDelta_bracket order hx hy,
    native_split_bracket_of_mem F hF hx hy, map_add, map_sub, tensorMap_lie,
    homogeneousEta, altTensor_apply, map_smul, TensorProduct.map_tmul, lie_sub]
  abel

private theorem bracket_identity_of_homogeneous {L V : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup V] [Module ℝ V] [LieRingModule L V] [LieModule ℝ L V]
    (f : P →ₗ⁅ℝ⁆ L) (d : P →ₗ[ℝ] V)
    (hd : ∀ {p q : Weight} {x y : P}, x ∈ grade p → y ∈ grade q →
      d ⁅x, y⁆ = ⁅f x, d y⁆ - ⁅f y, d x⁆) (x y : P) :
    d ⁅x, y⁆ = ⁅f x, d y⁆ - ⁅f y, d x⁆ := by
  let b := (LieAlgebra.ad ℝ P).toLinearMap
  let a := ((LieModule.toEnd ℝ L V).toLinearMap.comp f.toLinearMap).compl₂ d
  have h : b.compr₂ d = a - a.flip := by
    apply DirectSum.decompose_lhom_ext grade
    intro p
    apply LinearMap.ext
    intro u
    apply DirectSum.decompose_lhom_ext grade
    intro q
    apply LinearMap.ext
    intro v
    exact hd u.property v.property
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

private def bracketIdentityKernel {L V : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup V] [Module ℝ V] [LieRingModule L V] [LieModule ℝ L V]
    (f : P →ₗ⁅ℝ⁆ L) (d : P →ₗ[ℝ] V)
    (hd : ∀ x y, d ⁅x, y⁆ = ⁅f x, d y⁆ - ⁅f y, d x⁆) : LieSubalgebra ℝ P :=
  { d.ker with
    lie_mem' := fun {x y} hx hy => by
      change d x = 0 at hx
      change d y = 0 at hy
      change d ⁅x, y⁆ = 0
      rw [hd, hx, hy, lie_zero, lie_zero, sub_self] }

private theorem native_split_eq_zero_of_first_eq_one (F : P →ₗ⁅ℝ⁆ N)
    (hF : PreservesGrades (order := order) F)
    {p : Weight} (hp : p.1 = 1) (x : grade p) : ΔN (F x) = 0 := by
  have hpos : 0 < p.1 := by omega
  obtain ⟨y, hy⟩ := hF p hpos x
  have hr : (nativePositiveMomentum p hpos).1 0 = 1 := by
    simpa [nativePositiveMomentum, nativeMomentum] using hp
  rw [hy, realPositiveSplitTensor_lof, realSplitTensor_eq_zero_of_first_eq_one _ hr,
    LinearMap.zero_apply]

/-- The comparison map intertwines the presentation and native finite split tensors. -/
theorem tensorMap_gradedPresentationDelta (F : P →ₗ⁅ℝ⁆ N) (hF : PreservesGrades F) :
    (TensorProduct.map F.toLinearMap F.toLinearMap).comp ΔP =
      realPositiveSplitTensor.comp F.toLinearMap := by
  let d := splitDifference (order := order) F
  let S := bracketIdentityKernel F d
    (bracket_identity_of_homogeneous F d (splitDifference_lie_of_mem F hF))
  have hgen {p : Weight} {j : Option J} (hp : p.1 = 1) (hj : generator order j ∈ grade p) :
      generator order j ∈ S := by
    have hn := native_split_eq_zero_of_first_eq_one F hF hp ⟨generator order j, hj⟩
    change ΔN (F (generator order j)) = 0 at hn
    change d (generator order j) = 0
    simp [d, splitDifference, gradedPresentationDelta_generator, hn]
  have hS : S = ⊤ := by
    apply top_unique
    rw [← presentation_lieSpan_eq_top order]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨j, rfl⟩
    cases j with
    | none => exact hgen rfl (real_mem_presentationGrade order)
    | some j => exact hgen rfl (imaginary_mem_presentationGrade order j)
  apply LinearMap.ext
  intro x
  have hx : x ∈ S := hS ▸ LieSubalgebra.mem_top x
  exact sub_eq_zero.mp (show d x = 0 from hx)

private def presentationComponent (p : Weight) : P →ₗ[ℝ] grade p :=
  (DirectSum.component ℝ Weight (fun q => ↥(grade q)) p).comp
    (DirectSum.decomposeLinearEquiv grade).toLinearMap

private def nativeComponent (p : RealPositiveMomentum) : N →ₗ[ℝ] realMomentumGrade p.1 :=
  DirectSum.component ℝ RealPositiveMomentum (fun q => ↥(realMomentumGrade q.1)) p

private theorem presentationComponent_of_ne {p q : Weight} (h : q ≠ p) (x : grade q) :
    presentationComponent p (x : P) = 0 := by
  classical
  simp [presentationComponent, DirectSum.component.of, h]

/-- Projecting onto a native momentum detects the image of the matching presentation piece. -/
private theorem map_presentationComponent (F : P →ₗ⁅ℝ⁆ N)
    (hF : PreservesGrades (order := order) F)
    (p : Weight) (hp : 0 < p.1) (x : P) :
    F (presentationComponent p x : P) =
      realPositiveMomentumLof (nativePositiveMomentum p hp)
        (nativeComponent (nativePositiveMomentum p hp) (F x)) := by
  classical
  let r := nativePositiveMomentum p hp
  have h : F.toLinearMap.comp ((grade p).subtype.comp (presentationComponent p)) =
      (realPositiveMomentumLof r).comp ((nativeComponent r).comp F.toLinearMap) := by
    apply DirectSum.decompose_lhom_ext grade
    intro q
    apply LinearMap.ext
    intro u
    change F (presentationComponent p (u : P) : P) =
      realPositiveMomentumLof r (nativeComponent r (F u))
    by_cases hqp : q = p
    · subst q
      obtain ⟨v, hv⟩ := hF p hp u
      simp [presentationComponent, nativeComponent, r, hv, realPositiveMomentumLof]
    · rw [presentationComponent_of_ne hqp, Submodule.coe_zero, map_zero]
      by_cases hq : 0 < q.1
      · obtain ⟨v, hv⟩ := hF q hq u
        have hne : nativePositiveMomentum q hq ≠ r :=
          fun he => hqp (nativeMomentum_injective (congrArg Subtype.val he))
        rw [hv]
        simp [nativeComponent, realPositiveMomentumLof, DirectSum.component.of, hne]
      · have hu : (u : P) = 0 :=
          (Submodule.mem_bot (R := ℝ)).mp ((grade_eq_bot_of_first_nonpos hq).le u.property)
        change 0 = realPositiveMomentumLof r (nativeComponent r (F (u : P)))
        simp [hu]
  exact DFunLike.congr_fun h x

private theorem eq_zero_of_components_eq_zero {x : P}
    (h : ∀ p, presentationComponent p x = 0) : x = 0 := by
  apply (DirectSum.decomposeLinearEquiv grade).injective
  rw [map_zero]
  exact DirectSum.ext_component ℝ fun p => (h p).trans (map_zero _).symm

private theorem map_presentationComponent_eq_zero (F : P →ₗ⁅ℝ⁆ N)
    (hF : PreservesGrades (order := order) F)
    {x : P} (hx : F x = 0) (p : Weight) :
    F (presentationComponent p x : P) = 0 := by
  by_cases hp : 0 < p.1
  · rw [map_presentationComponent F hF p hp, hx, map_zero, map_zero]
  · have hx' : (presentationComponent p x : P) = 0 :=
      (Submodule.mem_bot (R := ℝ)).mp ((grade_eq_bot_of_first_nonpos hp).le (presentationComponent p x).property)
    rw [hx', map_zero]

private def lowerGrades (m : ℤ) : Submodule ℝ P :=
  ⨆ q : {q : Weight // 0 < q.1 ∧ q.1 < m}, grade q.1

private theorem lowerGrades_component_eq_zero {m : ℤ} {p : Weight}
    (hp : ¬ (0 < p.1 ∧ p.1 < m)) {x : P} (hx : x ∈ lowerGrades m) :
    presentationComponent p x = 0 := by
  have hle : lowerGrades (order := order) m ≤ (presentationComponent p).ker := by
    apply iSup_le
    intro q z hz
    have hne : q.1 ≠ p := fun he => hp (by simpa only [← he] using q.property)
    exact presentationComponent_of_ne hne ⟨z, hz⟩
  exact hle hx

private theorem restrict_lowerGrades_injective (F : P →ₗ⁅ℝ⁆ N)
    (hF : PreservesGrades (order := order) F) {m : ℤ}
    (ih : ∀ (p : Weight), 0 < p.1 → p.1 < m →
      ∀ (x : grade p), F x = 0 → (x : P) = 0) :
    Function.Injective (F.toLinearMap.comp (lowerGrades (order := order) m).subtype) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  change F (x : P) = 0 at hx
  apply Subtype.ext
  apply eq_zero_of_components_eq_zero
  intro p
  by_cases hp : 0 < p.1 ∧ p.1 < m
  · apply Subtype.ext
    exact ih p hp.1 hp.2 _ (map_presentationComponent_eq_zero F hF hx p)
  · exact lowerGrades_component_eq_zero hp x.property

private theorem tensorBlock_le_range (p : Weight) :
    presentationTensorBlock order p ≤
      (TensorProduct.map (lowerGrades (order := order) p.1).subtype
        (lowerGrades (order := order) p.1).subtype).range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, u, v, _, ha, ha', hb, hb', hu, hv, rfl⟩
  let G := lowerGrades (order := order) p.1
  have huG : u ∈ G := (le_iSup (fun q : {q : Weight // 0 < q.1 ∧ q.1 < p.1} =>
    grade q.1) ⟨a, ha, ha'⟩) hu
  have hvG : v ∈ G := (le_iSup (fun q : {q : Weight // 0 < q.1 ∧ q.1 < p.1} =>
    grade q.1) ⟨b, hb, hb'⟩) hv
  exact ⟨(⟨u, huG⟩ : G) ⊗ₜ[ℝ] (⟨v, hvG⟩ : G), TensorProduct.map_tmul ..⟩

/-- A Lie map from the positive Monster presentation into the native real BRST positive
algebra is injective if it preserves the exact bidegree and is injective in first coordinate
one. The scalar argument uses the tensor of the entire lower-first-coordinate subspace. -/
theorem positivePresentation_to_native_injective (F : P →ₗ⁅ℝ⁆ N) (hF : PreservesGrades F)
    (hbase : ∀ (p : Weight), p.1 = 1 → Function.Injective (fun x : grade p => F x)) :
    Function.Injective F := by
  have hnat := tensorMap_gradedPresentationDelta F hF
  have hpiece (m : ℕ) : ∀ (p : Weight), p.1.toNat = m →
      ∀ x : grade p, F x = 0 → (x : P) = 0 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hm x hx
      by_cases hpos : 0 < p.1
      · by_cases hfirst : p.1 = 1
        · have h : F x = F (0 : grade p) := by simpa only [Submodule.coe_zero, map_zero] using hx
          exact congrArg Subtype.val (hbase p hfirst h)
        · have hlt : 1 < p.1 := by omega
          -- Restrict both tensor factors to the smaller positive first coordinates.
          have hinj := restrict_lowerGrades_injective F hF (m := p.1) fun q hq hqp =>
            ih q.1.toNat (by omega) q rfl
          have ht := tensorBlock_le_range (order := order) p
            (gradedPresentationDelta_mem_tensorBlock order x.property)
          let i := (lowerGrades (order := order) p.1).subtype
          obtain ⟨t, ht⟩ := ht
          change TensorProduct.map i i t = ΔP (x : P) at ht
          have hz : TensorProduct.map F.toLinearMap F.toLinearMap (ΔP (x : P)) = 0 := by
            have h := DFunLike.congr_fun hnat (x : P)
            change TensorProduct.map F.toLinearMap F.toLinearMap (ΔP (x : P)) = ΔN (F x) at h
            rw [h, hx, map_zero]
          have ht0 : t = 0 := by
            let f := F.toLinearMap.comp i
            apply TensorProduct.map_injective_of_flat_flat f f hinj hinj
            rw [map_zero]
            change TensorProduct.map (F.toLinearMap.comp i) (F.toLinearMap.comp i) t = 0
            rw [← TensorProduct.map_map, ht, hz]
          apply eq_zero_of_gradedPresentationDelta_eq_zero order x.property hlt
          rw [← ht, ht0, map_zero]
      · exact (Submodule.mem_bot (R := ℝ)).mp ((grade_eq_bot_of_first_nonpos hpos).le x.property)
  change Function.Injective F.toLinearMap
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply eq_zero_of_components_eq_zero
  intro p
  apply Subtype.ext
  exact hpiece p.1.toNat p rfl _ (map_presentationComponent_eq_zero F hF hx p)

end D5.S3.VertexAlgebra.MonsterPositivePresentationInjectivity
