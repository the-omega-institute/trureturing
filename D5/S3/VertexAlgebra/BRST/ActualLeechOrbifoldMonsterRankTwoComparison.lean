/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterRankTwoComparison
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterRankTwoComparison
   mirror-E: none(waiver:native-real-BRST)
   anchors: []
   utility: none
   digest: Compare the rank-two Monster presentation with fixed real relative BRST. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterPositiveEmbedding
import D5.S3.VertexAlgebra.BRST.MonsterRankTwoPresentation

/-!
The comparison uses the rank-two presentation of the Monster Lie algebra, with the simple
weights of Borcherds, *Monstrous moonshine and monstrous Lie superalgebras* (1992),
and Jurisich, *Generalized Kac–Moody Lie algebras, free Lie algebras and the structure
of the Monster Lie algebra* (1998). A paper momentum `(m,n)` is the native momentum
`(m,-n)`. The same change of coordinates applies to the Cartan.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Classical DirectSum

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open MonsterPositiveCocycle MonsterPositiveStringPresentation
open MonsterPresentationBracketScalar (presentation_lieSpan_eq_top)
open MonsterRankTwoPresentation (CartanCoordinates cartanWeight cartanWeight_apply weightCoordinates)

local notation "Momentum" => (Fin 2 → ℤ)
local notation "L" => momentumRealLie
local notation "W" => realMomentumGrade
local notation "J" => MonsterRealImaginaryIndex
local notation "P" => PositivePresentation monsterRealOrder
local notation "G" => presentationGrade monsterRealOrder
local notation "M" => MonsterRankTwoPresentation.Presented monsterRealOrder

private def nativeCartanCoordinates : CartanCoordinates ≃ₗ[ℝ] CartanCoordinates where
  toFun h := ![h 0, -h 1]
  invFun h := ![h 0, -h 1]
  left_inv h := by ext i; fin_cases i <;> simp
  right_inv h := by ext i; fin_cases i <;> simp
  map_add' h k := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' r h := by ext i; fin_cases i <;> simp [smul_eq_mul]

/-- The native Cartan as a linear map from the paper coordinates. -/
def monsterCartanToRealBRST : CartanCoordinates →ₗ[ℝ] L :=
  realCartanClass.comp nativeCartanCoordinates.toLinearMap

theorem monsterCartanToRealBRST_apply (h : CartanCoordinates) :
    monsterCartanToRealBRST h = realCartanClass ![h 0, -h 1] := rfl

private theorem monsterCartanToRealBRST_injective :
    Function.Injective monsterCartanToRealBRST :=
  realCartanClass_injective.comp nativeCartanCoordinates.injective

private theorem cartan_mem_zero_grade (h : CartanCoordinates) :
    monsterCartanToRealBRST h ∈ W 0 := by
  change monsterCartanToRealBRST h ∈ realMomentumWeightSpace 0
  rw [mem_realMomentumWeightSpace, ← mem_realCartan_iff]
  exact LinearMap.mem_range_self realCartanClass (nativeCartanCoordinates h)

private theorem cartan_commutes (h k : CartanCoordinates) :
    ⁅monsterCartanToRealBRST h, monsterCartanToRealBRST k⁆ = 0 :=
  (realCartan_selfCentralizing (monsterCartanToRealBRST k)).mp
    (LinearMap.mem_range_self realCartanClass (nativeCartanCoordinates k))
    (realCartanEquiv (nativeCartanCoordinates h))

private theorem native_cartanWeight (p : Weight) (h : CartanCoordinates) :
    realMomentumWeight (monsterNativeMomentum p)
      (realCartanEquiv (nativeCartanCoordinates h)) = cartanWeight p h := by
  rw [realMomentumWeight_coordinates, cartanWeight_apply]
  simp [nativeCartanCoordinates, monsterNativeMomentum]
  ring

private theorem native_cartanWeight_neg (p : Weight) (h : CartanCoordinates) :
    realMomentumWeight (-monsterNativeMomentum p)
      (realCartanEquiv (nativeCartanCoordinates h)) = -cartanWeight p h := by
  rw [← native_cartanWeight p h, realMomentumWeight_coordinates, realMomentumWeight_coordinates]
  simp only [Pi.neg_apply, Int.cast_neg, mul_neg, neg_add]

private theorem lie_of_native_weight {p : Momentum} {x : L} (hx : x ∈ W p)
    (h : CartanCoordinates) :
    ⁅monsterCartanToRealBRST h, x⁆ =
      realMomentumWeight p (realCartanEquiv (nativeCartanCoordinates h)) • x := by
  change x ∈ LieModule.weightSpace L (realMomentumWeight p) at hx
  rw [LieModule.mem_weightSpace] at hx
  exact hx (realCartanEquiv (nativeCartanCoordinates h))

private theorem simpleWeight_eq (a : Option J) :
    MonsterRankTwoPresentation.simpleWeight monsterRealOrder a = monsterRealSimpleWeight a := by
  cases a <;> rfl

private theorem generator_native_weights (a : Option J) :
    monsterRealPositiveGenerator a ∈ W (monsterNativeMomentum (monsterRealSimpleWeight a)) ∧
      monsterRealNegativeGenerator a ∈ W (-monsterNativeMomentum (monsterRealSimpleWeight a)) := by
  cases a with
  | none =>
    simpa only [monsterRealSimpleWeight, monsterNativeMomentum_realRoot,
      monsterRealPositiveGenerator, monsterRealNegativeGenerator] using
      And.intro monsterRealSimpleE.property monsterRealSimpleF.property
  | some a =>
    obtain ⟨n, i⟩ := a
    simpa only [monsterRealSimpleWeight, monsterNativeMomentum_imaginaryRoot,
      monsterRealPositiveGenerator, monsterRealNegativeGenerator] using
      And.intro (monsterRealPositiveBasis n i).property (monsterRealNegativeBasis n i).property

private theorem simpleCartan_eq (a : Option J) :
    monsterRealSimpleCartan a =
      monsterCartanToRealBRST (weightCoordinates (monsterRealSimpleWeight a)) := by
  apply congrArg realCartanClass
  ext i
  fin_cases i <;> simp [monsterNativeMomentum, nativeCartanCoordinates, weightCoordinates]

/-- Evaluate the rank-two quotient in the actual fixed real relative BRST Lie algebra. -/
def monsterRankTwoToRealBRST : M →ₗ⁅ℝ⁆ L :=
  MonsterRankTwoPresentation.lift monsterRealOrder monsterCartanToRealBRST
    monsterRealPositiveGenerator monsterRealNegativeGenerator cartan_commutes
    (by
      intro h a
      rw [simpleWeight_eq, ← native_cartanWeight]
      exact lie_of_native_weight (generator_native_weights a).1 h)
    (by
      intro h a
      rw [simpleWeight_eq, ← native_cartanWeight_neg]
      exact lie_of_native_weight (generator_native_weights a).2 h)
    (by
      intro a b
      simpa only [simpleWeight_eq, simpleCartan_eq] using monsterRealSimple_mixed_lie a b)
    monsterRealPositive_serre monsterRealNegative_serre

@[simp] theorem monsterRankTwoToRealBRST_e (a : Option J) :
    monsterRankTwoToRealBRST (MonsterRankTwoPresentation.e monsterRealOrder a) =
      monsterRealPositiveGenerator a := by
  simp only [monsterRankTwoToRealBRST, MonsterRankTwoPresentation.lift_e]

@[simp] theorem monsterRankTwoToRealBRST_f (a : Option J) :
    monsterRankTwoToRealBRST (MonsterRankTwoPresentation.f monsterRealOrder a) =
      monsterRealNegativeGenerator a := by
  simp only [monsterRankTwoToRealBRST, MonsterRankTwoPresentation.lift_f]

@[simp] theorem monsterRankTwoToRealBRST_cartan (h : CartanCoordinates) :
    monsterRankTwoToRealBRST (MonsterRankTwoPresentation.cartan monsterRealOrder h) =
      monsterCartanToRealBRST h := by
  simp only [monsterRankTwoToRealBRST, MonsterRankTwoPresentation.lift_cartan]

private def negativeFreeToRealBRST : FreeLieAlgebra ℝ (Option J) →ₗ⁅ℝ⁆ L :=
  FreeLieAlgebra.lift ℝ monsterRealNegativeGenerator

private theorem negativeFreeToRealBRST_adIter
    (x y : FreeLieAlgebra ℝ (Option J)) (k : ℕ) :
    negativeFreeToRealBRST (adIter x k y) =
      adIter (negativeFreeToRealBRST x) k (negativeFreeToRealBRST y) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [adIter, adIter, LieHom.map_lie, ih]

private theorem serreIdeal_le_negative_ker :
    serreIdeal monsterRealOrder ≤ negativeFreeToRealBRST.ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro _ ⟨j, rfl⟩
  change negativeFreeToRealBRST (adIter (FreeLieAlgebra.of ℝ none) (monsterRealOrder j : ℕ)
    (FreeLieAlgebra.of ℝ (some j))) = 0
  rw [negativeFreeToRealBRST_adIter]
  simpa only [negativeFreeToRealBRST, FreeLieAlgebra.lift_of_apply] using
    monsterRealNegative_serre j

/-- The Serre evaluation on the native BPZ-dual negative generators. -/
def monsterNegativeToRealBRST : P →ₗ⁅ℝ⁆ L :=
  { (serreIdeal monsterRealOrder).toSubmodule.liftQ negativeFreeToRealBRST.toLinearMap
      serreIdeal_le_negative_ker with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => exact negativeFreeToRealBRST.map_lie x y }

@[simp] theorem monsterNegativeToRealBRST_generator (a : Option J) :
    monsterNegativeToRealBRST (generator monsterRealOrder a) = monsterRealNegativeGenerator a :=
  FreeLieAlgebra.lift_of_apply _ _

private theorem serre_hom_ext {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    {g k : P →ₗ⁅ℝ⁆ A}
    (h : ∀ a, g (generator monsterRealOrder a) = k (generator monsterRealOrder a)) : g = k := by
  have hcomp : g.comp (presentationQuotient monsterRealOrder) =
      k.comp (presentationQuotient monsterRealOrder) := FreeLieAlgebra.hom_ext h
  ext x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (serreIdeal monsterRealOrder).toSubmodule x
  exact DFunLike.congr_fun hcomp y

/-- The positive restriction is the existing native positive Serre evaluation. -/
theorem monsterRankTwoToRealBRST_comp_positive :
    monsterRankTwoToRealBRST.comp (MonsterRankTwoPresentation.positiveMap monsterRealOrder) =
      monsterPositiveToRealBRST := by
  apply serre_hom_ext
  intro a
  simp only [LieHom.comp_apply, MonsterRankTwoPresentation.positiveMap_generator,
    monsterRankTwoToRealBRST_e, monsterPositiveToRealBRST_generator]

/-- The negative restriction is evaluation on the native BPZ-dual generators. -/
theorem monsterRankTwoToRealBRST_comp_negative :
    monsterRankTwoToRealBRST.comp (MonsterRankTwoPresentation.negativeMap monsterRealOrder) =
      monsterNegativeToRealBRST := by
  apply serre_hom_ext
  intro a
  simp only [LieHom.comp_apply, MonsterRankTwoPresentation.negativeMap_generator,
    monsterRankTwoToRealBRST_f, monsterNegativeToRealBRST_generator]

/-- The evaluation agrees with the three native maps on every triangular expression. -/
theorem monsterRankTwoToRealBRST_triangle (xNeg xPos : P) (h : CartanCoordinates) :
    monsterRankTwoToRealBRST (MonsterRankTwoPresentation.negativeMap monsterRealOrder xNeg +
      MonsterRankTwoPresentation.cartan monsterRealOrder h +
      MonsterRankTwoPresentation.positiveMap monsterRealOrder xPos) =
    monsterNegativeToRealBRST xNeg + monsterCartanToRealBRST h + monsterPositiveToRealBRST xPos := by
  rw [map_add, map_add, monsterRankTwoToRealBRST_cartan,
    ← LieHom.comp_apply, monsterRankTwoToRealBRST_comp_negative,
    ← LieHom.comp_apply, monsterRankTwoToRealBRST_comp_positive]


/-- The evaluation carries the paper Cartan eigenspace to its native momentum space. -/
theorem monsterRankTwoToRealBRST_mem_weightSpace (p : Weight) (z : M)
    (hz : ∀ h : CartanCoordinates,
      ⁅MonsterRankTwoPresentation.cartan monsterRealOrder h, z⁆ = cartanWeight p h • z) :
    monsterRankTwoToRealBRST z ∈ W (monsterNativeMomentum p) := by
  change monsterRankTwoToRealBRST z ∈ LieModule.weightSpace L _
  refine (LieModule.mem_weightSpace (realMomentumWeight (monsterNativeMomentum p))
    (monsterRankTwoToRealBRST z)).mpr ?_
  intro h
  obtain ⟨k, rfl⟩ := (nativeCartanCoordinates.trans realCartanEquiv).surjective h
  have hk := congrArg monsterRankTwoToRealBRST (hz k)
  simp only [LieHom.map_lie, monsterRankTwoToRealBRST_cartan, map_smul] at hk
  change ⁅monsterCartanToRealBRST k, monsterRankTwoToRealBRST z⁆ =
    realMomentumWeight (monsterNativeMomentum p) (realCartanEquiv (nativeCartanCoordinates k)) •
      monsterRankTwoToRealBRST z
  rw [native_cartanWeight]
  exact hk

private def negativeMatchingGrade (p : Weight) : Submodule ℝ P :=
  G p ⊓ (W (-monsterNativeMomentum p)).comap monsterNegativeToRealBRST.toLinearMap

private theorem negativeMatchingGrade_bracket {p q : Weight} {x y : P}
    (hx : x ∈ negativeMatchingGrade p) (hy : y ∈ negativeMatchingGrade q) :
    ⁅x, y⁆ ∈ negativeMatchingGrade (p + q) := by
  refine ⟨presentationGrade_bracket monsterRealOrder hx.1 hy.1, ?_⟩
  change monsterNegativeToRealBRST ⁅x, y⁆ ∈ W (-monsterNativeMomentum (p + q))
  rw [LieHom.map_lie, map_add, neg_add]
  exact realWeight_lie_mem_add _ _ ⟨_, hx.2⟩ ⟨_, hy.2⟩

private def negativeMatchingGrades : LieSubalgebra ℝ P where
  toSubmodule := ⨆ p, negativeMatchingGrade p
  lie_mem' := by
    intro x y hx hy
    let U : Submodule ℝ P := ⨆ p, negativeMatchingGrade p
    change x ∈ U at hx
    change y ∈ U at hy
    change ⁅x, y⁆ ∈ U
    refine Submodule.iSup_induction (motive := fun x => ⁅x, y⁆ ∈ U) _ hx ?_ ?_ ?_
    · intro p x hx
      refine Submodule.iSup_induction (motive := fun y => ⁅x, y⁆ ∈ U) _ hy ?_ ?_ ?_
      · intro q y hy
        exact Submodule.mem_iSup_of_mem (p + q) (negativeMatchingGrade_bracket hx hy)
      · simp
      · intro u v hu hv
        rw [lie_add]
        exact add_mem hu hv
    · simp
    · intro u v hu hv
      rw [add_lie]
      exact add_mem hu hv

private theorem negativeMatchingGrades_eq_top : negativeMatchingGrades = ⊤ := by
  apply top_unique
  rw [← presentation_lieSpan_eq_top monsterRealOrder]
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨a, rfl⟩
  change generator monsterRealOrder a ∈ ⨆ p, negativeMatchingGrade p
  apply Submodule.mem_iSup_of_mem (monsterRealSimpleWeight a)
  refine ⟨?_, ?_⟩
  · cases a with
    | none => exact real_mem_presentationGrade monsterRealOrder
    | some j => exact imaginary_mem_presentationGrade monsterRealOrder j
  · change monsterNegativeToRealBRST (generator monsterRealOrder a) ∈
      W (-monsterNativeMomentum (monsterRealSimpleWeight a))
    rw [monsterNegativeToRealBRST_generator]
    exact (generator_native_weights a).2

/-- The native negative evaluation sends the paper grade `p` to `-monsterNativeMomentum p`. -/
theorem monsterNegativeToRealBRST_mem_grade {p : Weight} {x : P} (hx : x ∈ G p) :
    monsterNegativeToRealBRST x ∈ W (-monsterNativeMomentum p) := by
  have hall : x ∈ (⨆ q, negativeMatchingGrade q : Submodule ℝ P) := by
    change x ∈ negativeMatchingGrades
    rw [negativeMatchingGrades_eq_top]
    exact LieSubalgebra.mem_top x
  have hproj : (↑(DirectSum.decompose G x p) : P) ∈ negativeMatchingGrade p := by
    refine Submodule.iSup_induction
      (motive := fun y => (↑(DirectSum.decompose G y p) : P) ∈ negativeMatchingGrade p)
      _ hall ?_ ?_ ?_
    · intro q y hy
      by_cases heq : q = p
      · subst q
        rw [DirectSum.decompose_of_mem_same G hy.1]
        exact hy
      · rw [DirectSum.decompose_of_mem_ne G hy.1 heq]
        exact zero_mem _
    · simp
    · intro u v hu hv
      rw [DirectSum.decompose_add]
      exact add_mem hu hv
  rw [DirectSum.decompose_of_mem_same G hx] at hproj
  exact hproj.2

/-- The negative evaluation restricted to a single signed momentum space. -/
def monsterNegativeToRealBRSTGrade (p : Weight) : G p →ₗ[ℝ] W (-monsterNativeMomentum p) :=
  (monsterNegativeToRealBRST.toLinearMap.comp (G p).subtype).codRestrict _
    (fun x => monsterNegativeToRealBRST_mem_grade x.property)

private theorem presentationGrade_bot_of_first_nonpos (p : Weight) (hp : ¬ 0 < p.1) :
    G p = ⊥ :=
  presentationGrade_eq_bot_of_outside monsterRealOrder p
    (fun h => hp (h.symm ▸ (show 0 < realRoot.1 by decide))) (fun h => hp h.1)

set_option maxHeartbeats 800000 in
private theorem project_serre_half (g : P →ₗ[ℝ] L) (degree : Weight → Momentum)
    (hg : ∀ p (x : G p), g x ∈ W (degree p))
    (keep : Momentum → Prop) (retain : Prop)
    (hkeep : ∀ p, 0 < p.1 → (keep (degree p) ↔ retain)) (x : P) :
    projectMomentumReal keep (g x) = if retain then g x else 0 := by
  have heq : (projectMomentumReal keep).comp g = if retain then g else 0 := by
    apply DirectSum.decompose_lhom_ext G
    intro p
    apply LinearMap.ext
    intro y
    change projectMomentumReal keep (g y) = (if retain then g else 0) y
    by_cases hp : 0 < p.1
    · rw [projectMomentumReal_weight keep (degree p) ⟨g y, hg p y⟩]
      by_cases hr : retain
      · rw [ite_eq_left ((hkeep p hp).mpr hr), ite_eq_left hr]
      · rw [ite_eq_right (fun hk => hr ((hkeep p hp).mp hk)), ite_eq_right hr]
        rfl
    · have hy : (y : P) = 0 :=
        (Submodule.mem_bot ℝ).mp ((presentationGrade_bot_of_first_nonpos p hp).le y.property)
      rw [hy]
      exact ((projectMomentumReal keep).comp g).map_zero.trans ((if retain then g else 0).map_zero).symm
  by_cases hr : retain
  · rw [ite_eq_left hr] at heq ⊢
    exact LinearMap.congr_fun heq x
  · rw [ite_eq_right hr] at heq ⊢
    exact LinearMap.congr_fun heq x

set_option maxHeartbeats 800000 in
/-- A zero sum of the three native images forces each summand to vanish. -/
theorem monsterNativeTriangle_eq_zero {xNeg xPos : P} {h : CartanCoordinates}
    (hz : monsterNegativeToRealBRST xNeg + monsterCartanToRealBRST h +
      monsterPositiveToRealBRST xPos = 0) :
    monsterNegativeToRealBRST xNeg = 0 ∧ h = 0 ∧ monsterPositiveToRealBRST xPos = 0 := by
  let keep (p : Momentum) := p 0 < 0
  have hneg := project_serre_half monsterNegativeToRealBRST.toLinearMap
    (fun p => -monsterNativeMomentum p) (fun _ x => monsterNegativeToRealBRST_mem_grade x.property)
    keep True (by intro p hp; simpa [keep, monsterNativeMomentum] using hp) xNeg
  have hpos := project_serre_half monsterPositiveToRealBRST.toLinearMap
    monsterNativeMomentum (fun _ x => monsterPositiveToRealBRST_mem_grade x.property)
    keep False (by
      intro p hp
      simpa [keep, monsterNativeMomentum] using not_lt_of_ge hp.le) xPos
  have hc : projectMomentumReal keep (monsterCartanToRealBRST h) = 0 := by
    rw [projectMomentumReal_weight keep 0 ⟨_, cartan_mem_zero_grade h⟩]
    simp [keep]
  have hn := congrArg (projectMomentumReal keep) hz
  change projectMomentumReal keep (_ + _ + _) = _ at hn
  change projectMomentumReal keep (monsterNegativeToRealBRST xNeg) = _ at hneg
  change projectMomentumReal keep (monsterPositiveToRealBRST xPos) = _ at hpos
  rw [map_add, map_add, hneg, hc, hpos, map_zero] at hn
  simp only [ite_true, ite_false, add_zero] at hn
  change monsterNegativeToRealBRST xNeg = 0 at hn
  let keepZero (p : Momentum) := p = 0
  have hcz : projectMomentumReal keepZero (monsterCartanToRealBRST h) =
      monsterCartanToRealBRST h := by
    rw [projectMomentumReal_weight keepZero 0 ⟨_, cartan_mem_zero_grade h⟩]
    simp [keepZero]
  have hpz := project_serre_half monsterPositiveToRealBRST.toLinearMap
    monsterNativeMomentum (fun _ x => monsterPositiveToRealBRST_mem_grade x.property)
    keepZero False (by
      intro p hp
      simp only [keepZero, iff_false]
      intro heq
      have hc := congrFun heq (0 : Fin 2)
      change p.1 = 0 at hc
      omega) xPos
  rw [hn, zero_add] at hz
  have hCartan := congrArg (projectMomentumReal keepZero) hz
  change projectMomentumReal keepZero (_ + _) = _ at hCartan
  change projectMomentumReal keepZero (monsterPositiveToRealBRST xPos) = _ at hpz
  rw [map_add, hcz, hpz, map_zero] at hCartan
  simp only [ite_false, add_zero] at hCartan
  have hh : h = 0 := monsterCartanToRealBRST_injective (hCartan.trans monsterCartanToRealBRST.map_zero.symm)
  rw [hCartan, zero_add] at hz
  exact ⟨hn, hh, hz⟩

/-- The entire kernel is the image of the native negative Serre kernel. -/
theorem monsterRankTwoToRealBRST_eq_zero_iff (z : M) :
    monsterRankTwoToRealBRST z = 0 ↔
      ∃ xNeg : P, z = MonsterRankTwoPresentation.negativeMap monsterRealOrder xNeg ∧
        monsterNegativeToRealBRST xNeg = 0 := by
  constructor
  · intro hz
    obtain ⟨xNeg, h, xPos, rfl⟩ :=
      MonsterRankTwoPresentation.presentation_triangular_span monsterRealOrder z
    rw [monsterRankTwoToRealBRST_triangle] at hz
    obtain ⟨hneg, rfl, hpos⟩ := monsterNativeTriangle_eq_zero hz
    have hx : xPos = 0 :=
      monsterPositiveToRealBRST_injective (hpos.trans monsterPositiveToRealBRST.map_zero.symm)
    subst xPos
    exact ⟨xNeg, by simp, hneg⟩
  · rintro ⟨xNeg, rfl, hneg⟩
    rw [← LieHom.comp_apply, monsterRankTwoToRealBRST_comp_negative, hneg]

/-- Negative Serre injectivity suffices for injectivity of the full actual evaluation. -/
theorem monsterRankTwoToRealBRST_injective_of_negative
    (hNeg : Function.Injective monsterNegativeToRealBRST) :
    Function.Injective monsterRankTwoToRealBRST := by
  intro x y hxy
  have hzero : monsterRankTwoToRealBRST (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨xNeg, h, hx⟩ := (monsterRankTwoToRealBRST_eq_zero_iff (x - y)).mp hzero
  have hxNeg : xNeg = 0 := hNeg (hx.trans monsterNegativeToRealBRST.map_zero.symm)
  rw [hxNeg, map_zero] at h
  exact sub_eq_zero.mp h

private theorem weight_coe_cast {p q : Momentum} (h : p = q) (w : W p) :
    ((h ▸ w : W q) : L) = (w : L) := by
  subst q
  rfl

set_option maxHeartbeats 1000000 in
/-- Surjectivity on the two signed native grades suffices for surjectivity of the full evaluation. -/
theorem monsterRankTwoToRealBRST_surjective
    (hPos : ∀ p : Weight, 0 < p.1 → Function.Surjective (monsterPositiveToRealBRSTGrade p))
    (hNeg : ∀ p : Weight, 0 < p.1 → Function.Surjective (monsterNegativeToRealBRSTGrade p)) :
    Function.Surjective monsterRankTwoToRealBRST := by
  have hgrade (p : Momentum) (w : W p) :
      (w : L) ∈ monsterRankTwoToRealBRST.range := by
    rcases lt_trichotomy (p 0) 0 with hp | hp | hp
    · let q : Weight := (-p 0, p 1)
      have hq : -monsterNativeMomentum q = p := by
        ext i
        fin_cases i <;> simp [q, monsterNativeMomentum]
      obtain ⟨x, hx⟩ := hNeg q (neg_pos.mpr hp) (hq.symm ▸ w)
      refine ⟨MonsterRankTwoPresentation.negativeMap monsterRealOrder x, ?_⟩
      change (monsterRankTwoToRealBRST.comp (MonsterRankTwoPresentation.negativeMap
        monsterRealOrder)) x = (w : L)
      rw [monsterRankTwoToRealBRST_comp_negative]
      exact (congrArg (fun z : W (-monsterNativeMomentum q) => (z : L)) hx).trans
        (weight_coe_cast hq.symm w)
    · by_cases h : p = 0
      · subst p
        have hw : (w : L) ∈ realCartan :=
          (mem_realCartan_iff (w : L)).mpr ((mem_realMomentumWeightSpace 0 (w : L)).mp w.property)
        obtain ⟨k, hk⟩ := hw
        obtain ⟨c, rfl⟩ := nativeCartanCoordinates.surjective k
        exact ⟨MonsterRankTwoPresentation.cartan monsterRealOrder c,
          (monsterRankTwoToRealBRST_cartan c).trans hk⟩
      · have hbot := realMomentumWeightSpace_eq_bot_of_null p h (by
          rw [momentumRealBPZ_momentum_norm]
          simp [hp])
        have hw : (w : L) ∈ realMomentumWeightSpace p := w.property
        rw [hbot] at hw
        rw [(LieSubmodule.mem_bot (w : L)).mp hw]
        exact zero_mem _
    · let q : Weight := (p 0, -p 1)
      have hq : monsterNativeMomentum q = p := by
        ext i
        fin_cases i <;> simp [q, monsterNativeMomentum]
      obtain ⟨x, hx⟩ := hPos q hp (hq.symm ▸ w)
      refine ⟨MonsterRankTwoPresentation.positiveMap monsterRealOrder x, ?_⟩
      change (monsterRankTwoToRealBRST.comp (MonsterRankTwoPresentation.positiveMap
        monsterRealOrder)) x = (w : L)
      rw [monsterRankTwoToRealBRST_comp_positive]
      exact (congrArg (fun z : W (monsterNativeMomentum q) => (z : L)) hx).trans
        (weight_coe_cast hq.symm w)
  intro z
  have hsum (u : ⨁ p : Momentum, W p) :
      DirectSum.coeLinearMap W u ∈ monsterRankTwoToRealBRST.range := by
    induction u using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of p w =>
      rw [← DirectSum.lof_eq_of ℝ, DirectSum.coeLinearMap_lof]
      exact hgrade p w
    | add u v hu hv => rw [map_add]; exact add_mem hu hv
  obtain ⟨u, rfl⟩ := realMomentumWeightSpace_isInternal.surjective z
  exact hsum u

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
