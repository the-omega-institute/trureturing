/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterRealPresentation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterRealPresentation
   mirror-E: none(waiver:native-real-BRST)
   anchors: []
   utility: none
   digest: The positive Monster Serre presentation in the actual real relative BRST Lie algebra. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldFiniteOppositeTensor
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterRealRootStrings
import D5.S3.VertexAlgebra.BRST.MonsterPositiveStringPresentation

/-!
The simple momenta of the Monster presentation follow Borcherds, *Monstrous moonshine
and monstrous Lie superalgebras* (1992), and Jurisich, *Generalized Kac–Moody Lie
algebras, free Lie algebras and the structure of the Monster Lie algebra* (1998).
The presentation uses paper coordinates `(m,n)`; the native charge is `(m,-n)`.
The imaginary indices are taken from bases of the actual real BRST momentum spaces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 150000
set_option synthInstance.maxSize 512

noncomputable section

open scoped Classical DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open MonsterPositiveCocycle MonsterPositiveStringPresentation
open RealRootBracket (positiveRoot positiveRootClass opposite_root_lie_brackets
  monsterSimpleMomentum)
open private inclCycle from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldEvenCurrent

local notation "Momentum" => (Fin 2 → ℤ)
local notation "L" => momentumRealLie
local notation "W" => realMomentumGrade

/-- Convert paper weights to native hyperbolic-plane momenta. -/
def monsterNativeMomentum : Weight →+ Momentum where
  toFun p := ![p.1, -p.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' p q := by ext i; fin_cases i <;> simp [add_comm]

@[simp] theorem monsterNativeMomentum_realRoot :
    monsterNativeMomentum realRoot = positiveRoot := by
  ext i
  fin_cases i <;> simp [monsterNativeMomentum, realRoot, positiveRoot]

@[simp] theorem monsterNativeMomentum_imaginaryRoot (n : ℕ) :
    monsterNativeMomentum (imaginaryRoot n) = monsterSimpleMomentum n := by
  ext i
  fin_cases i <;> simp [monsterNativeMomentum, imaginaryRoot, monsterSimpleMomentum]

private theorem nonzero_real_root : ∃ e : W positiveRoot, e ≠ 0 := by
  have ha : momentumRealPart positiveRootClass ∈ W positiveRoot := by
    apply (mem_realMomentumWeightSpace positiveRoot _).mpr
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact ⟨_, rfl⟩
    · rw [positiveRootClass, inclCycle, LinearMap.comp_apply, coefficientConjugationMomentum_incl]
      exact ⟨_, rfl⟩
  have hb : momentumImaginaryPart positiveRootClass ∈ W positiveRoot := by
    apply (mem_realMomentumWeightSpace positiveRoot _).mpr
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact ⟨_, rfl⟩
    · rw [positiveRootClass, inclCycle, LinearMap.comp_apply, coefficientConjugationMomentum_incl]
      exact ⟨_, rfl⟩
  let a : W positiveRoot := ⟨momentumRealPart positiveRootClass, ha⟩
  let b : W positiveRoot := ⟨momentumImaginaryPart positiveRootClass, hb⟩
  by_cases h : a = 0
  · refine ⟨b, fun hz => opposite_root_lie_brackets.1 ?_⟩
    have h₁ : (a : L) = 0 := congrArg Subtype.val h
    have h₂ : (b : L) = 0 := congrArg Subtype.val hz
    simpa [h₁, h₂] using
      (show positiveRootClass = momentumRealValue (a : L) +
        Complex.I • momentumRealValue (b : L) from momentumH1_real_decomposition _)
  · exact ⟨a, h⟩

/-- A nonzero real class at the native real simple momentum. -/
def monsterRealSimpleE : W positiveRoot := Classical.choose nonzero_real_root

theorem monsterRealSimpleE_ne_zero : monsterRealSimpleE ≠ 0 :=
  Classical.choose_spec nonzero_real_root

private theorem real_root_pair_exists :
    ∃ f : W (-positiveRoot), realOppositeBPZ positiveRoot monsterRealSimpleE f = 1 := by
  have hne : realOppositeBPZ positiveRoot monsterRealSimpleE ≠ 0 := by
    intro hz
    apply monsterRealSimpleE_ne_zero
    apply (realOppositeBPZ positiveRoot).toPerfPair.injective
    simpa using hz
  obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hne
  have hval : realOppositeBPZ positiveRoot monsterRealSimpleE f ≠ 0 := by simpa using hf
  refine ⟨((realOppositeBPZ positiveRoot monsterRealSimpleE f)⁻¹ • f : W (-positiveRoot)), ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hval]

/-- A negative real generator normalized by signed BPZ pairing with the positive one. -/
def monsterRealSimpleF : W (-positiveRoot) := Classical.choose real_root_pair_exists

theorem monsterRealSimple_pair :
    realOppositeBPZ positiveRoot monsterRealSimpleE monsterRealSimpleF = 1 :=
  Classical.choose_spec real_root_pair_exists

local instance (p : Momentum) : FiniteDimensional ℝ (W p) :=
  realMomentumWeightSpace_finiteDimensional p

/-- The imaginary labels are a positive order and an index of its actual real basis. -/
abbrev MonsterRealImaginaryIndex :=
  Σ n : ℕ+, Fin (Module.finrank ℝ (W (monsterSimpleMomentum n)))

/-- The positive Serre exponent at an imaginary label. -/
abbrev monsterRealOrder (j : MonsterRealImaginaryIndex) : ℕ+ := j.1

/-- A basis of the actual real momentum space of each imaginary simple root. -/
def monsterRealPositiveBasis (n : ℕ+) :
    Module.Basis (Fin (Module.finrank ℝ (W (monsterSimpleMomentum n))))
      ℝ (W (monsterSimpleMomentum n)) :=
  Module.finBasis ℝ _

/-- The negative basis transported from the dual of the positive basis by signed BPZ. -/
def monsterRealNegativeBasis (n : ℕ+) :
    Module.Basis (Fin (Module.finrank ℝ (W (monsterSimpleMomentum n))))
      ℝ (W (-monsterSimpleMomentum n)) :=
  (monsterRealPositiveBasis n).dualBasis.map
    (realOppositeBPZ (monsterSimpleMomentum n)).flip.toPerfPair.symm

theorem monsterRealImaginary_pair (n : ℕ+)
    (i j : Fin (Module.finrank ℝ (W (monsterSimpleMomentum n)))) :
    realOppositeBPZ (monsterSimpleMomentum n)
      (monsterRealPositiveBasis n i) (monsterRealNegativeBasis n j) =
      if i = j then 1 else 0 := by
  rw [monsterRealNegativeBasis, Module.Basis.map_apply, LinearMap.apply_toPerfPair_flip,
    Module.Basis.dualBasis_apply_self]

/-- Values of the positive presentation's generators in the actual real Lie algebra. -/
def monsterRealPositiveGenerator : Option MonsterRealImaginaryIndex → L
  | none => monsterRealSimpleE
  | some ⟨n, i⟩ => monsterRealPositiveBasis n i

/-- The corresponding normalized negative generators in the actual real Lie algebra. -/
def monsterRealNegativeGenerator : Option MonsterRealImaginaryIndex → L
  | none => monsterRealSimpleF
  | some ⟨n, i⟩ => monsterRealNegativeBasis n i

private theorem realAdIter_mem {p q : Momentum} (x : W p) (y : W q) (k : ℕ) :
    adIter (x : L) k (y : L) ∈ W (k • p + q) := by
  induction k with
  | zero => simp [adIter]
  | succ k ih =>
    change _ ∈ realMomentumWeightSpace _
    simpa only [adIter, succ_nsmul', add_assoc] using
      realWeight_lie_mem_add p (k • p + q) x ⟨_, ih⟩

private theorem eq_zero_of_null {p : Momentum} {x : L}
    (hx : x ∈ W p) (hne : p ≠ 0) (hnull : p 0 = 0 ∨ p 1 = 0) : x = 0 := by
  have h := realMomentumWeightSpace_eq_bot_of_null p hne (by
    rw [momentumRealBPZ_momentum_norm]
    rcases hnull with h | h <;> simp [h])
  change x ∈ realMomentumWeightSpace p at hx
  rw [h] at hx
  exact (LieSubmodule.mem_bot x).mp hx

private theorem serre_null (n : ℕ) :
    n • positiveRoot + monsterSimpleMomentum n = ![(n : ℤ) + 1, 0] := by
  ext i
  fin_cases i <;> simp [positiveRoot, monsterSimpleMomentum, Pi.add_apply, nsmul_eq_mul]

/-- The positive real adjoint string vanishes at the exact Serre depth. -/
theorem monsterRealPositive_serre (j : MonsterRealImaginaryIndex) :
    adIter (monsterRealPositiveGenerator none) (monsterRealOrder j : ℕ)
      (monsterRealPositiveGenerator (some j)) = 0 := by
  obtain ⟨n, i⟩ := j
  have h := realAdIter_mem monsterRealSimpleE (monsterRealPositiveBasis n i) (n : ℕ)
  rw [serre_null] at h
  refine eq_zero_of_null h (fun hz => ?_) (Or.inr rfl)
  have hzero := congrFun hz (0 : Fin 2)
  change ((n : ℕ) : ℤ) + 1 = 0 at hzero
  omega

/-- The BPZ-dual negative generators satisfy the negative Serre relation. -/
theorem monsterRealNegative_serre (j : MonsterRealImaginaryIndex) :
    adIter (monsterRealNegativeGenerator none) (monsterRealOrder j : ℕ)
      (monsterRealNegativeGenerator (some j)) = 0 := by
  obtain ⟨n, i⟩ := j
  have h := realAdIter_mem monsterRealSimpleF (monsterRealNegativeBasis n i) (n : ℕ)
  rw [smul_neg, ← neg_add, serre_null] at h
  refine eq_zero_of_null h (fun hz => ?_) (Or.inr rfl)
  have hzero := congrFun hz (0 : Fin 2)
  change -(((n : ℕ) : ℤ) + 1) = 0 at hzero
  omega

local notation "P" => PositivePresentation monsterRealOrder
local notation "F" => FreeLieAlgebra ℝ (Option MonsterRealImaginaryIndex)

private def freeToRealBRST : F →ₗ⁅ℝ⁆ L :=
  FreeLieAlgebra.lift ℝ monsterRealPositiveGenerator

private theorem map_adIter {A B : Type*} [LieRing A] [LieAlgebra ℝ A]
    [LieRing B] [LieAlgebra ℝ B] (f : A →ₗ⁅ℝ⁆ B) (e x : A) (k : ℕ) :
    f (adIter e k x) = adIter (f e) k (f x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [adIter, adIter, LieHom.map_lie, ih]

private theorem serreIdeal_le_realBRST_ker : serreIdeal monsterRealOrder ≤ freeToRealBRST.ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro _ ⟨j, rfl⟩
  change freeToRealBRST (adIter (FreeLieAlgebra.of ℝ none) (monsterRealOrder j : ℕ)
    (FreeLieAlgebra.of ℝ (some j))) = 0
  rw [map_adIter]
  simpa only [freeToRealBRST, FreeLieAlgebra.lift_of_apply] using monsterRealPositive_serre j

/-- The positive Monster Serre map over ℝ, valued in the full native fixed BRST Lie algebra. -/
def monsterPositiveToRealBRST : P →ₗ⁅ℝ⁆ L :=
  { (serreIdeal monsterRealOrder).toSubmodule.liftQ freeToRealBRST.toLinearMap
      serreIdeal_le_realBRST_ker with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => exact freeToRealBRST.map_lie x y }

@[simp] theorem monsterPositiveToRealBRST_generator (j : Option MonsterRealImaginaryIndex) :
    monsterPositiveToRealBRST (generator monsterRealOrder j) = monsterRealPositiveGenerator j := by
  change freeToRealBRST (FreeLieAlgebra.of ℝ j) = _
  exact FreeLieAlgebra.lift_of_apply _ _

private theorem presentationQuotient_surjective :
    Function.Surjective (presentationQuotient monsterRealOrder) :=
  Submodule.Quotient.mk_surjective _

private theorem eq_top_of_contains_generators (S : LieSubalgebra ℝ P)
    (h : ∀ j, generator monsterRealOrder j ∈ S) : S = ⊤ := by
  let lift : F →ₗ⁅ℝ⁆ S := FreeLieAlgebra.lift ℝ fun j => ⟨_, h j⟩
  have hlift : S.incl.comp lift = presentationQuotient monsterRealOrder := by
    apply FreeLieAlgebra.hom_ext
    intro j
    change (lift (FreeLieAlgebra.of ℝ j) : P) = _
    rw [show lift (FreeLieAlgebra.of ℝ j) = ⟨_, h j⟩ from FreeLieAlgebra.lift_of_apply _ _]
    rfl
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := presentationQuotient_surjective x
  rw [← hlift]
  exact (lift y).property

local notation "G" => presentationGrade monsterRealOrder

private def matchingGrade (p : Weight) : Submodule ℝ P :=
  G p ⊓ (W (monsterNativeMomentum p)).comap monsterPositiveToRealBRST.toLinearMap

private theorem matchingGrade_lie {p q : Weight} {x y : P}
    (hx : x ∈ matchingGrade p) (hy : y ∈ matchingGrade q) :
    ⁅x, y⁆ ∈ matchingGrade (p + q) := by
  refine ⟨presentationGrade_bracket monsterRealOrder hx.1 hy.1, ?_⟩
  change monsterPositiveToRealBRST ⁅x, y⁆ ∈ W (monsterNativeMomentum (p + q))
  rw [LieHom.map_lie, map_add]
  exact realWeight_lie_mem_add _ _ ⟨_, hx.2⟩ ⟨_, hy.2⟩

private def matchingGrades : LieSubalgebra ℝ P where
  __ := ⨆ p, matchingGrade p
  lie_mem' := by
    intro x y hx hy
    let U : Submodule ℝ P := ⨆ p, matchingGrade p
    change x ∈ U at hx
    change y ∈ U at hy
    change ⁅x, y⁆ ∈ U
    refine Submodule.iSup_induction (motive := fun x => ⁅x, y⁆ ∈ U) _ hx ?_ ?_ ?_
    · intro p x hx
      refine Submodule.iSup_induction (motive := fun y => ⁅x, y⁆ ∈ U) _ hy ?_ ?_ ?_
      · intro q y hy
        exact Submodule.mem_iSup_of_mem (p + q) (matchingGrade_lie hx hy)
      · rw [lie_zero]
        exact zero_mem _
      · intro u v hu hv
        rw [lie_add]
        exact add_mem hu hv
    · rw [zero_lie]
      exact zero_mem _
    · intro u v hu hv
      rw [add_lie]
      exact add_mem hu hv

private theorem matchingGrades_eq_top : matchingGrades = ⊤ := by
  apply eq_top_of_contains_generators
  intro j
  change generator monsterRealOrder j ∈ ⨆ p, matchingGrade p
  cases j with
  | none =>
    apply Submodule.mem_iSup_of_mem realRoot
    refine ⟨real_mem_presentationGrade monsterRealOrder, ?_⟩
    change monsterPositiveToRealBRST (generator monsterRealOrder none) ∈
      W (monsterNativeMomentum realRoot)
    rw [monsterPositiveToRealBRST_generator, monsterNativeMomentum_realRoot]
    exact monsterRealSimpleE.property
  | some j =>
    apply Submodule.mem_iSup_of_mem (imaginaryRoot (monsterRealOrder j : ℕ))
    refine ⟨imaginary_mem_presentationGrade monsterRealOrder j, ?_⟩
    change monsterPositiveToRealBRST (generator monsterRealOrder (some j)) ∈
      W (monsterNativeMomentum (imaginaryRoot (monsterRealOrder j : ℕ)))
    rw [monsterPositiveToRealBRST_generator, monsterNativeMomentum_imaginaryRoot]
    obtain ⟨n, i⟩ := j
    exact (monsterRealPositiveBasis n i).property

/-- The quotient homomorphism carries each paper grade to its actual native real momentum. -/
theorem monsterPositiveToRealBRST_mem_grade {p : Weight} {x : P} (hx : x ∈ G p) :
    monsterPositiveToRealBRST x ∈ W (monsterNativeMomentum p) := by
  classical
  have hall : ∀ y : P, y ∈ (⨆ q, matchingGrade q : Submodule ℝ P) := fun y => by
    change y ∈ matchingGrades
    rw [matchingGrades_eq_top]
    exact LieSubalgebra.mem_top y
  have hproj : ∀ y : P, (↑(DirectSum.decompose G y p) : P) ∈ matchingGrade p := by
    intro y
    refine Submodule.iSup_induction
      (motive := fun y => (↑(DirectSum.decompose G y p) : P) ∈ matchingGrade p)
      _ (hall y) ?_ ?_ ?_
    · intro q y hy
      by_cases h : q = p
      · subst q
        rw [DirectSum.decompose_of_mem_same G hy.1]
        exact hy
      · rw [DirectSum.decompose_of_mem_ne G hy.1 h]
        exact zero_mem _
    · simp
    · intro u v hu hv
      rw [DirectSum.decompose_add]
      change (↑(DirectSum.decompose G u p) : P) + ↑(DirectSum.decompose G v p) ∈ _
      exact add_mem hu hv
  have h := hproj x
  rw [DirectSum.decompose_of_mem_same G hx] at h
  exact h.2

private theorem injectiveOn_generator_span {ι : Type*} (v : ι → P)
    (h : LinearIndependent ℝ (monsterPositiveToRealBRST ∘ v)) :
    Set.InjOn monsterPositiveToRealBRST (Submodule.span ℝ (Set.range v) : Set P) := by
  intro x hx y hy hxy
  rw [SetLike.mem_coe, ← Finsupp.range_linearCombination] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  apply congrArg (Finsupp.linearCombination ℝ v)
  apply h
  change monsterPositiveToRealBRST.toLinearMap (Finsupp.linearCombination ℝ v a) =
    monsterPositiveToRealBRST.toLinearMap (Finsupp.linearCombination ℝ v b) at hxy
  rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination] at hxy
  exact hxy

private theorem imaginary_grade_span (n : ℕ+) :
    G (imaginaryRoot n) = Submodule.span ℝ
      (Set.range fun i => generator monsterRealOrder (some (⟨n, i⟩ : MonsterRealImaginaryIndex))) := by
  change G (1, ((n : ℕ) : ℤ)) = _
  rw [presentationGrade_first monsterRealOrder _ (by omega)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨m, i⟩, hm, rfl⟩
    have hmn : m = n := PNat.coe_injective (Int.ofNat.inj hm)
    subst m
    exact Set.mem_range_self i
  · rintro ⟨i, rfl⟩
    exact ⟨⟨n, i⟩, rfl, rfl⟩

/-- The map is injective on each first-coordinate-one homogeneous space. -/
theorem monsterPositiveToRealBRST_injOn_first (n : ℤ) :
    Set.InjOn monsterPositiveToRealBRST (G (1, n) : Set P) := by
  by_cases hreal : n = -1
  · subst n
    change Set.InjOn monsterPositiveToRealBRST (G realRoot : Set P)
    rw [presentationGrade_real monsterRealOrder]
    intro x hx y hy hxy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [map_smul, monsterPositiveToRealBRST_generator] at hxy
    have hne : monsterRealPositiveGenerator none ≠ 0 :=
      fun hz => monsterRealSimpleE_ne_zero (Subtype.ext hz)
    have hab : a = b := by
      have h : (a - b) • monsterRealPositiveGenerator none = 0 := by rw [sub_smul, hxy, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hne)
    rw [hab]
  by_cases hn : 0 < n
  · let m : ℕ+ := ⟨n.toNat, by omega⟩
    have hm : ((m : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn.le
    rw [← hm]
    change Set.InjOn monsterPositiveToRealBRST (G (imaginaryRoot m) : Set P)
    rw [imaginary_grade_span]
    apply injectiveOn_generator_span
    change LinearIndependent ℝ (fun i => monsterPositiveToRealBRST (generator monsterRealOrder
      (some (⟨m, i⟩ : MonsterRealImaginaryIndex))))
    simp only [monsterPositiveToRealBRST_generator]
    exact (monsterRealPositiveBasis m).linearIndependent.map_injOn
      (W (monsterSimpleMomentum m)).subtype Subtype.val_injective.injOn
  · rw [presentationGrade_eq_bot_of_outside monsterRealOrder
      (p := (1, n)) (by simpa [realRoot] using hreal) (by simpa using hn)]
    intro x hx y hy _
    exact (Submodule.mem_bot ℝ).mp hx |>.trans ((Submodule.mem_bot ℝ).mp hy).symm

/-- The paper weight of an indexed simple generator. -/
def monsterRealSimpleWeight : Option MonsterRealImaginaryIndex → Weight
  | none => realRoot
  | some j => imaginaryRoot (monsterRealOrder j)

local notation "simpleMomentum" => fun j => monsterNativeMomentum (monsterRealSimpleWeight j)

private theorem simpleMomentum_first (j : Option MonsterRealImaginaryIndex) :
    simpleMomentum j 0 = 1 := by
  cases j <;> simp [monsterRealSimpleWeight, monsterNativeMomentum, realRoot, imaginaryRoot]

private theorem positiveGenerator_mem (j : Option MonsterRealImaginaryIndex) :
    monsterRealPositiveGenerator j ∈ W (simpleMomentum j) := by
  cases j with
  | none =>
    simp only [monsterRealSimpleWeight, monsterNativeMomentum_realRoot]
    exact monsterRealSimpleE.property
  | some j =>
    obtain ⟨n, i⟩ := j
    simp only [monsterRealSimpleWeight, monsterNativeMomentum_imaginaryRoot]
    exact (monsterRealPositiveBasis n i).property

private theorem negativeGenerator_mem (j : Option MonsterRealImaginaryIndex) :
    monsterRealNegativeGenerator j ∈ W (-simpleMomentum j) := by
  cases j with
  | none =>
    simp only [monsterRealSimpleWeight, monsterNativeMomentum_realRoot]
    exact monsterRealSimpleF.property
  | some j =>
    obtain ⟨n, i⟩ := j
    simp only [monsterRealSimpleWeight, monsterNativeMomentum_imaginaryRoot]
    exact (monsterRealNegativeBasis n i).property

private theorem simple_pair_of_same_momentum (a b : Option MonsterRealImaginaryIndex)
    (h : simpleMomentum a = simpleMomentum b) :
    momentumRealBPZ (monsterRealPositiveGenerator a) (monsterRealNegativeGenerator b) =
      if a = b then 1 else 0 := by
  rcases a with _ | ⟨n, i⟩ <;> rcases b with _ | ⟨m, j⟩
  · exact monsterRealSimple_pair
  · have hsecond := congrFun h (1 : Fin 2)
    simp [monsterRealSimpleWeight, monsterNativeMomentum, realRoot, imaginaryRoot] at hsecond
    omega
  · have hsecond := congrFun h (1 : Fin 2)
    simp [monsterRealSimpleWeight, monsterNativeMomentum, realRoot, imaginaryRoot] at hsecond
    omega
  · have hsecond := congrFun h (1 : Fin 2)
    have hnm : n = m := PNat.coe_injective (Int.ofNat.inj (neg_inj.mp hsecond))
    subst m
    have hp := monsterRealImaginary_pair n i j
    change momentumRealBPZ (monsterRealPositiveBasis n i : L)
      (monsterRealNegativeBasis n j : L) = _ at hp
    simpa only [monsterRealPositiveGenerator, monsterRealNegativeGenerator, Option.some.injEq,
      Sigma.mk.inj_iff, heq_eq_eq, true_and] using hp

/-- The raised native momentum of each simple generator. -/
def monsterRealSimpleCartan (j : Option MonsterRealImaginaryIndex) : L :=
  realCartanClass (fun i => (simpleMomentum j i : ℝ))

/-- Mixed simple brackets give the Cartan vector along the diagonal. Distinct momenta
have nonzero null difference, and distinct indices at one momentum are BPZ orthogonal. -/
theorem monsterRealSimple_mixed_lie (a b : Option MonsterRealImaginaryIndex) :
    ⁅monsterRealPositiveGenerator a, monsterRealNegativeGenerator b⁆ =
      if a = b then monsterRealSimpleCartan a else 0 := by
  by_cases h : simpleMomentum a = simpleMomentum b
  · have hneg := negativeGenerator_mem b
    rw [← h] at hneg
    rw [lie_realMomentumWeightSpace_neg _ _ _ (positiveGenerator_mem a) hneg,
      simple_pair_of_same_momentum a b h]
    by_cases hab : a = b <;> simp [hab, monsterRealSimpleCartan]
  · rw [ite_eq_right (fun hab => h (congrArg (fun j => simpleMomentum j) hab))]
    apply eq_zero_of_null
      (realWeight_lie_mem_add _ _ ⟨_, positiveGenerator_mem a⟩ ⟨_, negativeGenerator_mem b⟩)
    · simpa only [← sub_eq_add_neg, sub_ne_zero] using h
    · exact Or.inl (by simp [Pi.add_apply, Pi.neg_apply, simpleMomentum_first])

private theorem native_weightForm (p q : Weight) :
    realMomentumWeight (monsterNativeMomentum q)
      (realCartanEquiv (fun i => (monsterNativeMomentum p i : ℝ))) = weightForm p q := by
  rw [realMomentumWeight_coordinates]
  simp [monsterNativeMomentum, weightForm]
  ring

/-- The actual Cartan action has the symmetric Monster matrix entries, with opposite
signs on the BPZ-dual negative generators. -/
theorem monsterRealSimple_cartan_lie (a b : Option MonsterRealImaginaryIndex) :
    ⁅monsterRealSimpleCartan a, monsterRealPositiveGenerator b⁆ =
      weightForm (monsterRealSimpleWeight a) (monsterRealSimpleWeight b) •
        monsterRealPositiveGenerator b ∧
    ⁅monsterRealSimpleCartan a, monsterRealNegativeGenerator b⁆ =
      -(weightForm (monsterRealSimpleWeight a) (monsterRealSimpleWeight b)) •
        monsterRealNegativeGenerator b := by
  let h := realCartanEquiv (fun i => (simpleMomentum a i : ℝ))
  have hx := positiveGenerator_mem b
  have hy := negativeGenerator_mem b
  change monsterRealPositiveGenerator b ∈
    LieModule.weightSpace L (realMomentumWeight (simpleMomentum b)) at hx
  change monsterRealNegativeGenerator b ∈
    LieModule.weightSpace L (realMomentumWeight (-simpleMomentum b)) at hy
  rw [LieModule.mem_weightSpace] at hx hy
  have hx' := hx h
  have hy' := hy h
  have hw : realMomentumWeight (-simpleMomentum b) h = -realMomentumWeight (simpleMomentum b) h := by
    dsimp only [h]
    rw [realMomentumWeight_coordinates, realMomentumWeight_coordinates]
    simp only [Pi.neg_apply, Int.cast_neg, mul_neg, ← neg_add]
  change ⁅h, monsterRealPositiveGenerator b⁆ = _ at hx'
  change ⁅h, monsterRealNegativeGenerator b⁆ = _ at hy'
  rw [hw] at hy'
  exact ⟨hx'.trans (congrArg (· • monsterRealPositiveGenerator b) (native_weightForm _ _)),
    hy'.trans (congrArg (fun r => -r • monsterRealNegativeGenerator b) (native_weightForm _ _))⟩

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
