import Mathlib
import OmegaBuild.Commands

compile_only_with_mathlib
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

This file: Instance priorities, shortcut instances, simp set-up; Mathlib matrix lemmas restated with
classical decidability. -/

/-- The proposition that α is empty, that is, has no elements; a synonym for `IsEmpty α`. -/
def IsVoid := IsEmpty
@[simp 1001] lemma isEmpty_iff_isVoid α : IsEmpty α ↔ IsVoid α := .rfl
attribute [instance 20] MonTypeEquivalenceMon.monMonoid
  CommMonTypeEquivalenceCommMon.commMonCommMonoid GrpTypeEquivalenceGrp.grpGroup
  IsPurelyInseparable.isIntegral NonUnitalNonAssocSemiring.toAddCommMonoid
  IsDedekindDomain.toIsDomain SetLike.GradeZero.instCommSemiring SetLike.GradeZero.instMonoid
  SetLike.GradeZero.instSemiring SetLike.GradeZero.instRing SetLike.GradeZero.instCommRing
  SetLike.GradeZero.instCommMonoid MulSemiringAction.toDistribMulAction AddQuantale.instAddLeftMono
  AddQuantale.instAddRightMono LieAdmissibleAlgebra.toModule RightPreLieAlgebra.toModule
  LeftPreLieAlgebra.toModule LieAlgebra.toModule LieRing.toAddCommGroup
  Action.FintypeCat.instMulActionObjFiniteOf NonarchimedeanRing.toIsTopologicalRing
  NonarchimedeanAddGroup.toIsTopologicalAddGroup LieRinehartAlgebra.toIsScalarTower
  GroupConeClass.toSubmonoidClass IsAffineAddMonoid.toHasUniqueDiv IsAffineAddMonoid.toIsAddFG
  instNontrivialOfCharZero MeasureTheory.instSFiniteOfCountable
  CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCountable
  CategoryTheory.Limits.instHasCoproductsOfShapeOfHasCountableCoproductsOfCountable
  Torsor.toMulAction GradedMonoid.GradeZero.smul Prod.distribMulAction Prod.instStarModule
  PerfectField.ofFinite littleWedderburn BooleanRing.toRing BooleanRing.toCommRing
  FunLike.toDecidableEq
  Module.free_of_finite_type_torsion_free' IsOrderedCancelAddMonoid.toIsCancelAdd
  instIsLeftCancelAddOfAddLeftReflectLE instSMulZeroClass NonUnitalAlgSemiHomClass.toMulHomClass
  NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass CoalgHomClass.toSemilinearMapClass
  RingHomClass.toLinearMapClassNNRat RingHomClass.toLinearMapClassRat
  SemilinearMapClass.toAddHomClass CentroidHomClass.toAddMonoidHomClass BialgHomClass.toAlgHomClass
  MonoidWithZeroHomClass.toZeroHomClass Function.locallyCompactSpace IsAlgClosure.isAlgebraic
  IsPurelyInseparable.normal Quantale.instMulRightMono Quantale.instMulLeftMono
  NonUnitalNonAssocRing.toAddCommGroup CategoryTheory.CountableCategory.countableObj
  CStarAlgebra.instPosPart AddCommMonoidWithOne.toAddCommMonoid BialgHomClass.toMonoidHomClass
  ProperSMul.toContinuousSMul LieAdmissibleRing.toNonUnitalNonAssocRing
  IsValuativeTopology.instIsTopologicalAddGroup SemilinearIsometryClass.toSemilinearMapClass
  AlexandrovDiscrete.toLocallyCompactSpace Valuation.HasExtension.instIsScalarTower_valuationSubring
  OreLocalization.instDistribMulActionOfIsScalarTower Pi.starRing'
  CompletePartialOrder.toPartialOrder Valued.toUniformSpace TotallySeparatedSpace.t2Space
  Lean.Grind.OrderedRing.instIsCharPOfNatNatOfLawfulOrderLT Prod.continuousSMul Prod.isCentralScalar
  Prod.distribSMul Prod.smulZeroClass Prod.continuousConstSMul
  IsSemitopologicalSemiring.toContinuousAdd IsSemitopologicalSemiring.toSeparatelyContinuousMul
  CategoryTheory.Limits.hasColimitsOfShape_discrete Algebra.IsAlgebraic.isIntegral
attribute [instance 1100] MonoidHomClass.toMulHomClass RingHomClass.toAddMonoidHomClass
attribute [instance 900] DivisionRing.toRing AddMonoidWithOne.toAddMonoid AddGroupWithOne.toAddGroup
attribute [instance high] Pi.locallyCompactSpace_of_finite Pi.borelSpace
  AddEquivClass.instAddMonoidHomClass secondCountableTopologyEither_of_left
instance : SecondCountableTopology ℂ := inferInstance
instance {n} [Fintype n] : BorelSpace (n → ℂ) := inferInstance
instance {n} [Fintype n] : SecondCountableTopology (n → ℂ) := inferInstance
instance {n R} [Ring R] [Fintype n] [DecidableEq n] :
  Lean.Grind.IsCharP (Matrix n n R) (ringChar (Matrix n n R)) := inferInstance
variable {G A M} [Group G] (H : Subgroup G) [Semiring A] [AddCommMonoid M] [Module A M]
/-- The type of elements of a submodule S of a module M over a semiring A. -/
abbrev SubmoduleElem (S : Submodule A M) := ↥S
instance : CoeSort (Submodule A M) (Type _) := ⟨SubmoduleElem⟩
@[to_additive] instance : MulOneClass H := inferInstance
@[to_additive] instance : Monoid H := inferInstance
@[to_additive] instance : DivisionMonoid H := inferInstance
-- Equality is classical: every proposition is decidable (by choice), and the instances that compute
-- equality on the types used as index sets rank below, so that each index set has one instance.
-- `open Calc` brings eight of these computing instances back.
attribute [instance low] Classical.propDecidable
attribute [instance 101] Classical.decEq
attribute [instance 20] instDecidableEqSum instDecidableEqProd instDecidableEqPUnit FinEnum.decEq
  instDecidableEqFin instDecidableEqSigma Sigma.instDecidableEqSigma Subtype.instDecidableEq
  instDecidableEqEmpty Fintype.decidablePiFintype LinearOrder.toDecidableEq ZMod.decidableEq
  Matrix.decidableEq
scoped[Calc] attribute [instance] instDecidableEqSum instDecidableEqProd instDecidableEqPUnit
  instDecidableEqFin Sigma.instDecidableEqSigma Subtype.instDecidableEq Fintype.decidablePiFintype
  ZMod.decidableEq
scoped[Fint] attribute [instance low] Fintype.ofFinite
-- erases these simp lemmas for every importer; the lemmas are only named in order to be erased
set_option warning.simp.varHead false in
attribute [simp ←, simp] Matrix.conjTranspose_eq_transpose_of_trivial MonoidHom.CompTriple.comp_eq
  LinearMap.identityMapOfZeroModuleIsZero LowerAdjoint.closure_le_closed_iff_le smul_left_cancel_iff
  PartialOrder.mkOfAddGroupCone_le_iff mul_cancel_left_mem_nonZeroDivisors IsAddKleinFour.card_four'
  MeasureTheory.lintegral_of_isEmpty PartialOrder.mkOfGroupCone_le_iff Nat.card_eq_zero_of_infinite
  IsRegular.smul_eq_zero_iff_right
  Unitary.star_mul_self_of_mem Representation.isTrivial_def inv_mul_cancel_of_invertible bot_eq_one'
  EmbeddingLike.map_eq_one_iff Submodule.smul_coe_torsionBy Valuation.IsUniformizer.val star_trivial
  SetLike.GradeZero.coe_ofNat Associates.coe_unit_eq_one inv_mul_cancel_comm_assoc nsmul_eq_zero_iff
  SetLike.GradeZero.coe_mul RingHomCompTriple.comp_eq Finset.Ioc_eq_empty_of_le Finset.univ_eq_empty
  IsRegular.smul_right_inj IsAddKleinFour.card_four RootPairing.indexNeg_neg BooleanRing.mul_add_mul
  Submodule.smul_mem_iff' IsKleinFour.card_four' Nat.sub_eq_zero_of_le IsUnit.inv_mul_cancel
  IsUnit.mul_inv_cancel GroupWithZero.dvd_iff Ring.inverse_non_unit ciSup_of_not_bddAbove tsum_empty
  inv_mul_cancel_comm mul_inv_cancel_comm Set.iInter_of_empty CharP.cast_eq_zero IsEmpty.exists_iff
  IsMin.finsetIio_eq Set.Icc_eq_empty RCLike.star_def map_one_eq_zero inf_of_le_right inf_of_le_left
  FunLike.coe_mul Nat.card_unique map_inv_eq_map map_neg_eq_map nhds_discrete smul_left_inj norm_map
  RKHS.coe_smul tsum_comp_neg Nat.sub_self conj_trivial bot_eq_zero'
attribute [simp] ZMod.natCast_self Finset.prod_mul_distrib Finset.sum_add_distrib
  MeasureTheory.integral_const_mul Matrix.mulVec_diagonal Matrix.mul_inv_rev
  MeasureTheory.integral_mul_const Ideal.map_span Complex.norm_exp Set.range_subset_iff
  Nat.factorial_ne_zero finrank_real_of_complex Subgroup.mem_subgroupOf Matrix.sub_mulVec
  Matrix.add_mulVec Matrix.blockTriangular_diagonal Matrix.mulVec_smul Matrix.smul_mulVec
  Module.finrank_pi_fintype Matrix.mulVec_add Pi.single_apply sub_eq_zero
  Subgroup.index_ne_zero_of_finite
-- directions of library equivalences, for dot notation; the adjoint of a matrix
alias ⟨_, Function.Injective.of_ker⟩ := injective_iff_map_eq_zero
alias ⟨_, Function.Bijective.of_existsUnique⟩ := Function.bijective_iff_existsUnique
alias ⟨IsCompact.compactSpace, _⟩ := isCompact_iff_compactSpace
alias ⟨_, Continuous.of_at⟩ := continuous_iff_continuousAt
alias ⟨_, Filter.Eventually.all⟩ := Filter.eventually_all
alias ⟨_, CharP.of_eq_zero⟩ := CharP.charP_iff_prime_eq_zero
open Matrix in lemma star_mulVec_dotProduct {m n} [Fintype m] [Fintype n] [StarRing A] (B : Matrix m
  n A) x y : star (B *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ Bᴴ *ᵥ y := by rw [star_mulVec, dotProduct_mulVec]
-- Mathlib states these lemmas with the computing instance; here they are for the classical one.
attribute [simp ←, simp] Matrix.fromBlocks_one
open Matrix Kronecker
variable {m n R : Type*}
@[simp] lemma diagonal_classical {i} [Zero R] d : @diagonal n R i _ d = diagonal d := by congr!
@[simp] lemma one_classical {i} [Zero R] [One R] :
  @OfNat.ofNat _ 1 (@One.toOfNat1 _ (@one n R i _ _)) = 1 := by congr!
@[simp] lemma fromBlocks_one' [Zero R] [One R] :
  fromBlocks 1 0 0 1 = (1 : Matrix (m ⊕ n) (m ⊕ n) R) := by simp [← ext_iff, one_apply]
variable [CommRing R] [Fintype m] [Fintype n] (A : Matrix m m R) (D : Matrix n n R)
@[simp] lemma det_classical {i} : @det m i _ R _ A = A.det := by congr
@[simp] lemma det_fromBlocks_zero₁₂' C : (fromBlocks A 0 C D).det = A.det * D.det := by
  convert A.det_fromBlocks_zero₁₂ ..
@[simp] lemma det_fromBlocks_zero₂₁' B : (fromBlocks A B 0 D).det = A.det * D.det := by
  convert A.det_fromBlocks_zero₂₁ ..
@[simp] lemma det_fromBlocks_one₁₁' (B : Matrix m n R) C : (fromBlocks 1 B C D).det =
  (D - C * B).det := by convert B.det_fromBlocks_one₁₁ ..
@[simp] lemma det_fromBlocks_one₂₂' (B : Matrix m n R) C : (fromBlocks A B C 1).det =
  (A - B * C).det := by convert A.det_fromBlocks_one₂₂ ..
@[simp] lemma charpoly_fromBlocks_zero₂₁' B : (fromBlocks A B 0 D).charpoly =
  A.charpoly * D.charpoly := by convert A.charpoly_fromBlocks_zero₂₁ ..
lemma inv_fromBlocks_zero₂₁_of_isUnit_iff' B (h : IsUnit A ↔ IsUnit D) : (fromBlocks A B 0 D)⁻¹ =
  fromBlocks A⁻¹ (-(A⁻¹ * B * D⁻¹)) 0 D⁻¹ := by convert A.inv_fromBlocks_zero₂₁_of_isUnit_iff B D h
lemma det_kronecker' : (A ⊗ₖ D).det = A.det ^ Fintype.card n * D.det ^ Fintype.card m := by
  convert A.det_kronecker D
lemma twoBlockTriangular_det₀ p [DecidablePred p] (h : ∀ i, ¬p i → ∀ j, p j → A i j = 0) :
    A.det = (A.toSquareBlockProp p).det * (A.toSquareBlockProp (¬p ·)).det := by
  convert A.twoBlockTriangular_det p h
variable {A D}
@[simp] lemma isUnit_fromBlocks_zero₂₁' {B} : IsUnit (fromBlocks A B 0 D) ↔ IsUnit A ∧ IsUnit D :=
  by convert Matrix.isUnit_fromBlocks_zero₂₁
@[simp] lemma isUnit_fromBlocks_zero₁₂' {C} : IsUnit (fromBlocks A 0 C D) ↔ IsUnit A ∧ IsUnit D :=
  by convert Matrix.isUnit_fromBlocks_zero₁₂
variable {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) R)
lemma det_succ_row' i : A.det = ∑ j, (-1) ^ (i.1 + j.1) * A i j *
  (A.submatrix i.succAbove j.succAbove).det := by convert A.det_succ_row i
lemma det_succ_column' j : A.det = ∑ i, (-1) ^ (i.1 + j.1) * A i j *
  (A.submatrix i.succAbove j.succAbove).det := by convert A.det_succ_column j
lemma det_succ_row_zero' : A.det = ∑ j, (-1) ^ j.1 * A 0 j *
  (A.submatrix .succ j.succAbove).det := by convert A.det_succ_row_zero
lemma det_succ_column_zero' : A.det = ∑ i, (-1) ^ i.1 * A i 0 *
  (A.submatrix i.succAbove .succ).det := by convert A.det_succ_column_zero
lemma adjugate_fin_succ_eq_det_submatrix' i j : A.adjugate i j = (-1) ^ (j.1 + i) * (A.submatrix
  j.succAbove i.succAbove).det := by convert A.adjugate_fin_succ_eq_det_submatrix ..
lemma det_vandermonde_ne_zero_iff' [IsDomain R] {v : Fin k → R} : (vandermonde v).det ≠ 0 ↔
  v.Injective := by convert Matrix.det_vandermonde_ne_zero_iff (v := v)
