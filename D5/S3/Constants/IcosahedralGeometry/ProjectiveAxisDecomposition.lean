/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecomposition
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The explicit F5 icosahedral action has projective axis orbits of sizes 6, 10, and 15. -/

/- Library-search audit trail (2026-08-28):
   * No D5 declaration covers the concrete 31-point action or its three orbits.
   * Pinned Mathlib supplies the generic projectivization and orbit-stabilizer APIs,
     but no declaration contains the source matrices or this finite computation.
   * Loogle and LeanSearch returned only those generic APIs; no exact third-party
     theorem was found. The detailed receipt is `/tmp/SEARCH-ob3.md`. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

abbrev F5 := ZMod 5
abbrev Vector := Fin 3 → F5

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The actual projective plane over `F₅`; finite coordinates are introduced only
through an equivalence below. -/
abbrev ProjectiveAxis := Projectivization F5 Vector

/-- The private finite chart used to evaluate the concrete certificates. -/
private abbrev AxisChart := Fin 31

noncomputable instance : Fintype ProjectiveAxis := Fintype.ofFinite ProjectiveAxis

noncomputable instance : DecidableEq ProjectiveAxis := Classical.decEq ProjectiveAxis

private theorem inv_f5 (x : F5) : x⁻¹ = x ^ 3 := by
  by_cases hx : x = 0
  · simp [hx]
  · apply ZMod.inv_eq_of_mul_eq_one
    calc
      x * x ^ 3 = x ^ 4 := by ring
      _ = 1 := by
        simpa using (ZMod.pow_card_sub_one_eq_one (p := 5) hx)

/-- A representative is projectively normalized by making its first nonzero
coordinate equal to one. -/
def IsNormalized (v : Vector) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

instance (v : Vector) : Decidable (IsNormalized v) := by
  unfold IsNormalized
  infer_instance

def normalizedVectors : Finset Vector :=
  Finset.univ.filter IsNormalized

/-- A canonical normalized representative of a projective direction. -/
abbrev NormalizedVector := normalizedVectors

def normalize (v : Vector) : NormalizedVector := by
  by_cases h0 : v 0 ≠ 0
  · refine ⟨fun i => v 0 ^ 3 * v i, ?_⟩
    simp only [normalizedVectors, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Or.inl
    rw [← inv_f5]
    exact inv_mul_cancel₀ h0
  by_cases h1 : v 1 ≠ 0
  · refine ⟨fun i => v 1 ^ 3 * v i, ?_⟩
    simp only [normalizedVectors, Finset.mem_filter, Finset.mem_univ, true_and]
    have hz0 : v 0 = 0 := not_ne_iff.mp h0
    apply Or.inr
    apply Or.inl
    constructor
    · simp [hz0]
    · rw [← inv_f5]
      exact inv_mul_cancel₀ h1
  by_cases h2 : v 2 ≠ 0
  · refine ⟨fun i => v 2 ^ 3 * v i, ?_⟩
    simp only [normalizedVectors, Finset.mem_filter, Finset.mem_univ, true_and]
    have hz0 : v 0 = 0 := not_ne_iff.mp h0
    have hz1 : v 1 = 0 := not_ne_iff.mp h1
    apply Or.inr
    apply Or.inr
    refine ⟨by simp [hz0], by simp [hz1], ?_⟩
    rw [← inv_f5]
    exact inv_mul_cancel₀ h2
  · refine ⟨![1, 0, 0], ?_⟩
    simp [normalizedVectors, IsNormalized]

/-- The canonical normalized vector represented by each chart index. -/
private def axisVector : AxisChart → Vector :=
  ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3],
    ![0, 1, 4], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 0, 3],
    ![1, 0, 4], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3],
    ![1, 1, 4], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3],
    ![1, 2, 4], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3],
    ![1, 3, 4], ![1, 4, 0], ![1, 4, 1], ![1, 4, 2], ![1, 4, 3],
    ![1, 4, 4]]

private def axisIndex (v : Vector) : AxisChart :=
  if v 0 = 0 then
    if v 1 = 0 then
      0
    else
      ⟨(v 2).val + 1, by
        have h2 := (v 2).val_lt
        omega⟩
  else
    ⟨6 + 5 * (v 1).val + (v 2).val, by
      have h1 := (v 1).val_lt
      have h2 := (v 2).val_lt
      omega⟩

private theorem axisIndex_axisVector (p : AxisChart) :
    axisIndex (axisVector p) = p := by
  fin_cases p <;> rfl

private theorem axisVector_axisIndex (v : NormalizedVector) :
    axisVector (axisIndex v.1) = v.1 := by
  fin_cases v <;> ext i <;> fin_cases i <;> rfl

/-- The chart lists every normalized projective representative exactly once. -/
theorem axisVector_unique_complete :
    ∀ v : NormalizedVector, ∃! p : AxisChart, axisVector p = v.1 := by
  intro v
  refine ⟨axisIndex v.1, axisVector_axisIndex v, ?_⟩
  intro p hp
  calc
    p = axisIndex (axisVector p) := (axisIndex_axisVector p).symm
    _ = axisIndex v.1 := congrArg axisIndex hp

/-- The order-three matrix `A` displayed in the source. -/
def matrixA : Matrix (Fin 3) (Fin 3) F5 :=
  ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]

/-- The order-five matrix `B` displayed in the source. -/
def matrixB : Matrix (Fin 3) (Fin 3) F5 :=
  ![![4, 4, 3], ![1, 0, 4], ![0, 1, 4]]

private def matrixAInv : Matrix (Fin 3) (Fin 3) F5 :=
  ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]

private def matrixBInv : Matrix (Fin 3) (Fin 3) F5 :=
  ![![1, 2, 1], ![1, 1, 2], ![1, 1, 1]]

/-- The projective permutation induced by the source matrix `A`. -/
private def projectiveA : Equiv.Perm AxisChart :=
  { toFun := ![6, 0, 7, 9, 8, 10, 1, 11, 21, 16, 26, 2, 12, 24, 18,
      30, 3, 13, 22, 20, 29, 4, 14, 25, 17, 28, 5, 15, 23, 19, 27]
    invFun := ![1, 6, 11, 16, 21, 26, 0, 2, 4, 3, 5, 7, 12, 17, 22,
      27, 9, 24, 14, 29, 19, 8, 18, 28, 13, 23, 10, 30, 25, 20, 15]
    left_inv := by decide
    right_inv := by decide }

/-- The projective permutation induced by the source matrix `B`. -/
private def projectiveB : Equiv.Perm AxisChart :=
  { toFun := ![24, 10, 16, 4, 27, 13, 26, 8, 3, 15, 17, 18, 6, 12, 30,
      2, 22, 0, 21, 25, 23, 14, 9, 19, 1, 29, 5, 7, 28, 20, 11]
    invFun := ![17, 24, 15, 8, 3, 26, 12, 27, 7, 22, 1, 30, 13, 5, 21,
      9, 2, 10, 11, 23, 29, 18, 16, 20, 0, 19, 6, 4, 28, 25, 14]
    left_inv := by decide
    right_inv := by decide }

/-- The chart permutations agree pointwise with projectivizing the source matrices. -/
theorem source_matrix_actions :
    (∀ p, (normalize (matrixA.mulVec (axisVector p))).1 =
      axisVector (projectiveA p)) ∧
    (∀ p, (normalize (matrixB.mulVec (axisVector p))).1 =
      axisVector (projectiveB p)) := by
  decide

private def icosahedralWords : List (List (Fin 4)) :=
  [[], [0], [1], [2], [3], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0],
   [2, 1], [2, 2], [3, 0], [3, 1], [3, 3], [0, 2, 0], [0, 2, 1],
   [0, 2, 2], [0, 3, 0], [0, 3, 1], [0, 3, 3], [1, 2, 0], [1, 2, 1],
   [1, 2, 2], [1, 3, 0], [1, 3, 1], [1, 3, 3], [2, 0, 2], [2, 0, 3],
   [2, 1, 3], [2, 2, 1], [3, 0, 2], [3, 1, 2], [3, 3, 0],
   [0, 2, 0, 2], [0, 2, 0, 3], [0, 2, 1, 3], [0, 3, 0, 2],
   [0, 3, 1, 2], [0, 3, 3, 0], [1, 2, 0, 2], [1, 2, 0, 3],
   [1, 2, 1, 3], [1, 3, 0, 2], [1, 3, 1, 2], [2, 0, 2, 0],
   [2, 0, 2, 1], [2, 0, 3, 1], [2, 1, 3, 0], [3, 0, 2, 1],
   [3, 1, 2, 0], [0, 2, 0, 2, 0], [0, 2, 0, 2, 1],
   [0, 2, 1, 3, 0], [0, 3, 1, 2, 0], [1, 2, 0, 2, 0],
   [1, 2, 0, 2, 1], [2, 0, 3, 1, 2], [2, 1, 3, 0, 2],
   [0, 2, 1, 3, 0, 2]]

private def evaluateLetter : Fin 4 → Equiv.Perm AxisChart :=
  ![projectiveA, projectiveA⁻¹, projectiveB, projectiveB⁻¹]

private def evaluateWord (word : List (Fin 4)) : Equiv.Perm AxisChart :=
  word.foldl (fun g letter => g * evaluateLetter letter) 1

/-- The source identifies its order-60 matrix group with `A₅`. -/
abbrev IcosahedralGroup := alternatingGroup (Fin 5)

private def alternatingPermA : Equiv.Perm (Fin 5) :=
  { toFun := ![1, 2, 0, 3, 4]
    invFun := ![2, 0, 1, 3, 4]
    left_inv := by decide
    right_inv := by decide }

private def alternatingPermB : Equiv.Perm (Fin 5) :=
  { toFun := ![1, 2, 3, 4, 0]
    invFun := ![4, 0, 1, 2, 3]
    left_inv := by decide
    right_inv := by decide }

private def alternatingA : IcosahedralGroup :=
  ⟨alternatingPermA, by
    change Equiv.Perm.sign alternatingPermA = 1
    decide⟩

private def alternatingB : IcosahedralGroup :=
  ⟨alternatingPermB, by
    change Equiv.Perm.sign alternatingPermB = 1
    decide⟩

private def evaluateAlternatingLetter : Fin 4 → IcosahedralGroup :=
  ![alternatingA, alternatingA⁻¹, alternatingB, alternatingB⁻¹]

private def evaluateAlternatingWord (word : List (Fin 4)) : IcosahedralGroup :=
  word.foldl (fun g letter => g * evaluateAlternatingLetter letter) 1

private def representativeWord (g : IcosahedralGroup) : List (Fin 4) :=
  (icosahedralWords.find? fun word => evaluateAlternatingWord word = g).getD []

private def actionPermutation (g : IcosahedralGroup) : Equiv.Perm AxisChart :=
  evaluateWord (representativeWord g)

private theorem actionPermutation_one : actionPermutation 1 = 1 := by
  decide

set_option maxHeartbeats 4000000 in
-- This certificate checks all products in the explicit 60-element chart action.
set_option maxRecDepth 100000 in
private theorem actionPermutation_mul :
    ∀ g h : IcosahedralGroup,
      actionPermutation (g * h) = actionPermutation g * actionPermutation h := by
  decide

private theorem source_generator_chart_actions :
    actionPermutation alternatingA = projectiveA ∧
      actionPermutation alternatingB = projectiveB := by
  decide

private instance chartMulAction : MulAction IcosahedralGroup AxisChart where
  smul g p := actionPermutation g p
  one_smul p := by
    change actionPermutation (1 : IcosahedralGroup) p = p
    rw [actionPermutation_one]
    rfl
  mul_smul g h p := by
    change actionPermutation (g * h) p =
      actionPermutation g (actionPermutation h p)
    rw [actionPermutation_mul]
    rfl

private def evaluateMatrixLetter : Fin 4 → Matrix (Fin 3) (Fin 3) F5 :=
  ![matrixA, matrixAInv, matrixB, matrixBInv]

private def evaluateMatrixWord (word : List (Fin 4)) : Matrix (Fin 3) (Fin 3) F5 :=
  word.foldl (fun matrix letter => matrix * evaluateMatrixLetter letter) 1

private def actionMatrix (g : IcosahedralGroup) : Matrix (Fin 3) (Fin 3) F5 :=
  evaluateMatrixWord (representativeWord g)

private theorem actionMatrix_one : actionMatrix 1 = 1 := by
  decide

set_option maxHeartbeats 12000000 in
-- This certificate checks all products in the explicit 60-element linear representation.
set_option maxRecDepth 100000 in
private theorem actionMatrix_mul :
    ∀ g h : IcosahedralGroup, actionMatrix (g * h) = actionMatrix g * actionMatrix h := by
  intro g h
  fin_cases g <;> fin_cases h <;> decide

/-- The concrete `A₅` representation acts linearly on the source's
three-dimensional `F₅` vector space. -/
instance : DistribMulAction IcosahedralGroup Vector where
  smul g v := (actionMatrix g).mulVec v
  one_smul v := by
    change (actionMatrix 1).mulVec v = v
    rw [actionMatrix_one, Matrix.one_mulVec]
  mul_smul g h v := by
    change (actionMatrix (g * h)).mulVec v =
      (actionMatrix g).mulVec ((actionMatrix h).mulVec v)
    rw [actionMatrix_mul, Matrix.mulVec_mulVec]
  smul_zero g := Matrix.mulVec_zero (actionMatrix g)
  smul_add g v w := Matrix.mulVec_add (actionMatrix g) v w

instance : SMulCommClass IcosahedralGroup F5 Vector where
  smul_comm g a v := by
    change (actionMatrix g).mulVec (a • v) = a • (actionMatrix g).mulVec v
    exact Matrix.mulVec_smul (actionMatrix g) a v

set_option maxRecDepth 100000 in
/-- The standard `A₅` generators act linearly by the two displayed source matrices. -/
theorem source_generator_actions :
    actionMatrix alternatingA = matrixA ∧ actionMatrix alternatingB = matrixB := by
  decide

/-- The explicit matrix of the invariant quadratic form from the source. -/
def formMatrix : Matrix (Fin 3) (Fin 3) F5 :=
  ![![2, 1, 1], ![1, 2, 1], ![1, 1, 2]]

private def chartQuadraticForm (p : AxisChart) : F5 :=
  dotProduct (axisVector p) (formMatrix.mulVec (axisVector p))

private def chartFivefoldAxes : Finset AxisChart :=
  Finset.univ.filter fun p => chartQuadraticForm p = 0

private def chartThreefoldAxes : Finset AxisChart :=
  Finset.univ.filter fun p => chartQuadraticForm p = 2 ∨ chartQuadraticForm p = 3

private def chartTwofoldAxes : Finset AxisChart :=
  Finset.univ.filter fun p => chartQuadraticForm p = 1 ∨ chartQuadraticForm p = 4

private abbrev ChartFivefoldAxis := chartFivefoldAxes

private def chartAxisOrbit (p : AxisChart) : Finset AxisChart :=
  Finset.univ.image fun g : IcosahedralGroup => g • p

set_option maxHeartbeats 4000000 in
-- This finite check enumerates the fivefold stabilizers in the 60-element group.
set_option maxRecDepth 100000 in
private theorem chartFiveCycle_mul_closed :
    ∀ p : ChartFivefoldAxis, ∀ g h : IcosahedralGroup,
      (g • p.1 = p.1 ∧ g ^ 5 = 1) → (h • p.1 = p.1 ∧ h ^ 5 = 1) →
        (g * h) • p.1 = p.1 ∧ (g * h) ^ 5 = 1 := by
  decide

set_option maxHeartbeats 4000000 in
-- This finite check enumerates inverses in the fivefold stabilizers.
set_option maxRecDepth 100000 in
private theorem chartFiveCycle_inv_closed :
    ∀ p : ChartFivefoldAxis, ∀ g : IcosahedralGroup,
      (g • p.1 = p.1 ∧ g ^ 5 = 1) → g⁻¹ • p.1 = p.1 ∧ g⁻¹ ^ 5 = 1 := by
  decide

private def chartFiveCycleSubgroup (p : ChartFivefoldAxis) : Subgroup IcosahedralGroup where
  carrier := {g | g • p.1 = p.1 ∧ g ^ 5 = 1}
  one_mem' := by
    constructor
    · exact one_smul IcosahedralGroup p.1
    · exact one_pow 5
  mul_mem' := by
    intro g h hg hh
    exact chartFiveCycle_mul_closed p g h hg hh
  inv_mem' := by
    intro g hg
    exact chartFiveCycle_inv_closed p g hg

private instance (p : ChartFivefoldAxis) : DecidablePred (· ∈ chartFiveCycleSubgroup p) := by
  intro g
  change Decidable (g • p.1 = p.1 ∧ g ^ 5 = 1)
  infer_instance

/-- The displayed projective matrix group has the source-stated order 60. -/
theorem icosahedralGroup_card : Fintype.card IcosahedralGroup = 60 := by
  rw [card_alternatingGroup]
  norm_num

set_option maxHeartbeats 4000000 in
-- The certificate exhaustively checks 31 axes against the 60-element action.
set_option maxRecDepth 100000 in
private theorem chartFiniteAxisCertificate :
    chartFivefoldAxes ∩ chartThreefoldAxes = ∅ ∧
      chartFivefoldAxes ∩ chartTwofoldAxes = ∅ ∧
      chartThreefoldAxes ∩ chartTwofoldAxes = ∅ ∧
      chartFivefoldAxes ∪ chartThreefoldAxes ∪ chartTwofoldAxes = Finset.univ ∧
      chartFivefoldAxes.card = 6 ∧
      chartThreefoldAxes.card = 10 ∧
      chartTwofoldAxes.card = 15 ∧
      (∀ p ∈ chartFivefoldAxes, chartAxisOrbit p = chartFivefoldAxes) ∧
      (∀ p ∈ chartThreefoldAxes, chartAxisOrbit p = chartThreefoldAxes) ∧
      (∀ p ∈ chartTwofoldAxes, chartAxisOrbit p = chartTwofoldAxes) ∧
      (∀ p ∈ chartFivefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 10) ∧
      (∀ p ∈ chartThreefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 6) ∧
      (∀ p ∈ chartTwofoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 4) := by
  decide

set_option maxHeartbeats 4000000 in
-- The normalizer certificate enumerates each fivefold axis and group element.
set_option maxRecDepth 100000 in
private theorem chartFivefoldNormalizerCertificate :
    ∀ p : ChartFivefoldAxis,
      Fintype.card (chartFiveCycleSubgroup p) = 5 ∧
        ∀ g : IcosahedralGroup,
          g ∈ MulAction.stabilizer IcosahedralGroup p.1 ↔
            g ∈ Subgroup.normalizer (chartFiveCycleSubgroup p : Set IcosahedralGroup) := by
  intro p
  fin_cases p <;> constructor
  all_goals
    first
    | decide
    | intro g
      fin_cases g <;>
        rw [Subgroup.mem_normalizer_iff] <;>
        decide

private theorem axisVector_ne_zero (p : AxisChart) : axisVector p ≠ 0 := by
  fin_cases p <;> decide

set_option maxRecDepth 100000 in
private theorem nonzeroVector_chart_complete :
    ∀ v : Vector, v ≠ 0 → ∃ p : AxisChart, ∃ a : F5, a • v = axisVector p := by
  decide

private def chartPoint (p : AxisChart) : ProjectiveAxis :=
  Projectivization.mk F5 (axisVector p) (axisVector_ne_zero p)

/-- The cardinality 31 is derived from the actual projective space. -/
theorem projectiveAxis_card : Nat.card ProjectiveAxis = 31 := by
  change Nat.card (Projectivization F5 Vector) = 31
  calc
    Nat.card (Projectivization F5 Vector) =
        ∑ i ∈ Finset.range 3, Nat.card F5 ^ i :=
      Projectivization.card_of_finrank F5 Vector (n := 3) (by simp [Vector])
    _ = 31 := by norm_num [F5]

private theorem chartPoint_surjective : Function.Surjective chartPoint := by
  intro x
  induction x using Projectivization.ind with
  | _ v hv =>
      obtain ⟨p, a, ha⟩ := nonzeroVector_chart_complete v hv
      refine ⟨p, ?_⟩
      apply (Projectivization.mk_eq_mk_iff' F5
        (axisVector p) v (axisVector_ne_zero p) hv).mpr
      exact ⟨a, ha⟩

private theorem chartPoint_bijective : Function.Bijective chartPoint := by
  apply (Nat.bijective_iff_surjective_and_card chartPoint).mpr
  refine ⟨chartPoint_surjective, ?_⟩
  rw [projectiveAxis_card]
  simp [AxisChart]

/-- The explicit 31-entry table is a coordinate equivalence for the actual
projective plane, not its definition. -/
noncomputable def projectiveChart : ProjectiveAxis ≃ Fin 31 :=
  (Equiv.ofBijective chartPoint chartPoint_bijective).symm

@[simp]
private theorem projectiveChart_symm_apply (p : AxisChart) :
    projectiveChart.symm p = chartPoint p := by
  rfl

@[simp]
private theorem projectiveChart_chartPoint (p : AxisChart) :
    projectiveChart (chartPoint p) = p := by
  rw [← projectiveChart_symm_apply, projectiveChart.apply_symm_apply]

@[simp]
private theorem projectiveChart_symm_embedding_apply (p : AxisChart) :
    projectiveChart (projectiveChart.symm.toEmbedding p) = p := by
  exact projectiveChart.apply_symm_apply p

private theorem normalize_ne_zero (v : Vector) : (normalize v).1 ≠ 0 := by
  intro hv
  have hn := (normalize v).2
  simp [normalizedVectors, IsNormalized, hv] at hn

set_option maxRecDepth 100000 in
private theorem normalize_scalar (v : Vector) (hv : v ≠ 0) :
    ∃ a : F5, a • v = (normalize v).1 := by
  revert v
  decide

private theorem mk_normalize (v : Vector) (hv : v ≠ 0) :
    Projectivization.mk F5 (normalize v).1 (normalize_ne_zero v) =
      Projectivization.mk F5 v hv := by
  obtain ⟨a, ha⟩ := normalize_scalar v hv
  exact (Projectivization.mk_eq_mk_iff' F5 _ _ _ _).mpr ⟨a, ha⟩

private theorem source_letter_actions (letter : Fin 4) :
    actionMatrix (evaluateAlternatingLetter letter) = evaluateMatrixLetter letter := by
  fin_cases letter <;> decide

set_option maxRecDepth 100000 in
private theorem source_matrix_letter_actions :
    ∀ letter : Fin 4, ∀ p : AxisChart,
      (normalize ((evaluateMatrixLetter letter).mulVec (axisVector p))).1 =
        axisVector (evaluateLetter letter p) := by
  intro letter p
  fin_cases letter <;> fin_cases p <;> decide

private theorem alternatingLetter_chartPoint (letter : Fin 4) (p : AxisChart) :
    evaluateAlternatingLetter letter • chartPoint p =
      chartPoint (evaluateLetter letter p) := by
  rw [chartPoint, Projectivization.smul_mk]
  change Projectivization.mk F5
      ((actionMatrix (evaluateAlternatingLetter letter)).mulVec (axisVector p)) _ =
    Projectivization.mk F5 (axisVector (evaluateLetter letter p)) _
  symm
  apply (Projectivization.mk_eq_mk_iff' F5 _ _ _ _).mpr
  obtain ⟨a, ha⟩ := normalize_scalar
    ((actionMatrix (evaluateAlternatingLetter letter)).mulVec (axisVector p))
    ((smul_ne_zero_iff_ne (evaluateAlternatingLetter letter)).mpr (axisVector_ne_zero p))
  refine ⟨a, ha.trans ?_⟩
  rw [source_letter_actions, source_matrix_letter_actions]

private theorem foldl_chartPoint :
    ∀ word : List (Fin 4), ∀ g : IcosahedralGroup, ∀ e : Equiv.Perm AxisChart,
      (∀ p, g • chartPoint p = chartPoint (e p)) →
        ∀ p,
          (word.foldl (fun h letter => h * evaluateAlternatingLetter letter) g) •
              chartPoint p =
            chartPoint
              ((word.foldl (fun f letter => f * evaluateLetter letter) e) p) := by
  intro word
  induction word with
  | nil =>
      intro g e h p
      exact h p
  | cons letter word ih =>
      intro g e h p
      apply ih (g * evaluateAlternatingLetter letter)
        (e * evaluateLetter letter)
      intro q
      rw [mul_smul, alternatingLetter_chartPoint, h]
      rfl

private theorem evaluateAlternatingWord_chartPoint
    (word : List (Fin 4)) (p : AxisChart) :
    evaluateAlternatingWord word • chartPoint p = chartPoint (evaluateWord word p) := by
  apply foldl_chartPoint word 1 1
  intro q
  simp

set_option maxHeartbeats 4000000 in
-- The finite certificate normalizes all 60 explicit representatives of `A₅`.
set_option maxRecDepth 100000 in
private theorem representativeWord_complete (g : IcosahedralGroup) :
    evaluateAlternatingWord (representativeWord g) = g := by
  fin_cases g <;> decide

private theorem chartPoint_smul (g : IcosahedralGroup) (p : AxisChart) :
    g • chartPoint p = chartPoint (g • p) := by
  calc
    g • chartPoint p =
        evaluateAlternatingWord (representativeWord g) • chartPoint p := by
      rw [representativeWord_complete]
    _ = chartPoint (evaluateWord (representativeWord g) p) :=
      evaluateAlternatingWord_chartPoint (representativeWord g) p
    _ = chartPoint (g • p) := rfl

/-- The coordinate equivalence intertwines the finite chart action with
Mathlib's induced projective action. -/
theorem projectiveChart_smul (g : IcosahedralGroup) (p : ProjectiveAxis) :
    projectiveChart (g • p) = g • projectiveChart p := by
  have hp : chartPoint (projectiveChart p) = p := by
    simpa only [projectiveChart_symm_apply] using projectiveChart.symm_apply_apply p
  calc
    projectiveChart (g • p) =
        projectiveChart (g • chartPoint (projectiveChart p)) := by rw [hp]
    _ = projectiveChart (chartPoint (g • projectiveChart p)) := by
      rw [chartPoint_smul]
    _ = g • projectiveChart p := projectiveChart_chartPoint _

/-- The source quadratic form `q(v) = vᵀHv`, evaluated on the normalized
coordinate supplied by the proved projective equivalence. -/
noncomputable def quadraticForm (p : ProjectiveAxis) : F5 :=
  chartQuadraticForm (projectiveChart p)

/-- The six isotropic, fivefold axes in the actual projective plane. -/
noncomputable def fivefoldAxes : Finset ProjectiveAxis :=
  chartFivefoldAxes.map projectiveChart.symm.toEmbedding

/-- The ten nonsquare, threefold axes in the actual projective plane. -/
noncomputable def threefoldAxes : Finset ProjectiveAxis :=
  chartThreefoldAxes.map projectiveChart.symm.toEmbedding

/-- The fifteen nonzero-square, twofold axes in the actual projective plane. -/
noncomputable def twofoldAxes : Finset ProjectiveAxis :=
  chartTwofoldAxes.map projectiveChart.symm.toEmbedding

private theorem mem_mappedAxes (p : ProjectiveAxis) (s : Finset AxisChart) :
    p ∈ s.map projectiveChart.symm.toEmbedding ↔ projectiveChart p ∈ s := by
  constructor
  · rw [Finset.mem_map]
    rintro ⟨q, hq, hqp⟩
    subst p
    rw [projectiveChart_symm_embedding_apply]
    exact hq
  · intro hp
    rw [Finset.mem_map]
    exact ⟨projectiveChart p, hp, projectiveChart.symm_apply_apply p⟩

theorem mem_fivefoldAxes_iff (p : ProjectiveAxis) :
    p ∈ fivefoldAxes ↔ quadraticForm p = 0 := by
  rw [fivefoldAxes, mem_mappedAxes]
  simp [chartFivefoldAxes, quadraticForm]

theorem mem_threefoldAxes_iff (p : ProjectiveAxis) :
    p ∈ threefoldAxes ↔ quadraticForm p = 2 ∨ quadraticForm p = 3 := by
  rw [threefoldAxes, mem_mappedAxes]
  simp [chartThreefoldAxes, quadraticForm]

theorem mem_twofoldAxes_iff (p : ProjectiveAxis) :
    p ∈ twofoldAxes ↔ quadraticForm p = 1 ∨ quadraticForm p = 4 := by
  rw [twofoldAxes, mem_mappedAxes]
  simp [chartTwofoldAxes, quadraticForm]

/-- The subtype of actual projective axes in the concrete isotropic class `𝒜₅`. -/
noncomputable abbrev FivefoldAxis := fivefoldAxes

/-- The finite orbit in the actual projective plane under the induced action. -/
noncomputable def axisOrbit (p : ProjectiveAxis) : Finset ProjectiveAxis :=
  Finset.univ.image fun g : IcosahedralGroup => g • p

private theorem axisOrbit_eq_map (p : ProjectiveAxis) :
    axisOrbit p = (chartAxisOrbit (projectiveChart p)).map
      projectiveChart.symm.toEmbedding := by
  classical
  ext q
  constructor
  · simp only [axisOrbit, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨g, rfl⟩
    rw [Finset.mem_map]
    refine ⟨g • projectiveChart p, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
    · apply projectiveChart.injective
      rw [projectiveChart_smul, projectiveChart_symm_embedding_apply]
  · rw [Finset.mem_map]
    rintro ⟨r, hr, rfl⟩
    rw [chartAxisOrbit, Finset.mem_image] at hr
    obtain ⟨g, _, rfl⟩ := hr
    rw [axisOrbit, Finset.mem_image]
    refine ⟨g, Finset.mem_univ g, ?_⟩
    apply projectiveChart.injective
    rw [projectiveChart_smul, projectiveChart_symm_embedding_apply]

private theorem stabilizer_eq_chart (p : ProjectiveAxis) :
    MulAction.stabilizer IcosahedralGroup p =
      MulAction.stabilizer IcosahedralGroup (projectiveChart p) := by
  ext g
  change g • p = p ↔ g • projectiveChart p = projectiveChart p
  rw [← projectiveChart_smul]
  exact projectiveChart.injective.eq_iff.symm

private noncomputable def stabilizerEquivChart (p : ProjectiveAxis) :
    MulAction.stabilizer IcosahedralGroup p ≃
      MulAction.stabilizer IcosahedralGroup (projectiveChart p) :=
  { toFun := fun g => ⟨g.1, by
      change g.1 • projectiveChart p = projectiveChart p
      rw [← projectiveChart_smul]
      exact congrArg projectiveChart g.2⟩
    invFun := fun g => ⟨g.1, by
      apply projectiveChart.injective
      rw [projectiveChart_smul]
      exact g.2⟩
    left_inv := by intro g; rfl
    right_inv := by intro g; rfl }

private theorem stabilizer_card_eq_chart (p : ProjectiveAxis) :
    Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
      Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
  Fintype.card_congr (stabilizerEquivChart p)

private noncomputable def toChartFivefoldAxis (p : FivefoldAxis) : ChartFivefoldAxis :=
  ⟨projectiveChart p.1, by
    exact (mem_mappedAxes p.1 chartFivefoldAxes).mp p.2⟩

/-- The five-cycle subgroup, transported along the proved equivariant chart. -/
noncomputable def fiveCycleSubgroup (p : FivefoldAxis) : Subgroup IcosahedralGroup :=
  chartFiveCycleSubgroup (toChartFivefoldAxis p)

noncomputable instance (p : FivefoldAxis) :
    DecidablePred (· ∈ fiveCycleSubgroup p) := Classical.decPred _

theorem mem_fiveCycleSubgroup_iff (p : FivefoldAxis) (g : IcosahedralGroup) :
    g ∈ fiveCycleSubgroup p ↔ g • p.1 = p.1 ∧ g ^ 5 = 1 := by
  change (g • projectiveChart p.1 = projectiveChart p.1 ∧ g ^ 5 = 1) ↔ _
  rw [← projectiveChart_smul]
  constructor <;> rintro ⟨h, h5⟩
  · exact ⟨projectiveChart.injective h, h5⟩
  · exact ⟨congrArg projectiveChart h, h5⟩

/-- Finite icosahedral axis decomposition of the actual projective plane over
`F₅`: the concrete quadratic classes are the three orbits of sizes 6, 10,
and 15, with stabilizer orders 10, 6, and 4. -/
theorem finite_icosahedral_axis_decomposition :
    Disjoint fivefoldAxes threefoldAxes ∧
      Disjoint fivefoldAxes twofoldAxes ∧
      Disjoint threefoldAxes twofoldAxes ∧
      fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes =
        (Finset.univ : Finset (Projectivization F5 Vector)) ∧
      fivefoldAxes.card = 6 ∧
      threefoldAxes.card = 10 ∧
      twofoldAxes.card = 15 ∧
      (∀ p ∈ fivefoldAxes, axisOrbit p = fivefoldAxes) ∧
      (∀ p ∈ threefoldAxes, axisOrbit p = threefoldAxes) ∧
      (∀ p ∈ twofoldAxes, axisOrbit p = twofoldAxes) ∧
      (∀ p ∈ fivefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 10) ∧
      (∀ p ∈ threefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 6) ∧
      (∀ p ∈ twofoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 4) ∧
      (∀ p : FivefoldAxis,
        Fintype.card (fiveCycleSubgroup p) = 5 ∧
          IsCyclic (fiveCycleSubgroup p) ∧
          MulAction.stabilizer IcosahedralGroup p.1 =
            Subgroup.normalizer (fiveCycleSubgroup p : Set IcosahedralGroup)) := by
  classical
  rcases chartFiniteAxisCertificate with
    ⟨h53Inter, h52Inter, h32Inter, hunion, hcard5, hcard3, hcard2,
      horbit5, horbit3, horbit2, hstab5, hstab3, hstab2⟩
  have h53Chart : Disjoint chartFivefoldAxes chartThreefoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h53Inter
  have h52Chart : Disjoint chartFivefoldAxes chartTwofoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h52Inter
  have h32Chart : Disjoint chartThreefoldAxes chartTwofoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h32Inter
  have h53 : Disjoint fivefoldAxes threefoldAxes := by
    rw [Finset.disjoint_left]
    intro p hp5 hp3
    exact Finset.disjoint_left.mp h53Chart
      ((mem_mappedAxes p chartFivefoldAxes).mp hp5)
      ((mem_mappedAxes p chartThreefoldAxes).mp hp3)
  have h52 : Disjoint fivefoldAxes twofoldAxes := by
    rw [Finset.disjoint_left]
    intro p hp5 hp2
    exact Finset.disjoint_left.mp h52Chart
      ((mem_mappedAxes p chartFivefoldAxes).mp hp5)
      ((mem_mappedAxes p chartTwofoldAxes).mp hp2)
  have h32 : Disjoint threefoldAxes twofoldAxes := by
    rw [Finset.disjoint_left]
    intro p hp3 hp2
    exact Finset.disjoint_left.mp h32Chart
      ((mem_mappedAxes p chartThreefoldAxes).mp hp3)
      ((mem_mappedAxes p chartTwofoldAxes).mp hp2)
  have hactualUnion : fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes = Finset.univ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rw [fivefoldAxes, threefoldAxes, twofoldAxes,
      mem_mappedAxes, mem_mappedAxes, mem_mappedAxes]
    have hp : projectiveChart p ∈
        chartFivefoldAxes ∪ chartThreefoldAxes ∪ chartTwofoldAxes := by
      rw [hunion]
      exact Finset.mem_univ _
    simpa only [Finset.mem_union] using hp
  refine ⟨h53, h52, h32, hactualUnion, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [fivefoldAxes] using hcard5
  · simpa [threefoldAxes] using hcard3
  · simpa [twofoldAxes] using hcard2
  · intro p hp
    rw [axisOrbit_eq_map, fivefoldAxes, horbit5 (projectiveChart p)
      ((mem_mappedAxes p chartFivefoldAxes).mp hp)]
  · intro p hp
    rw [axisOrbit_eq_map, threefoldAxes, horbit3 (projectiveChart p)
      ((mem_mappedAxes p chartThreefoldAxes).mp hp)]
  · intro p hp
    rw [axisOrbit_eq_map, twofoldAxes, horbit2 (projectiveChart p)
      ((mem_mappedAxes p chartTwofoldAxes).mp hp)]
  · intro p hp
    calc
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
          Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
        stabilizer_card_eq_chart p
      _ = 10 := hstab5 (projectiveChart p)
        ((mem_mappedAxes p chartFivefoldAxes).mp hp)
  · intro p hp
    calc
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
          Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
        stabilizer_card_eq_chart p
      _ = 6 := hstab3 (projectiveChart p)
        ((mem_mappedAxes p chartThreefoldAxes).mp hp)
  · intro p hp
    calc
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
          Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
        stabilizer_card_eq_chart p
      _ = 4 := hstab2 (projectiveChart p)
        ((mem_mappedAxes p chartTwofoldAxes).mp hp)
  · intro p
    obtain ⟨hcycleCard, hnormalizerMem⟩ :=
      chartFivefoldNormalizerCertificate (toChartFivefoldAxis p)
    have hNatCard : Nat.card (fiveCycleSubgroup p) = 5 := by
      simpa [Nat.card_eq_fintype_card, fiveCycleSubgroup] using hcycleCard
    refine ⟨?_, isCyclic_of_prime_card hNatCard, ?_⟩
    · calc
        Fintype.card (fiveCycleSubgroup p) = Nat.card (fiveCycleSubgroup p) :=
          Nat.card_eq_fintype_card.symm
        _ = 5 := hNatCard
    ext g
    rw [stabilizer_eq_chart]
    exact hnormalizerMem g

#print axioms icosahedralGroup_card
#print axioms finite_icosahedral_axis_decomposition

section FidelityProbes

/-- Quotient discrimination probe: the first two coordinate lines remain
distinct in Mathlib's projectivization. -/
theorem projective_coordinate_axes_ne :
    Projectivization.mk F5 (![1, 0, 0] : Vector) (by decide) ≠
      Projectivization.mk F5 (![0, 1, 0] : Vector) (by decide) := by
  intro h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrFun ha 0
  simpa [Pi.smul_apply] using h0

/-- Reverse probe: the public theorem forces every isotropic axis to lie in the
claimed partition and to have stabilizer order ten. -/
example (p : ProjectiveAxis) (hp : p ∈ fivefoldAxes) :
    p ∈ fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes ∧
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 10 := by
  rcases finite_icosahedral_axis_decomposition with
    ⟨_, _, _, _, _, _, _, _, _, _, hstab5, _, _, _⟩
  exact ⟨by simp [hp], hstab5 p hp⟩

/-- Trivialization probe: a one-element action cannot have the source's three
different nonzero stabilizer orders. -/
example {X : Type*} [Fintype X] [DecidableEq X] [MulAction Unit X] :
    ¬ ((∃ x : X, Fintype.card (MulAction.stabilizer Unit x) = 10) ∧
       (∃ x : X, Fintype.card (MulAction.stabilizer Unit x) = 6) ∧
       (∃ x : X, Fintype.card (MulAction.stabilizer Unit x) = 4)) := by
  rintro ⟨⟨x, hx⟩, _⟩
  let e : MulAction.stabilizer Unit x ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨(), by exact one_smul Unit x⟩
      left_inv := by
        intro g
        apply Subtype.ext
        cases g.1
        rfl
      right_inv := by intro u; cases u; rfl }
  have hcard : Fintype.card (MulAction.stabilizer Unit x) = 1 := by
    calc
      Fintype.card (MulAction.stabilizer Unit x) = Fintype.card Unit :=
        Fintype.card_congr e
      _ = 1 := Fintype.card_unit
  omega

end FidelityProbes

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
