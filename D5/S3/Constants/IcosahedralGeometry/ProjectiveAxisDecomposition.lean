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
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

abbrev F5 := ZMod 5
abbrev Vector := Fin 3 → F5

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

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

/-- A finite coordinate chart for the 31 points of `P²(F₅)`. -/
abbrev ProjectiveAxis := Fin 31

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
def axisVector : ProjectiveAxis → Vector :=
  ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3],
    ![0, 1, 4], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 0, 3],
    ![1, 0, 4], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3],
    ![1, 1, 4], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3],
    ![1, 2, 4], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3],
    ![1, 3, 4], ![1, 4, 0], ![1, 4, 1], ![1, 4, 2], ![1, 4, 3],
    ![1, 4, 4]]

private def axisIndex (v : Vector) : ProjectiveAxis :=
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

private theorem axisIndex_axisVector (p : ProjectiveAxis) :
    axisIndex (axisVector p) = p := by
  fin_cases p <;> rfl

private theorem axisVector_axisIndex (v : NormalizedVector) :
    axisVector (axisIndex v.1) = v.1 := by
  fin_cases v <;> ext i <;> fin_cases i <;> rfl

/-- The chart lists every normalized projective representative exactly once. -/
theorem axisVector_unique_complete :
    ∀ v : NormalizedVector, ∃! p : ProjectiveAxis, axisVector p = v.1 := by
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
def projectiveA : Equiv.Perm ProjectiveAxis :=
  { toFun := ![6, 0, 7, 9, 8, 10, 1, 11, 21, 16, 26, 2, 12, 24, 18,
      30, 3, 13, 22, 20, 29, 4, 14, 25, 17, 28, 5, 15, 23, 19, 27]
    invFun := ![1, 6, 11, 16, 21, 26, 0, 2, 4, 3, 5, 7, 12, 17, 22,
      27, 9, 24, 14, 29, 19, 8, 18, 28, 13, 23, 10, 30, 25, 20, 15]
    left_inv := by decide
    right_inv := by decide }

/-- The projective permutation induced by the source matrix `B`. -/
def projectiveB : Equiv.Perm ProjectiveAxis :=
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

private def evaluateLetter : Fin 4 → Equiv.Perm ProjectiveAxis :=
  ![projectiveA, projectiveA⁻¹, projectiveB, projectiveB⁻¹]

private def evaluateWord (word : List (Fin 4)) : Equiv.Perm ProjectiveAxis :=
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

private def actionPermutation (g : IcosahedralGroup) : Equiv.Perm ProjectiveAxis :=
  evaluateWord (representativeWord g)

private theorem actionPermutation_one : actionPermutation 1 = 1 := by
  decide

set_option maxHeartbeats 4000000 in
-- This certificate checks all products in the explicit 60-element action.
set_option maxRecDepth 100000 in
private theorem actionPermutation_mul :
    ∀ g h : IcosahedralGroup,
      actionPermutation (g * h) = actionPermutation g * actionPermutation h := by
  decide

/-- The standard `A₅` generators act by the two matrices displayed in the source. -/
theorem source_generator_actions :
    actionPermutation alternatingA = projectiveA ∧
      actionPermutation alternatingB = projectiveB := by
  decide

instance : MulAction IcosahedralGroup ProjectiveAxis where
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

/-- The explicit matrix of the invariant quadratic form from the source. -/
def formMatrix : Matrix (Fin 3) (Fin 3) F5 :=
  ![![2, 1, 1], ![1, 2, 1], ![1, 1, 2]]

/-- The source quadratic form `q(v) = vᵀHv`, evaluated on a projective
representative. Its square class is independent of the representative. -/
def quadraticForm (p : ProjectiveAxis) : F5 :=
  dotProduct (axisVector p) (formMatrix.mulVec (axisVector p))

/-- The six isotropic, fivefold axes. -/
def fivefoldAxes : Finset ProjectiveAxis :=
  Finset.univ.filter fun p => quadraticForm p = 0

/-- The ten nonsquare, threefold axes. -/
def threefoldAxes : Finset ProjectiveAxis :=
  Finset.univ.filter fun p => quadraticForm p = 2 ∨ quadraticForm p = 3

/-- The fifteen nonzero-square, twofold axes. -/
def twofoldAxes : Finset ProjectiveAxis :=
  Finset.univ.filter fun p => quadraticForm p = 1 ∨ quadraticForm p = 4

/-- The subtype of axes in the concrete isotropic class `𝒜₅`. -/
abbrev FivefoldAxis := fivefoldAxes

/-- The finite orbit of an axis under the concrete matrix group. -/
def axisOrbit (p : ProjectiveAxis) : Finset ProjectiveAxis :=
  Finset.univ.image fun g : IcosahedralGroup => g • p

set_option maxHeartbeats 4000000 in
-- This finite check enumerates the fivefold stabilizers in the 60-element group.
set_option maxRecDepth 100000 in
private theorem fiveCycle_mul_closed :
    ∀ p : FivefoldAxis, ∀ g h : IcosahedralGroup,
      (g • p.1 = p.1 ∧ g ^ 5 = 1) → (h • p.1 = p.1 ∧ h ^ 5 = 1) →
        (g * h) • p.1 = p.1 ∧ (g * h) ^ 5 = 1 := by
  decide

set_option maxHeartbeats 4000000 in
-- This finite check enumerates inverses in the fivefold stabilizers.
set_option maxRecDepth 100000 in
private theorem fiveCycle_inv_closed :
    ∀ p : FivefoldAxis, ∀ g : IcosahedralGroup,
      (g • p.1 = p.1 ∧ g ^ 5 = 1) → g⁻¹ • p.1 = p.1 ∧ g⁻¹ ^ 5 = 1 := by
  decide

/-- Inside a fivefold-axis stabilizer, these are exactly the rotations whose
order divides five. -/
def fiveCycleSubgroup (p : FivefoldAxis) : Subgroup IcosahedralGroup where
  carrier := {g | g • p.1 = p.1 ∧ g ^ 5 = 1}
  one_mem' := by
    constructor
    · exact one_smul IcosahedralGroup p.1
    · exact one_pow 5
  mul_mem' := by
    intro g h hg hh
    exact fiveCycle_mul_closed p g h hg hh
  inv_mem' := by
    intro g hg
    exact fiveCycle_inv_closed p g hg

instance (p : FivefoldAxis) : DecidablePred (· ∈ fiveCycleSubgroup p) := by
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
private theorem finite_axis_certificate :
    fivefoldAxes ∩ threefoldAxes = ∅ ∧
      fivefoldAxes ∩ twofoldAxes = ∅ ∧
      threefoldAxes ∩ twofoldAxes = ∅ ∧
      fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes = Finset.univ ∧
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
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 4) := by
  decide

set_option maxHeartbeats 4000000 in
-- The normalizer certificate enumerates each fivefold axis and group element.
set_option maxRecDepth 100000 in
private theorem fivefold_normalizer_certificate :
    ∀ p : FivefoldAxis,
      Fintype.card (fiveCycleSubgroup p) = 5 ∧
        ∀ g : IcosahedralGroup,
          g ∈ MulAction.stabilizer IcosahedralGroup p.1 ↔
            g ∈ Subgroup.normalizer (fiveCycleSubgroup p : Set IcosahedralGroup) := by
  intro p
  fin_cases p <;> constructor
  all_goals
    first
    | decide
    | intro g
      fin_cases g <;>
        rw [Subgroup.mem_normalizer_iff] <;>
        decide

/-- Finite icosahedral axis decomposition over `F₅`: the concrete quadratic
classes are precisely the three orbits, of sizes 6, 10, and 15, with stabilizer
orders 10, 6, and 4. A fivefold-axis stabilizer is the normalizer of its
cyclic subgroup of order five. -/
theorem finite_icosahedral_axis_decomposition :
    Disjoint fivefoldAxes threefoldAxes ∧
      Disjoint fivefoldAxes twofoldAxes ∧
      Disjoint threefoldAxes twofoldAxes ∧
      fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes = Finset.univ ∧
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
  rcases finite_axis_certificate with
    ⟨h53Inter, h52Inter, h32Inter, hunion, hcard5, hcard3, hcard2,
      horbit5, horbit3, horbit2, hstab5, hstab3, hstab2⟩
  have h53 : Disjoint fivefoldAxes threefoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h53Inter
  have h52 : Disjoint fivefoldAxes twofoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h52Inter
  have h32 : Disjoint threefoldAxes twofoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h32Inter
  refine ⟨h53, h52, h32, hunion, hcard5, hcard3, hcard2,
    horbit5, horbit3, horbit2, hstab5, hstab3, hstab2, ?_⟩
  intro p
  obtain ⟨hcycleCard, hnormalizerMem⟩ := fivefold_normalizer_certificate p
  have hNatCard : Nat.card (fiveCycleSubgroup p) = 5 := by
    simpa [Nat.card_eq_fintype_card] using hcycleCard
  refine ⟨hcycleCard, isCyclic_of_prime_card hNatCard, ?_⟩
  ext g
  exact hnormalizerMem g

#print axioms icosahedralGroup_card
#print axioms finite_icosahedral_axis_decomposition

section FidelityProbes

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
