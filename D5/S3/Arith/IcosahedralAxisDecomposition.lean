/- GID: D5/S3/Arith/IcosahedralAxisDecomposition
   generality: I
   mirror-B: D5/B/S3/Arith/IcosahedralAxisDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: P2(F5) splits 6/10/15; A5 axes match, including orders 0 and 1. -/

/- Library-search audit trail (2026-08-25):
* Six-way repository searches by theorem vocabulary, Mathlib vocabulary, digest phrases, nearby
  modules, generalized orbit shapes, and alternate axis terminology found no existing theorem
  identifying the 31 projective points with the 6, 10, and 15 cyclic-axis classes.
* Loogle's projectivization equality query returned `Projectivization.mk_eq_mk_iff'`; its
  cardinality query returned `Fintype.card_congr`; and its orbit-stabilizer query returned
  `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. The first two are used below. The
  last did not directly apply to the concrete canonical-generator encoding used for computation.
* Local Mathlib searches also found `Projectivization.ind`, `Equiv.sigmaFiberEquiv`, and
  `Fintype.equivOfCardEq`. No library theorem supplies this concrete quadratic classification or
  the three alternating-group normalizer computations, so those finite statements use `decide`.
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.FinCases

namespace D5.S3.Arith.IcosahedralAxisDecomposition

open scoped LinearAlgebra.Projectivization Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The three-dimensional discriminant boundary over `ZMod 5`. -/
abbrev BoundaryVector := Fin 3 → ZMod 5

/-- Normalized representatives `[1,y,z]`, `[0,1,z]`, and `[0,0,1]` for `P²(F₅)`. -/
def FiniteProjectivePlane :=
  (ZMod 5 × ZMod 5) ⊕ (ZMod 5 ⊕ Unit)

instance finiteProjectivePlaneFintype : Fintype FiniteProjectivePlane :=
  inferInstanceAs (Fintype ((ZMod 5 × ZMod 5) ⊕ (ZMod 5 ⊕ Unit)))

instance finiteProjectivePlaneDecidableEq : DecidableEq FiniteProjectivePlane :=
  inferInstanceAs (DecidableEq ((ZMod 5 × ZMod 5) ⊕ (ZMod 5 ⊕ Unit)))

/-- The nonzero vector represented by a normalized projective point. -/
def projectiveVector : FiniteProjectivePlane → BoundaryVector
  | .inl (y, z) => ![1, y, z]
  | .inr (.inl z) => ![0, 1, z]
  | .inr (.inr _) => ![0, 0, 1]

private theorem projectiveVector_ne_zero (p : FiniteProjectivePlane) :
    projectiveVector p ≠ 0 := by
  cases p with
  | inl yz =>
      intro h
      have h0 := congrFun h 0
      norm_num [projectiveVector] at h0
  | inr rest =>
      cases rest with
      | inl z =>
          intro h
          have h1 := congrFun h 1
          norm_num [projectiveVector] at h1
      | inr u =>
          intro h
          have h2 := congrFun h 2
          apply (one_ne_zero : (1 : ZMod 5) ≠ 0)
          change (1 : ZMod 5) = 0 at h2
          exact h2

/-- The normalized representative mapped into Mathlib's projectivization. -/
def toProjectivization (p : FiniteProjectivePlane) :
    Projectivization (ZMod 5) BoundaryVector :=
  Projectivization.mk (ZMod 5) (projectiveVector p) (projectiveVector_ne_zero p)

private theorem toProjectivization_injective : Function.Injective toProjectivization := by
  intro p q hpq
  rw [toProjectivization, toProjectivization,
    Projectivization.mk_eq_mk_iff'] at hpq
  rcases hpq with ⟨a, ha⟩
  rcases p with yz | rest
  · rcases yz with ⟨y, z⟩
    rcases q with yz' | rest'
    · rcases yz' with ⟨y', z'⟩
      have h0 := congrFun ha 0
      have h1 := congrFun ha 1
      have h2 := congrFun ha 2
      norm_num [projectiveVector] at h0
      simp [projectiveVector, h0] at h1 h2
      simp [h1, h2]
      rfl
    · rcases rest' with z' | u
      · have h0 := congrFun ha 0
        norm_num [projectiveVector] at h0
      · have h0 := congrFun ha 0
        norm_num [projectiveVector] at h0
  · rcases rest with z | u
    · rcases q with yz' | rest'
      · have h0 := congrFun ha 0
        have h1 := congrFun ha 1
        norm_num [projectiveVector] at h0
        simp [projectiveVector, h0] at h1
      · rcases rest' with z' | u'
        · have h1 := congrFun ha 1
          have h2 := congrFun ha 2
          norm_num [projectiveVector] at h1
          simp [projectiveVector, h1] at h2
          simp [h2]
          rfl
        · have h1 := congrFun ha 1
          norm_num [projectiveVector] at h1
    · rcases q with yz' | rest'
      · have h0 := congrFun ha 0
        have h2 := congrFun ha 2
        norm_num [projectiveVector] at h0
        simp [projectiveVector, h0] at h2
      · rcases rest' with z' | u'
        · have h1 := congrFun ha 1
          have h2 := congrFun ha 2
          norm_num [projectiveVector] at h1
          simp [projectiveVector, h1] at h2
        · rcases u with ⟨⟩
          rcases u' with ⟨⟩
          rfl

private theorem toProjectivization_surjective : Function.Surjective toProjectivization := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
      by_cases h0 : v 0 = 0
      · by_cases h1 : v 1 = 0
        · have h2 : v 2 ≠ 0 := by
            intro h2
            apply hv
            funext i
            fin_cases i <;> simp [h0, h1, h2]
          refine ⟨.inr (.inr ()), ?_⟩
          unfold toProjectivization
          rw [Projectivization.mk_eq_mk_iff']
          refine ⟨(v 2)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [projectiveVector, h0, h1, h2]
        · refine ⟨.inr (.inl (v 2 / v 1)), ?_⟩
          unfold toProjectivization
          rw [Projectivization.mk_eq_mk_iff']
          refine ⟨(v 1)⁻¹, ?_⟩
          funext i
          fin_cases i <;>
            simp [projectiveVector, h0, h1, div_eq_mul_inv, mul_comm]
      · refine ⟨.inl (v 1 / v 0, v 2 / v 0), ?_⟩
        unfold toProjectivization
        rw [Projectivization.mk_eq_mk_iff']
        refine ⟨(v 0)⁻¹, ?_⟩
        funext i
        fin_cases i <;> simp [projectiveVector, h0, div_eq_mul_inv, mul_comm]
        all_goals ac_rfl

/-- The normalized model is exactly Mathlib's projective plane over `ZMod 5`. -/
noncomputable def finiteProjectivePlaneEquiv :
    FiniteProjectivePlane ≃ Projectivization (ZMod 5) BoundaryVector :=
  Equiv.ofBijective toProjectivization
    ⟨toProjectivization_injective, toProjectivization_surjective⟩

noncomputable instance projectivizationFintype :
    Fintype (Projectivization (ZMod 5) BoundaryVector) :=
  Fintype.ofEquiv FiniteProjectivePlane finiteProjectivePlaneEquiv

/-- The source matrix of the invariant quadratic form on the discriminant boundary. -/
def projectiveQuadraticMatrix : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  !![2, 1, 1; 1, 2, 1; 1, 1, 2]

/-- The invariant quadratic value on a normalized projective representative. -/
def projectiveQuadratic (p : FiniteProjectivePlane) : ZMod 5 :=
  dotProduct (projectiveVector p)
    (Matrix.mulVec projectiveQuadraticMatrix (projectiveVector p))

/-- The three projective axis kinds: isotropic, nonsquare, and square. -/
inductive AxisKind where
  | fivefold
  | threefold
  | twofold
  deriving DecidableEq

/-- Classification by quadratic value, invariant under rescaling a projective vector. -/
def projectiveAxisKind (p : FiniteProjectivePlane) : AxisKind :=
  if projectiveQuadratic p = 0 then .fivefold
  else if projectiveQuadratic p = 2 ∨ projectiveQuadratic p = 3 then .threefold
  else .twofold

/-- The finite set of projective points of a specified axis kind. -/
def projectiveAxisPointSet (kind : AxisKind) : Finset FiniteProjectivePlane :=
  Finset.univ.filter fun p => projectiveAxisKind p = kind

/-- The subtype of projective points of a specified axis kind. -/
abbrev ProjectiveAxisPoints (kind : AxisKind) :=
  {p : FiniteProjectivePlane // projectiveAxisKind p = kind}

/-- The six isotropic projective directions. -/
abbrev FivefoldProjectivePoints := ProjectiveAxisPoints .fivefold

/-- The ten nonsquare projective directions. -/
abbrev ThreefoldProjectivePoints := ProjectiveAxisPoints .threefold

/-- The fifteen square projective directions. -/
abbrev TwofoldProjectivePoints := ProjectiveAxisPoints .twofold

/-- The projective plane is the total space of the three classification fibers. -/
def projectiveAxisPartitionEquiv :
    (Σ kind, ProjectiveAxisPoints kind) ≃ FiniteProjectivePlane :=
  Equiv.sigmaFiberEquiv projectiveAxisKind

/- **The projective plane has 31 points.** This identifies the explicit normalized model with
Mathlib's quotient-based projectivization and records the cardinality of both presentations. -/
theorem finite_projective_plane_cardinality :
    Fintype.card (Projectivization (ZMod 5) BoundaryVector) = 31 ∧
      Fintype.card FiniteProjectivePlane = 31 := by
  constructor
  · rw [← Fintype.card_congr finiteProjectivePlaneEquiv]
    decide
  · decide

#print axioms finite_projective_plane_cardinality

/- **Disjoint axis partition.** Every projective point has exactly one of the three kinds. -/
theorem finite_projective_axis_partition :
    projectiveAxisPointSet .fivefold ∪ projectiveAxisPointSet .threefold ∪
        projectiveAxisPointSet .twofold = Finset.univ ∧
      Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .threefold) ∧
      Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .twofold) ∧
      Disjoint (projectiveAxisPointSet .threefold) (projectiveAxisPointSet .twofold) := by
  decide

#print axioms finite_projective_axis_partition

/- **Projective axis counts.** The isotropic, nonsquare, and square fibers have sizes 6, 10,
and 15. -/
theorem finite_projective_axis_cardinalities :
    Fintype.card FivefoldProjectivePoints = 6 ∧
      Fintype.card ThreefoldProjectivePoints = 10 ∧
      Fintype.card TwofoldProjectivePoints = 15 := by
  decide

#print axioms finite_projective_axis_cardinalities

/-- The abstract rotational icosahedral group in its standard `A₅` presentation. -/
abbrev IcosahedralRotationGroup := alternatingGroup (Fin 5)

/-- The first `p` powers of a proposed cyclic-axis generator. -/
def cyclicAxis (p : Nat) (g : IcosahedralRotationGroup) :
    Finset IcosahedralRotationGroup :=
  (Finset.range p).image fun k => g ^ k

/-- The concrete generator condition used at the fixed orders 2, 3, and 5. -/
def axisGeneratorCondition (p : Nat) (g : IcosahedralRotationGroup) : Prop :=
  g ≠ 1 ∧ g ^ p = 1

private instance axisGeneratorConditionDecidable (p : Nat) (g : IcosahedralRotationGroup) :
    Decidable (axisGeneratorCondition p g) :=
  inferInstanceAs (Decidable (g ≠ 1 ∧ g ^ p = 1))

/-- A base-five code that totally orders the concrete permutations of five letters. -/
def permutationCode (g : IcosahedralRotationGroup) : Nat :=
  ∑ i : Fin 5, (g.1 i).val * 5 ^ i.val

/-- A generator is canonical when its code is minimal among its nontrivial listed powers. -/
def IsCanonicalCyclicAxis (p : Nat) (g : IcosahedralRotationGroup) : Prop :=
  axisGeneratorCondition p g ∧
    ∀ k ∈ Finset.range p, 0 < k → permutationCode g ≤ permutationCode (g ^ k)

private instance isCanonicalCyclicAxisDecidable (p : Nat) (g : IcosahedralRotationGroup) :
    Decidable (IsCanonicalCyclicAxis p g) :=
  inferInstanceAs (Decidable (axisGeneratorCondition p g ∧
    ∀ k ∈ Finset.range p, 0 < k → permutationCode g ≤ permutationCode (g ^ k)))

/-- Canonically represented cyclic axes of the requested order parameter. -/
abbrev CyclicAxes (p : Nat) :=
  {g : IcosahedralRotationGroup // IsCanonicalCyclicAxis p g}

/-- Membership in the finite list of powers defining a cyclic axis. -/
def axisContains (p : Nat) (g x : IcosahedralRotationGroup) : Prop :=
  x ∈ cyclicAxis p g

private instance axisContainsDecidable (p : Nat) (g x : IcosahedralRotationGroup) :
    Decidable (axisContains p g x) :=
  inferInstanceAs (Decidable (x ∈ cyclicAxis p g))

/-- Two represented axes are conjugate when a conjugate generator lies on the second axis. -/
def axesAreConjugate (p : Nat) (g h : IcosahedralRotationGroup) : Prop :=
  ∃ x : IcosahedralRotationGroup, axisContains p h (x * g * x⁻¹)

private instance axesAreConjugateDecidable
    (p : Nat) (g h : IcosahedralRotationGroup) : Decidable (axesAreConjugate p g h) :=
  inferInstanceAs (Decidable
    (∃ x : IcosahedralRotationGroup, axisContains p h (x * g * x⁻¹)))

/-- The normalizer, encoded as the finite set of elements preserving a represented cyclic axis. -/
def cyclicAxisNormalizer (p : Nat) (g : IcosahedralRotationGroup) :
    Finset IcosahedralRotationGroup :=
  Finset.univ.filter fun x => axisContains p g (x * g * x⁻¹)

/-- The centralizer of a concrete rotation, encoded as a finite set. -/
def elementCentralizer (x : IcosahedralRotationGroup) :
    Finset IcosahedralRotationGroup :=
  Finset.univ.filter fun g => g * x = x * g

/-- Fivefold cyclic axes in `A₅`. -/
abbrev FivefoldAxes := CyclicAxes 5

/-- Threefold cyclic axes in `A₅`. -/
abbrev ThreefoldAxes := CyclicAxes 3

/-- Twofold cyclic axes in `A₅`. -/
abbrev TwofoldAxes := CyclicAxes 2

private theorem fivefold_axis_card : Fintype.card FivefoldAxes = 6 := by
  set_option maxRecDepth 100000 in
    decide

private theorem threefold_axis_card : Fintype.card ThreefoldAxes = 10 := by
  set_option maxRecDepth 100000 in
    decide

private theorem twofold_axis_card : Fintype.card TwofoldAxes = 15 := by
  set_option maxRecDepth 100000 in
    decide

private theorem fivefold_axes_conjugate :
    ∀ g h : FivefoldAxes, axesAreConjugate 5 g h := by
  set_option maxRecDepth 100000 in
    decide

private theorem threefold_axes_conjugate :
    ∀ g h : ThreefoldAxes, axesAreConjugate 3 g h := by
  set_option maxRecDepth 100000 in
    decide

private theorem twofold_axes_conjugate :
    ∀ g h : TwofoldAxes, axesAreConjugate 2 g h := by
  set_option maxRecDepth 100000 in
    decide

/- **The three cyclic-axis families are single conjugacy orbits of sizes 6, 10, and 15.** -/
theorem icosahedral_axis_orbits :
    Fintype.card FivefoldAxes = 6 ∧
      Fintype.card ThreefoldAxes = 10 ∧
      Fintype.card TwofoldAxes = 15 ∧
      (∀ g h : FivefoldAxes, axesAreConjugate 5 g h) ∧
      (∀ g h : ThreefoldAxes, axesAreConjugate 3 g h) ∧
      (∀ g h : TwofoldAxes, axesAreConjugate 2 g h) := by
  exact ⟨fivefold_axis_card, threefold_axis_card, twofold_axis_card,
    fivefold_axes_conjugate, threefold_axes_conjugate, twofold_axes_conjugate⟩

#print axioms icosahedral_axis_orbits

/- **Axis stabilizers.** The normalizer orders are 10, 6, and 4; at order two the normalizer
equals the generator centralizer. -/
private theorem fivefold_normalizer_card :
    ∀ g : FivefoldAxes, (cyclicAxisNormalizer 5 g).card = 10 := by
  set_option maxRecDepth 100000 in
    decide

private theorem threefold_normalizer_card :
    ∀ g : ThreefoldAxes, (cyclicAxisNormalizer 3 g).card = 6 := by
  set_option maxRecDepth 100000 in
    decide

private theorem twofold_normalizer_card :
    ∀ g : TwofoldAxes, (cyclicAxisNormalizer 2 g).card = 4 := by
  set_option maxRecDepth 100000 in
    decide

private theorem twofold_normalizer_eq_centralizer :
    ∀ g : TwofoldAxes, cyclicAxisNormalizer 2 g = elementCentralizer g := by
  set_option maxRecDepth 100000 in
    decide

theorem icosahedral_axis_stabilizer_orders :
    (∀ g : FivefoldAxes, (cyclicAxisNormalizer 5 g).card = 10) ∧
      (∀ g : ThreefoldAxes, (cyclicAxisNormalizer 3 g).card = 6) ∧
      (∀ g : TwofoldAxes, (cyclicAxisNormalizer 2 g).card = 4) ∧
      (∀ g : TwofoldAxes, cyclicAxisNormalizer 2 g = elementCentralizer g) := by
  exact ⟨fivefold_normalizer_card, threefold_normalizer_card,
    twofold_normalizer_card, twofold_normalizer_eq_centralizer⟩

#print axioms icosahedral_axis_stabilizer_orders

/-- A noncanonical finite equivalence between isotropic points and fivefold axes. -/
noncomputable def fivefoldProjectiveAxisEquiv :
    FivefoldProjectivePoints ≃ FivefoldAxes :=
  Fintype.equivOfCardEq
    (finite_projective_axis_cardinalities.1.trans fivefold_axis_card.symm)

/-- A noncanonical finite equivalence between nonsquare points and threefold axes. -/
noncomputable def threefoldProjectiveAxisEquiv :
    ThreefoldProjectivePoints ≃ ThreefoldAxes :=
  Fintype.equivOfCardEq
    (finite_projective_axis_cardinalities.2.1.trans threefold_axis_card.symm)

/-- A noncanonical finite equivalence between square points and twofold axes. -/
noncomputable def twofoldProjectiveAxisEquiv :
    TwofoldProjectivePoints ≃ TwofoldAxes :=
  Fintype.equivOfCardEq
    (finite_projective_axis_cardinalities.2.2.trans twofold_axis_card.symm)

/- **Finite icosahedral axis decomposition.** Each quadratic fiber is in bijection with the
corresponding cyclic-axis orbit. These are finite-cardinality equivalences, not a claimed
geometric or equivariant identification with the real or complex icosahedron. -/
theorem finite_icosahedral_axis_decomposition :
    Function.Bijective fivefoldProjectiveAxisEquiv ∧
      Function.Bijective threefoldProjectiveAxisEquiv ∧
      Function.Bijective twofoldProjectiveAxisEquiv := by
  exact ⟨fivefoldProjectiveAxisEquiv.bijective,
    threefoldProjectiveAxisEquiv.bijective,
    twofoldProjectiveAxisEquiv.bijective⟩

#print axioms finite_icosahedral_axis_decomposition

/- **Degenerate-order audit.** At parameter zero every nonidentity element is selected, whereas
at parameter one no generator satisfies the defining condition. -/
theorem cyclic_axes_degenerate_orders :
    Fintype.card (CyclicAxes 0) = 59 ∧ Fintype.card (CyclicAxes 1) = 0 := by
  constructor <;> set_option maxRecDepth 100000 in decide

#print axioms cyclic_axes_degenerate_orders

end D5.S3.Arith.IcosahedralAxisDecomposition
