import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift
import Mathlib.Order.ULift

/-! The diagonal product is the readout in the coefficient law. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MvPolynomial
open scoped BigOperators

universe u v w

noncomputable section

private abbrev Params := Σ ι : Type u, Σ R : Type w, Σ _ : Fintype ι, CommRing R

private abbrev signature : Signature where
  Params := Params.{u, w}
  State p := p.1 → p.1 → p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u, w} :=
  realize signature (fun _ p a =>
    letI := p.2.2.1
    letI := p.2.2.2
    ∏ i, a i i) Empty.elim

private def rejected : Realization signature.{u, w} :=
  realize signature (fun _ p _ =>
    letI := p.2.2.2
    0) Empty.elim

private abbrev arena : Arena where
  signature := signature.{u, w}
  Law r := ∀ {ι : Type u} {κ : Type v} {R : Type w}
    [f : Fintype ι] [DecidableEq ι] [LinearOrder κ] [c : CommRing R]
    (label : ι → ι → κ) (a : ι → ι → R)
    (_ : ∀ i j, i ≠ j → a i j ≠ 0 → label i i < label i j ∨ label j j < label i j),
    let M : Matrix ι ι (MvPolynomial κ R) :=
      Matrix.of fun i j => monomial (Finsupp.single (label i j) 1) (a i j)
    (M.det.coeff (∑ i, Finsupp.single (label i i) 1) = r.readout () ⟨ι, R, f, c⟩ a) ∧
      (IsDomain R → (∀ i, a i i ≠ 0) → M.det ≠ 0)

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  let label : ULift.{u} (Fin 1) → ULift.{u} (Fin 1) → ULift.{v} (Fin 1) :=
    fun _ _ => 0
  let a : ULift.{u} (Fin 1) → ULift.{u} (Fin 1) → ULift.{w} ℤ := fun _ _ => 1
  have hp : ∀ i j, i ≠ j → a i j ≠ 0 → label i i < label i j ∨ label j j < label i j :=
    fun i j hij _ => (hij (Subsingleton.elim i j)).elim
  have ha := (coeff_det_of_diagonal_priority label a hp).1
  have hb := (h label a hp).1
  have hz := ha.symm.trans hb
  exact one_ne_zero (by simpa [a, rejected, realize] using hz : (1 : ULift.{w} ℤ) = 0)

def source_registration :
    Registration arena.{u, v, w} (type_of% (@coeff_det_of_diagonal_priority.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coeff_det_of_diagonal_priority.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{w} ℤ, inferInstance, inferInstance⟩,
      (fun _ _ => 1), (fun _ _ => 0), ?_⟩
    simpa [actual, realize] using (one_ne_zero : (1 : ULift.{w} ℤ) ≠ 0)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coeff_det_of_diagonal_priority.{u, v, w}) (Realization signature.{u, w}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant.coeff_det_of_diagonal_priority.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant
