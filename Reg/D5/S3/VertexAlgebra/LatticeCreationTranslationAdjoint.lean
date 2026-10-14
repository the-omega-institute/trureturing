import D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
open _root_.D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := Sigma fun lattice : LatticeData =>
  Sigma fun _charge : Charge lattice => Sigma fun _degree : ℤ => Oscillator lattice

abbrev Parameters.lattice (parameter : Parameters) : LatticeData := parameter.1

abbrev Parameters.charge (parameter : Parameters) : Charge parameter.lattice := parameter.2.1

abbrev Parameters.degree (parameter : Parameters) : ℤ := parameter.2.2.1

abbrev Parameters.left (parameter : Parameters) : Oscillator parameter.lattice := parameter.2.2.2

def signature : Signature where
  Params := Parameters
  State parameter := Oscillator parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameter right => fockForm parameter.lattice
      (creationCoeff parameter.lattice parameter.charge parameter.degree * parameter.left) right)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter right,
    realization.readout () parameter right =
      fockForm parameter.lattice parameter.left
        (translationCoeff parameter.lattice (-parameter.charge) parameter.degree right)

def rejected : Realization signature :=
  realize signature (fun _ parameter right => actual.readout () parameter right + 1)
    (fun empty => nomatch empty)

def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro axis; exact Fin.elim0 axis
  even_diagonal := by intro axis; exact Fin.elim0 axis

private theorem actual_law : arena.Law actual := by
  intro parameter right
  exact creation_translation_adjoint parameter.lattice parameter.charge
    parameter.degree parameter.left right

private theorem rejected_failure : ¬arena.Law rejected := by
  intro law
  have contradiction := law (⟨zeroLattice, 0, 0, 0⟩ : Parameters) 0
  change fockForm zeroLattice (creationCoeff zeroLattice 0 0 * 0) 0 + 1 =
    fockForm zeroLattice 0 (translationCoeff zeroLattice 0 0 0) at contradiction
  norm_num at contradiction

def sourceRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint.creation_translation_adjoint)) where
  actual := actual
  bridge := by
    constructor
    · intro source parameter right
      exact source parameter.lattice parameter.charge parameter.degree parameter.left right
    · intro law lattice charge degree left right
      exact law ⟨lattice, charge, degree, left⟩ right
  variation := ⟨actual_law, rejected, rejected_failure⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_failure⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨zeroLattice, 0, 0, 1⟩, 0, 1, ?_⟩
    change fockForm zeroLattice (creationCoeff zeroLattice 0 0 * 1) 0 ≠
      fockForm zeroLattice (creationCoeff zeroLattice 0 0 * 1) 1
    rw [creation_translation_adjoint, creation_translation_adjoint]
    simp [translationCoeff, translatedPolynomial, fockForm_vacuum_left]

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint.creation_translation_adjoint)
    (type_of% (realize signature
      (fun _ parameter right => fockForm parameter.lattice
        (creationCoeff parameter.lattice parameter.charge parameter.degree * parameter.left) right)
      (fun empty => nomatch empty))) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint.creation_translation_adjoint.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter right => fockForm parameter.lattice
      (creationCoeff parameter.lattice parameter.charge parameter.degree * parameter.left) right)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint
