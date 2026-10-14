import D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm

namespace Family
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

structure AuxiliaryParameters where
  lattice : LatticeData
  frame : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  xAxis : Fin lattice.rank
  yAxis : Fin lattice.rank

abbrev balanceSignature : Signature where
  Params := AuxiliaryParameters
  State parameters := Fin parameters.lattice.rank × Fin parameters.lattice.rank
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def balanceActual : Realization balanceSignature :=
  realize balanceSignature
    (fun _ parameters axes => gramPair parameters.lattice
      (fun axis => star (parameters.frame axes.1 axis)) (parameters.frame axes.2))
    (fun empty => nomatch empty)

def balanceArena : Arena where
  signature := balanceSignature
  Law observation := ∀ (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank),
    xAxis ≠ yAxis →
    (∀ axis, star (frame xAxis axis) = frame xAxis axis) →
    (∀ axis, star (frame yAxis axis) = frame yAxis axis) →
    (∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0) →
    (∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) →
    ∀ first second,
    ((axisAuxDegree D xAxis yAxis first : ℂ) +
      (axisAuxDegree D xAxis yAxis second : ℂ)) *
      observation.readout () ⟨D, frame, xAxis, yAxis⟩ (first, second) = 0

abbrev balanceStatement : Prop :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.frame_hermitian_aux_balance)

theorem balance_bridge : balanceStatement ↔ balanceArena.Law balanceActual := Iff.rfl

theorem balance_positive : balanceArena.Law balanceActual :=
  _root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.frame_hermitian_aux_balance

abbrev selectionSignature : Signature where
  Params := AuxiliaryParameters
  State parameters := Oscillator parameters.lattice × Oscillator parameters.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def selectionActual : Realization selectionSignature :=
  realize selectionSignature
    (fun _ parameters polynomials => fockForm parameters.lattice
      (coordinateSub parameters.lattice parameters.frame polynomials.1)
      (coordinateSub parameters.lattice parameters.frame polynomials.2))
    (fun empty => nomatch empty)

def selectionArena : Arena where
  signature := selectionSignature
  Law observation := ∀ (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank),
    xAxis ≠ yAxis →
    (∀ axis, star (frame xAxis axis) = frame xAxis axis) →
    (∀ axis, star (frame yAxis axis) = frame yAxis axis) →
    (∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0) →
    (∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) →
    ∀ (left right : Oscillator D) (leftDegree rightDegree : ℤ),
    MvPolynomial.IsWeightedHomogeneous (auxiliaryWeight D xAxis yAxis) left leftDegree →
    MvPolynomial.IsWeightedHomogeneous (auxiliaryWeight D xAxis yAxis) right rightDegree →
    leftDegree + rightDegree ≠ 0 →
    observation.readout () ⟨D, frame, xAxis, yAxis⟩ (left, right) = 0

abbrev selectionStatement : Prop :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.fockForm_auxiliary_selection)

theorem selection_bridge : selectionStatement ↔ selectionArena.Law selectionActual := Iff.rfl

theorem selection_positive : selectionArena.Law selectionActual :=
  _root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.fockForm_auxiliary_selection

structure CreatorParameters where
  lattice : LatticeData
  frame : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  index : Index lattice

abbrev creatorSignature : Signature where
  Params := CreatorParameters
  State parameters := Oscillator parameters.lattice × Oscillator parameters.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ × ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def creatorActual : Realization creatorSignature :=
  realize creatorSignature
    (fun _ parameters polynomials =>
      (fockForm parameters.lattice
        (coordinateSub parameters.lattice parameters.frame
          (MvPolynomial.X parameters.index * polynomials.1))
        (coordinateSub parameters.lattice parameters.frame polynomials.2),
       (parameters.index.2 + 1 : ℂ) * fockForm parameters.lattice
        (coordinateSub parameters.lattice parameters.frame polynomials.1)
        (coordinateSub parameters.lattice parameters.frame
          (coordinateDerivative parameters.lattice parameters.frame
            (fun axis => star (parameters.frame parameters.index.1 axis))
            parameters.index.2 polynomials.2))))
    (fun empty => nomatch empty)

def creatorArena : Arena where
  signature := creatorSignature
  Law observation := ∀ (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (index : Index D)
    (left right : Oscillator D),
    (observation.readout () ⟨D, frame, index⟩ (left, right)).1 =
    (observation.readout () ⟨D, frame, index⟩ (left, right)).2

abbrev creatorStatement : Prop :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.substituted_creator_adjoint)

theorem creator_bridge : creatorStatement ↔ creatorArena.Law creatorActual := Iff.rfl

theorem creator_positive : creatorArena.Law creatorActual :=
  _root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.substituted_creator_adjoint

def balanceEvidenceObligation : Type := Registration balanceArena balanceStatement

def selectionEvidenceObligation : Type := Registration selectionArena selectionStatement

def creatorEvidenceObligation : Type := Registration creatorArena creatorStatement

def balanceContractObligation : Type 3 :=
  LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
  (@_root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.frame_hermitian_aux_balance)
  (Realization balanceSignature) Unit Unit

def selectionContractObligation : Type 3 :=
  LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
  (@_root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.fockForm_auxiliary_selection)
  (Realization selectionSignature) Unit Unit

def creatorContractObligation : Type 3 :=
  LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
  (@_root_.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection.substituted_creator_adjoint)
  (Realization creatorSignature) Unit Unit

#print axioms balance_bridge
#print axioms balance_positive
#print axioms selection_bridge
#print axioms selection_positive
#print axioms creator_bridge
#print axioms creator_positive

end
end Family
end Reg.D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection
