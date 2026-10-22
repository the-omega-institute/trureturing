import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator

noncomputable section

abbrev signature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Module.End ℂ
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter p =>
    (Q parameter.1 parameter.2 * Q parameter.1 parameter.2) * C parameter.1 p)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : ℤ),
    readout.readout () ⟨D, H⟩ p - C D p * (Q D H * Q D H) = 0

def sourceStatement : Prop :=
  ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : ℤ),
    (Q D H * Q D H) * C D p - C D p * (Q D H * Q D H) = 0

theorem sourceBridge : sourceStatement ↔ arena.Law actual := Iff.rfl

theorem exactTarget : sourceStatement :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator.square_c_commutator

theorem actualPositive : arena.Law actual := sourceBridge.mp exactTarget

def registrationFromEvidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdependence : ObservationalDependence signature actual) :
    Registration arena
      (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator.square_c_commutator)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualPositive, bad, hbad⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨bad, ?_, (by funext empty; exact nomatch empty), hbad⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := hdependence

#print axioms sourceBridge
#print axioms exactTarget
#print axioms actualPositive
#print axioms registrationFromEvidence

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator
