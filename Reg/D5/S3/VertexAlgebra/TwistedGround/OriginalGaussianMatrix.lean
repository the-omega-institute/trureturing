import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix

/-! The registration mirrors the finite-section theorem while leaving exact
source-observation selection unresolved. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix

structure Parameters where
  N : ℕ
  z : ℂ

abbrev signature : Signature where
  Params := Parameters
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def bound (p : Parameters) : Prop :=
  ‖Matrix.toEuclideanCLM (n := Fin p.N) (𝕜 := Complex)
      (finiteSection p.N p.z)‖ ≤ ‖p.z‖ ^ 2

def actual : Realization signature :=
  realize signature (fun _ p x => x = true ∧ bound p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p : Parameters, ‖p.z‖ < 1 → R.readout () p true

theorem sourceBridge :
    (type_of% (@D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix.finiteSection_opNorm_le)) ↔
      arena.Law actual := by
  constructor
  · intro h p hp
    simpa [actual, bound, realize] using h p.N p.z hp
  · intro h N z hz
    have hh := h ⟨N, z⟩ hz
    simpa [actual, bound, realize] using hh

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hh := h ⟨0, 0⟩ (by simp)
  exact hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, true, false, ?_⟩
  have hbound : bound ⟨0, 0⟩ :=
    finiteSection_opNorm_le 0 0 (by simp)
  simp [actual, bound, realize, hbound]

def family : Registration arena (type_of%
    (@D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix.finiteSection_opNorm_le)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp finiteSection_opNorm_le, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      have hji : j = i := by cases j; cases i; rfl
      exact (hj hji).elim
    · intro i
      exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix.finiteSection_opNorm_le)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix.finiteSection_opNorm_le
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceBridge
#print axioms family

noncomputable section
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
abbrev eqSignature : Signature where
  Params := Type
  State T := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def eqActual : Realization eqSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def eqRejected : Realization eqSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨ℂ, 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

namespace pairScalar_comm
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (s t : ℕ), R.readout () _ (pairScalar s t) (pairScalar t s)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h 0 0
def family : Registration arena (type_of% (@pairScalar_comm)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@pairScalar_comm, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairScalar_comm) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix.pairScalar_comm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix.pairScalar_comm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pairScalar_comm
end

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
