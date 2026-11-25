import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo

/-! The second absolute coordinate as a readout of the actual antighost. -/

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST (ComplexState b0)
open _root_.D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativeNormTwo
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open private fixedCoord_groundState from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo

abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ComplexState) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ x => σ x) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ x => σ x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ComplexState, ρ (b0 x) = -R.readout () () x

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hzero := h 0
  change ρ (b0 0) = -(σ 0 + 1) at hzero
  have hz : (0 : ℂ) = -1 := by simpa only [map_zero, zero_add] using hzero
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)) hz.symm

def family : Registration arena (type_of% (@rho_b0)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rho_b0, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro role
    refine ⟨(), ψ₁₃, 0, ?_⟩
    change σ ψ₁₃ ≠ σ 0
    rw [map_zero, σ, ψ₁₃, fixedCoord_groundState]
    simp [ket]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rho_b0) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo.family
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
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo
