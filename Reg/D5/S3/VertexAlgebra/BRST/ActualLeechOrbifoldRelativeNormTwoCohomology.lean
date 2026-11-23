import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwoCohomology

/-! The coefficient readout of the degree-one BRST class. -/

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativeNormTwo

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwoCohomology

abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Cohomology 1) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ x => cohomologyOne x) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ x => cohomologyOne x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () psiClass = 1

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  change cohomologyOne psiClass + 1 = 1 at h
  rw [cohomologyOne_psiClass] at h
  exact one_ne_zero (add_left_cancel (h.trans (add_zero 1).symm))

def family : Registration arena (type_of% cohomologyOne_psiClass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cohomologyOne_psiClass, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro role
    refine ⟨(), psiClass, 0, ?_⟩
    change cohomologyOne psiClass ≠ cohomologyOne (0 : Cohomology 1)
    rw [cohomologyOne_psiClass, cohomologyOne.map_zero]
    exact one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    cohomologyOne_psiClass (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwoCohomology.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwoCohomology.family
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
    owner := `D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwoCohomology
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwoCohomology
