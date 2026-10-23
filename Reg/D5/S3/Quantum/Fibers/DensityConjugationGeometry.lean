import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.DensityConjugationGeometry

/-! Source-bound audit of Hausdorff dimension on the literal physical quotient. -/
noncomputable section
open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fibers.RealCopyConjugation
open _root_.D5.S3.Quantum.Fibers.DensityConjugationGeometry
namespace Reg.D5.S3.Quantum.Fibers.DensityConjugationGeometry

abbrev signature : Signature where
  Params := Unit
  State _ := Set fiveModeOrbitQuotient
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ s => dimH s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () fiveModeNonrealQuotient = 24
private theorem rejected_law : ¬ arena.Law rejected := by
  norm_num [arena, rejected, realize]

def family : Registration arena (type_of% five_mode_nonreal_quotient_dimension) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨five_mode_nonreal_quotient_dimension, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), fiveModeNonrealQuotient, ∅, ?_⟩
    intro h
    change dimH fiveModeNonrealQuotient = dimH (∅ : Set fiveModeOrbitQuotient) at h
    rw [five_mode_nonreal_quotient_dimension, dimH_empty] at h
    norm_num at h

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    five_mode_nonreal_quotient_dimension (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.DensityConjugationGeometry.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.DensityConjugationGeometry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => dimH s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.DensityConjugationGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Quantum.Fibers.DensityConjugationGeometry
