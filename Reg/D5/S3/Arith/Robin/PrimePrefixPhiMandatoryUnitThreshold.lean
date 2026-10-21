import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold
open MeasureTheory
open _root_.D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ v t => Real.exp (-v*t)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {τ w : ℝ}, 0 ≤ w → ∀ v : ℝ,
    (∫ t : ℝ, R.readout () v t ∂(ENNReal.ofReal w • Measure.dirac τ)) =
      w * Real.exp (-v*τ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (τ := 0) (w := 1) (by norm_num) 0
  norm_num [rejected, realize] at h0

def family : Registration arena (type_of% (@atom_kernel_integral)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@atom_kernel_integral, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    change Real.exp (-(1 : ℝ)*0) ≠ Real.exp (-1*1)
    intro h
    have := Real.exp_injective h
    norm_num at this

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@atom_kernel_integral)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% ℝ) Unit where
  unitName := `D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold.atom_kernel_integral.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold.family
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
    owner := `D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold
