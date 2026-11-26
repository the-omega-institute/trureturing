import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.BinaryTraceZeroSimilarity
import Reg.Support.SingleDependentReadout

/-! Equality with a conjugate of the representative. -/

set_option autoImplicit false

namespace Reg.D5.S1.Eigenstructure.BinaryTraceZeroSimilarity

open _root_.D5.S1.Eigenstructure.BinaryTraceZeroSimilarity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 2)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat) (fun _ => Mat → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ input output => input = output) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ M : Mat, M ≠ 0 → M.trace = 0 → ∃ (k : Fin 6) (g : Matˣ),
    R.readout () () M ((g : Mat) * representative k * (↑g⁻¹ : Mat))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, bad⟩ := h (representative 0) (by decide) (by decide)
  exact bad

def family : Registration arena (type_of% exists_conjugate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_conjugate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : Mat), 1, ?_⟩
    intro h
    have hz : (1 : Mat) = 0 := Eq.mp (congrFun h 0) rfl
    exact one_ne_zero hz

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_conjugate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Eigenstructure.BinaryTraceZeroSimilarity.unit
  realizationName := `Reg.D5.S1.Eigenstructure.BinaryTraceZeroSimilarity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ input output => input = output) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.BinaryTraceZeroSimilarity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Eigenstructure.BinaryTraceZeroSimilarity
