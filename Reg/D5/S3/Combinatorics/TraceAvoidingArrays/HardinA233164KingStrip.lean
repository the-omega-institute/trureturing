import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The complete literal count sequence is the single observed readout. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () 1 = 11 ∧ R.readout () () 2 = 64 ∧ R.readout () () 3 = 1280 ∧
    (∀ n : ℕ, 1 < n → R.readout () () n = 4^(2*n-3)*(2^n+12)) ∧
    (∀ n : ℕ, 3 < n → (R.readout () () n : ℤ) =
      48*R.readout () () (n-1)-512*R.readout () () (n-2)) ∧
    (PowerSeries.mk fun n => (R.readout () () n : ℚ)) =
      X*(11-464*X+3840*X^2)*((1-16*X)*(1-32*X))⁻¹

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1
  change a 1 + 1 = 11 at hh
  have ha := result.1
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    have hz : a 0 = 0 := by unfold a; decide +kernel
    rw [hz, result.1]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
