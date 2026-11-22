import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
  (Boundary Row horizontal antidiagonal boundary cross)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects literalCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

namespace Transition
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 168) (fun _ => Fin 168) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ i j => T i j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ i j => T i j + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Boundary) (d : ℕ), Valid p d → ∀ s : Fin 168,
    (∑ q : Row, if cross p q + bondDefects horizontal q q ≤ d ∧
      cl (boundary q) (d - (cross p q + bondDefects horizontal q q)) = s
      then (1 : ℤ) else 0) = r.readout () (cl p d) s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Boundary := ![0, 1, 0, 1, 0, 1]
  have hp : Valid p 2 := by unfold Valid; decide +kernel
  have hh := h p 2 hp 0
  have ha := transition_counts p 2 hp 0
  change _ = T (cl p 2) 0 + 1 at hh
  linarith

def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    change T 0 0 ≠ T 0 2
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer.Transition.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i j => T i j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transition

namespace Count
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature :=
  realize signature (fun _ _ n => literalCount (q := 3) horizontal antidiagonal 2 n)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => literalCount (q := 3) horizontal antidiagonal 2 n + 1)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, (r.readout () () (n + 1) : ℤ) =
    dotProduct initial ((T ^ n).mulVec terminal)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  have ha := count_transfer 0
  change ((literalCount (q := 3) horizontal antidiagonal 2 (0 + 1) + 1 : ℕ) : ℤ) =
    dotProduct initial ((T ^ 0).mulVec terminal) at hh
  rw [Nat.cast_add, Nat.cast_one] at hh
  linarith
private theorem count_zero : literalCount (q := 3) horizontal antidiagonal 2 0 = 0 := by
  decide +kernel
private theorem count_one_pos : 0 < literalCount (q := 3) horizontal antidiagonal 2 1 := by
  unfold literalCount
  apply Finset.card_pos.mpr
  refine ⟨(fun p => ![0, 0, 0, 1, 0, 1, 0] p.2), ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide +kernel⟩

def family : Registration arena (type_of% @count_transfer) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨count_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change literalCount (q := 3) horizontal antidiagonal 2 0 ≠
      literalCount (q := 3) horizontal antidiagonal 2 1
    rw [count_zero]
    exact Nat.ne_of_lt count_one_pos

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_transfer) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer.Count.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n =>
    literalCount (q := 3) horizontal antidiagonal 2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Count
end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
