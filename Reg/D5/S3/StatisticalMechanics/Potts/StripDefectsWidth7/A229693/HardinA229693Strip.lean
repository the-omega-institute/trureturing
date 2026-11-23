import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for exact defective-strip counts and finite transfer data. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] a

open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
  (horizontal antidiagonal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (literalCount)

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
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Count.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
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

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (t : ℕ),
    (r.readout () () (t + 15) : ℤ) = 126 * r.readout () () (t + 14) - 6345 * r.readout () () (t +
      13) + 165456 * r.readout () () (t + 12) - 2474469 * r.readout () () (t + 11) + 22918302 *
      r.readout () () (t + 10) - 138045627 * r.readout () () (t + 9) + 554666940 * r.readout () ()
      (t + 8) - 1494608922 * r.readout () () (t + 7) + 2659094568 * r.readout () () (t + 6) -
      2986698420 * r.readout () () (t + 5) + 1913187600 * r.readout () () (t + 4) - 531441000 *
      r.readout () () (t + 3)
private theorem rejected_at (h : arena.Law rejected) (t : ℕ) : False := by
  have hb := h t
  have ha := result t
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_zero : a 0 = 0 := by
  unfold a
  decide +kernel
private theorem count_one_pos : 0 < a 1 := by
  unfold a
  apply Finset.card_pos.mpr
  refine ⟨(fun p => ![0, 0, 0, 1, 0, 1, 0] p.2), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by decide +kernel⟩
def family : Registration arena (type_of% @result) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [count_zero]
    exact Nat.ne_of_lt count_one_pos

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Recurrence.auditUnit
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
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
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

end Recurrence

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
