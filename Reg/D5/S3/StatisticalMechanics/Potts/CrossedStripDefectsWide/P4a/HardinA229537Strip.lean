import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537Strip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for exact defective-strip counts and finite transfer data. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537Strip
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537Strip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] a

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ),
    (R.readout () () (n + 15) : ℤ) =
      6 * R.readout () () (n + 14) + 23 * R.readout () () (n + 13) - 102 * R.readout () () (n + 12) - 288 * R.readout () () (n + 11) +
      250 * R.readout () () (n + 10) + 787 * R.readout () () (n + 9) - 238 * R.readout () () (n + 8) - 741 * R.readout () () (n + 7) +
      124 * R.readout () () (n + 6) + 196 * R.readout () () (n + 5) - 16 * R.readout () () (n + 4) - 16 * R.readout () () (n + 3)
private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_zero : a 0 = 0 := by
  unfold a
  decide +kernel
private theorem count_pos : 0 < a 2 := by
  unfold a
  unfold _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  apply Finset.card_pos.mpr
  refine ⟨(fun x => ![![0, 1],
    ![0, 1],
    ![0, 1],
    ![1, 2]] x.1 x.2), ?_⟩
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
    refine ⟨(), 0, 2, ?_⟩
    change a 0 ≠ a 2
    rw [count_zero]
    exact Nat.ne_of_lt count_pos

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229537Strip.Recurrence.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537Strip
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
end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537Strip
