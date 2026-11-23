import D5.S3.Combinatorics.Parking.MaximumLetterGaps
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound registrations for the literal observations. -/

open _root_.D5.S3.Combinatorics.Parking.DescentRefinement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Parking.MaximumLetterGaps

noncomputable section

namespace maximumMultiplicity

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Nat)
    (fun _ => List Nat) (fun _ => Nat)

private def actual : Realization signature :=
  realize signature (fun _ m w => w.count m) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law f := ∀ {n m : Nat}, m ≤ n → ∀ w, BoundedParking n m w →
    f.readout () m w ≤ n - m + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (n := 1) (m := 1) (by decide) [1] (by simp [BoundedParking, RankBound])
  simp [rejected, realize] at he

def family : Registration arena (type_of% @max_count_cut) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@max_count_cut, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨1, [], [1], ?_⟩
    change (0 : Nat) ≠ 1
    decide

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@max_count_cut) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Parking.MaximumLetterGaps.maximumMultiplicity.unit
  realizationName := `Reg.D5.S3.Combinatorics.Parking.MaximumLetterGaps.maximumMultiplicity.family
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
    owner := `D5.S3.Combinatorics.Parking.MaximumLetterGaps
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end maximumMultiplicity

end
end Reg.D5.S3.Combinatorics.Parking.MaximumLetterGaps
