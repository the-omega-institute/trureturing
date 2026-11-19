import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Golomb.NotikMinimizers

namespace Reg.D5.S3.Combinatorics.Golomb.NotikMinimizers

open _root_.D5.S3.Combinatorics.Golomb.NotikMinimizers
open _root_.D5.S3.Combinatorics.Golomb.Replay (endLength)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ → Prop)

/-- At each gap count, observe the predicate on candidate minimum lengths. -/
def actual : Realization signature :=
  realize signature (fun _ _ gaps => MinimumAt gaps) (fun e => nomatch e)

/-- Substitute the nine-mark predicate for the observed eight-mark predicate. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => MinimumAt 8) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 7 34 ∧ MinimumAt 8 44 ∧ MinimumAt 9 55

private theorem nine_marks_reject_34 : ¬ MinimumAt 8 34 := by
  rintro ⟨⟨z, hzero, hlast, hz⟩, _, _⟩
  have lower := result.2.1.2.1 (fun i => (z i : ℝ)) hz
  change ((44 : ℤ) : ℝ) ≤ (z (Fin.last 8) : ℝ) - (z 0 : ℝ) at lower
  rw [hzero, hlast] at lower
  norm_num at lower

private theorem bridge : claim ↔ arena.Law actual := Iff.rfl

private theorem actual_positive : arena.Law actual := bridge.mp result

private theorem rejected_law : ¬ arena.Law rejected := fun law => nine_marks_reject_34 law.1

private theorem actual_observes_size : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 7, 8, ?_⟩
  intro equal
  have same := congrFun equal (34 : ℤ)
  have holds : actual.readout i () 7 34 := actual_positive.1
  exact nine_marks_reject_34 (Eq.mp same holds)

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Combinatorics.Golomb.NotikMinimizers.result) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_observes_size

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Golomb.NotikMinimizers.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Golomb.NotikMinimizers.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Golomb.NotikMinimizers.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ gaps => MinimumAt gaps) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Golomb.NotikMinimizers
    definition := some {
      owner := `D5.S3.Combinatorics.Golomb.NotikMinimizers
      name := `D5.S3.Combinatorics.Golomb.NotikMinimizers.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms _root_.D5.S3.Combinatorics.Golomb.NotikMinimizers.result
#print axioms bridge
#print axioms actual_positive
#print axioms rejected_law
#print axioms actual_observes_size
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Golomb.NotikMinimizers
