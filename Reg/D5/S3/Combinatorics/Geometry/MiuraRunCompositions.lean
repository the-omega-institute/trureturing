import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraRunCompositions
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source-bound dependent-family evidence for the actual mathematical operands. -/

namespace Reg.D5.S3.Combinatorics.Geometry.MiuraRunCompositions

open _root_.D5.S3.Combinatorics.Geometry.MiuraRunCompositions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) r N => Nat.card (PositiveLengths N r))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ N r : ℕ, 1 ≤ r → r ≤ N →
    R.readout () r N = (N - 1).choose (r - 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1 (by decide) (by decide)
  norm_num [rejected, realize] at hb

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 2, 3, ?_⟩
  change Nat.card (PositiveLengths 2 2) ≠ Nat.card (PositiveLengths 3 2)
  rw [positive_lengths_card 2 2 (by decide) (by decide),
    positive_lengths_card 3 2 (by decide) (by decide)]
  norm_num

def registration : Registration arena (type_of% (@positive_lengths_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_lengths_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_lengths_card)
    (type_of% (realize signature (fun (_ : Unit) r N => Nat.card (PositiveLengths N r))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraRunCompositions.positive_lengths_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraRunCompositions.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) r N => Nat.card (PositiveLengths N r))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.MiuraRunCompositions
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.Combinatorics.Geometry.MiuraRunCompositions
