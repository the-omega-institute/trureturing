import D5.S3.Combinatorics.Parking.DescentGapKernel
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound registrations for the literal observations. -/

open _root_.D5.S3.Combinatorics.Parking.DescentRefinement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Parking.DescentGapKernel

noncomputable section

namespace profileMass

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Nat)
    (fun _ => Nat) (fun _ => Finset (List Nat))

private def actual : Realization signature :=
  realize signature (fun _ k r => profiles k r) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law f := ∀ k r (hs : List Nat), hs ∈ f.readout () k r ↔ hs.length = k ∧ hs.sum = r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 0 []).mpr ⟨rfl, rfl⟩
  simp [rejected, realize] at he

def family : Registration arena (type_of% @mem_profiles) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_profiles, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨0, 0, 1, ?_⟩
    change profiles 0 0 ≠ profiles 0 1
    intro h
    have he : [] ∈ profiles 0 0 := (mem_profiles 0 0 []).mpr ⟨rfl, rfl⟩
    rw [h, mem_profiles] at he
    exact Nat.zero_ne_one he.2

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mem_profiles) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Parking.DescentGapKernel.profileMass.unit
  realizationName := `Reg.D5.S3.Combinatorics.Parking.DescentGapKernel.profileMass.family
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
    owner := `D5.S3.Combinatorics.Parking.DescentGapKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end profileMass

end
end Reg.D5.S3.Combinatorics.Parking.DescentGapKernel
