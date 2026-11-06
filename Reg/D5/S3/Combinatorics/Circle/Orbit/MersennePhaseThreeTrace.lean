import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.Orbit.MersennePhaseThreeTrace
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace

open scoped BigOperators
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun d => Fin d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ d j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * d) => i.val % d = j.val),
      actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (_hd : 3 ≤ d) (j : Fin d),
    R.readout () d j = modulus (3 * d) *
      ((if j.val = d - 3 then (1 : ℤ) else 0) -
        (if j.val = d - 1 then (1 : ℤ) else 0))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 3 (by decide) ⟨0, by decide⟩
  norm_num [rejected, realize, modulus] at h0

noncomputable def registration : Registration arena (type_of% (@actual_phase_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_phase_trace, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    have h0 := actual_phase_trace 3 (by decide) ⟨0, by decide⟩
    have h2 := actual_phase_trace 3 (by decide) ⟨2, by decide⟩
    refine ⟨3, ⟨0, by decide⟩, ⟨2, by decide⟩, ?_⟩
    change (∑ k ∈ Finset.univ.filter (fun k : Fin (3 * 3) => k.val % 3 = 0),
      actualSource (3 * 3) ((2 ^ 3 - 1) * (2 ^ (3 + 1) - 3)) k) ≠
      (∑ k ∈ Finset.univ.filter (fun k : Fin (3 * 3) => k.val % 3 = 2),
      actualSource (3 * 3) ((2 ^ 3 - 1) * (2 ^ (3 + 1) - 3)) k)
    rw [h0, h2]
    norm_num [modulus]

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@actual_phase_trace)
      (type_of% (realize signature (fun _ d j =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * d) => i.val % d = j.val),
          actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * d) => i.val % d = j.val),
      actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace
