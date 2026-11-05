import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Faithful whole-family audit attempt for narrow_classification.
The remaining five public source results have no registration in this mirror.
Kernel compilation of this record alone does not establish source binding. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit

namespace Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
namespace narrow_classification

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ X Q => diameter X Q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X Q : ℕ}, 3 ≤ X → Odd X → 0 < Q → Q < X →
    2 * R.readout () X Q < X →
    2 ≤ period X Q ∧
    period X Q = orderOf (2 : ZMod (denominator X Q)) ∧
    denominator X Q = 2 ^ period X Q - 1 ∧
    2 * R.readout () X Q = X - Nat.gcd X Q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (X := 3) (Q := 1) (by decide) (by decide)
    (by decide) (by decide) (by norm_num [rejected, realize])).2.2.2
  norm_num [rejected, realize] at hh

private theorem diameter_zero_seed (X : ℕ) : diameter X 0 = 0 := by
  classical
  unfold diameter
  split_ifs with h
  · have hz (z : ℕ) (hz : z ∈ orbit X 0) : z = 0 := by
      obtain ⟨n, _, he⟩ := Finset.mem_image.mp hz
      simpa [residue] using he.symm
    rw [hz _ ((orbit X 0).max'_mem h), hz _ ((orbit X 0).min'_mem h)]
  · rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨Q, _, hQX, _, _, hdiam, _⟩ :=
    exists_narrow_of_mersenne_dvd (X := 3) (t := 2)
      (by decide) (by decide) (by decide) (by norm_num)
  refine ⟨3, 0, Q, ?_⟩
  change diameter 3 0 ≠ diameter 3 Q
  rw [diameter_zero_seed]
  omega

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification)
    (type_of% (realize signature (fun _ X Q => diameter X Q) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X Q => diameter X Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg", "arg"]
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end narrow_classification
end Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
