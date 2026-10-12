import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Resource.LogDet.PathSpectralClassical
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.LogDet.PathSpectralClassical
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Resource.LogDet.PathSpectralClassical

universe u

abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f x => f x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ),
    (cfc f A).trace.re = ∑ i, R.readout () f (hA.eigenvalues i)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  have hA : (0 : Matrix n n ℂ).IsHermitian := by simp
  have bad := h 0 hA (fun _ => 1)
  have good := trace_cfc_eq_sum 0 hA (fun _ => 1)
  have contradiction := good.symm.trans bad
  norm_num [rejected, realize] at contradiction

def registration : Registration arena.{u} (type_of% (@trace_cfc_eq_sum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_cfc_eq_sum.{u}, rejected, rejected_law⟩
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
    refine ⟨id, 0, 1, ?_⟩
    norm_num [actual, realize]

noncomputable def registration_1 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum.{u})
      (type_of% (realize signature
        (fun _ f x => f x) (fun e => nomatch e))) Unit Unit := {
  unitName :=
    `D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum.__information_unit
  realizationName :=
    `Reg.D5.S3.Resource.LogDet.PathSpectralClassical.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ f x => f x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Resource.LogDet.PathSpectralClassical
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
#print axioms registration_1
#print axioms _root_.D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum

end Reg.D5.S3.Resource.LogDet.PathSpectralClassical
