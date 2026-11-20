import D5.S3.TotalVariation.MinimumParityInputs
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source audit for the mass function realized by a minimum-size input family. -/

open _root_.D5.S3.TotalVariation.GroupedParityBias
open _root_.D5.S3.TotalVariation.QuotientParitySpectrum
open _root_.D5.S3.TotalVariation.MinimumParityInputs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.TotalVariation.MinimumParityInputs

noncomputable section

open scoped BigOperators

universe u v

abbrev signature : Signature where
  Params := Type u
  State A := A → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := A → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ p => p) (fun a => nomatch a)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [AddCommGroup A] [Fintype A] [Module (ZMod 2) A]
    (p : A → ℝ) (_hnorm : ∑ a, p a = 1)
    (_hreal : ∃ H : AddSubgroup A, ∃ s : A, quotientCriterion H s p),
    (∀ {J : Type v} [Fintype J] (d : J → A) (t : A) (r : J → ℝ),
      law d t r = p → minimumInputCount p ≤ Fintype.card J) ∧
    (∃ (J : Type u) (_ : Fintype J) (d : J → A) (t : A) (r : J → ℝ),
      (∀ j, |r j| ≤ 1) ∧ law d t r = R.readout () A p ∧
        Fintype.card J = minimumInputCount p)

private theorem two_add {A : Type u} [AddCommGroup A] [Module (ZMod 2) A] (x : A) :
    x + x = 0 := by
  calc
    x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} (ZMod 2)
  let p := law (fun _ : A => (0 : A)) 0 (fun _ => 1)
  have hm : moment p 0 = 1 := by
    unfold p
    rw [moment_from_inputs two_add]
    norm_num [sign]
  have hnorm : ∑ a, p a = 1 := by simpa [moment, sign] using hm
  have hcond := (affine_law_iff_quotient_criterion two_add p hnorm).mp
    ⟨A, inferInstance, fun _ => 0, 0, fun _ => 1, fun _ => by norm_num, rfl⟩
  obtain ⟨J, inst, d, t, r, _, heq, _⟩ := (h p hnorm hcond).2
  change law d t r = (fun _ => 0) at heq
  have hzero : moment (law d t r) 0 = 1 := by
    rw [moment_from_inputs two_add]
    norm_num [sign]
  rw [heq] at hzero
  simp [moment] at hzero

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (ULift.up ())
  norm_num [actual, realize] at hh

def sourceRegistration :
    Registration arena.{u,v} (type_of% @minimum_input_count_exact.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minimum_input_count_exact, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro other unequal
        exact (unequal (Subsingleton.elim _ _)).elim
      · funext a
        exact nomatch a
    · intro a
      exact nomatch a
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@minimum_input_count_exact.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.MinimumParityInputs.unit
  realizationName := `Reg.D5.S3.TotalVariation.MinimumParityInputs.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.MinimumParityInputs
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "body", "arg", "body", "arg",
        "body", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.MinimumParityInputs
