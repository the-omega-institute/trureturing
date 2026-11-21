import D5.S3.TotalVariation.QuotientParitySpectrum
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Data.ZMod.Basic

/-! Source audit for the realizing law in the shifted quotient criterion. -/

open _root_.D5.S3.TotalVariation.GroupedParityBias
open _root_.D5.S3.TotalVariation.QuotientParitySpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.TotalVariation.QuotientParitySpectrum

noncomputable section
open scoped BigOperators

universe u

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
  Law R := ∀ {A : Type u} [AddCommGroup A] [Fintype A]
      (_two : ∀ x : A, x + x = 0) (p : A → ℝ) (_hnorm : ∑ x, p x = 1),
    (∃ (J : Type u) (_ : Fintype J) (c : J → A) (s : A) (q : J → ℝ),
      (∀ i, |q i| ≤ 1) ∧ law c s q = R.readout () A p) ↔
    ∃ H : AddSubgroup A, ∃ s : A, quotientCriterion H s p

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} (ZMod 2)
  let p := law (fun _ : A => (0 : A)) 0 (fun _ => 1)
  have htwo (x : A) : x + x = 0 := by
    apply ULift.down_injective
    change x.down + x.down = 0
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  have normalized (p : A → ℝ) (hzero : moment p 0 = 1) : ∑ x, p x = 1 := by
    simpa [moment, sign] using hzero
  have hnorm : ∑ x, p x = 1 := by
    apply normalized
    unfold p
    rw [moment_factor htwo]
    norm_num [sign]
  have hcond := (affine_law_iff_quotient_criterion htwo p hnorm).mp
    ⟨A, inferInstance, fun _ => 0, 0, fun _ => 1, fun _ => by norm_num, rfl⟩
  obtain ⟨J, inst, c, s, q, _, hqeq⟩ := (h htwo p hnorm).mpr hcond
  change law c s q = (fun _ => 0) at hqeq
  have hzero : moment (law c s q) 0 = 1 := by
    rw [moment_factor htwo]
    norm_num [sign]
  rw [hqeq] at hzero
  simp [moment] at hzero

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (ULift.up ())
  norm_num [actual, realize] at hh

def sourceRegistration :
    Registration arena.{u} (type_of% @affine_law_iff_quotient_criterion.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_law_iff_quotient_criterion, rejected, rejected_law⟩
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
      (@affine_law_iff_quotient_criterion.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.QuotientParitySpectrum.unit
  realizationName := `Reg.D5.S3.TotalVariation.QuotientParitySpectrum.sourceRegistration
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
    owner := `D5.S3.TotalVariation.QuotientParitySpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.QuotientParitySpectrum
