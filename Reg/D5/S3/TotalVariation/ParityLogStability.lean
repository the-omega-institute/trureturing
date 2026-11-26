import D5.S3.TotalVariation.ParityLogStability
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Batteries.Tactic.OpenPrivate

/-! Source-bound audits for stability and sharpness of logarithmic parity recovery. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.ParityLogStability
open _root_.D5.S3.TotalVariation.Pinsker (totalVariation)
open private twoPointMass from D5.S3.TotalVariation.ParityLogStability

namespace Reg.D5.S3.TotalVariation.ParityLogStability.Sharpness

noncomputable section

open scoped BigOperators

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Bool → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ e => twoPointMass e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => twoPointMass 4) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (e c : ℝ), 0 < e → e < 1 → c < 2 →
    ∃ q : ℝ, e < q ∧ q < 1 ∧
      c * totalVariation (twoPointMass q) (R.readout () () e) / e <
        Real.log q - Real.log e

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, hq₁, hbound⟩ := h (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  have hq₀ : 0 < q := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq₀ (by norm_num : (0 : ℝ) < 1 / 2))
  rw [Real.log_div hq₀.ne' (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hlog
  have htv : totalVariation (twoPointMass q) (twoPointMass 4) = (4 - q) / 2 := by
    have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
    unfold totalVariation
    rw [hu]
    have hpos : 0 ≤ (4 - q) / 2 := by linarith
    have hminus : (1 - q) / 2 - (1 - 4) / 2 = (4 - q) / 2 := by ring
    have hplus : (1 + q) / 2 - (1 + 4) / 2 = -((4 - q) / 2) := by ring
    simp [twoPointMass, hminus, hplus, abs_of_nonneg hpos]
    ring
  change 1 * totalVariation (twoPointMass q) (twoPointMass 4) / (1 / 2) < _ at hbound
  rw [htv] at hbound
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h false
  norm_num [actual, realize, twoPointMass] at hh

def sourceRegistration : Registration arena (type_of% @log_bernoulli_bias_sharp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨log_bernoulli_bias_sharp, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_bernoulli_bias_sharp) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.ParityLogStability.Sharpness.unit
  realizationName := `Reg.D5.S3.TotalVariation.ParityLogStability.Sharpness.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => twoPointMass e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.ParityLogStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg",
        "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.ParityLogStability.Sharpness

namespace Reg.D5.S3.TotalVariation.ParityLogStability.Stability

noncomputable section

universe u

open scoped BigOperators

abbrev signature : Signature where
  Params := Type u
  State A := A → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := A → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ p x => 2 * p x) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [AddCommGroup A] [Fintype A]
    (_two : ∀ x : A, x + x = 0) (p q : A → ℝ) (_hmass : ∑ x, p x = ∑ x, q x)
    (a : A) (e : ℝ) (_he : 0 < e)
    (_hp : ∀ ψ, e ≤ |moment p ψ|) (_hq : ∀ ψ, e ≤ |moment q ψ|),
    |logCoefficient a (R.readout () A p) - logCoefficient a q| ≤
      2 * totalVariation p q / e

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  classical
  let A := ULift.{u} (ZMod 1)
  let _ : Fintype A := Fintype.ofFinite _
  have hzero (x : A) : x = 0 := Subsingleton.elim _ _
  have hsign (ψ : AddChar A ℂ) (x : A) : sign ψ x = 1 := by simp [hzero x, sign]
  let p : A → ℝ := fun _ => 1
  have hfloor (ψ : AddChar A ℂ) : (1 : ℝ) ≤ |moment p ψ| := by
    simp [moment, p, hsign]
  have hcoeff (r : ℝ) : logCoefficient (0 : A) (fun _ => r) = -2 * Real.log |r| := by
    simp [logCoefficient, moment, hsign, AddChar.card_eq]
  have hb := h (A := A) (fun x => hzero (x + x)) p p rfl 0 1 (by norm_num) hfloor hfloor
  change |logCoefficient (0 : A) (fun _ => 2 * 1) - logCoefficient (0 : A) p| ≤
    2 * totalVariation p p / 1 at hb
  rw [show (fun _ : A => (2 : ℝ) * 1) = fun _ => 2 by simp, hcoeff,
    show p = (fun _ : A => 1) by rfl, hcoeff] at hb
  norm_num [totalVariation, Real.log_one] at hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_pos hlog] at hb
  linarith

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (ULift.up ())
  norm_num [actual, realize] at hh

def sourceRegistration : Registration arena.{u} (type_of% @log_parity_coefficient_stability.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_parity_coefficient_stability, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_parity_coefficient_stability.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.ParityLogStability.Stability.unit
  realizationName := `Reg.D5.S3.TotalVariation.ParityLogStability.Stability.sourceRegistration
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
    owner := `D5.S3.TotalVariation.ParityLogStability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.ParityLogStability.Stability
