/- SOURCE_ONLY_UNCOMPILED. Migrated whole source-family attempts for the
actual weighted-column remainder owner. Every telescope is retained; raw Expr
paths, source binding and enrollment remain UNVERIFIED. The local norm
realizations and their proof organization do not expose D5 private content. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ActualColumnRemainder
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.ActualColumnRemainder
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ActualColumnRemainder
open _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit

abbrev normSignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def normActual : Realization normSignature :=
  realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem normDependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [normActual, realize]

private theorem one_not_summable : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro hs
  have hz : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  norm_num at hz

def weighted_coupling_first_jet_error_arena : Arena where
  signature := normSignature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) {m : ℤ} (hm : A < |(m : ℝ)|),
    r.readout () () (couplingColumn c S v m - couplingFirstJet c S v m) ≤
      2 * arithmeticBoundaryBudget c * weightedHeadMass S v /
        (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - A))

private theorem weighted_coupling_first_jet_error_actual_law : weighted_coupling_first_jet_error_arena.Law normActual := by
  exact @weighted_coupling_first_jet_error

private theorem weighted_coupling_first_jet_error_rejected_law : ¬ weighted_coupling_first_jet_error_arena.Law normRejected := by
  intro hall
  have h := hall (c := 2) (by decide) (∅ : Finset ℤ) (fun _ => (0 : ℂ))
    (A := 0) (by norm_num) (by simp) (m := 1) (by norm_num)
  norm_num [weighted_coupling_first_jet_error_arena, normRejected, realize, weightedHeadMass] at h

def weighted_coupling_first_jet_error_family : Registration weighted_coupling_first_jet_error_arena
    (type_of% (@weighted_coupling_first_jet_error)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨weighted_coupling_first_jet_error_actual_law, normRejected, weighted_coupling_first_jet_error_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normRejected, ?_, rfl, weighted_coupling_first_jet_error_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := normDependence

noncomputable def registration_6 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@weighted_coupling_first_jet_error) (type_of% normActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualColumnRemainder.weighted_coupling_first_jet_error.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualColumnRemainder.weighted_coupling_first_jet_error_family
  realizationSource := none
  generated := false
  arena := .source ⟨weighted_coupling_first_jet_error_arena⟩
  objectArena := .source ⟨weighted_coupling_first_jet_error_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weighted_coupling_first_jet_error_arena ⟨weighted_coupling_first_jet_error_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualColumnRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def paired_first_jet_remainder_tail_arena : Arena where
  signature := normSignature
  Law r := ∀ {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) (hsep : A < (M : ℝ) + 1),
    Summable (fun j : ℕ =>
      r.readout () () (couplingColumn c S v ((M + j + 1 : ℕ) : ℤ) -
        couplingFirstJet c S v ((M + j + 1 : ℕ) : ℤ)) ^ 2 +
      ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ)) -
        couplingFirstJet c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    (∑' j : ℕ,
      (‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ) -
        couplingFirstJet c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ)) -
          couplingFirstJet c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
      pairedRemainderBudget c M A S v

private theorem paired_first_jet_remainder_tail_actual_law : paired_first_jet_remainder_tail_arena.Law normActual := by
  exact @paired_first_jet_remainder_tail

private theorem paired_first_jet_remainder_tail_rejected_law : ¬ paired_first_jet_remainder_tail_arena.Law normRejected := by
  intro hall
  have hs := (hall (c := 2) (M := 1) (by decide) (by decide)
    (∅ : Finset ℤ) (fun _ => (0 : ℂ)) (A := 0) (by norm_num) (by simp)
    (by norm_num)).1
  have hone : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [paired_first_jet_remainder_tail_arena, normRejected, realize, couplingColumn, couplingFirstJet] using hs
  exact one_not_summable hone

def paired_first_jet_remainder_tail_family : Registration paired_first_jet_remainder_tail_arena
    (type_of% (@paired_first_jet_remainder_tail)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨paired_first_jet_remainder_tail_actual_law, normRejected, paired_first_jet_remainder_tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normRejected, ?_, rfl, paired_first_jet_remainder_tail_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := normDependence

noncomputable def registration_7 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@paired_first_jet_remainder_tail) (type_of% normActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualColumnRemainder.paired_first_jet_remainder_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualColumnRemainder.paired_first_jet_remainder_tail_family
  realizationSource := none
  generated := false
  arena := .source ⟨paired_first_jet_remainder_tail_arena⟩
  objectArena := .source ⟨paired_first_jet_remainder_tail_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source paired_first_jet_remainder_tail_arena ⟨paired_first_jet_remainder_tail_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualColumnRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Weil.ZetaBridge.ActualColumnRemainder
