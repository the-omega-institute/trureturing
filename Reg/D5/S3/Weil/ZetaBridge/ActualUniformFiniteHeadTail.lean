import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail

open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit

abbrev normSignature : Signature.{0, 0, 0, 0, 0} where
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
  realize normSignature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

private theorem normDependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [normActual, realize]

def actual_finite_head_uniform_tail_lower_arena : Arena where
  signature := normSignature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c) (S : Finset ℤ) (hS : S.Nonempty),
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ v : ℤ → ℂ, ∀ N : ℕ, N0 ≤ N →
      Summable (fun j : ℕ =>
        (r.readout () () (couplingColumn c S v ((N + j + 1 : ℕ) : ℤ))) ^ 2 +
          ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
      C * (∑ n ∈ S, ‖v n‖ ^ 2) / ((N : ℝ) + 1) ^ (2 * S.card - 1) ≤
        ∑' j : ℕ,
          (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
            ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2)

private theorem actual_law : actual_finite_head_uniform_tail_lower_arena.Law normActual := by
  exact @_root_.D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower

private theorem rejected_law : ¬ actual_finite_head_uniform_tail_lower_arena.Law normRejected := by
  intro hall
  obtain ⟨C, hC, N0, hN⟩ := hall (c := 2) (by decide) ({0} : Finset ℤ) (by simp)
  let v : ℤ → ℂ := fun _ => 0
  let f : ℕ → ℝ := fun j => (1 : ℝ) ^ 2 +
    ‖couplingColumn 2 ({0} : Finset ℤ) v (-((N0 + j + 1 : ℕ) : ℤ))‖ ^ 2
  have hs : Summable f := (hN v N0 le_rfl).1
  have hnonneg (j : ℕ) : 0 ≤ f j := by dsimp [f]; positivity
  have hone (j : ℕ) : (1 : ℝ) ≤ f j := by
    simp [f, v, couplingColumn]
  obtain ⟨r, hr⟩ := exists_nat_gt (∑' j : ℕ, f j)
  have hlower : (r : ℝ) ≤ ∑ j ∈ Finset.range r, f j := by
    calc
      (r : ℝ) = ∑ _j ∈ Finset.range r, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hone j)
  have hupper : (∑ j ∈ Finset.range r, f j) ≤ ∑' j : ℕ, f j :=
    Summable.sum_le_tsum (Finset.range r) (fun j _ => hnonneg j) hs
  exact (not_le_of_gt hr) (hlower.trans hupper)

def actual_finite_head_uniform_tail_lower_family :
    Registration actual_finite_head_uniform_tail_lower_arena
      (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨actual_law, normRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normRejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := normDependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower)
    (type_of% normActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower_family
  realizationSource := none
  generated := false
  arena := .source ⟨actual_finite_head_uniform_tail_lower_arena⟩
  objectArena := .source ⟨actual_finite_head_uniform_tail_lower_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actual_finite_head_uniform_tail_lower_arena
    ⟨actual_finite_head_uniform_tail_lower_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body",
        "body", "body", "body", "fn", "arg", "fn", "arg", "body",
        "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail
