import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedTailComparison
import Reg.Support.DependentFamily

/-! The proposed profile is evaluated at the integer position in the conclusion. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedTailComparison


open _root_.D5.S1.Words.Patterns.Separable.OccupiedTailComparison
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := ℤ → ℝ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f x => f x) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ x => |(x : ℝ)| + 1) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R :=
    ∀ (f : ℤ → ℝ) (F A B : ℝ) (N : ℕ)
    (_hF : 0 < F) (_hA : 0 < A) (_hB : 0 ≤ B)
    (_hf : ∀ x, 0 ≤ f x) (_hbound : ∀ x, f x ≤ F)
    (_hvanish : Summable fun x => (f x) ^ 2)
    (_hgain : ∀ x : ℤ, (N : ℤ) < |x| →
      A * (f x) ^ 2 ≤ ∑' n : ℕ, kernelWeight n *
        (f (x + (n + 1 : ℤ)) + f (x - (n + 1 : ℤ)) - 2 * f x))
    (_hcost : ∀ x : ℤ, (N : ℤ) < |x| →
      (∑' n : ℕ, (lossWeight n * (f (x + (n + 1 : ℤ))) ^ 2 +
        lossWeight n * (f (x - (n + 1 : ℤ))) ^ 2)) ≤ B * (f x) ^ 2),
    ∃ t : ℝ, 0 < t ∧ ∀ x : ℤ, t * R.readout () f x ≤ rawOccupation x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (fun _ => 0) 1 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by simp) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨t, ht, hbound⟩ := hz
  obtain ⟨n, hn⟩ := exists_nat_gt (ceiling / t)
  have hN : ceiling < (n : ℝ) * t := (div_lt_iff₀ ht).mp hn
  have hc := actual_occupation_subsolution_comparison.2.2.2.2.1 (n : ℤ)
  have hh := hbound (n : ℤ)
  change t * (|((n : ℤ) : ℝ)| + 1) ≤ rawOccupation (n : ℤ) at hh
  rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)] at hh
  nlinarith only [hh, hc.2, hN, ht]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨fun x : ℤ => (x : ℝ), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @actual_lower_from_tail_estimates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_lower_from_tail_estimates, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_lower_from_tail_estimates) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedTailComparison.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedTailComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f x => f x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedTailComparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedTailComparison
