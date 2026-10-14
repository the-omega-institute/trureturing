import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
open Finset

namespace Reg.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform

abbrev signature : Signature where
  Params := Σ _ : ℂ, Σ _ : ℂ, Σ _ : ℕ, ℕ
  State _ := ℕ → ℂ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i pars u =>
    if i then
      (-1 : ℂ) ^ pars.2.2.1 * ∑ m ∈ range (pars.2.2.1 + 1),
        ((Nat.factorial m * Nat.stirlingSecond pars.2.2.1 m : ℕ) : ℂ) *
          pars.1 ^ m * pars.2.1 ^ (pars.2.2.1 - m) * u (m + pars.2.2.2)
    else
      ∑ m ∈ range (pars.2.2.1 + 1),
        (-1 : ℂ) ^ m *
          ((Nat.factorial m * Nat.stirlingSecond (pars.2.2.1 + 1) (m + 1) : ℕ) : ℂ) *
          pars.2.1 ^ (pars.2.2.1 - m) * u (2 * m + pars.2.2.2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p q : ℂ) (ell c : ℕ) (u : ℕ → ℂ),
    (∀ n : ℕ, u (n + 2) = p * u (n + 1) + q * u n) →
    r.readout false ⟨p, q, ell, c⟩ u = r.readout true ⟨p, q, ell, c⟩ u

private noncomputable def bad (i : Bool) : Realization signature :=
  realize signature
    (fun j pars u => if j = i then actual.readout j pars u + 1 else actual.readout j pars u)
    (fun e => nomatch e)

private theorem bad_not_law (i : Bool) : ¬ arena.Law (bad i) := by
  intro h
  have hx := h 0 0 0 0 (fun _ => 0) (by intro n; simp)
  cases i <;>
    norm_num [bad, actual, realize, Nat.stirlingSecond_succ_succ] at hx <;> cases hx

noncomputable def registration : Registration arena (type_of% (@result)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, bad false, bad_not_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad i, ?_, rfl, bad_not_law i⟩
      intro j hj
      funext pars u
      simp only [bad, realize, if_neg hj]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨0, 0, 0, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    cases i <;> norm_num [actual, realize, Nat.stirlingSecond_succ_succ] }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.result)
    (type_of% (realize signature (fun i pars u =>
      if i then
        (-1 : ℂ) ^ pars.2.2.1 * ∑ m ∈ range (pars.2.2.1 + 1),
          ((Nat.factorial m * Nat.stirlingSecond pars.2.2.1 m : ℕ) : ℂ) *
            pars.1 ^ m * pars.2.1 ^ (pars.2.2.1 - m) * u (m + pars.2.2.2)
      else
        ∑ m ∈ range (pars.2.2.1 + 1),
          (-1 : ℂ) ^ m *
            ((Nat.factorial m * Nat.stirlingSecond (pars.2.2.1 + 1) (m + 1) : ℕ) : ℂ) *
            pars.2.1 ^ (pars.2.2.1 - m) * u (2 * m + pars.2.2.2))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i pars u =>
    if i then
      (-1 : ℂ) ^ pars.2.2.1 * ∑ m ∈ range (pars.2.2.1 + 1),
        ((Nat.factorial m * Nat.stirlingSecond pars.2.2.1 m : ℕ) : ℂ) *
          pars.1 ^ m * pars.2.1 ^ (pars.2.2.1 - m) * u (m + pars.2.2.2)
    else
      ∑ m ∈ range (pars.2.2.1 + 1),
        (-1 : ℂ) ^ m *
          ((Nat.factorial m * Nat.stirlingSecond (pars.2.2.1 + 1) (m + 1) : ℕ) : ℂ) *
          pars.2.1 ^ (pars.2.2.1 - m) * u (2 * m + pars.2.2.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
