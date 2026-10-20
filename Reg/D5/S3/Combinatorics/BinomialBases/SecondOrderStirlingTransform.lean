import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
open Finset Polynomial

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
  realize signature (fun i pars u => (show ℂ from
    if i then
      (-1 : ℂ) ^ pars.2.2.1 * ∑ m ∈ range (pars.2.2.1 + 1),
        ((Nat.factorial m * Nat.stirlingSecond pars.2.2.1 m : ℕ) : ℂ) *
          pars.1 ^ m * pars.2.1 ^ (pars.2.2.1 - m) * u (m + pars.2.2.2)
    else
      ∑ m ∈ range (pars.2.2.1 + 1),
        (-1 : ℂ) ^ m *
          ((Nat.factorial m * Nat.stirlingSecond (pars.2.2.1 + 1) (m + 1) : ℕ) : ℂ) *
          pars.2.1 ^ (pars.2.2.1 - m) * u (2 * m + pars.2.2.2)))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p q : ℂ) (ell c : ℕ) (u : ℕ → ℂ),
    (∀ n : ℕ, u (n + 2) = p * u (n + 1) + q * u n) →
    @Eq ℂ (r.readout false ⟨p, q, ell, c⟩ u) (r.readout true ⟨p, q, ell, c⟩ u)

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
    (type_of% (realize signature (fun i pars u => (show ℂ from
      if i then
        (-1 : ℂ) ^ pars.2.2.1 * ∑ m ∈ range (pars.2.2.1 + 1),
          ((Nat.factorial m * Nat.stirlingSecond pars.2.2.1 m : ℕ) : ℂ) *
            pars.1 ^ m * pars.2.1 ^ (pars.2.2.1 - m) * u (m + pars.2.2.2)
      else
        ∑ m ∈ range (pars.2.2.1 + 1),
          (-1 : ℂ) ^ m *
            ((Nat.factorial m * Nat.stirlingSecond (pars.2.2.1 + 1) (m + 1) : ℕ) : ℂ) *
            pars.2.1 ^ (pars.2.2.1 - m) * u (2 * m + pars.2.2.2)))
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
  readout := some (realize signature (fun i pars u => (show ℂ from
    if i then
      (-1 : ℂ) ^ pars.2.2.1 * ∑ m ∈ range (pars.2.2.1 + 1),
        ((Nat.factorial m * Nat.stirlingSecond pars.2.2.1 m : ℕ) : ℂ) *
          pars.1 ^ m * pars.2.1 ^ (pars.2.2.1 - m) * u (m + pars.2.2.2)
    else
      ∑ m ∈ range (pars.2.2.1 + 1),
        (-1 : ℂ) ^ m *
          ((Nat.factorial m * Nat.stirlingSecond (pars.2.2.1 + 1) (m + 1) : ℕ) : ℂ) *
          pars.2.1 ^ (pars.2.2.1 - m) * u (2 * m + pars.2.2.2)))
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

namespace Monomial

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℂ
  State _ := ℕ → ℂ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i pars value => if i then
      pars.2.2 * value (pars.2.1 + pars.1)
    else
      pair value pars.1 (C pars.2.2 * X ^ pars.2.1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : ℕ → ℂ) (c : ℕ) (k : ℕ) (a : ℂ), r.readout false ⟨c, k, a⟩ u = r.readout true ⟨c, k, a⟩ u

private noncomputable def bad (i : Bool) : Realization signature :=
  realize signature
    (fun j pars value => if j = i then actual.readout j pars value + 1 else actual.readout j pars value)
    (fun e => nomatch e)

private theorem bad_not_law (i : Bool) : ¬ arena.Law (bad i) := by
  intro h
  have positive : arena.Law actual := @_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_monomial
  have ht := positive (fun _ => 1) 0 0 1
  have hx := h (fun _ => 1) 0 0 1
  cases i <;> simp [bad, realize] at hx
  · have hz : (1 : ℂ) = 0 := by linear_combination hx - ht
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination ht - hx
    exact one_ne_zero hz

noncomputable def registration : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_monomial)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_monomial, bad false, bad_not_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad i, ?_, rfl, bad_not_law i⟩
      intro j hj
      funext pars value
      simp only [bad, realize, if_neg hj]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨0, 0, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    cases i <;> norm_num [actual, realize, pair, Polynomial.lsum, Polynomial.sum_def] }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_monomial)
    (type_of% (realize signature (fun i pars value => if i then
      pars.2.2 * value (pars.2.1 + pars.1)
    else
      pair value pars.1 (C pars.2.2 * X ^ pars.2.1)) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_monomial.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.Monomial.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i pars value => if i then
      pars.2.2 * value (pars.2.1 + pars.1)
    else
      pair value pars.1 (C pars.2.2 * X ^ pars.2.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Monomial

namespace Scalar

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℂ, Polynomial ℂ
  State _ := ℕ → ℂ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i pars value => if i then
      pars.2.1 * pair value pars.1 pars.2.2
    else
      pair value pars.1 (C pars.2.1 * pars.2.2)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : ℕ → ℂ) (c : ℕ) (a : ℂ) (f : Polynomial ℂ), r.readout false ⟨c, a, f⟩ u = r.readout true ⟨c, a, f⟩ u

private noncomputable def bad (i : Bool) : Realization signature :=
  realize signature
    (fun j pars value => if j = i then actual.readout j pars value + 1 else actual.readout j pars value)
    (fun e => nomatch e)

private theorem bad_not_law (i : Bool) : ¬ arena.Law (bad i) := by
  intro h
  have positive : arena.Law actual := @_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_scalar
  have ht := positive (fun _ => 1) 0 1 1
  have hx := h (fun _ => 1) 0 1 1
  cases i <;> simp [bad, realize] at hx
  · have hz : (1 : ℂ) = 0 := by linear_combination hx - ht
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination ht - hx
    exact one_ne_zero hz

noncomputable def registration : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_scalar)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_scalar, bad false, bad_not_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad i, ?_, rfl, bad_not_law i⟩
      intro j hj
      funext pars value
      simp only [bad, realize, if_neg hj]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨0, 1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hp (u : ℕ → ℂ) : pair u 0 (1 : Polynomial ℂ) = u 0 := by
      simpa using pair_monomial u 0 0 1
    cases i <;> norm_num [actual, realize, hp] }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_scalar)
    (type_of% (realize signature (fun i pars value => if i then
      pars.2.1 * pair value pars.1 pars.2.2
    else
      pair value pars.1 (C pars.2.1 * pars.2.2)) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_scalar.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.Scalar.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i pars value => if i then
      pars.2.1 * pair value pars.1 pars.2.2
    else
      pair value pars.1 (C pars.2.1 * pars.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Scalar

end Reg.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
