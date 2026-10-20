import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
open _root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform (pair)
open Finset Polynomial

namespace Reg.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform

namespace Connection

abbrev signature : Signature where
  Params := Σ _ : ℂ, Σ _ : ℂ, ℕ
  State _ := ℂ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Polynomial ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i pars value => if i then
      ∑ m ∈ range (pars.2.2 + 1), C (S value pars.1 pars.2.1 pars.2.2 m) * newton pars.2.1 pars.1 m
    else
      newton 0 value pars.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (alpha : ℂ) (b : ℂ) (a : ℂ) (n : ℕ), r.readout false ⟨b, a, n⟩ alpha = r.readout true ⟨b, a, n⟩ alpha

private noncomputable def bad (i : Bool) : Realization signature :=
  realize signature
    (fun j pars value => if j = i then actual.readout j pars value + 1 else actual.readout j pars value)
    (fun e => nomatch e)

private theorem bad_not_law (i : Bool) : ¬ arena.Law (bad i) := by
  intro h
  have positive : arena.Law actual := @_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.connection
  have ht := positive 0 1 0 2
  have hx := h 0 1 0 2
  cases i <;> simp [bad, realize] at hx
  · have hz : (1 : Polynomial ℂ) = 0 := by linear_combination hx - ht
    exact one_ne_zero hz
  · have hz : (1 : Polynomial ℂ) = 0 := by linear_combination ht - hx
    exact one_ne_zero hz

noncomputable def registration : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.connection)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.connection, bad false, bad_not_law false⟩
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
    refine ⟨⟨1, 0, 2⟩, 0, 1, ?_⟩
    have hv (j : Bool) (v : ℂ) :
        actual.readout j ⟨1, 0, 2⟩ v = newton 0 v 2 := by
      cases j
      · rfl
      · exact (_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.connection v 1 0 2).symm
    intro h
    rw [hv, hv] at h
    have hx := congrArg (Polynomial.eval 1) h
    norm_num [newton, Polynomial.eval_mul, Polynomial.eval_sub] at hx }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.connection)
    (type_of% (realize signature (fun i pars value => if i then
      ∑ m ∈ range (pars.2.2 + 1), C (S value pars.1 pars.2.1 pars.2.2 m) * newton pars.2.1 pars.1 m
    else
      newton 0 value pars.2.2) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.connection.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.Connection.registration
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
      ∑ m ∈ range (pars.2.2 + 1), C (S value pars.1 pars.2.1 pars.2.2 m) * newton pars.2.1 pars.1 m
    else
      newton 0 value pars.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
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

end Connection

namespace Reflection

abbrev signature : Signature where
  Params := Σ _ : ℂ, Σ _ : ℂ, ℕ
  State _ := ℂ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Polynomial ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i pars value => if i then
      C ((-1 : ℂ) ^ pars.2.2) * G (-pars.1) pars.2.1 (pars.2.1 - value) pars.2.2
    else
      (G pars.1 pars.2.1 value pars.2.2).comp (-C pars.2.1 - X)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (alpha : ℂ) (b : ℂ) (a : ℂ) (n : ℕ), r.readout false ⟨alpha, b, n⟩ a = r.readout true ⟨alpha, b, n⟩ a

private noncomputable def bad (i : Bool) : Realization signature :=
  realize signature
    (fun j pars value => if j = i then actual.readout j pars value + 1 else actual.readout j pars value)
    (fun e => nomatch e)

private theorem bad_not_law (i : Bool) : ¬ arena.Law (bad i) := by
  intro h
  have positive : arena.Law actual := @_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.reflection
  have ht := positive 0 1 0 1
  have hx := h 0 1 0 1
  cases i <;> simp [bad, realize] at hx
  · have hz : (1 : Polynomial ℂ) = 0 := by linear_combination hx - ht
    exact one_ne_zero hz
  · have hz : (1 : Polynomial ℂ) = 0 := by linear_combination ht - hx
    exact one_ne_zero hz

noncomputable def registration : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.reflection)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.reflection, bad false, bad_not_law false⟩
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
    refine ⟨⟨0, 1, 1⟩, 0, 1, ?_⟩
    intro h
    have hx := congrArg (Polynomial.eval 0) h
    cases i <;> norm_num [actual, realize, G, Polynomial.eval_comp] at hx }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.reflection)
    (type_of% (realize signature (fun i pars value => if i then
      C ((-1 : ℂ) ^ pars.2.2) * G (-pars.1) pars.2.1 (pars.2.1 - value) pars.2.2
    else
      (G pars.1 pars.2.1 value pars.2.2).comp (-C pars.2.1 - X)) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.reflection.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.Reflection.registration
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
      C ((-1 : ℂ) ^ pars.2.2) * G (-pars.1) pars.2.1 (pars.2.1 - value) pars.2.2
    else
      (G pars.1 pars.2.1 value pars.2.2).comp (-C pars.2.1 - X)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reflection

namespace Transform

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℂ, Σ _ : Polynomial ℂ, Σ _ : ℂ, Σ _ : ℂ, Σ _ : ℂ, Σ _ : ℕ, ℕ
  State _ := ℕ → ℂ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i pars value => (show ℂ from if i then
      (-1 : ℂ) ^ pars.2.2.2.2.2.2.1 * ∑ m ∈ range (pars.2.2.2.2.2.2.1 + 1), (Nat.factorial m : ℂ) * pars.2.2.2.2.1 ^ m * S (-pars.2.2.2.1) pars.2.2.2.2.1 (pars.2.2.2.2.1 - pars.2.2.2.2.2.1) pars.2.2.2.2.2.2.1 m * pars.2.1 ^ (pars.2.2.2.2.2.2.1 - m) * pair value pars.2.2.2.2.2.2.2 (pars.2.2.1 ^ m)
    else
      ∑ m ∈ range (pars.2.2.2.2.2.2.1 + 1), (-1 : ℂ) ^ m * (Nat.factorial m : ℂ) * pars.2.2.2.2.1 ^ m * S pars.2.2.2.1 pars.2.2.2.2.1 pars.2.2.2.2.2.1 pars.2.2.2.2.2.2.1 m * pars.2.1 ^ (pars.2.2.2.2.2.2.1 - m) * value (pars.1 * m + pars.2.2.2.2.2.2.2))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d : ℕ) (q : ℂ) (A : Polynomial ℂ) (alpha : ℂ) (b : ℂ) (a : ℂ) (ell : ℕ) (c : ℕ) (u : ℕ → ℂ) (hd : 1 ≤ d) (hdegree : A.degree < (d : WithBot ℕ)) (hzero : A.eval 0 = 0) (hu : ∀ n : ℕ, u (n + d) = q * u n + ∑ j ∈ A.support, A.coeff j * u (n + j)), @Eq ℂ (r.readout false ⟨d, q, A, alpha, b, a, ell, c⟩ u) (r.readout true ⟨d, q, A, alpha, b, a, ell, c⟩ u)

private noncomputable def bad (i : Bool) : Realization signature :=
  realize signature
    (fun j pars value => if j = i then actual.readout j pars value + 1 else actual.readout j pars value)
    (fun e => nomatch e)

private theorem bad_not_law (i : Bool) : ¬ arena.Law (bad i) := by
  intro h
  have positive : arena.Law actual := @_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.result
  have ht := positive 1 1 0 0 1 1 1 0 (fun _ => 1) (by omega) (by simp) (by simp) (by intro n; simp)
  have hx := h 1 1 0 0 1 1 1 0 (fun _ => 1) (by omega) (by simp) (by simp) (by intro n; simp)
  cases i <;> simp [bad, realize] at hx
  · have hz : (1 : ℂ) = 0 := by linear_combination hx - ht
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination ht - hx
    exact one_ne_zero hz

noncomputable def registration : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.result)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.result, bad false, bad_not_law false⟩
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
    refine ⟨⟨1, 1, 0, 0, 1, 0, 1, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hp (u : ℕ → ℂ) : pair u 0 (1 : Polynomial ℂ) = u 0 := by
      simpa using _root_.D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform.pair_monomial u 0 0 1
    cases i <;> norm_num [actual, realize, S, connectionRow, hp, Finset.sum_range_succ] }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.result)
    (type_of% (realize signature (fun i pars value => (show ℂ from if i then
      (-1 : ℂ) ^ pars.2.2.2.2.2.2.1 * ∑ m ∈ range (pars.2.2.2.2.2.2.1 + 1), (Nat.factorial m : ℂ) * pars.2.2.2.2.1 ^ m * S (-pars.2.2.2.1) pars.2.2.2.2.1 (pars.2.2.2.2.1 - pars.2.2.2.2.2.1) pars.2.2.2.2.2.2.1 m * pars.2.1 ^ (pars.2.2.2.2.2.2.1 - m) * pair value pars.2.2.2.2.2.2.2 (pars.2.2.1 ^ m)
    else
      ∑ m ∈ range (pars.2.2.2.2.2.2.1 + 1), (-1 : ℂ) ^ m * (Nat.factorial m : ℂ) * pars.2.2.2.2.1 ^ m * S pars.2.2.2.1 pars.2.2.2.2.1 pars.2.2.2.2.2.1 pars.2.2.2.2.2.2.1 m * pars.2.1 ^ (pars.2.2.2.2.2.2.1 - m) * value (pars.1 * m + pars.2.2.2.2.2.2.2))) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.Transform.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i pars value => (show ℂ from if i then
      (-1 : ℂ) ^ pars.2.2.2.2.2.2.1 * ∑ m ∈ range (pars.2.2.2.2.2.2.1 + 1), (Nat.factorial m : ℂ) * pars.2.2.2.2.1 ^ m * S (-pars.2.2.2.1) pars.2.2.2.2.1 (pars.2.2.2.2.1 - pars.2.2.2.2.2.1) pars.2.2.2.2.2.2.1 m * pars.2.1 ^ (pars.2.2.2.2.2.2.1 - m) * pair value pars.2.2.2.2.2.2.2 (pars.2.2.1 ^ m)
    else
      ∑ m ∈ range (pars.2.2.2.2.2.2.1 + 1), (-1 : ℂ) ^ m * (Nat.factorial m : ℂ) * pars.2.2.2.2.1 ^ m * S pars.2.2.2.1 pars.2.2.2.2.1 pars.2.2.2.2.2.1 pars.2.2.2.2.2.2.1 m * pars.2.1 ^ (pars.2.2.2.2.2.2.1 - m) * value (pars.1 * m + pars.2.2.2.2.2.2.2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Transform

namespace Bases

inductive Role
  | rt | rtDelta | tr | trDelta | connection | product
  deriving DecidableEq, Inhabited

instance : Fintype Role where
  elems := {.rt, .rtDelta, .tr, .trDelta, .connection, .product}
  complete := by
    intro i
    cases i <;> simp

abbrev signature : Signature where
  Params := Σ _ : ℂ, Σ _ : ℂ, Σ _ : ℂ, ℕ
  State _ := ℕ
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i p k => match i with
    | .rt => ∑ j ∈ range (p.2.2.2 + 1), T p.2.2.1 p.2.1 p.2.2.2 j * R p.2.2.1 p.2.1 j k
    | .rtDelta => (X ^ p.2.2.2 : Polynomial ℂ).coeff k
    | .tr => ∑ j ∈ range (p.2.2.2 + 1), R p.2.2.1 p.2.1 p.2.2.2 j * T p.2.2.1 p.2.1 j k
    | .trDelta => (X ^ p.2.2.2 : Polynomial ℂ).coeff k
    | .connection => S p.1 p.2.1 p.2.2.1 p.2.2.2 k
    | .product => ∑ j ∈ range (p.2.2.2 + 1), R 0 p.1 p.2.2.2 j * T p.2.2.1 p.2.1 j k)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (alpha b a : ℂ) (n k : ℕ),
    r.readout .rt ⟨alpha, b, a, n⟩ k = r.readout .rtDelta ⟨alpha, b, a, n⟩ k ∧
    r.readout .tr ⟨alpha, b, a, n⟩ k = r.readout .trDelta ⟨alpha, b, a, n⟩ k ∧
    r.readout .connection ⟨alpha, b, a, n⟩ k = r.readout .product ⟨alpha, b, a, n⟩ k

private noncomputable def bad (i : Role) : Realization signature :=
  realize signature
    (fun j pars k => if j = i then actual.readout j pars k + 1 else actual.readout j pars k)
    (fun e => nomatch e)

private theorem bad_not_law (i : Role) : ¬ arena.Law (bad i) := by
  intro h
  have positive : arena.Law actual := @_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.basis_change
  have ht := positive 0 1 0 1 1
  have hx := h 0 1 0 1 1
  cases i <;> simp [bad, realize] at hx
  · have hz : (1 : ℂ) = 0 := by linear_combination hx.1 - ht.1
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination ht.1 - hx.1
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination hx.2.1 - ht.2.1
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination ht.2.1 - hx.2.1
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination hx.2.2 - ht.2.2
    exact one_ne_zero hz
  · have hz : (1 : ℂ) = 0 := by linear_combination ht.2.2 - hx.2.2
    exact one_ne_zero hz

noncomputable def registration : Registration arena (type_of% (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.basis_change)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.basis_change, bad .rt, bad_not_law .rt⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad i, ?_, rfl, bad_not_law i⟩
      intro j hj
      funext pars k
      simp only [bad, realize, if_neg hj]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨0, 1, 0, 1⟩, 0, 1, ?_⟩
    cases i <;> norm_num [actual, realize, T, R, S, connectionRow, newton, Finset.sum_range_succ] }

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.basis_change)
    (type_of% (realize signature (fun i p k => match i with
    | .rt => ∑ j ∈ range (p.2.2.2 + 1), T p.2.2.1 p.2.1 p.2.2.2 j * R p.2.2.1 p.2.1 j k
    | .rtDelta => (X ^ p.2.2.2 : Polynomial ℂ).coeff k
    | .tr => ∑ j ∈ range (p.2.2.2 + 1), R p.2.2.1 p.2.1 p.2.2.2 j * T p.2.2.1 p.2.1 j k
    | .trDelta => (X ^ p.2.2.2 : Polynomial ℂ).coeff k
    | .connection => S p.1 p.2.1 p.2.2.1 p.2.2.2 k
    | .product => ∑ j ∈ range (p.2.2.2 + 1), R 0 p.1 p.2.2.2 j * T p.2.2.1 p.2.1 j k)
    (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.basis_change.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform.Bases.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i p k => match i with
    | .rt => ∑ j ∈ range (p.2.2.2 + 1), T p.2.2.1 p.2.1 p.2.2.2 j * R p.2.2.1 p.2.1 j k
    | .rtDelta => (X ^ p.2.2.2 : Polynomial ℂ).coeff k
    | .tr => ∑ j ∈ range (p.2.2.2 + 1), R p.2.2.1 p.2.1 p.2.2.2 j * T p.2.2.1 p.2.1 j k
    | .trDelta => (X ^ p.2.2.2 : Polynomial ℂ).coeff k
    | .connection => S p.1 p.2.1 p.2.2.1 p.2.2.2 k
    | .product => ∑ j ∈ range (p.2.2.2 + 1), R 0 p.1 p.2.2.2 j * T p.2.2.1 p.2.1 j k)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Bases

end Reg.D5.S3.Combinatorics.BinomialBases.MonicAnnihilatorStirlingTransform
