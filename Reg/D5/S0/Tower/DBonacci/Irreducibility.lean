import D5.S0.Tower.DBonacci.Irreducibility
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S0.Tower.DBonacci.Irreducibility
open Polynomial
open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace rootLocation
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature
  (fun _ _ q => X ^ q - ∑ i ∈ Finset.range q, X ^ i) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 2 ≤ q) {z : ℂ},
    (r.readout () () q).IsRoot z → (1 ≤ ‖z‖ ↔ z = (dbonacciPerronRoot q : ℂ))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 2 (by decide) (z := 1) (by simp [bad, realize])).mp (by norm_num)
  have hre := congrArg Complex.re he
  have hb := one_lt_dbonacciPerronRoot 2 (by decide)
  simp only [Complex.one_re, Complex.ofReal_re] at hre
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun p : ℂ[X] => p.coeff 0) he
  norm_num [actual, realize, Finset.sum_range_succ, pow_zero, pow_one,
    Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_zero] at hc
  simp only [pow_zero, pow_one, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_X_zero] at hc
  norm_num at hc

def evidence : Registration arena (type_of% @dbonacci_complex_root_location) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dbonacci_complex_root_location, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@dbonacci_complex_root_location) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S0.Tower.DBonacci.Irreducibility.rootLocation.unit
  realizationName := `Reg.D5.S0.Tower.DBonacci.Irreducibility.rootLocation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ q => X ^ q - ∑ i ∈ Finset.range q, X ^ i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.DBonacci.Irreducibility
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end rootLocation

namespace simpleRoot
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature
  (fun _ _ q => X ^ q - ∑ i ∈ Finset.range q, X ^ i) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 2 ≤ q),
    (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℂ[X]).IsRoot
        (dbonacciPerronRoot q : ℂ) ∧
    (r.readout () () q).derivative.eval (dbonacciPerronRoot q : ℂ) ≠ 0
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 2 (by decide)).2
  exact he (by simp [bad, realize])
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun p : ℂ[X] => p.coeff 0) he
  norm_num [actual, realize, Finset.sum_range_succ, pow_zero, pow_one,
    Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_zero] at hc
  simp only [pow_zero, pow_one, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_X_zero] at hc
  norm_num at hc

def evidence : Registration arena (type_of% @dbonacciPerronRoot_simple) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dbonacciPerronRoot_simple, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@dbonacciPerronRoot_simple) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S0.Tower.DBonacci.Irreducibility.simpleRoot.unit
  realizationName := `Reg.D5.S0.Tower.DBonacci.Irreducibility.simpleRoot.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ q => X ^ q - ∑ i ∈ Finset.range q, X ^ i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.DBonacci.Irreducibility
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end simpleRoot

namespace irreducible
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature
  (fun _ _ q => X ^ q - ∑ i ∈ Finset.range q, X ^ i) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 2 ≤ q),
    Irreducible (r.readout () () q) ∧
    Irreducible (X ^ q - ∑ i ∈ Finset.range q, X ^ i : ℚ[X])
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 2 (by decide)).1
  simpa [bad, realize] using he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun p : ℤ[X] => p.coeff 0) he
  norm_num [actual, realize, Finset.sum_range_succ, pow_zero, pow_one,
    Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_zero] at hc
  simp only [pow_zero, pow_one, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_X_zero] at hc
  norm_num at hc

def evidence : Registration arena (type_of% @dbonacci_irreducible) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dbonacci_irreducible, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@dbonacci_irreducible) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S0.Tower.DBonacci.Irreducibility.irreducible.unit
  realizationName := `Reg.D5.S0.Tower.DBonacci.Irreducibility.irreducible.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ q => X ^ q - ∑ i ∈ Finset.range q, X ^ i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.DBonacci.Irreducibility
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end irreducible

end Reg.D5.S0.Tower.DBonacci.Irreducibility
