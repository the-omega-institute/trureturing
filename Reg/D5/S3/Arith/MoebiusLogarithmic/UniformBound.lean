import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.MoebiusLogarithmic.UniformBound
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.MoebiusLogarithmic
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.MoebiusLogarithmic.UniformBound

private theorem distinct_base_values : coprimeLogSum 1 1 ≠ coprimeLogSum 1 2 := by
  have hzero : coprimeLogSum 1 1 = 0 := by norm_num [coprimeLogSum]
  have htwo : coprimeLogSum 1 2 = Real.log 2 := by
    norm_num [coprimeLogSum, show Finset.Ioc 0 2 = {1, 2} by decide]
  rw [hzero, htwo]
  exact (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))).symm

namespace Base

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x => coprimeLogSum 1 x) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, 1 ≤ x →
    0 ≤ R.readout () () x ∧ R.readout () () x ≤ 2 * (1 - 1 / x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by norm_num)
  norm_num [rejected, realize] at hb

def registration : Registration arena
    (∀ x : ℝ, 1 ≤ x →
    0 ≤ coprimeLogSum 1 x ∧ coprimeLogSum 1 x ≤ 2 * (1 - 1 / x)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨logarithmic_base_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      cases e
  dependence := by
    intro i
    cases i
    exact ⟨(), (1 : ℝ), (2 : ℝ), distinct_base_values⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.MoebiusLogarithmic.logarithmic_base_bound)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ _ x => coprimeLogSum 1 x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.MoebiusLogarithmic.logarithmic_base_bound.__information_unit,
  realizationName := `Reg.D5.S3.Arith.MoebiusLogarithmic.UniformBound.Base.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ x => coprimeLogSum 1 x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.MoebiusLogarithmic.UniformBound,
    definition := none, coordinates := #[],
    readouts := #[
      { path := #["body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration
end Base

namespace Uniform

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ q x => coprimeLogSum q x) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (x : ℝ), 1 ≤ q → 0 < x →
    0 ≤ R.readout () q x ∧ R.readout () q x ≤ 2 * q / Nat.totient q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1 (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

def registration : Registration arena
    (∀ (q : ℕ) (x : ℝ), 1 ≤ q → 0 < x →
    0 ≤ coprimeLogSum q x ∧ coprimeLogSum q x ≤ 2 * q / Nat.totient q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coprime_log_uniform_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      cases e
  dependence := by
    intro i
    cases i
    exact ⟨(1 : ℕ), (1 : ℝ), (2 : ℝ), distinct_base_values⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.MoebiusLogarithmic.coprime_log_uniform_bound)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ q x => coprimeLogSum q x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.MoebiusLogarithmic.coprime_log_uniform_bound.__information_unit,
  realizationName := `Reg.D5.S3.Arith.MoebiusLogarithmic.UniformBound.Uniform.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ q x => coprimeLogSum q x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.MoebiusLogarithmic.UniformBound,
    definition := none, coordinates := #[0],
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration
end Uniform

end Reg.D5.S3.Arith.MoebiusLogarithmic.UniformBound
