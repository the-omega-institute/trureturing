import D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! The logarithm of the actual compact factorial excess is a real readout
on the full family of natural compact parameters. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic

open _root_.D5.S3.Arith.FactorialRatio.Compression.SharpLoss
open _root_.D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Quadratic

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ r s => Real.log (compactExcess r s : ℝ))
    (fun e => nomatch e)

noncomputable def rejected (role : Fin 2) : Realization signature :=
  realize signature (fun i r s =>
    if i = role then
      if role = 0 then -1 else (12 + 19 * Real.log 4) * (r : ℝ) ^ 2 + 1
    else Real.log (compactExcess r s : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s : ℕ), 2 ≤ r → s < r ^ 2 →
    0 ≤ R.readout 0 r s ∧
      R.readout 1 r s ≤ (12 + 19 * Real.log 4) * (r : ℝ) ^ 2

private theorem rejected_law (role : Fin 2) : ¬ arena.Law (rejected role) := by
  intro h
  have hh := h 2 0 (by decide) (by decide)
  fin_cases role
  · have hlo := hh.1
    change (0 : ℝ) ≤ -1 at hlo
    norm_num at hlo
  · have hhi := hh.2
    change (12 + 19 * Real.log 4) * (2 : ℝ) ^ 2 + 1 ≤
      (12 + 19 * Real.log 4) * (2 : ℝ) ^ 2 at hhi
    linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨3, 0, 2, ?_⟩
  change Real.log (compactExcess 3 0 : ℝ) ≠ Real.log (compactExcess 3 2 : ℝ)
  have hzero : compactExcess 3 0 = 1 := by decide
  have htwo : compactExcess 3 2 = 2 := by decide
  rw [hzero, htwo, Nat.cast_one, Nat.cast_ofNat, Real.log_one]
  exact (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))).symm

noncomputable def family : Registration arena (type_of% @uniform_quadratic_log_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_quadratic_log_bound, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro i hi
      funext r s
      simp [actual, rejected, realize, hi]
    · intro e
      exact nomatch e
  dependence := dependence

end Quadratic

noncomputable def quadraticAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@uniform_quadratic_log_bound) (Realization Quadratic.signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic.uniform_quadratic_log_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic.Quadratic.family
  realizationSource := none
  generated := false
  arena := .source ⟨Quadratic.arena⟩
  objectArena := .source ⟨Quadratic.arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source Quadratic.arena ⟨Quadratic.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Quadratic.signature
    (fun _ r s => Real.log (compactExcess r s : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "fn", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Compression.UniformQuadratic
