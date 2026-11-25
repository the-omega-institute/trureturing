import D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! The two location and two value occurrences of the entropy minimum bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum

open Set
open _root_.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
open _root_.D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun i _ t => if i.val < 2 then t else entropyIntegral t)
    (fun e => nomatch e)

def rejected (role : Fin 4) : Realization signature :=
  realize signature (fun i p t =>
    if i = role then
      if role.val = 0 ∨ role.val = 3 then -100 else 100
    else actual.readout i p t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
    (∀ v ∈ Icc (0 : ℝ) 1, entropyIntegral t ≤ entropyIntegral v) →
    (7607566 / 10000000 : ℝ) ≤ R.readout 0 () t ∧
      R.readout 1 () t ≤ (76075661 / 100000000 : ℝ) ∧
      (55020623 / 100000000 : ℝ) < -R.readout 2 () t ∧
      -R.readout 3 () t < (55020624 / 100000000 : ℝ)

private theorem rejected_law (role : Fin 4) : ¬ arena.Law (rejected role) := by
  intro h
  obtain ⟨t, ht⟩ := entropy_profile.2.2.2.2.1.exists
  have hh := h t ht.1 ht.2
  fin_cases role
  · have hbad := hh.1
    change (7607566 / 10000000 : ℝ) ≤ -100 at hbad
    norm_num at hbad
  · have hbad := hh.2.1
    change (100 : ℝ) ≤ 76075661 / 100000000 at hbad
    norm_num at hbad
  · have hbad := hh.2.2.1
    change (55020623 / 100000000 : ℝ) < -100 at hbad
    norm_num at hbad
  · have hbad := hh.2.2.2
    change -(-100 : ℝ) < 55020624 / 100000000 at hbad
    norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  fin_cases role
  · refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num
  · refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num
  · refine ⟨(), 0, 1, ?_⟩
    change entropyIntegral 0 ≠ entropyIntegral 1
    rw [entropy_profile.2.1, entropy_profile.2.2.1]
    norm_num
  · refine ⟨(), 0, 1, ?_⟩
    change entropyIntegral 0 ≠ entropyIntegral 1
    rw [entropy_profile.2.1, entropy_profile.2.2.1]
    norm_num

def family : Registration arena (type_of% @entropy_minimum_enclosure) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_minimum_enclosure, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro i hi
      funext p t
      simp [rejected, realize, hi]
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entropy_minimum_enclosure) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum.entropy_minimum_enclosure.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i _ t => if i.val < 2 then t else entropyIntegral t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum
