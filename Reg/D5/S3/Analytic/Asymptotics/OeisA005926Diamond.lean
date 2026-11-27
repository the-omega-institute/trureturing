import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Analytic.Asymptotics.OeisA005926Diamond

namespace Reg.D5.S3.Analytic.Asymptotics.OeisA005926Diamond

open LeanInformationAudit Filter
open _root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Topology BigOperators

noncomputable section

namespace Limit

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ _ N => (∑ n ∈ Finset.Icc 1 N, (thetaCoefficient n : ℝ)) / (N : ℝ) ^ (3 / 2 : ℝ))
  (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := Tendsto (fun N : ℕ => R.readout () () N) atTop (𝓝 (Real.pi / 48))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (Real.pi / 48)) := h
  exact (ne_of_gt (div_pos Real.pi_pos (by norm_num)))
    (tendsto_nhds_unique h' tendsto_const_nhds)

def family : Registration arena (type_of% @_root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    cases i
    by_contra! h
    have hz : actual.readout () () 0 = 0 := by simp [actual, realize]
    apply rejected_law
    have he : (fun N : ℕ => actual.readout () () N) = fun _ => 0 := by
      funext N
      exact (h () N (0 : ℕ)).trans hz
    have hl : Tendsto (fun N : ℕ => actual.readout () () N) atTop (𝓝 (Real.pi / 48)) :=
      _root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.result
    rw [he] at hl
    exact hl

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond.result.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.Limit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ N => (∑ n ∈ Finset.Icc 1 N, (thetaCoefficient n : ℝ)) / (N : ℝ) ^ (3 / 2 : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

private theorem some_coefficient_ne_zero : ∃ n, thetaCoefficient n ≠ 0 := by
  by_contra! h
  have he : (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, (thetaCoefficient n : ℝ)) / (N : ℝ) ^ (3 / 2 : ℝ)) =
      fun _ => 0 := by
    funext N
    simp [h]
  have hl := _root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.result
  rw [he] at hl
  exact (ne_of_gt (div_pos Real.pi_pos (by norm_num)))
    (tendsto_nhds_unique hl tendsto_const_nhds)

namespace Coefficient

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => thetaCoefficient n) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence (i : signature.Role) :
    ∃ p x y, actual.readout i p x ≠ actual.readout i p y := by
  obtain ⟨n, hn⟩ := some_coefficient_ne_zero
  refine ⟨(), n, 0, ?_⟩
  change thetaCoefficient n ≠ thetaCoefficient 0
  rwa [theta_coefficient_of_lt_three 0 (by decide)]

namespace Initial

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, n < 3 → R.readout () () n = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Int.one_ne_zero (h 0 (by decide))

def family : Registration arena (type_of% @theta_coefficient_of_lt_three) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨theta_coefficient_of_lt_three, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Coefficient.dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.theta_coefficient_of_lt_three) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond.theta_coefficient_of_lt_three.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.Coefficient.Initial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => thetaCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Initial

namespace Shell

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n = (2 * Nat.card (latticeShell n) : ℕ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := theta_coefficient_lattice 0
  rw [theta_coefficient_of_lt_three 0 (by decide)] at ha
  exact Int.one_ne_zero ((h 0).trans ha.symm)

def family : Registration arena (type_of% @theta_coefficient_lattice) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨theta_coefficient_lattice, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Coefficient.dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.theta_coefficient_lattice) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond.theta_coefficient_lattice.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.Coefficient.Shell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => thetaCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Shell

end Coefficient

namespace Cutoff

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature := realize signature
  (fun _ _ N => ∑ n ∈ Finset.Icc 1 N, thetaCoefficient n) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, R.readout () () N = (2 * Nat.card (latticeCut N) : ℕ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := theta_inclusive_cutoff 0
  have hzero : (∑ n ∈ Finset.Icc 1 0, thetaCoefficient n) = 0 := by simp
  exact Int.one_ne_zero ((h 0).trans (ha.symm.trans hzero))

def family : Registration arena (type_of% @theta_inclusive_cutoff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨theta_inclusive_cutoff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    cases i
    by_contra! h
    have hz : actual.readout () () 0 = 0 := by simp [actual, realize]
    have he : (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, (thetaCoefficient n : ℝ)) / (N : ℝ) ^ (3 / 2 : ℝ)) =
        fun _ => 0 := by
      funext N
      rw [← Int.cast_sum]
      have hx := (h () N (0 : ℕ)).trans hz
      change (∑ n ∈ Finset.Icc 1 N, thetaCoefficient n) = 0 at hx
      simp [hx]
    have hl := _root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.result
    rw [he] at hl
    exact (ne_of_gt (div_pos Real.pi_pos (by norm_num)))
      (tendsto_nhds_unique hl tendsto_const_nhds)

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.theta_inclusive_cutoff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond.theta_inclusive_cutoff.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.OeisA005926Diamond.Cutoff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ N => ∑ n ∈ Finset.Icc 1 N, thetaCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.OeisA005926Diamond
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cutoff

end

end Reg.D5.S3.Analytic.Asymptotics.OeisA005926Diamond
