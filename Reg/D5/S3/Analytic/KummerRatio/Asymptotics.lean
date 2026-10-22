import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KummerRatio.Asymptotics
import Reg.D5.S3.Analytic.KummerRatio.Series

/-! Observation of Kummer evaluations in the positive endpoint asymptotic. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.KummerRatio.Defs
open _root_.D5.S3.Analytic.KummerRatio.Asymptotics
open LeanInformationAudit Filter Topology

noncomputable section
namespace Reg.D5.S3.Analytic.KummerRatio.Asymptotics

abbrev signature := _root_.Reg.D5.S3.Analytic.KummerRatio.Series.signature
abbrev actual := _root_.Reg.D5.S3.Analytic.KummerRatio.Series.actual
abbrev rejected := _root_.Reg.D5.S3.Analytic.KummerRatio.Series.zeroReadout

def arena : Arena where
  signature := signature
  Law R := ∀ {s c : ℝ}, 0 < s → 0 < c →
    Tendsto (fun x : ℝ => Real.exp (-x) * x ^ (c - s) * R.readout () ⟨s, c⟩ x)
      atTop (𝓝 (Real.Gamma c / Real.Gamma s))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := @h 1 1 (by norm_num) (by norm_num)
  have hbad : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 1) := by
    simpa [rejected, Series.zeroReadout, realize] using hz
  have he := tendsto_nhds_unique (tendsto_const_nhds (x := (0 : ℝ))) hbad
  norm_num at he

def family : Registration arena (type_of% @tendsto_kummer_atTop) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tendsto_kummer_atTop, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Analytic.KummerRatio.Series.Zero.family.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tendsto_kummer_atTop) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Asymptotics.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Asymptotics.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Asymptotics
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms tendsto_kummer_atTop
#print axioms audit

end Reg.D5.S3.Analytic.KummerRatio.Asymptotics
end
