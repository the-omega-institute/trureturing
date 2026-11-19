import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
import Reg.Support.SingleDependentReadout

noncomputable section
open Set Filter Topology LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm

namespace Normalization

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ x : ℝ}, 1 < x → ∀ {n : ℕ}, 1 ≤ n →
    R.readout () () (lcmPowerF κ x n) (normalizedF κ x ((x ^ n)⁻¹))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (κ := 2) (x := 2) (by norm_num) (n := 1) (by norm_num)

def family : Registration arena (type_of% @lcmPowerF_normalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lcmPowerF_normalized, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have hh := congrFun heq 0
    norm_num [actual, realize] at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lcmPowerF_normalized) (Realization signature) Unit Unit where
  unitName := `LcmPowerLeadingTerm.lcmPowerF_normalized.unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm.Normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalization

namespace LeadingLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ κ x => coefficient κ x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ x : ℝ}, 1 < κ → 1 < x →
    Tendsto (fun n : ℕ => lcmPowerF κ x n * x ^ n) atTop (𝓝 (R.readout () κ x))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (κ := 2) (x := 2) (by norm_num) (by norm_num)
  have hgood := lcmPowerF_scaled_limit (κ := 2) (x := 2) (by norm_num) (by norm_num)
  have heq := tendsto_nhds_unique hgood hbad
  have hp := coefficient_pos (κ := 2) (x := 2) (by norm_num) (by norm_num)
  change coefficient 2 2 = -1 at heq
  linarith

def family : Registration arena (type_of% @lcmPowerF_scaled_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lcmPowerF_scaled_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 1, 2, ?_⟩
    change coefficient 2 1 ≠ coefficient 2 2
    have hp := coefficient_pos (κ := 2) (x := 2) (by norm_num) (by norm_num)
    simpa only [coefficient, sub_self, zero_mul, zero_div, Real.one_rpow] using hp.ne

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lcmPowerF_scaled_limit) (Realization signature) Unit Unit where
  unitName := `LcmPowerLeadingTerm.lcmPowerF_scaled_limit.unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm.LeadingLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ κ x => coefficient κ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LeadingLimit

namespace Continuity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ xn κ => lcmPowerF κ xn.1 xn.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ κ => if κ = 2 then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, 1 < x → ∀ {n : ℕ}, 1 ≤ n →
    ContinuousOn (fun κ : ℝ => R.readout () (x, n) κ) (Ioi 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h (x := 2) (by norm_num) (n := 1) (by norm_num)).continuousAt
    (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  have hdist : dist (2 + δ / 2) (2 : ℝ) < δ := by
    rw [Real.dist_eq, show 2 + δ / 2 - 2 = δ / 2 by ring, abs_of_pos (by positivity)]
    linarith
  have hh := hd hdist
  have hne : 2 + δ / 2 ≠ (2 : ℝ) := by linarith
  norm_num [rejected, realize, hne] at hh

def family : Registration arena (type_of% @continuousOn_lcmPowerF) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuousOn_lcmPowerF, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(2, 1), 0, 2, ?_⟩
    change lcmPowerF 0 2 ((1 : ℕ) : ℝ) ≠ lcmPowerF 2 2 ((1 : ℕ) : ℝ)
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    norm_num [lcmPowerF, Real.rpow_two, div_ne_zero_iff, hl]
    exact (div_ne_zero hl (mul_ne_zero (by norm_num) hl)).symm

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@continuousOn_lcmPowerF) (Realization signature) Unit Unit where
  unitName := `LcmPowerLeadingTerm.continuousOn_lcmPowerF.unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm.Continuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ xn κ => lcmPowerF κ xn.1 xn.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continuity

end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
