import D5.S3.Analytic.Resolvent.EntireLogDerivDifference
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The logarithmic derivative difference is observed at the two prescribed points. -/

noncomputable section
namespace Reg.D5.S3.Analytic.Resolvent.EntireLogDerivDifference
open _root_.D5.S3.Analytic.Resolvent.EntireLogDerivDifference
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex LeanInformationAudit

namespace Growth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : ℂ → ℂ} {a : ℂ} {α C : ℝ}
    (_hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α)),
    0 ≤ (max C 0) * (1 + ‖a‖) ^ (max α 0) + max (-Real.log ‖F a‖) 0 ∧
      ∀ z : ℂ, ‖(F a)⁻¹ * F (a + z)‖ ≤
        R.readout () () (((max C 0) * (1 + ‖a‖) ^ (max α 0) + max (-Real.log ‖F a‖) 0) *
          (1 + ‖z‖) ^ (max α 0))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hD⟩ := h (F := fun _ => 1) (a := 0) (α := 0) (C := 0)
    (by intro z; norm_num)
  have hz := hD 0
  norm_num [rejected, realize] at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp 0 ≠ Real.exp 1
  exact Real.exp_injective.ne (by norm_num)

def family : Registration arena (type_of% @normalized_growth) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_growth, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalized_growth) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.Analytic.Resolvent.EntireLogDerivDifference.normalized_growth
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Resolvent.EntireLogDerivDifference.Growth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.EntireLogDerivDifference
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Growth

namespace ZeroSum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ F : ℂ → ℂ, Σ _ : ℂ, {z : ℂ // F z = 0})
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p m => m / (1 + ‖p.2.2.1 - p.2.1‖ ^ 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : ℂ → ℂ} {a : ℂ} {α C : ℝ}
    (_hF : Differentiable ℂ F) (_hα : α < 2)
    (_hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α)),
    Summable (fun ρ : {z : ℂ // F z = 0} =>
      R.readout () ⟨F, a, ρ⟩ (analyticOrderNatAt F ρ.1 : ℝ)) ∧
    ∀ b : ℂ,
      (∑' ρ : {z : ℂ // F z = 0},
        (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) ≤
        (1 + ‖a - b‖ + ‖a - b‖ ^ 2) * (∑' ρ : {z : ℂ // F z = 0},
          (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - b‖ ^ 2)) ∧
      (F b ≠ 0 →
        let H := 2 * ((max C 0) * (1 + ‖b‖) ^ (max α 0) + max (-Real.log ‖F b‖) 0) *
          (5 / 2 : ℝ) ^ (max α 0) / ((2 - max α 0) * Real.log (3 / 2))
        (∑' ρ : {z : ℂ // F z = 0},
          (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - b‖ ^ 2)) ≤ H ∧
        (∑' ρ : {z : ℂ // F z = 0},
          (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) ≤
          (1 + ‖a - b‖ + ‖a - b‖ ^ 2) * H)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (F := fun _ => 0) (a := 0) (α := 0) (C := 0)
    (by fun_prop) (by norm_num) (by intro z; norm_num)
  have hh := hh.1
  change Summable (fun _ : {z : ℂ // (fun _ : ℂ => (0 : ℂ)) z = 0} => (1 : ℝ)) at hh
  let j : ℕ → {z : ℂ // (fun _ : ℂ => (0 : ℂ)) z = 0} := fun n => ⟨n, rfl⟩
  have hj : Function.Injective j := by
    intro n m h
    have hh := congrArg Subtype.val h
    change (n : ℂ) = (m : ℂ) at hh
    exact_mod_cast hh
  have hn := Summable.comp_injective
    (f := fun _ : {z : ℂ // (fun _ : ℂ => (0 : ℂ)) z = 0} => (1 : ℝ)) (i := j) hh hj
  have hz : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hn.tendsto_atTop_zero
  norm_num at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨(fun _ : ℂ => 0), 0, ⟨0, rfl⟩⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @entire_zero_summable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entire_zero_summable, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entire_zero_summable) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.Analytic.Resolvent.EntireLogDerivDifference.entire_zero_summable
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Resolvent.EntireLogDerivDifference.ZeroSum.family
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
    (fun _ p m => m / (1 + ‖p.2.2.1 - p.2.1‖ ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.EntireLogDerivDifference
    definition := none
    coordinates := #[0, 1, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ZeroSum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℂ, ℂ)
    (fun _ => ℂ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p F => logDeriv F p.2 - logDeriv F p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a s : ℂ} {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {α C : ℝ} (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α))
    (ha : F a ≠ 0) (hs : F s ≠ 0),
    HasSum (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℂ) * ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹))
      (R.readout () ⟨a, s⟩ F)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 1 (fun _ : ℂ => (1 : ℂ)) (differentiable_const 1)
    0 0 (by norm_num) (by intro z; simp) (by norm_num) (by norm_num)
  haveI : IsEmpty {z : ℂ // (fun _ : ℂ => (1 : ℂ)) z = 0} :=
    ⟨fun ρ => one_ne_zero ρ.2⟩
  have hzero : HasSum (fun ρ : {z : ℂ // (fun _ : ℂ => (1 : ℂ)) z = 0} =>
      (analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) ρ.1 : ℂ) *
        (((1 : ℂ) - ρ.1)⁻¹ - ((0 : ℂ) - ρ.1)⁻¹)) 0 := by
    exact hasSum_zero.congr_fun (fun ρ => isEmptyElim ρ)
  have he := hh.unique hzero
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 1⟩, (fun _ => 1), (fun z => z), ?_⟩
  norm_num [actual, realize, logDeriv_apply]

def family : Registration arena (type_of% @entire_logDeriv_difference_hasSum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entire_logDeriv_difference_hasSum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entire_logDeriv_difference_hasSum) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.Analytic.Resolvent.EntireLogDerivDifference.entire_logDeriv_difference_hasSum
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Resolvent.EntireLogDerivDifference.family
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
    (fun _ p F => logDeriv F p.2 - logDeriv F p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ → ℂ)
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.EntireLogDerivDifference
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Centered
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex LeanInformationAudit
open Zeta23.WeilEF

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) (hf0 : f 0 = 1)
    {B : ℝ} (hB : 2 ≤ B) (hfB : ∀ w, ‖w‖ ≤ 24 / 25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83 / 100),
    R.readout () () (logDeriv (Cf (22 / 25) f) z - logDeriv (Cf (22 / 25) f) 0) ≤
      ((44795000 * Real.log B + ‖logDeriv (Cf (22 / 25) f) 0‖) /
        (83 / 100 : ℝ)) * ‖z‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (f := fun _ : ℂ => 1) (fun _ _ => analyticAt_const)
    rfl (B := 2) (by norm_num) (by intro w hw; norm_num) (z := 0) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @centered_cf) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@centered_cf, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@centered_cf) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.Analytic.Resolvent.EntireLogDerivDifference.centered_cf
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Resolvent.EntireLogDerivDifference.Centered.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.EntireLogDerivDifference
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Centered

namespace Truncation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex LeanInformationAudit
open Zeta23.WeilEF

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ {F : ℂ → ℂ} {a s : ℂ} {β D R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R))
    (ha : F a ≠ 0) (hs : F s ≠ 0)
    (hβ : 0 ≤ β)
    (hg : ∀ z : ℂ, ‖z‖ ≤ (24 / 25 : ℝ) * R →
      ‖(F a)⁻¹ * F (a + z)‖ ≤ Real.exp (D * (1 + ‖z‖) ^ β))
    (hsR : ‖s - a‖ ≤ (83 / 100) * R)
    (t : Finset {z : ℂ // F z = 0})
    (ht : ∀ ρ : {z : ℂ // F z = 0}, ρ ∈ t ↔ ‖ρ.1 - a‖ ≤ (22 / 25) * R),
    A.readout () () (logDeriv F s - logDeriv F a -
      ∑ ρ ∈ t, (analyticOrderNatAt F ρ.1 : ℂ) *
        ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)) ≤
      (2 * 44795000 / (83 / 100 : ℝ)) *
        Real.log (max 2 (Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ β))) * ‖s - a‖ / R ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let t : Finset {z : ℂ // (fun _ : ℂ => (1 : ℂ)) z = 0} := ∅
  have hh := h (F := fun _ : ℂ => 1) (fun _ _ => analyticAt_const) (a := 0) (s := 0)
    (by norm_num) (by norm_num) (β := 0) (D := 0) (by norm_num)
    (R := 1) (by intro z hz; norm_num) (by norm_num) t (by
      intro ρ; exact False.elim (one_ne_zero ρ.2))
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @entire_logDeriv_difference_truncation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entire_logDeriv_difference_truncation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entire_logDeriv_difference_truncation) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.Analytic.Resolvent.EntireLogDerivDifference.entire_logDeriv_difference_truncation
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Resolvent.EntireLogDerivDifference.Truncation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.EntireLogDerivDifference
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Truncation

end Reg.D5.S3.Analytic.Resolvent.EntireLogDerivDifference
