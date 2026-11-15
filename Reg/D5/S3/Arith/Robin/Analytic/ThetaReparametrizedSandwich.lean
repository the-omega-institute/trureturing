import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (B)
open _root_.D5.S3.Weil.Mertens.ActualThetaTailLaplace (F)

namespace Reg.D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich

/-- The two literal E₃ occurrences vary independently over the complete real domain. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Mertens.E₃ x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ}, 2 < x → 2 < Chebyshev.theta x →
    -F (Chebyshev.theta x) + (V.readout false () x + Mertens.E₂p x) ≤ B x ∧
    B x ≤ -F x + (V.readout true () x + Mertens.E₂p x)

private theorem actual_law : arena.Law actual := @actual_theta_reparametrized_sandwich

private theorem source_bridge :
    (type_of% (@actual_theta_reparametrized_sandwich)) ↔ arena.Law actual := Iff.rfl

private theorem lawful_domain_inhabited : ∃ x : ℝ, 2 < x ∧ 2 < Chebyshev.theta x := by
  have hratio := _root_.D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have he : ∀ᶠ x : ℝ in atTop, 2 < x ∧ 2 < Chebyshev.theta x := by
    filter_upwards [eventually_gt_atTop (4 : ℝ),
      hratio.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with x hx hr
    have hx0 : 0 < x := by linarith
    have ht := (lt_div_iff₀ hx0).mp hr
    exact ⟨by linarith, by linarith⟩
  exact he.exists

def rejected (i : Bool) : Realization signature :=
  realize signature
    (fun j _ x => if j = i then
      if i then B x + F x - Mertens.E₂p x - 1
      else B x + F (Chebyshev.theta x) - Mertens.E₂p x + 1
      else Mertens.E₃ x)
    (fun e => nomatch e)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  obtain ⟨x, hx, ht⟩ := lawful_domain_inhabited
  have hb := h hx ht
  cases i
  · have hl := hb.1
    change -F (Chebyshev.theta x) +
      ((B x + F (Chebyshev.theta x) - Mertens.E₂p x + 1) + Mertens.E₂p x) ≤ B x at hl
    linarith only [hl]
  · have hu := hb.2
    change B x ≤ -F x + ((B x + F x - Mertens.E₂p x - 1) + Mertens.E₂p x) at hu
    linarith only [hu]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.exp (-2), ?_⟩
  change Mertens.E₃ 0 ≠ Mertens.E₃ (Real.exp (-2))
  have hf : ⌊Real.exp (-2)⌋₊ = 0 :=
    Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  simp only [Mertens.E₃, hf, Nat.floor_zero, Finset.Ioc_self, Finset.filter_empty,
    Finset.sum_empty, Real.log_zero, Real.log_exp, Real.log_neg_eq_log, zero_add]
  intro heq
  linarith only [heq, hpos]

def family : Registration arena (type_of% (@actual_theta_reparametrized_sandwich)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      funext p x
      simp only [actual, rejected, realize, if_neg hji]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_theta_reparametrized_sandwich) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich.actual_theta_reparametrized_sandwich.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Mertens.E₃ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich
