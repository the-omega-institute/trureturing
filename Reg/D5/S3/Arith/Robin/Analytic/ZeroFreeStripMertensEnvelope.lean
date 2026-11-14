import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import Reg.Support.DependentFamily

/-! The complete strip-conditional source law and its audit obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (B)

namespace Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => B x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 / 2 →
    (∀ rho : ℂ, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1 - alpha) →
    ∃ C T : ℝ, 0 ≤ C ∧ Real.exp 1 ≤ T ∧ ∀ x : ℝ, T ≤ x →
      |V.readout () () x| ≤ C / (Real.rpow x alpha * Real.log x)

private theorem actual_law : arena.Law actual := @actual_B_critical_strip_envelope

private theorem source_bridge :
    (type_of% (@actual_B_critical_strip_envelope)) ↔ arena.Law actual := Iff.rfl

private abbrev PositiveUniformStrip : Prop :=
  ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ 1 / 2 ∧
    ∀ rho : ℂ, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1 - alpha

private theorem law_of_no_positive_strip (h : ¬ PositiveUniformStrip)
    (V : Realization signature) : arena.Law V := by
  intro alpha ha hhalf hstrip
  exact (h ⟨alpha, ha, hhalf, hstrip⟩).elim

private theorem rejected_family_requires_positive_strip {V : Realization signature}
    (h : ¬ arena.Law V) : PositiveUniformStrip := by
  by_contra hn
  exact h (law_of_no_positive_strip hn V)

/- The full source law and its equivalence bridge do not complete a four-slot
   audit. Variation requires a rejected whole family. The preceding proof shows
   that any such rejection implies the existence of a positive uniform strip:
   there is alpha in (0,1/2] bounding every actual nontrivial zero by 1-alpha.
   This existence statement is not identified with RH. Sensitivity and actual
   observational dependence also remain obligations; no Contract.Registration
   or validated audit is asserted here. -/

end Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
