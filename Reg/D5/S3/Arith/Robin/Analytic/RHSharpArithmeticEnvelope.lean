import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace Reg.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope

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
  Law V := ∀ hRH : RiemannHypothesis,
    (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ x : ℝ in atTop,
      1 < Chebyshev.theta x ∧ |D x * V.readout () () x + 2| < firstLiMass + epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ x : ℝ, max 2 Y ≤ x ∧ 1 < Chebyshev.theta x ∧
        |D x * V.readout () () x + 2 + firstLiMass| < epsilon) ∧
    Filter.liminf (fun x : ℝ => D x * V.readout () () x) atTop = -2 - firstLiMass

private theorem actual_law : arena.Law actual := by
  exact @actual_B_lower_endpoint

private theorem source_bridge :
    (type_of% (@actual_B_lower_endpoint)) ↔ arena.Law actual := Iff.rfl

/- This source law and its equivalence bridge do not constitute a completed
   four-slot audit. No Contract.Registration is declared here. The missing evidence
   is a lawful enrolled-template readout, whole-family variation and sensitivity,
   actual observational dependence, sourceSelection and current binding evidence.
   Refuting this RH-conditional law for a rejected family entails RH: when RH is
   false the law holds for every family. An anchor equality would change the
   source law and is therefore not added. -/

namespace CenteredRoot
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => Filter ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 𝓝 (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := Tendsto (fun x : ℝ => D x * (S x - A x)) atTop (V.readout () () 0)
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique S_sub_A_limit h
  norm_num at he
def family : Registration arena (type_of% @S_sub_A_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨S_sub_A_limit, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    exact fun he => zero_ne_one (nhds_injective he)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@S_sub_A_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.S_sub_A_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.CenteredRoot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨CenteredRoot.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CenteredRoot

end Reg.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
