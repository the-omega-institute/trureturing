import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability

/-! Faithful registration of the actual integrability and physical-overlap bound. -/

noncomputable section
universe u v
open Matrix Set MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Topology
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1),
    let M := supported_relative_modular_model Φ ρ σ support
    let w : ℝ → EuclideanSpace ℂ (M.data.J × M.data.I) := fun t => WithLp.toLp 2
      ((M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
        M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η))
    let inputOverlap := (cfc (fun x : ℝ => x ^ (1 - q)) M.data.R *
      cfc (fun x : ℝ => x ^ q) M.data.S).trace.re
    let outputOverlap := (cfc (fun x : ℝ => x ^ (1 - q)) M.data.T *
      cfc (fun x : ℝ => x ^ q) M.data.Q).trace.re
    R.readout () ()
      (IntegrableOn (fun t : ℝ => t ^ (q + 1) * ‖w t‖ ^ 2) (Ioi 0))
      ((∫ t in Ioi (0 : ℝ), t ^ (q + 1) * ‖w t‖ ^ 2) ≤
        (outputOverlap - inputOverlap) / (Real.sin (Real.pi * q) / Real.pi))

set_option maxHeartbeats 0 in
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  apply _root_.Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.rejected_law
  intro a b ia da na ib db nb Φ ρ σ support m hm
  let M := supported_relative_modular_model Φ ρ σ support
  change m • 1 ≤ M.data.A → m • 1 ≤ M.data.B → False
  intro hfloorA hfloorB
  change False
  have hfalse : False :=
    @h a b ia da na ib db nb Φ ρ σ support (1 / 2) (by norm_num) (by norm_num)
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

def family : Registration arena.{u,v}
    (type_of% @actual_lieb_overlap_resolvent_integral_budget.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_lieb_overlap_resolvent_integral_budget, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_lieb_overlap_resolvent_integral_budget.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget.actual_lieb_overlap_resolvent_integral_budget.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
