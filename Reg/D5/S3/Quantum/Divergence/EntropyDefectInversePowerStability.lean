import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability

/-! Faithful dependent-readout registration for the actual supported fractional inverse-power estimate. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability

/-- Observe the actual inequality, retaining both real operands. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ)
    (m : ℝ) (_hm : 0 < m) (alpha : ℝ) (_halpha0 : 0 < alpha) (_halpha1 : alpha < 1),
    let M := supported_relative_modular_model Φ ρ σ support
    m • 1 ≤ M.data.A → m • 1 ≤ M.data.B →
    let d := cfc (fun x : ℝ => x ^ (-alpha)) M.data.A *ᵥ M.data.ξ -
      M.data.V *ᵥ (cfc (fun x : ℝ => x ^ (-alpha)) M.data.B *ᵥ M.data.η)
    R.readout () () (Real.sqrt (star d ⬝ᵥ d).re)
      ((Real.sin (Real.pi * alpha) / Real.pi) *
        _root_.D5.S3.Analytic.Interpolation.CapWeightedEnergy.sharpConstant alpha *
        (2 / m) ^ alpha *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) ^ ((1 - alpha) / 2))

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
    @h a b ia da na ib db nb Φ ρ σ support m hm (1 / 2) (by norm_num) (by norm_num)
      hfloorA hfloorB
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v}
    (type_of% @entropy_defect_inverse_power_stability.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_defect_inverse_power_stability, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entropy_defect_inverse_power_stability.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability.entropy_defect_inverse_power_stability.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability
