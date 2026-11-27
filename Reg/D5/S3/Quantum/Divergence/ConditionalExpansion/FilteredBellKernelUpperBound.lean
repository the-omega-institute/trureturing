import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellKernelUpperBound

/-! Source equivalence for the conditional Bell-kernel upper bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
open _root_.FilteredBellKernelProjection (filtered_channel_bell_upper_bound)
open _root_.FilteredChannelConditionalGap (exists_filtered_channel filterAction)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act ratios)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
open RHLinalg (rtrace)

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellKernelUpperBound

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A E : Type} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E] [Nonempty E]
    (G : Matrix (A × E) (A × E) ℂ) (_hG : G.PosDef)
    (_hnorm : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1)
    (N : QuantumChannel A (A × E)) (_hN : ∀ X, act N X = filterAction G X)
    (_hd : 2 ≤ Fintype.card A) (γ : ℝ) (_hγ : 1 ≤ γ) (orth : Bool),
    R.readout () () (sInf (ratios N γ orth))
      (rtrace (((Fintype.card A : ℝ)⁻¹ • partialTraceLeft G⁻¹)⁻¹) / Fintype.card E)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let G : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ := 1
  have hG : G.PosDef := Matrix.PosDef.one
  have hnorm : (Fintype.card Unit : ℝ)⁻¹ • partialTraceRight G = 1 := by
    ext i j
    simp [G, partialTraceRight, Matrix.one_apply, Prod.mk.injEq]
  obtain ⟨N, hN⟩ := exists_filtered_channel G hG hnorm
  exact h G hG hnorm N hN (by simp) 1 le_rfl false

private theorem dependence : ObservationalDependence observation actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad := congrFun he 0
  norm_num [actual, realize] at hbad

def family : Registration arena (type_of% @filtered_channel_bell_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@filtered_channel_bell_upper_bound, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@filtered_channel_bell_upper_bound) (Realization observation) Unit Unit where
  unitName := `FilteredBellKernelProjection.filtered_channel_bell_upper_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellKernelUpperBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellKernelUpperBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellKernelUpperBound
