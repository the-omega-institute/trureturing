import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryUpperBound
import D5.S3.Quantum.Foundation.FinitePreparationChannel

/-! Source-bound observations for the Bell-kernel construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion
open RHLinalg (rtrace)
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap (bellProjector)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (amp gap posTrace)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance (pureState)
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel (finite_preparation_quantum_channel)
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport)
open UnitaryReconstruction.LiuWildChoiObstruction (pairMatrix)

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryUpperBound

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

namespace SuccessProbability

universe u v

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private def law (R : Realization observation) : Prop :=
  ∀ {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (_hd : 2 ≤ Fintype.card A),
    let P := bellProjector A
    let Q := 1 - spectralSupport (amp N (1 - P))
    let d : ℝ := Fintype.card A
    let p := rtrace (Q * amp N P) / d ^ 2
    let recovery := bellKernelRecovery N
    R.readout () () 0 p ∧ p ≤ 1 ∧
      (∀ Y : Matrix B B ℂ, Y.PosSemidef →
        rtrace (CStarMatrix.ofMatrix.symm (recovery (CStarMatrix.ofMatrix Y))) ≤ rtrace Y) ∧
      (∀ X : Matrix A A ℂ,
        CStarMatrix.ofMatrix.symm (recovery (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) =
          (p : ℂ) • X) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ σ : DensityState (Option A × A),
        pairMatrix ρ * pairMatrix σ = 0 ∧
        0 < gap 1 (pairMatrix ρ) (pairMatrix σ) ∧
        gap 1 (amp N (pairMatrix ρ)) (amp N (pairMatrix σ)) /
          gap 1 (pairMatrix ρ) (pairMatrix σ) < d ^ 2 * p + ε

private abbrev arena : Arena where
  signature := observation
  Law := law.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A := ULift.{u} (Fin 2)
  let B := ULift.{v} Unit
  let ω : DensityState B :=
    pureState (Pi.single (default : B) (1 : ℂ)) (by simp [dotProduct, Pi.single_apply])
  obtain ⟨N, _⟩ := finite_preparation_quantum_channel (fun _ : A => ω)
  have hd : 2 ≤ Fintype.card A := by simp [A]
  exact (h N hd).1

def family : Registration arena.{u,v} (type_of% @heralded_recovery_upper_bound.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@heralded_recovery_upper_bound.{u,v}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 0
    norm_num [actual, realize] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heralded_recovery_upper_bound.{u,v}) (Realization observation) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.ConditionalExpansion.heralded_recovery_upper_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryUpperBound.SuccessProbability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryUpperBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end SuccessProbability

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryUpperBound
