import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit
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
open Filter Topology
open RHLinalg (rtrace)
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap (bellProjector)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (amp gap posTrace)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance (pureState)
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel (finite_preparation_quantum_channel)
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport)
open UnitaryReconstruction.LiuWildChoiObstruction (pairMatrix)

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

namespace PositiveTraceQuotient

universe u

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x / y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {B0 X0 P : Matrix n n ℂ} (_hB : B0.PosSemidef) (_hX : X0.PosSemidef)
    (_hP : IsStarProjection P) (_hker : ∀ v : n → ℂ, B0 *ᵥ v = 0 ↔ P *ᵥ v = v),
    Tendsto (fun ε : ℝ => R.readout () () (posTrace (ε • X0 - B0)) ε)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (rtrace (P * X0)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Empty
  let Z : Matrix n n ℂ := 0
  have hzero : IsStarProjection Z := IsStarProjection.zero (Matrix n n ℂ)
  have hkernel (v : n → ℂ) : Z *ᵥ v = 0 ↔ Z *ᵥ v = v := by
    have hv : v = 0 := funext fun i => i.down.elim
    rw [hv]
  have hbad := h (B0 := Z) (X0 := Z) (P := Z) Matrix.PosSemidef.zero
    Matrix.PosSemidef.zero hzero hkernel
  have hlimit : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
    simpa [rejected, realize, Z, rtrace] using hbad
  have heq := tendsto_nhds_unique tendsto_const_nhds hlimit
  norm_num at heq

def family : Registration arena.{u} (type_of% @bell_kernel_limit.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bell_kernel_limit.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 1
    norm_num [actual, realize] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bell_kernel_limit.{u}) (Realization observation) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.ConditionalExpansion.bell_kernel_limit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit.PositiveTraceQuotient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x / y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end PositiveTraceQuotient

namespace RatioComparison

universe u v

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B) (_hd : 2 ≤ Fintype.card A)
    (η : ℝ) (_hη : 0 < η),
    let P := bellProjector A
    let B₀ := amp N (1 - P)
    let Pker := 1 - spectralSupport B₀
    ∃ ρ σ : DensityState (Option A × A),
      pairMatrix ρ * pairMatrix σ = 0 ∧
      0 < gap 1 (pairMatrix ρ) (pairMatrix σ) ∧
      R.readout () () (gap 1 (amp N (pairMatrix ρ)) (amp N (pairMatrix σ)) /
          gap 1 (pairMatrix ρ) (pairMatrix σ)) (rtrace (Pker * amp N P) + η)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A := ULift.{u} (Fin 2)
  let B := ULift.{v} Unit
  let ω : DensityState B :=
    pureState (Pi.single (default : B) (1 : ℂ)) (by simp [dotProduct, Pi.single_apply])
  obtain ⟨N, _⟩ := finite_preparation_quantum_channel (fun _ : A => ω)
  have hd : 2 ≤ Fintype.card A := by simp [A]
  obtain ⟨_, _, _, _, hfalse⟩ := h N hd 1 (by norm_num)
  exact hfalse

def family : Registration arena.{u,v} (type_of% @exists_bell_kernel_ratio_le.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_bell_kernel_ratio_le.{u,v}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 0
    norm_num [actual, realize] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_bell_kernel_ratio_le.{u,v}) (Realization observation) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.ConditionalExpansion.exists_bell_kernel_ratio_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit.RatioComparison.family
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
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end RatioComparison

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit
