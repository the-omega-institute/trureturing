import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap

/-! Source-bound observation of the input-gap normalization in the exact Bell witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder CStarAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance (pureState)
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel
  (finite_preparation_quantum_channel)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (amp E gap posTrace ptr)
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap
open UnitaryReconstruction.LiuWildChoiObstruction (pairMatrix)

open private pad from D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

private def basisState (n : Type*) [Fintype n] [DecidableEq n] (i : n) : DensityState n :=
  pureState (Pi.single i (1 : ℂ)) (by simp [dotProduct, Pi.single_apply])

namespace InputGap

private abbrev readoutSignature := signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

private def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ _ x y => x / y) (fun e => nomatch e)

private def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

private abbrev arena.{u, v} : Arena where
  signature := readoutSignature
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (ω : DensityState A) (ε : ℝ)
    (_hε : 0 < ε) (_hεD : ε ≤ (Fintype.card A : ℝ) ^ 2 - 1),
    let d : ℝ := Fintype.card A
    let D : ℝ := d ^ 2 - 1
    let P := bellProjector A
    let C := 1 - P
    let ρ := D⁻¹ • pad C (0 : Matrix A A ℂ)
    let σ := D⁻¹ • pad (ε • P) ((D - ε) • pairMatrix ω)
    Fintype.card (Option A) = Fintype.card A + 1 ∧
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ σ.PosSemidef ∧ σ.trace = 1 ∧ ρ * σ = 0 ∧
      E 1 (ptr ρ) (ptr σ) = (D - ε) / D ∧
      gap 1 ρ σ = R.readout () () ε D ∧ 0 < gap 1 ρ σ ∧
      gap 1 (amp N ρ) (amp N σ) = posTrace (ε • amp N P - amp N C) / D ∧
      gap 1 (amp N ρ) (amp N σ) / gap 1 ρ σ =
        posTrace (ε • amp N P - amp N C) / ε ∧
      (gap 1 (amp N ρ) (amp N σ) = 0 ↔ ε • amp N P ≤ amp N C) ∧
      (gap 1 (amp N ρ) (amp N σ) / gap 1 ρ σ = 0 ↔ ε • amp N P ≤ amp N C)

private theorem rejected_law.{u, v} : ¬ arena.{u, v}.Law rejected := by
  intro h
  let A := ULift.{u} (Fin 2)
  let B := ULift.{v} Unit
  let ω := basisState A ⟨0⟩
  obtain ⟨N, _⟩ := finite_preparation_quantum_channel
    (fun _ : A => basisState B ⟨()⟩)
  have hd : Fintype.card A = 2 := by simp [A]
  obtain ⟨_, _, _, _, _, _, _, hg, hp, _⟩ :=
    h N ω 1 (by norm_num) (by rw [hd]; norm_num)
  exact (ne_of_gt hp) hg

def family.{u, v} : Registration arena.{u, v} (type_of% @bell_padded_gap.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bell_padded_gap, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 1
    change (0 : ℝ) / 1 = 1 / 1 at he
    simpa using he

def registration.{u, v} :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bell_padded_gap.{u, v}) (Realization readoutSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap.bell_padded_gap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap.InputGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature (fun _ _ x y => x / y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end InputGap

#print axioms InputGap.registration

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap
