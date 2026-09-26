import D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct
import Reg.Support.CounterexampleRecord
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct
open LeanInformationAudit
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := `D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct ++ `result
    statementIdentity := "sha256:1827d3c4f136610e54299b27544d45f96997126173122d2b1a8e5ecba84c077d"
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

/-- The claim, read as a predicate on kernel pairs. -/
def predicate (k : FiniteKernelPair) : Prop :=
  PositiveDoublyStochastic k.P → PositiveDoublyStochastic k.Q →
    MixesInTwoSteps k.P → MixesInTwoSteps k.Q → oppositeInnerProduct k.P k.Q = 1

/-- The sign of a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The kernel `P(x, y) = (1 + x₁ y₂ / 2)/4` on `{−1, 1}²`. -/
def kernelP (x y : Bool × Bool) : ℝ := (1 + 1 / 2 * sgn x.1 * sgn y.2) / 4

/-- The pair `(P, Pᵀ)`. -/
def counterexamplePair : FiniteKernelPair := ⟨Bool × Bool, kernelP, fun x y => kernelP y x⟩

/-- The predicate fails on `(P, Pᵀ)`. -/
theorem predicate_fails : ¬ predicate (counterexamplePair) := by
  intro h
  let r : ℝ := 1 / 2
  let P : Bool × Bool → Bool × Bool → ℝ := kernelP
  let Q : Bool × Bool → Bool × Bool → ℝ := fun x y => P y x
  have hcard : (Fintype.card (Bool × Bool) : ℝ) = 4 := by simp
  have hP : PositiveDoublyStochastic P := by
    refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
    · rcases x with ⟨_ | _, _ | _⟩ <;> rcases y with ⟨_ | _, _ | _⟩ <;> norm_num [P, kernelP, sgn, r]
    · rcases x with ⟨_ | _, _ | _⟩ <;>
        simp [P, kernelP, sgn, r, Fintype.sum_prod_type] <;> norm_num
    · rcases y with ⟨_ | _, _ | _⟩ <;>
        simp [P, kernelP, sgn, r, Fintype.sum_prod_type] <;> norm_num
  have hQ : PositiveDoublyStochastic Q := ⟨fun x y => hP.1 y x, fun x => hP.2.2 x, fun y => hP.2.1 y⟩
  have hPP : MixesInTwoSteps P := by
    intro x z
    rw [hcard]
    rcases x with ⟨_ | _, _ | _⟩ <;> rcases z with ⟨_ | _, _ | _⟩ <;>
      simp [P, kernelP, sgn, r, Fintype.sum_prod_type] <;> norm_num
  have hQQ : MixesInTwoSteps Q := by
    intro x z
    rw [hcard]
    rcases x with ⟨_ | _, _ | _⟩ <;> rcases z with ⟨_ | _, _ | _⟩ <;>
      simp [Q, P, kernelP, sgn, r, Fintype.sum_prod_type] <;> norm_num
  have hval : oppositeInnerProduct P Q = 5 / 4 := by
    unfold oppositeInnerProduct
    rw [hcard]
    simp [Q, P, kernelP, sgn, r, Fintype.sum_prod_type]
    norm_num
  have := h hP hQ hPP hQQ
  change oppositeInnerProduct P Q = 1 at this
  rw [hval] at this
  norm_num at this

def embedding : Fin 1 → FiniteKernelPair := fun _ => counterexamplePair

def decision : ∀ w : Fin 1, Decidable (predicate (embedding w)) :=
  fun _ => .isFalse predicate_fails

def arena := WitnessArena.ofCarrier (Fin 1) FiniteKernelPair predicate embedding decision

def reads := counterexampleRealization (fun _ : Fin 1 => false)

theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩

theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads := ⟨arena.law_refutes⟩

theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue := arena.variation law

theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena := arena.sensitivity law

register_information_theorem result in arena
  readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (FiniteKernelPair) escape continues (open)

#print axioms predicate_fails
#print axioms bridge
#print axioms variation
#print axioms sensitivity

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Estimation.TimeArrow.TwoStepMixingOppositeProduct
