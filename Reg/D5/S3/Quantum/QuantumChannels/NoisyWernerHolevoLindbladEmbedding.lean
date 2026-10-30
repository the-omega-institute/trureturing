import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
import Reg.Support.DependentFamily

/-! Source-bound audit of the noisy qutrit Werner–Holevo embedding criterion. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding

open _root_.D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the channel as its real noise parameter varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => wernerHolevo x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => wernerHolevo 0) (fun e => nomatch e)

/-- Retain the parameter interval and the complete GKSL exponential equivalence. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x : ℝ, x ∈ Set.Icc 0 (2 / 3 : ℝ) →
    ((∃ G, IsGKSLGenerator G ∧ generatorExp G = r.readout () () x) ↔ x = 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : IsGKSLGenerator (0 : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) := by
    refine ⟨0, 0, Fin.elim0, Matrix.isHermitian_zero, ?_⟩
    intro X
    simp
  have hexp : generatorExp (0 : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) =
      wernerHolevo 0 := by
    unfold generatorExp wernerHolevo
    simp only [map_zero, NormedSpace.exp_zero, map_one]
    simp
    rfl
  have hbad := (h (1 / 3) (by constructor <;> norm_num)).mp ⟨0, hzero, hexp⟩
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change wernerHolevo 0 ≠ wernerHolevo 1
  intro h
  have hentry := congrArg
    (fun T : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) =>
      T (Matrix.single 0 1 1) 0 1) h
  norm_num [wernerHolevo, Matrix.transposeLinearEquiv, Matrix.trace,
    Matrix.single, Matrix.one_apply] at hentry

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ x => wernerHolevo x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
      name := `D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
