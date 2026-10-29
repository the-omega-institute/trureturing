import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
import Reg.Support.DependentFamily

/-! Source-bound audit of the equality between tester and canonical POVM robustness. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality

open _root_.D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe equality on the two real robustness values in the conclusion. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain all finite spaces, the common density, and both POVM hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (y x j k : Type) [Fintype y] [DecidableEq y] [Fintype x] [DecidableEq x]
      [Fintype j] [DecidableEq j] [Fintype k] [DecidableEq k]
      (ρ : Matrix x x ℂ) (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ),
      IsDensity ρ → ((∀ a, (m a).PosSemidef) ∧ ∑ a, m a = 1) →
      ((∀ b, (n b).PosSemidef) ∧ ∑ b, n b = 1) →
        R.readout () ()
          (testerRobustness (fun a => Matrix.kronecker (m a) ρ)
            (fun b => Matrix.kronecker (n b) ρ))
          (povmRobustness (fun a => Matrix.kronecker (m a)
            (1 : Matrix (Fin ρ.rank) (Fin ρ.rank) ℂ))
            (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin ρ.rank) (Fin ρ.rank) ℂ)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hρ : IsDensity (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
    ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩
  have hm : (∀ a : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef) ∧
      ∑ _a : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 :=
    ⟨fun _ => Matrix.PosSemidef.one, by simp⟩
  exact h (Fin 1) (Fin 1) (Fin 1) (Fin 1) 1 (fun _ => 1) (fun _ => 1) hρ hm hm

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℝ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hfalse

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
      (@_root_.D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
      name := `D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
