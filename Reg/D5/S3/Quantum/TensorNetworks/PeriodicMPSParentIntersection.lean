import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
import Reg.Support.DependentFamily

/-! Exact source law and observational dependence for actual periodic parent gluing.
A complete four-slot registration additionally needs whole-family variation,
sensitivity and lawful source-selection evidence. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection

open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Word 4 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Word 4 → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f g => f = g) (fun e => nomatch e)

def originalStatement : Prop :=
  ∀ (A B : Fin 2 → Bond) (r : ℕ), (twoFlattening A r).rank = 4 → ∀ b : Word r,
    (∃ X : Fin 2 → Bond, ∀ (w : Word 3) j,
      competitorSlice B b (Fin.snoc w j) = gamma A 3 (X j) w) →
    (∃ Y : Fin 2 → Bond, ∀ i (w : Word 3),
      competitorSlice B b (Fin.cons i w) = gamma A 3 (Y i) w) →
    ∃ Z : Bond, competitorSlice B b = gamma A 4 Z

def arena : Arena where
  signature := signature
  Law R := ∀ (A B : Fin 2 → Bond) (r : ℕ), (twoFlattening A r).rank = 4 → ∀ b : Word r,
    (∃ X : Fin 2 → Bond, ∀ (w : Word 3) j,
      competitorSlice B b (Fin.snoc w j) = gamma A 3 (X j) w) →
    (∃ Y : Fin 2 → Bond, ∀ i (w : Word 3),
      competitorSlice B b (Fin.cons i w) = gamma A 3 (Y i) w) →
    ∃ Z : Bond, R.readout () () (competitorSlice B b) (gamma A 4 Z)

theorem source_equivalence : originalStatement ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := actual_competitor_gluing

theorem actual_observational_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : Word 4 → ℂ), 1, ?_⟩
  intro he
  have hbad : (1 : Word 4 → ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  have hv := congrFun hbad (fun _ => 0)
  norm_num at hv

#print axioms source_equivalence
#print axioms actual_law
#print axioms actual_observational_dependence

abbrev recoverySignature : Signature where
  Params := ℕ
  State r := Word (r + 4) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ r := (Word (r + 4) → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def recoveryActual : Realization recoverySignature :=
  realize recoverySignature (fun _ _ f g => f = g) (fun e => nomatch e)

def recoveryOriginalStatement : Prop :=
  ∀ r : ℕ, (∃ A : Fin 2 → Bond, (twoFlattening A r).rank = 4) ∧
    ∀ A B : Fin 2 → Bond, (twoFlattening A r).rank = 4 →
      (rawThree B r = rawThree A r ↔
        ∃ c : ℂ, ‖c‖ = 1 ∧ gamma B (r + 4) 1 = c • gamma A (r + 4) 1)

def recoveryArena : Arena where
  signature := recoverySignature
  Law R := ∀ r : ℕ, (∃ A : Fin 2 → Bond, (twoFlattening A r).rank = 4) ∧
    ∀ A B : Fin 2 → Bond, (twoFlattening A r).rank = 4 →
      (rawThree B r = rawThree A r ↔
        ∃ c : ℂ, ‖c‖ = 1 ∧ R.readout () r (gamma B (r + 4) 1) (c • gamma A (r + 4) 1))

theorem recovery_source_equivalence :
    recoveryOriginalStatement ↔ recoveryArena.Law recoveryActual := Iff.rfl

theorem recovery_actual_law : recoveryArena.Law recoveryActual :=
  rank_locus_inhabited_and_phase_recovery

theorem recovery_observational_dependence :
    ObservationalDependence recoverySignature recoveryActual := by
  intro i
  refine ⟨0, (0 : Word 4 → ℂ), 1, ?_⟩
  intro he
  have hbad : (1 : Word 4 → ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  have hv := congrFun hbad (fun _ => 0)
  norm_num at hv

#print axioms recovery_source_equivalence
#print axioms recovery_actual_law
#print axioms recovery_observational_dependence

end
end Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
