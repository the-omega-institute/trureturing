import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
import Reg.Support.DependentFamily

/-! Faithful actual-state and actual-POVM audit variations for the symmetric ensemble. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
open _root_.D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (success)
open _root_.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)
open _root_.D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
namespace States

abbrev signature : Signature where
  Params := Σ _a : ℝ, Σ _b : ℝ, ℝ
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := QubitMatrix
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => rho p.1 p.2.1 p.2.2 i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a b c : ℝ), 0 < a → 0 < c → c < 1 →
    0 < a * (1 - a) - b ^ 2 → ∀ i,
      (rho a b c i).PosDef ∧ trace (r.readout () ⟨a, b, c⟩ i) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := (h (1 / 2) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0).2
  norm_num [rejected, realize] at ht

def family : Registration arena (type_of% (@states_posDef)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨states_posDef, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1 / 2, 1 / 4, 1 / 2⟩, 0, 1, ?_⟩
    intro h
    have he := congrArg (fun M : QubitMatrix => M 0 1) h
    norm_num [actual, realize, rho] at he

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@states_posDef) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric.States.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric.States.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => rho p.1 p.2.1 p.2.2 i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "fn", "arg", "arg"]
        stateBinder := 7, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end States
namespace Pair

abbrev signature : Signature where
  Params := Σ _a : ℝ, Σ _b : ℝ, ℝ
  State _ := Fin 3 → QubitMatrix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 3 → QubitMatrix
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ E i => (2 : ℂ) • E i) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a b c : ℝ), 0 < b → |c - a| ≤ b →
    finitePOVM pairPovm ∧ success (rho a b c) pairPovm = (1 + 2 * b) / 3 ∧
      ∀ E, finitePOVM E →
        ((∀ F, finitePOVM F →
          success (rho a b c) F ≤ success (rho a b c) E) ↔
          r.readout () ⟨a, b, c⟩ E = pairPovm)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := pair_classification (1 / 2) (1 / 4) (1 / 2) (by norm_num) (by norm_num)
  have ho := h (1 / 2) (1 / 4) (1 / 2) (by norm_num) (by norm_num)
  have heq := (ho.2.2 pairPovm ht.1).mp ((ht.2.2 pairPovm ht.1).mpr rfl)
  have he := congrArg (fun E : Fin 3 → QubitMatrix => E 0 0 0) heq
  norm_num [rejected, realize, pairPovm, vecMulVec, Pi.smul_apply] at he

def family : Registration arena (type_of% (@pair_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pair_classification, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨0, 0, 0⟩, 0, (fun _ => 1), ?_⟩
    intro h
    have he := congrArg (fun E : Fin 3 → QubitMatrix => E 0 0 0) h
    change (0 : ℂ) = 1 at he
    norm_num at he

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pair_classification) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric.Pair.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric.Pair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ E => E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "body",
          "arg", "fn", "arg"]
        stateBinder := 5, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Pair
end Reg.D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
