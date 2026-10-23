import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization
open LeanInformationAudit Matrix
open scoped MatrixOrder ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.AlternativeMeanLinearization
noncomputable section
open Classical

abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A ↦ decide A.PosDef) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

private theorem zero_not_posDef : ¬ (0 : Matrix (Fin 1) (Fin 1) ℂ).PosDef := by
  intro h
  have h0 := h.diag_pos (i := 0)
  simpa using h0

private theorem observed_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change decide (0 : Matrix (Fin 1) (Fin 1) ℂ).PosDef ≠
    decide (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef
  simp [zero_not_posDef, Matrix.PosDef.one]

namespace Riccati

/-- The whole original Riccati statement, with its A-positivity premise observed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ},
    R.readout () n A = true → B.PosDef →
    (gmInv A B).PosDef ∧ gmInv A B * A * gmInv A B = B

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := (law (n := 1) (A := 0) (B := 1) rfl Matrix.PosDef.one).1
  have hz : gmInv (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
    norm_num [gmInv, cfc_apply_zero]
  rw [hz] at bad
  exact zero_not_posDef bad

def evidence : Registration arena (type_of% (@riccati)) where
  actual := actual
  bridge := by
    constructor
    · intro source n A B hA hB
      exact source (of_decide_eq_true hA) hB
    · intro law n A B hA hB
      exact law (decide_eq_true hA) hB
  variation := ⟨by
    intro n A B hA hB
    exact riccati (of_decide_eq_true hA) hB, rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := observed_dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.Riccati.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AlternativeMeanLinearization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end Riccati

namespace RiccatiUnique

/-- The whole original uniqueness statement, including the independent equation premise. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A B Y : Matrix (Fin n) (Fin n) ℂ},
    R.readout () n A = true → Y.PosDef → Y * A * Y = B → gmInv A B = Y

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law (n := 1) (A := 0) (B := 0) (Y := 1) rfl
    Matrix.PosDef.one (by simp)
  have hz : gmInv (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 = 0 := by
    norm_num [gmInv, cfc_apply_zero]
  rw [hz] at bad
  exact zero_ne_one bad

def evidence : Registration arena (type_of% (@riccati_unique)) where
  actual := actual
  bridge := by
    constructor
    · intro source n A B Y hA hY heq
      exact source (of_decide_eq_true hA) hY heq
    · intro law n A B Y hA hY heq
      exact law (decide_eq_true hA) hY heq
  variation := ⟨by
    intro n A B Y hA hY heq
    exact riccati_unique (of_decide_eq_true hA) hY heq, rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := observed_dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati_unique)
      (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati_unique.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.RiccatiUnique.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AlternativeMeanLinearization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end RiccatiUnique
end
end Reg.D5.S3.Quantum.Matrix.AlternativeMeanLinearization
