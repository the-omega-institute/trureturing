import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Optimization.GlobalZZGateTimeBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the nonnegative global-ZZ schedule time bound. -/

namespace Reg.D5.S3.Quantum.Optimization.GlobalZZGateTimeBound

open _root_.D5.S3.Quantum.Optimization.GlobalZZGateTimeBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the time bound for each dimension and coupling matrix. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n M => gateBound n * offDiagSup M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain all dimensions, symmetry and diagonal hypotheses, and schedule feasibility. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ), 2 ≤ n → ∀ M : Matrix (Fin n) (Fin n) ℝ,
    M.IsSymm → (∀ i, M i i = 0) →
    ∃ lam, IsFeasible M lam ∧ ∑ m, lam m ≤ r.readout () n M

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨lam, hlam, hbound⟩ := h 2 (by norm_num) 0 (by rfl) (by simp)
  have hnonneg : 0 ≤ ∑ m, lam m := Finset.sum_nonneg fun m _ => hlam.1 m
  change ∑ m, lam m ≤ (-1 : ℝ) at hbound
  linarith

private theorem offDiagSup_zero (n : ℕ) :
    offDiagSup (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro p _
    cases p with
    | none => exact le_rfl
    | some e => simp
  · exact Finset.le_sup'
      (fun p : Option (Fin n × Fin n) =>
        p.elim (0 : ℝ) (fun e => if e.1 < e.2 then |(0 : Matrix (Fin n) (Fin n) ℝ) e.1 e.2|
          else 0))
      (Finset.mem_univ none)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, (fun _ _ => 1), ?_⟩
  change gateBound 2 * offDiagSup (0 : Matrix (Fin 2) (Fin 2) ℝ) ≠
    gateBound 2 * offDiagSup ((fun _ _ => 1) : Matrix (Fin 2) (Fin 2) ℝ)
  have hentry : (1 : ℝ) ≤
      offDiagSup ((fun _ _ => 1) : Matrix (Fin 2) (Fin 2) ℝ) := by
    have h := Finset.le_sup'
      (fun p : Option (Fin 2 × Fin 2) =>
        p.elim (0 : ℝ) (fun e => if e.1 < e.2 then |(1 : ℝ)| else 0))
      (Finset.mem_univ (some ((0 : Fin 2), (1 : Fin 2))))
    norm_num at h
    simpa only [offDiagSup, abs_one] using h
  rw [offDiagSup_zero]
  norm_num [gateBound]
  linarith

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
      (@_root_.D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.source_registration
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
    (realize signature (fun _ n M => gateBound n * offDiagSup M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Optimization.GlobalZZGateTimeBound
    definition := some {
      owner := `D5.S3.Quantum.Optimization.GlobalZZGateTimeBound
      name := `D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Optimization.GlobalZZGateTimeBound
