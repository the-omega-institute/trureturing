import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Optimization.PrepareMeasureLkBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the uniform strict prepare-and-measure bound. -/

namespace Reg.D5.S3.Quantum.Optimization.PrepareMeasureLkBound

open _root_.D5.S3.Quantum.Optimization.PrepareMeasureLkBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the partition functional for every rank parameter and matrix size. -/
abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State p := Matrix (Fin p.2.1) (Fin p.2.2) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M => Lk p.1 M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain the uniform constant, its strict bound, and every rectangular matrix. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, c < k ∧
    ∀ n m (M : Matrix (Fin n) (Fin m) ℝ),
      r.readout () ⟨k, n, m⟩ M ≤ c * L M

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, _, hc⟩ := h 3 (by norm_num)
  have hbad := hc 1 1 0
  have hzero : L (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
    simp [L]
  change (1 : ℝ) ≤ c * L (0 : Matrix (Fin 1) (Fin 1) ℝ) at hbad
  rw [hzero, mul_zero] at hbad
  exact (not_le_of_gt zero_lt_one) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 1⟩, 0, (fun _ _ => 1), ?_⟩
  change Lk 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) ≠
    Lk 1 ((fun _ _ => 1) : Matrix (Fin 1) (Fin 1) ℝ)
  change
    (Finset.univ : Finset (Fin 1 → Fin 1)).sup' Finset.univ_nonempty
      (fun f => manhattan (fun j q => fiberSum f (0 : Matrix (Fin 1) (Fin 1) ℝ) j q)) ≠
    (Finset.univ : Finset (Fin 1 → Fin 1)).sup' Finset.univ_nonempty
      (fun f => manhattan (fun j q => fiberSum f (fun _ _ => 1) j q))
  simp [manhattan, fiberSum, eq_iff_true_of_subsingleton]

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
      (@_root_.D5.S3.Quantum.Optimization.PrepareMeasureLkBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Optimization.PrepareMeasureLkBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Optimization.PrepareMeasureLkBound.source_registration
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
    (realize signature (fun _ p M => Lk p.1 M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Optimization.PrepareMeasureLkBound
    definition := some {
      owner := `D5.S3.Quantum.Optimization.PrepareMeasureLkBound
      name := `D5.S3.Quantum.Optimization.PrepareMeasureLkBound.claim
      path := #[] }
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Optimization.PrepareMeasureLkBound
