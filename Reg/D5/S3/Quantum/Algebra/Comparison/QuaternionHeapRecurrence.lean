import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence
import Reg.Support.DependentFamily

/-! A source-bound audit of the first-kind Chebyshev readout of the quaternion heap recurrence. -/

namespace Reg.D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence
open Polynomial.Chebyshev
open scoped Quaternion InnerProductSpace

noncomputable section

private abbrev signature : Signature where
  Params := ℕ → ℍ[ℝ]
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ x n => (T ℝ (n : ℤ)).eval ⟪x 0, x 1⟫_ℝ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ (x : ℕ → ℍ[ℝ]),
    (Quaternion.normSq (x 0) = 1 ∧ Quaternion.normSq (x 1) = 1 ∧
      ∀ n, x (n + 2) = x (n + 1) * star (x n) * x (n + 1)) ↔
    ∀ n : ℕ, Quaternion.normSq (x n) = 1 ∧
      x (n + 1) = (U ℝ (n : ℤ)).eval ⟪x 0, x 1⟫_ℝ • x 1 -
        (U ℝ ((n : ℤ) - 1)).eval ⟪x 0, x 1⟫_ℝ • x 0 ∧
      ⟪x 0, x n⟫_ℝ = r.readout () x n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfirst : Quaternion.normSq (1 : ℍ[ℝ]) = 1 := map_one _
  have hinput : Quaternion.normSq ((fun _ : ℕ => (1 : ℍ[ℝ])) 0) = 1 ∧
      Quaternion.normSq ((fun _ : ℕ => (1 : ℍ[ℝ])) 1) = 1 ∧
      ∀ n : ℕ, (1 : ℍ[ℝ]) = 1 * star (1 : ℍ[ℝ]) * 1 := ⟨hfirst, hfirst, by simp⟩
  have hfalse := ((h (fun _ => 1)).mp hinput 0).2.2
  change ⟪(1 : ℍ[ℝ]), (1 : ℍ[ℝ])⟫_ℝ = 0 at hfalse
  rw [Quaternion.inner_self, hfirst] at hfalse
  exact one_ne_zero hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let x : ℕ → ℍ[ℝ] := fun n => (-1 : ℍ[ℝ]) ^ n
  refine ⟨x, 0, 1, fun h => ?_⟩
  change (T ℝ 0).eval ⟪x 0, x 1⟫_ℝ = (T ℝ 1).eval ⟪x 0, x 1⟫_ℝ at h
  have hinner : ⟪x 0, x 1⟫_ℝ = -1 := by
    simp [x, Quaternion.inner_def]
  norm_num [hinner] at h

private def source_registration : Registration arena (type_of% @normSq_and_chebyshev) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normSq_and_chebyshev, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def normSq_and_chebyshev_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@normSq_and_chebyshev) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence.normSq_and_chebyshev_unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ x n => (T ℝ (n : ℤ)).eval ⟪x 0, x 1⟫_ℝ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence
