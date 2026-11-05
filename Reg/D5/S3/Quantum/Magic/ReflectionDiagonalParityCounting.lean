import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
import Reg.Support.DependentFamily

/-! Source-bound audit of the parity-network label-count lower bound. -/

namespace Reg.D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting

open _root_.D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the number of updates in a network of the selected width. -/
abbrev signature : Signature where
  Params := ℕ
  State m := List (Fin m × Fin m)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ gs => gs.length) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep the initial/final parity and complete output-coverage hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {m : ℕ}, 0 < m → ∀ (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool),
    (∀ j, (∑ i, ls j i) = true) →
    (∀ j, (∑ i, labels gs ls j i) = true) →
    (∀ v : Fin m → Bool, (∑ i, v i) = false → v ≠ 0 → v ∈ outputs gs ls) →
    2 ^ (m - 1) + m - 2 ≤ r.readout () m gs

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hstart : ∀ j : Fin 2, (∑ i : Fin 2, (j == i)) = true := by decide
  have hend : ∀ j : Fin 2,
      (∑ i : Fin 2, labels [(0, 1), (0, 1)] (fun j i => j == i) j i) = true := by
    decide
  have hseen : ∀ v : Fin 2 → Bool, (∑ i, v i) = false → v ≠ 0 →
      v ∈ outputs [(0, 1), (0, 1)] (fun j i => j == i) := by decide
  have hbad := h (by decide : 0 < 2) [(0, 1), (0, 1)]
    (fun j i => j == i) hstart hend hseen
  change 2 ^ (2 - 1) + 2 - 2 ≤ (0 : ℕ) at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, [], [(0, 0)], ?_⟩
  change (0 : ℕ) ≠ 1
  decide

def source_registration : Registration arena
    (∀ {m : ℕ}, 0 < m → ∀ (gs : List (Fin m × Fin m))
      (ls : Fin m → Fin m → Bool),
      (∀ j, (∑ i, ls j i) = true) →
      (∀ j, (∑ i, labels gs ls j i) = true) →
      (∀ v : Fin m → Bool, (∑ i, v i) = false → v ≠ 0 → v ∈ outputs gs ls) →
      2 ^ (m - 1) + m - 2 ≤ gs.length) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting.count_bound)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ gs => gs.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting.count_bound
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
