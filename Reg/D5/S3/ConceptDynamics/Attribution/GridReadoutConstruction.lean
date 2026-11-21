import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction
import Reg.Support.SingleDependentReadout

/-! The scaled readout construction observes the support budget of the regular seed orbits. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction

open _root_.D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction
open _root_.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.PermutationGrid (Profile relabel)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Nat

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ k n => k ! * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m n c : ℕ}, 2 ≤ k → 0 < m → 0 < c → k - 1 ∣ m → ∀ w : Fin n → ℕ,
    k * (k - 1) * (∑ j, w j) = c * m →
    (∀ t U : ℕ, 0 < t → k * (t - 1) ≤ U → ∀ x : Fin t → ℕ,
      k * (k - 1) * (∑ i, x i) = U * m →
      ∃ a : Fin n → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
        (∀ i, ∑ j, a j i * w j = c * x i)) →
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S)
      (v : S → ℝ) (f : Profile (Fin k) m → S → Fin k),
      (∀ s, 0 < v s) ∧ (∑ s, v s = 1) ∧ (∀ (g : Equiv.Perm (Fin k)) s, v (g • s) = v s) ∧
      (∀ p i, ∑ s, (if f p s = i then v s else 0) = (p.val i : ℝ) / m) ∧
      (∀ g p s, f (relabel g p) (g • s) = g (f p s)) ∧ Fintype.card S ≤ R.readout () k n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro alternate
  let unitWeights : Fin 1 → ℕ := fun _ => 1
  have cover (t U : ℕ) (_ : 0 < t) (_ : 2 * (t - 1) ≤ U) (x : Fin t → ℕ)
      (h : 2 * (2 - 1) * (∑ i, x i) = U * 2) :
      ∃ a : Fin 1 → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
        (∀ i, ∑ j, a j i * unitWeights j = 1 * x i) := by
    refine ⟨fun _ => x, fun _ => ?_, fun i => ?_⟩
    · change (∑ i, x i) = U
      omega
    · simp [unitWeights]
  obtain ⟨S, _, _, w, _, _, total, _, _, _, budget⟩ :=
    alternate (k := 2) (m := 2) (n := 1) (c := 1)
      (by decide) (by decide) (by decide) (by decide) unitWeights (by decide) cover
  have empty : IsEmpty S := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero budget)
  let _ := empty
  simp at total

def family : Registration arena (type_of% (@law_of_scaled_block_allocations)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨law_of_scaled_block_allocations, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    exact (by decide : (0 : ℕ) ≠ 2)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@law_of_scaled_block_allocations) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction.budget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => k ! * n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction
