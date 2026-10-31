import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.NCycleNondisturbingGenerators
import Reg.Support.DependentFamily

/-! Source-bound audit of the convex decomposition of binary cyclic laws. -/

namespace Reg.D5.S3.QuantumContext.NCycleNondisturbingGenerators

open _root_.D5.S3.QuantumContext.NCycleNondisturbingGenerators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe membership in the stated convex hull at each cycle size. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Bool → Bool → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ n r => @decide (r ∈ convexHull ℝ (allGenerators n)) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ r : Fin n → Bool → Bool → ℝ,
    (∀ i b c, 0 ≤ r i b c) → (∀ i, ∑ b, ∑ c, r i b c = 1) →
    (∀ i c, ∑ b, r i b c = ∑ d, r (finRotate n i) c d) →
    R.readout () n r = true

private def diagonal : Fin 1 → Bool → Bool → ℝ :=
  fun _ b c => if b = false ∧ c = false then 1 else 0

private theorem diagonal_nonneg (i : Fin 1) (b c : Bool) : 0 ≤ diagonal i b c := by
  simp only [diagonal]
  split_ifs <;> norm_num

private theorem diagonal_normalized (i : Fin 1) : ∑ b, ∑ c, diagonal i b c = 1 := by
  simp only [Fintype.sum_bool]
  norm_num [diagonal]

private theorem diagonal_consistent (i : Fin 1) (c : Bool) :
    ∑ b, diagonal i b c = ∑ d, diagonal (finRotate 1 i) c d := by
  cases c <;> norm_num [diagonal, Fintype.sum_bool]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) diagonal diagonal_nonneg diagonal_normalized
    diagonal_consistent
  change false = true at hbad
  contradiction

private theorem hull_nonneg {n : ℕ} {r : Fin n → Bool → Bool → ℝ}
    (hr : r ∈ convexHull ℝ (allGenerators n)) (i : Fin n) (b c : Bool) :
    0 ≤ r i b c := by
  have hsub : allGenerators n ⊆ {r : Fin n → Bool → Bool → ℝ | 0 ≤ r i b c} := by
    rintro r (⟨s, rfl⟩ | ⟨γ, rfl⟩) <;> simp only [Set.mem_ofPred_eq] <;>
      split_ifs <;> norm_num
  apply convexHull_min hsub ?_ hr
  intro x hx y hy u v hu hv _
  exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, diagonal, (fun _ _ _ => -1), ?_⟩
  have hyes : diagonal ∈ convexHull ℝ (allGenerators 1) :=
    decomposition 1 (by norm_num) diagonal diagonal_nonneg diagonal_normalized
      diagonal_consistent
  have hno : (fun _ _ _ => (-1 : ℝ)) ∉ convexHull ℝ (allGenerators 1) := by
    intro h
    have hb := hull_nonneg h 0 false false
    norm_num at hb
  simp [actual, realize, hyes, hno]

def source_registration : Registration arena (type_of% @decomposition) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [actual, realize, arena] using decomposition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.NCycleNondisturbingGenerators.decomposition)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.NCycleNondisturbingGenerators.unit
  realizationName := `Reg.D5.S3.QuantumContext.NCycleNondisturbingGenerators.source_registration
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
    (fun _ n r => @decide (r ∈ convexHull ℝ (allGenerators n)) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.NCycleNondisturbingGenerators
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.QuantumContext.NCycleNondisturbingGenerators.decomposition
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumContext.NCycleNondisturbingGenerators
