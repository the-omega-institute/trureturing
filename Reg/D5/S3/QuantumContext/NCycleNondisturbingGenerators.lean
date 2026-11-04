import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.NCycleNondisturbingGenerators
import Reg.Support.DependentFamily

/-! Source-bound audit of the convex decomposition of binary cyclic laws. -/

namespace Reg.D5.S3.QuantumContext.NCycleNondisturbingGenerators

open _root_.D5.S3.QuantumContext.NCycleNondisturbingGenerators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds (deterministicPostprocess)

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe each context probability occurring in the nonnegativity hypothesis. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : Fin n, Σ _ : Bool, Bool
  State q := Fin q.1 → Bool → Bool → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q r => r q.2.1 q.2.2.1 q.2.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ r : Fin n → Bool → Bool → ℝ,
    (∀ i b c, 0 ≤ R.readout () ⟨n, i, b, c⟩ r) → (∀ i, ∑ b, ∑ c, r i b c = 1) →
    (∀ i c, ∑ b, r i b c = ∑ d, r (finRotate n i) c d) →
    r ∈ convexHull ℝ (allGenerators n)

private def diagonal : Fin 1 → Bool → Bool → ℝ :=
  fun _ b c => if b = c then if b then -1 else 2 else 0

private theorem diagonal_normalized (i : Fin 1) : ∑ b, ∑ c, diagonal i b c = 1 := by
  simp only [Fintype.sum_bool]
  norm_num [diagonal]

private theorem diagonal_consistent (i : Fin 1) (c : Bool) :
    ∑ b, diagonal i b c = ∑ d, diagonal (finRotate 1 i) c d := by
  cases c <;> norm_num [diagonal, Fintype.sum_bool]

private theorem hull_nonneg {n : ℕ} {r : Fin n → Bool → Bool → ℝ}
    (hr : r ∈ convexHull ℝ (allGenerators n)) (i : Fin n) (b c : Bool) :
    0 ≤ r i b c := by
  have hsub : allGenerators n ⊆ {r : Fin n → Bool → Bool → ℝ | 0 ≤ r i b c} := by
    rintro r (⟨s, rfl⟩ | ⟨γ, rfl⟩) <;> simp only [Set.mem_ofPred_eq]
    · dsimp only [deterministicPostprocess]
      split_ifs <;> norm_num
    · dsimp only [D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation.parityBox]
      split_ifs <;> norm_num
  apply convexHull_min hsub ?_ hr
  exact (convex_Ici (𝕜 := ℝ) (0 : ℝ)).linear_preimage
    ((LinearMap.proj (R := ℝ) c : (Bool → ℝ) →ₗ[ℝ] ℝ).comp
      ((LinearMap.proj (R := ℝ) b : (Bool → Bool → ℝ) →ₗ[ℝ] Bool → ℝ).comp
        (LinearMap.proj (R := ℝ) i :
          (Fin n → Bool → Bool → ℝ) →ₗ[ℝ] Bool → Bool → ℝ)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) diagonal (fun _ _ _ => le_rfl) diagonal_normalized
    diagonal_consistent
  have hb := hull_nonneg hbad 0 true true
  norm_num [diagonal] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, false, false⟩, (fun _ _ _ => 0), (fun _ _ _ => 1), ?_⟩
  exact zero_ne_one

def source_registration : Registration arena (type_of% @decomposition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨decomposition, rejected, rejected_law⟩
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
    (fun _ q r => r q.2.1 q.2.2.1 q.2.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.NCycleNondisturbingGenerators
    definition := none
    coordinates := #[0, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.QuantumContext.NCycleNondisturbingGenerators.decomposition
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumContext.NCycleNondisturbingGenerators
