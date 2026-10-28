import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
import Reg.Support.DependentFamily

/-! Source-family registration for strict multipartite coefficient extrema. -/

namespace Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r n m : ℕ}, 2 ≤ r → r ≤ n → 1 ≤ m →
    ∀ a : Fin r → ℕ, (∀ i, 0 < a i) → ∑ i, a i = n →
      (recH (minParts r n) (2 * m) ≤ R.readout () ⟨r, a⟩ (2 * m) ∧
        (R.readout () ⟨r, a⟩ (2 * m) = recH (minParts r n) (2 * m) →
          SameParts a (minParts r n))) ∧
      (R.readout () ⟨r, a⟩ (2 * m) ≤ recH (balancedParts r n) (2 * m) ∧
        (R.readout () ⟨r, a⟩ (2 * m) = recH (balancedParts r n) (2 * m) →
          SameParts a (balancedParts r n)))

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) (n := 2) (m := 1) (by decide) (by decide) (by decide)
    (fun _ => 1) (by intro i; decide) (by simp)
  have hp : 0 < recH (minParts 2 2) 2 :=
    recH_two_mul_pos (by decide) _ (by intro i; simp [minParts]) (m := 1) (by decide)
  exact (not_le_of_gt hp) hh.1.1

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, fun _ => 2⟩, 0, 1, ?_⟩
  change recH (r := 2) (fun _ => 2) 0 ≠ recH (r := 2) (fun _ => 2) 1
  rw [recH_zero, recH_eq _ (show 1 ≤ (1 : ℕ) by decide)]
  norm_num

def source : Registration arena (type_of% @recH_extremal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recH_extremal, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@recH_extremal) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
