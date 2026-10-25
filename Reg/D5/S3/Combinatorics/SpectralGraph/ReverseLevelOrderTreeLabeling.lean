import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling
import Reg.Support.DependentFamily
import Mathlib.Combinatorics.SimpleGraph.Star

/-! Source-bound observation of relabeled adjacency entries in tree column tails. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling

open _root_.D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The labeling and the two entry indices retain their complete source domains. -/
abbrev Parameters := Σ n : ℕ, Σ _ : Fin n ≃ Fin n, Σ _ : Fin n, Fin n

abbrev signature : Signature where
  Params := Parameters
  State p := Matrix (Fin p.1) (Fin p.1) ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M => M (p.2.1.symm p.2.2.2) (p.2.1.symm p.2.2.1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep the entire tree, root, reverse-level-order and unique column-tail statement. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (g : SimpleGraph (Fin n)) [DecidableRel g.Adj],
    g.IsTree → ∀ (r : Fin n) (l : Fin n ≃ Fin n),
      @StrictAnti (Fin n) (Fin n) (Preorder.lift (g.dist r)) inferInstance l →
      ∀ i : Fin n, i.val + 1 < n →
        ∃! j : Fin n, i < j ∧ R.readout () ⟨n, l, i, j⟩ (g.adjMatrix ℕ) ≠ 0

private theorem two_vertex_labeling :
    @StrictAnti (Fin 2) (Fin 2)
      (Preorder.lift ((SimpleGraph.starGraph (1 : Fin 2)).dist 1)) inferInstance
      (Equiv.refl (Fin 2)) := by
  intro a b hab
  change (SimpleGraph.starGraph (1 : Fin 2)).dist 1 a <
    (SimpleGraph.starGraph (1 : Fin 2)).dist 1 b at hab
  change b.val < a.val
  have hd : (SimpleGraph.starGraph (1 : Fin 2)).dist 1 0 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr (by simp)
  fin_cases a <;> fin_cases b <;> simp_all

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨j, hj, _⟩ := h 2 (SimpleGraph.starGraph (1 : Fin 2))
    (SimpleGraph.isTree_starGraph 1) 1 (Equiv.refl _) two_vertex_labeling 0 (by decide)
  exact hj.2 rfl

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, Equiv.refl _, 0, 1⟩, 0, (fun _ _ => 1), ?_⟩
  exact Nat.zero_ne_one

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
      (@_root_.D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling.source_registration
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
    (fun _ p M => M (p.2.1.symm p.2.2.2) (p.2.1.symm p.2.2.1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling
      name := `D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling.claim
      path := #[] }
    coordinates := #[0, 5, 7, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling
