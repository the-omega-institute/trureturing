import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.RegularCHS.Defs
import Reg.Support.DependentFamily

/-! Source operand registrations for regular graph CHS coefficients. -/

namespace Reg.D5.S3.Combinatorics.Graph.RegularCHS.Defs
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
noncomputable section
open Classical

private abbrev signature : Signature where
  Params := ℕ
  State n := SimpleGraph (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ G => G.adjMatrix ℝ) (fun e => nomatch e)

private theorem actual_eq (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    actual.readout () n G = G.adjMatrix ℝ := by
  ext i j
  by_cases h : G.Adj i j <;> simp [actual, realize, SimpleGraph.adjMatrix_apply, h]

private def rejected : Realization signature :=
  realize signature (fun _ _ _ i j => if i.val = 0 ∧ j.val = 1 then 1 else 0)
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (R.readout () n G).IsHermitian

private theorem rejected_not_hermitian : ¬ arena.Law rejected := by
  intro h
  have he := (h (⊥ : SimpleGraph (Fin 2))).apply 0 1
  norm_num [rejected, realize] at he

def adjMatrix_isHermitianFamily : Registration arena (type_of% @adjMatrix_isHermitian) where
  actual := actual
  bridge := by
    constructor
    · intro h n G inst
      rw [actual_eq]
      exact h G
    · intro h n G inst
      rw [← actual_eq n G]
      exact h G
  variation := ⟨by
    intro n G inst
    rw [actual_eq]
    exact adjMatrix_isHermitian G, rejected, rejected_not_hermitian⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_hermitian⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨2, ⊥, ⊤, ?_⟩
    intro he
    have he' : (⊥ : SimpleGraph (Fin 2)).adjMatrix ℝ =
        (⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ :=
      (actual_eq 2 (⊥ : SimpleGraph (Fin 2))).symm.trans
        (he.trans (actual_eq 2 (⊤ : SimpleGraph (Fin 2))))
    have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) he'
    norm_num [actual, realize, SimpleGraph.adjMatrix_apply, SimpleGraph.bot_adj, SimpleGraph.top_adj] at hentry

def adjMatrix_isHermitianAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjMatrix_isHermitian) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Defs.adjMatrixIsHermitianUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Defs.adjMatrix_isHermitianFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨adjMatrix_isHermitianFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ G => G.adjMatrix ℝ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.RegularCHS.Defs
