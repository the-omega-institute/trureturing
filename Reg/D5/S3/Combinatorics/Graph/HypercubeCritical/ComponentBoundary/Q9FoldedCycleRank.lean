import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank

/-! The two readouts are the residual dimension and the integer negative-degree vector. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false

open scoped Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank

private abbrev rankSignature.{u, v} : Signature where
  Params := Σ V : Type u, Σ E : Type v, Σ _ : Fintype V, Fintype E
  State p := Matrix p.1 p.2.1 (ZMod 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def rankActual.{u, v} : Realization rankSignature.{u, v} :=
  realize rankSignature (fun _ p B => @residualRank _ _ p.2.2.1 p.2.2.2 B) Empty.elim

private def rankRejected.{u, v} : Realization rankSignature.{u, v} :=
  realize rankSignature (fun _ _ _ => 0) Empty.elim

private abbrev rankArena.{u, v} : Arena where
  signature := rankSignature.{u, v}
  Law R := ∀ {V : Type u} {E : Type v} [vType : Fintype V] [eType : Fintype E]
    (B : Matrix V E (ZMod 2)),
    R.readout () ⟨V, E, vType, eType⟩ B + 2 * B.rank = Fintype.card E + (B * Bᵀ).rank

private theorem rankRejected_law.{u, v} : ¬ rankArena.{u, v}.Law rankRejected.{u, v} := by
  intro h
  have bad := h (0 : Matrix (ULift.{u} Unit) (ULift.{v} Unit) (ZMod 2))
  simp [rankRejected, realize] at bad

noncomputable def rankEvidence.{u, v} :
    Registration rankArena.{u, v} (type_of% (@residual_rank_add_twice_rank.{u, v})) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨residual_rank_add_twice_rank, rankRejected, rankRejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rankRejected, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, rankRejected_law⟩
    · intro anchor
      exact nomatch anchor
  dependence := by
    rintro ⟨⟩
    let one : Matrix (ULift.{max u v} Unit) (ULift.{max u v} Unit) (ZMod 2) := 1
    let oneRect : Matrix (ULift.{u} Unit) (ULift.{v} Unit) (ZMod 2) := fun _ _ => 1
    have hb : oneRect.rank = 1 := by
      have h := Matrix.rank_submatrix one
        (Equiv.ulift.trans Equiv.ulift.symm : ULift.{u} Unit ≃ ULift.{max u v} Unit)
        (Equiv.ulift.trans Equiv.ulift.symm : ULift.{v} Unit ≃ ULift.{max u v} Unit)
      have he : one.submatrix
          (Equiv.ulift.trans Equiv.ulift.symm : ULift.{u} Unit ≃ ULift.{max u v} Unit)
          (Equiv.ulift.trans Equiv.ulift.symm : ULift.{v} Unit ≃ ULift.{max u v} Unit) =
          oneRect := by
        ext i j
        simp only [one, oneRect, Matrix.submatrix_apply, Matrix.one_apply]
        rw [ite_eq_left (Subsingleton.elim _ _)]
      rw [he] at h
      simpa [one] using h
    have hl : oneRect * oneRectᵀ = 1 := by
      ext i j
      rw [Matrix.mul_apply]
      simp [oneRect, Matrix.one_apply, show i = j from Subsingleton.elim _ _]
      rfl
    have hz := residual_rank_add_twice_rank
      (0 : Matrix (ULift.{u} Unit) (ULift.{v} Unit) (ZMod 2))
    have ho := residual_rank_add_twice_rank oneRect
    simp at hz
    rw [hb, hl, Matrix.rank_one] at ho
    simp at ho
    refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit, inferInstance, inferInstance⟩, 0, oneRect, ?_⟩
    change residualRank 0 ≠ residualRank oneRect
    omega

noncomputable def rankRegistration.{u, v} :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@residual_rank_add_twice_rank.{u, v}) (Realization rankSignature.{u, v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank.residual_rank_add_twice_rank.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank.rankEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena.{u, v}⟩
  objectArena := .source ⟨rankArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena.{u, v} ⟨rankEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature.{u, v}
    (fun _ p B => @residualRank _ _ p.2.2.1 p.2.2.2 B) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev rowSignature.{u} : Signature.{u + 1, u, 0, u, 0} where
  Params := Σ V : Type u, Σ _ : Fintype V, Σ _ : DecidableEq V,
    Σ G : SimpleGraph V, DecidableRel G.Adj
  State p := p.2.2.2.1.edgeSet → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def rowActual.{u} : Realization rowSignature.{u} :=
  realize rowSignature
    (fun _ p w => @negativeDegree _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w) Empty.elim

private def rowRejected.{u} : Realization rowSignature.{u} :=
  realize rowSignature (fun _ _ _ => 0) Empty.elim

local notation "sw(" G ", " s ", " z ")" => s + Matrix.mulVecLin (Matrix.transpose (incidence G)) z
local notation "target(" G ", " q ")" => (fun v => (SimpleGraph.degree G v : ℤ) - 2 * q v)

private abbrev rowArena.{u} : Arena where
  signature := rowSignature.{u}
  Law R := ∀ {V : Type u} [vType : Fintype V] [vEq : DecidableEq V] (G : SimpleGraph V)
    [adj : DecidableRel G.Adj] (s : G.edgeSet → ZMod 2) (z₀ : V → ZMod 2) (q : V → ℤ),
    (incidence G).mulVecLin (sw(G, s, z₀)) = (fun v => (q v : ZMod 2)) →
    (∀ w, R.readout () ⟨V, vType, vEq, G, adj⟩ w = q →
      ∃ c : Cycles (incidence G), w = sw(G, s, z₀) + (c : G.edgeSet → ZMod 2)) ∧
    ((∃ z, signedRow G (sw(G, s, z)) = target(G, q)) ↔
      ∃ c : Cycles (incidence G), negativeDegree G (sw(G, s, z₀) + c.val) = q ∧
        (bicycles (incidence G)).mkQ c = 0) ∧
    (2 * (incidence G).rank =
        Fintype.card G.edgeSet + (incidence G * (incidence G)ᵀ).rank →
      (∃ w, negativeDegree G w = q) →
      ∃ z, signedRow G (sw(G, s, z)) = target(G, q))

private abbrev oneEdge.{u} : SimpleGraph (ULift.{u} Bool) := ⊤

private theorem rowRejected_law.{u} : ¬ rowArena.{u}.Law rowRejected.{u} := by
  intro h
  have parity : (incidence oneEdge.{u}).mulVecLin (sw(oneEdge.{u}, 0, 0)) =
      fun _ => ((0 : ℤ) : ZMod 2) := by
    change (incidence oneEdge.{u}).mulVecLin (sw(oneEdge.{u}, 0, 0)) = 0
    simp
  obtain ⟨c, hc⟩ := (h oneEdge.{u} 0 0 0 parity).1 (fun _ => 1) rfl
  have hc' : (fun _ => 1 : oneEdge.{u}.edgeSet → ZMod 2) = c.val := by simpa using hc
  have hz := congrFun (LinearMap.mem_ker.mp c.property) (⟨false⟩ : ULift.{u} Bool)
  rw [← hc'] at hz
  exact (by decide :
    (incidence oneEdge.{u}).mulVecLin (fun _ => 1) (⟨false⟩ : ULift.{u} Bool) ≠ 0) hz

def rowEvidence.{u} : Registration rowArena.{u} (type_of% (@exact_signed_rows.{u})) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨exact_signed_rows, rowRejected, rowRejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rowRejected, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, rowRejected_law⟩
    · intro anchor
      exact nomatch anchor
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨ULift.{u} Bool, inferInstance, inferInstance, oneEdge.{u}, inferInstance⟩,
      (fun _ => 0), (fun _ => 1), ?_⟩
    intro eqRows
    exact (by decide :
      negativeDegree oneEdge.{u} (fun _ => 0) ⟨false⟩ ≠
        negativeDegree oneEdge.{u} (fun _ => 1) ⟨false⟩) (congrFun eqRows ⟨false⟩)

def rowRegistration.{u} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exact_signed_rows.{u}) (Realization rowSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank.exact_signed_rows.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank.rowEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rowArena.{u}⟩
  objectArena := .source ⟨rowArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowArena.{u} ⟨rowEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature.{u}
    (fun _ p w => @negativeDegree _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "domain", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank
