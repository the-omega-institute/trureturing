import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual

noncomputable section
open scoped BigOperators Classical

namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual

open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

structure Parameters where
  V : Type u
  finite : Fintype V
  equality : DecidableEq V
  graph : SimpleGraph V

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := Configuration p.graph → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.V → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def actual : Realization signature.{u} :=
  realize signature (fun _ p δ => by
    letI := p.finite
    letI := p.equality
    exact blockMoment p.graph δ) (fun e => nomatch e)

@[reducible] def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [finite : Fintype V] [equality : DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool)
    (_proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (_nonzero : ∀ v, Ω v ≠ 0) (u w : V)
    (_largeU : 2 ≤ (G.neighborFinset u).card)
    (_largeW : 2 ≤ (G.neighborFinset w).card)
    (_distinct : G.neighborFinset u ≠ G.neighborFinset w),
    ∃ δ : Configuration G → ℝ,
      (∑ S, δ S) = 0 ∧
      (∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) ∧
      (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * blockMoment G δ v) = 0 ∧
      ∃ v, r.readout () ⟨V, finite, equality, G⟩ δ v ≠ 0

private def square : SimpleGraph (ULift.{u} (Bool × Bool)) where
  Adj x y := x.down.1 ≠ y.down.1
  symm := ⟨by intro x y h; exact h.symm⟩
  loopless := ⟨by intro x h; exact h rfl⟩

private theorem square_centers : ∃ a b : ULift.{u} (Bool × Bool),
    2 ≤ (square.neighborFinset a).card ∧
    2 ≤ (square.neighborFinset b).card ∧
    square.neighborFinset a ≠ square.neighborFinset b := by
  let a : ULift.{u} (Bool × Bool) := ⟨(false, false)⟩
  let b : ULift.{u} (Bool × Bool) := ⟨(true, false)⟩
  have hnA : square.neighborFinset a = {⟨(true, false)⟩, ⟨(true, true)⟩} := by
    ext v
    rcases v with ⟨⟨x, y⟩⟩
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> cases y <;> simp [square, a]
  have hnB : square.neighborFinset b = {⟨(false, false)⟩, ⟨(false, true)⟩} := by
    ext v
    rcases v with ⟨⟨x, y⟩⟩
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> cases y <;> simp [square, b]
  have hd : square.neighborFinset a ≠ square.neighborFinset b := by
    rw [hnA, hnB]
    intro heq
    have ht := congrArg (fun N => a ∈ N) heq
    simp [a] at ht
  exact ⟨a, b, by rw [hnA]; simp, by rw [hnB]; simp, hd⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨a, b, ha, hb, hd⟩ := square_centers
  obtain ⟨δ, _, _, _, v, hv⟩ := h square (fun x => x.down.1)
    (by intro x y hxy; exact hxy)
    (fun _ => 1) (by intro v; norm_num) a b ha hb hd
  exact hv rfl

@[reducible] private def sample : Parameters.{u} where
  V := ULift.{u} (Bool × Bool)
  finite := inferInstance
  equality := inferInstance
  graph := square

private theorem moment_neg {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (δ : Configuration G → ℝ) (v : V) :
    blockMoment G (-δ) v = -blockMoment G δ v := by
  simp only [blockMoment, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

def family : Registration arena.{u}
    (type_of% (@diagonal_residual_of_distinct_neighborhoods.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_residual_of_distinct_neighborhoods.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨a, b, ha, hb, hd⟩ := square_centers
    obtain ⟨δ, _trace, _means, _balance, v, hv⟩ :=
      diagonal_residual_of_distinct_neighborhoods square (fun x => x.down.1)
        (by intro x y hxy; exact hxy) (fun _ => 1) (by intro w; norm_num)
        a b ha hb hd
    refine ⟨sample, δ, -δ, ?_⟩
    intro heq
    have hvv := congrFun heq v
    change blockMoment square δ v = blockMoment square (-δ) v at hvv
    rw [moment_neg] at hvv
    exact hv (by linarith)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonal_residual_of_distinct_neighborhoods.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual.diagonal_residual_of_distinct_neighborhoods.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p δ => by
    letI := p.finite
    letI := p.equality
    exact blockMoment p.graph δ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
