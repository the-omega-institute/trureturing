import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates

noncomputable section
open scoped BigOperators Classical

namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates

open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private residual_eq_ker from
  D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

structure Parameters where
  V : Type u
  finite : Fintype V
  equality : DecidableEq V
  graph : SimpleGraph V
  family : Finset (Finset V)
  member : family

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := Configuration p.graph → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def actual : Realization signature.{u} :=
  realize signature (fun _ p δ => by
    letI := p.finite
    letI := p.equality
    exact blockingMoment p.graph p.member.val δ) (fun e => nomatch e)

@[reducible] def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [finite : Fintype V] [equality : DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V))
    (_independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (_large : ∀ N ∈ F, 2 ≤ N.card) (x : F → ℝ),
    ∃ δ : Configuration G → ℝ,
      (∑ S, δ S) = 0 ∧
      (∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) ∧
      ∀ N : F, r.readout () ⟨V, finite, equality, G, F, N⟩ δ = x N

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} (Fin 2) := ⟨0⟩
  let b : ULift.{u} (Fin 2) := ⟨1⟩
  have hab : a ≠ b := by simp [a, b]
  obtain ⟨δ, _, _, hδ⟩ := h (V := ULift.{u} (Fin 2)) (⊥) {{a,b}}
    (by simp) (by intro N hN; simp only [Finset.mem_singleton] at hN; subst N; simp [hab])
    (fun _ => 1)
  have hh := hδ ⟨{a,b}, by simp⟩
  norm_num [rejected, realize] at hh

@[reducible] private def sample : Parameters.{u} where
  V := ULift.{u} (Fin 2)
  finite := inferInstance
  equality := inferInstance
  graph := ⊥
  family := {{⟨0⟩, ⟨1⟩}}
  member := ⟨{⟨0⟩, ⟨1⟩}, by simp⟩

private theorem sample_independent : ∀ N ∈ sample.{u}.family,
    ∀ a ∈ N, ∀ b ∈ N, ¬sample.{u}.graph.Adj a b := by simp [sample]

private theorem sample_large : ∀ N ∈ sample.{u}.family, 2 ≤ N.card := by
  intro N hN
  simp only [sample, Finset.mem_singleton] at hN
  subst N
  change 2 ≤ ({(⟨0⟩ : ULift.{u} (Fin 2)), (⟨1⟩ : ULift.{u} (Fin 2))} :
    Finset (ULift.{u} (Fin 2))).card
  have hne : (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ := by decide
  simp [hne]

def family : Registration arena.{u}
    (type_of% (@arbitrary_diagonal_blocking_coordinates.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@arbitrary_diagonal_blocking_coordinates.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨δ₀, _trace₀, _mean₀, h₀⟩ := arbitrary_diagonal_blocking_coordinates
      sample.graph sample.family sample_independent sample_large (fun _ => 0)
    obtain ⟨δ₁, _trace₁, _mean₁, h₁⟩ := arbitrary_diagonal_blocking_coordinates
      sample.graph sample.family sample_independent sample_large (fun _ => 1)
    refine ⟨sample, δ₀, δ₁, ?_⟩
    intro heq
    have hz : actual.readout i sample δ₀ = 0 := h₀ sample.member
    have hone : actual.readout i sample δ₁ = 1 := h₁ sample.member
    rw [hz, hone] at heq
    exact zero_ne_one heq

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@arbitrary_diagonal_blocking_coordinates.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates.arbitrary_diagonal_blocking_coordinates.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates.family
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
    exact blockingMoment p.graph p.member.val δ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

namespace Dimension

structure Parameters where
  V : Type u
  finite : Fintype V
  equality : DecidableEq V
  graph : SimpleGraph V
  family : Finset (Finset V)

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := p.family → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def actual : Realization signature.{u} :=
  realize signature (fun _ p weight => by
    letI := p.finite
    letI := p.equality
    exact Module.finrank ℝ (attainableResidual p.graph p.family weight)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [finite : Fintype V] [equality : DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V))
    (_independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (_large : ∀ N ∈ F, 2 ≤ N.card) (weight : F → ℝ)
    (_nonzero : ∃ N, weight N ≠ 0),
    r.readout () ⟨V, finite, equality, G, F⟩ weight = F.card - 1

/-- The source is reconstructed, while the dimension readout is invariant
under every source-admissible nonzero weight. -/
theorem source_equivalence :
    (type_of% (@residual_dimension_exact.{u})) ↔ arena.{u}.Law actual := Iff.rfl

#print axioms source_equivalence

end Dimension

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
