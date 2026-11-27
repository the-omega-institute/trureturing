import D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Register the diagonal multiplicity modulo two as the readout of the rank cut. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity

open Finset
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

private abbrev Params := Σ V : Type u, Σ _ : Fintype V, Σ _ : V → ℕ, Σ _ : V, ℕ

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.1 → p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def diagonal (p : Params.{u}) (e : p.1 → p.1 → ℕ) : ℕ :=
  letI : Fintype p.1 := p.2.1
  (∑ a ∈ univ.filter (fun a => p.2.2.1 a = p.2.2.2.2), e a a) % 2

def actual : Realization signature.{u} :=
  realize signature (fun _ p e => diagonal p e) (fun e => nomatch e)

def constantZero : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [f : Fintype V] (rank : V → ℕ) (top : V) (r : ℕ)
    (e : V → V → ℕ), r < rank top →
    (∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank a < rank b) →
    (∀ a ∈ univ.filter (fun a => rank a ≤ r), (∑ b, e a b) % 2 = 1) →
    (∀ b ∈ univ.filter (fun b => rank b ≤ r), (∑ a, e a b) % 2 = 1) →
    R.readout () ⟨V, f, rank, top, r⟩ e =
      ((univ.filter fun a => rank a = r).card +
        (∑ b ∈ univ.filter (fun b => rank b ≤ r), e top b) +
        ∑ a ∈ univ.filter (fun a => rank a < r),
          ∑ b ∈ univ.filter (fun b => r < rank b), e a b) % 2

private def testRank (v : ULift.{u} Bool) : ℕ := if v.down then 1 else 0

private def testEdges (a b : ULift.{u} Bool) : ℕ :=
  if a.down = false ∧ b.down = false then 1 else 0

private def testParams : Params.{u} :=
  ⟨ULift.{u} Bool, inferInstance, testRank, ⟨true⟩, 0⟩

private theorem constant_zero_fails : ¬ arena.{u}.Law constantZero.{u} := by
  intro h
  have failure := h testRank ⟨true⟩ 0 testEdges (by decide)
    (by decide) (by decide) (by decide)
  have rhs : ((univ.filter fun a : ULift.{u} Bool => testRank a = 0).card +
      (∑ b ∈ univ.filter (fun b : ULift.{u} Bool => testRank b ≤ 0), testEdges ⟨true⟩ b) +
      ∑ a ∈ univ.filter (fun a : ULift.{u} Bool => testRank a < 0),
        ∑ b ∈ univ.filter (fun b : ULift.{u} Bool => 0 < testRank b), testEdges a b) % 2 = 1 := by
    decide
  exact (by decide : (0 : ℕ) ≠ 1) (failure.trans rhs)

def family : Registration arena.{u} (type_of% @diagonal_parity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_parity, constantZero, constant_zero_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨constantZero, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, constant_zero_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨testParams, fun _ _ => 0, testEdges, ?_⟩
    change diagonal testParams (fun _ _ => 0) ≠ diagonal testParams testEdges
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@diagonal_parity.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity.diagonal
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p e => diagonal p e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
