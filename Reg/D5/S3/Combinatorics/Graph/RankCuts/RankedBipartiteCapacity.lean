import D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Register the total odd-rank edge charge as the capacity readout. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity

open Finset
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

private abbrev Params := Σ V : Type u, Σ _ : Fintype V, Σ _ : V → ℕ, V

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.1 → p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def charge (p : Params.{u}) (e : p.1 → p.1 → ℕ) : ℕ := by
  letI : Fintype p.1 := p.2.1
  classical
  exact ∑ a, ∑ b, if a ≠ p.2.2.2 ∧ p.2.2.1 a % 2 = 1 ∧ p.2.2.1 b % 2 = 1
    then e a b else 0

def actual : Realization signature.{u} :=
  realize signature (fun _ p e => charge p e) (fun e => nomatch e)

def constantZero : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law S := ∀ {V : Type u} [f : Fintype V] [DecidableEq V] (rank : V → ℕ)
    (top : V) (k ka kb : ℕ) (e : V → V → ℕ) (R : Finset ℕ),
    (∀ r ∈ R, r < rank top ∧ r % 2 = 1) →
    (∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank a < rank b) →
    (∀ a ≠ top, 1 ≤ ∑ b, e a b) →
    (∀ b ≠ top, 1 ≤ ∑ a, e a b) →
    (∀ a ≠ top, (∑ b, e a b) ≤ k) →
    (∀ b ≠ top, (∑ a, e a b) ≤ k) →
    (∑ b, e top b) ≤ ka →
    (∑ a, e a top) ≤ kb →
    (∑ r ∈ R, max ((univ.filter fun a => rank a ≤ r).card -
        ((univ.filter fun a => rank a < r).card * k + ka))
      ((univ.filter fun a => r ≤ rank a ∧ a ≠ top).card -
        (((univ.filter fun a => r < rank a).erase top).card * k + kb))) ≤
    S.readout () ⟨V, f, rank, top⟩ e

private def testRank (v : ULift.{u} Bool) : ℕ := if v.down then 2 else 1

private def testEdges (a b : ULift.{u} Bool) : ℕ :=
  if a.down = false ∧ b.down = false then 1 else 0

private def testParams : Params.{u} :=
  ⟨ULift.{u} Bool, inferInstance, testRank, ⟨true⟩⟩

private theorem constant_zero_fails : ¬ arena.{u}.Law constantZero.{u} := by
  intro h
  have failure := h testRank ⟨true⟩ 1 0 0 testEdges {1} (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change (1 : ℕ) ≤ 0 at failure
  omega

private theorem charge_congr_decidable {V : Type u} [f : Fintype V] [DecidableEq V]
    (rank : V → ℕ) (top : V) (e : V → V → ℕ) :
    charge ⟨V, f, rank, top⟩ e =
      ∑ a, ∑ b, if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then e a b else 0 := by
  unfold charge
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases h : a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 <;> simp [h]

def family : Registration arena.{u} (type_of% @paid_edges_ge_rank_capacity.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h V f de rank top k ka kb e R hr ho hrl hcl hru hcu htr htc
      change _ ≤ charge ⟨V, f, rank, top⟩ e
      rw [charge_congr_decidable]
      exact h rank top k ka kb e R hr ho hrl hcl hru hcu htr htc
    · intro h V f de rank top k ka kb e R hr ho hrl hcl hru hcu htr htc
      have hh := h rank top k ka kb e R hr ho hrl hcl hru hcu htr htc
      change _ ≤ charge ⟨V, f, rank, top⟩ e at hh
      rwa [charge_congr_decidable] at hh
  variation := ⟨by
    intro V f de rank top k ka kb e R hr ho hrl hcl hru hcu htr htc
    change _ ≤ charge ⟨V, f, rank, top⟩ e
    rw [charge_congr_decidable]
    exact paid_edges_ge_rank_capacity rank top k ka kb e R hr ho hrl hcl hru hcu htr htc,
    constantZero, constant_zero_fails⟩
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
    change charge testParams (fun _ _ => 0) ≠ charge testParams testEdges
    unfold testParams
    rw [charge_congr_decidable, charge_congr_decidable]
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@paid_edges_ge_rank_capacity.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity.charge
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
