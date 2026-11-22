import D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Register the number of changes of the strict crossing readout. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity

open Finset LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

private abbrev Params := Σ I : Type u, Σ _ : Fintype I, Σ n : ℕ, Σ _ : Fin n → ℕ, I → ℕ

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def changes (p : Params.{u}) (hi : p.1 → ℕ) : ℕ :=
  letI : Fintype p.1 := p.2.1
  let cuts := p.2.2.2.1
  let lo := p.2.2.2.2
  ∑ b : Fin (p.2.2.1 + 1), if paddedParity cuts lo hi b.val =
    paddedParity cuts lo hi (b.val + 1) then 0 else 1

private def actual : Realization signature.{u} :=
  realize signature (fun _ p e => changes p e) (fun a => nomatch a)

private def aboveBound : Realization signature.{u} :=
  realize signature (fun _ p _ => 2 * @Fintype.card p.1 p.2.1 + 1)
    (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [f : Fintype I] {n : ℕ} (cuts : Fin n → ℕ),
    Monotone cuts → ∀ (lo hi : I → ℕ),
      R.readout () ⟨I, f, n, cuts, lo⟩ hi ≤ 2 * Fintype.card I

private def oneCut : Params.{u} :=
  ⟨ULift.{u} PUnit, inferInstance, 1, fun _ => 1, fun _ => 0⟩

private theorem above_bound_fails : ¬ arena.{u}.Law aboveBound.{u} := by
  intro law
  have impossible := law (I := ULift.{u} PUnit) (n := 1) (fun _ => 1)
    (fun _ _ _ => le_rfl) (fun _ => 0) (fun _ => 2)
  change 2 * Fintype.card (ULift.{u} PUnit) + 1 ≤ 2 * Fintype.card (ULift.{u} PUnit)
    at impossible
  omega

def family : Registration arena.{u} (type_of% @changes_le_twice_jumps.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨changes_le_twice_jumps, aboveBound, above_bound_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨aboveBound, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, above_bound_fails⟩
    · intro a
      exact nomatch a
  dependence := by
    intro role
    refine ⟨oneCut, fun _ => 0, fun _ => 2, ?_⟩
    change changes oneCut (fun _ => 0) ≠ changes oneCut (fun _ => 2)
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@changes_le_twice_jumps.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity.changes
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p e => changes p e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity
    definition := none
    coordinates := #[0, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity
