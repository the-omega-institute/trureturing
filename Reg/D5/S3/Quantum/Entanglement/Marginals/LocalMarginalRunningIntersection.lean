import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift

/-! Source-equivalence registration for the rank formula with adjacent overlap counts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRank
open _root_.D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection

universe u v
noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] {K : Type v} [Field K]
    {allowed : Finset V → Prop} (_closed : DownwardClosed allowed) (regions : List (Finset V))
    (_h : RunningIntersection regions),
    R.readout () ()
      (Module.finrank K (marginalMap (allowed := allowed) (K := K) {s | s ∈ regions}).range +
        (regions.zipWith (fun s t => regionPairCount allowed (s ∩ t)) regions.tail).sum)
      (regions.map (regionPairCount allowed)).sum

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have closed : DownwardClosed (fun _ : Finset (ULift.{u} Unit) => True) := by
    unfold DownwardClosed
    intros
    exact True.intro
  exact @h (ULift.{u} Unit) _ _ (ULift.{v} ℚ) _ (fun _ => True) closed [] trivial

def family : Registration arena.{u,v} (type_of% @finrank_add_adjacentOverlap.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finrank_add_adjacentOverlap, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact Nat.one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finrank_add_adjacentOverlap.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection.finrank_add_adjacentOverlap.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection
