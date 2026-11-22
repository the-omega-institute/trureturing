import D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.CutFactorization
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel
open _root_.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazard (hit)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology

abbrev Params := ℕ
abbrev signature : Signature where
  Params := Params
  State k := UnboundedTuple k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ p => tupleHits p) (fun a => nomatch a)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => True) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (e : ℤ) (K H : ℕ),
    ∀ᶠ n in atTop, ∀ (big : Tuple.threshold K H k < n) (p : Tuple K H k)
      (π : Avoider n), p.Event n big π →
        (actualCanonicalFirstKLiteralHit k e n π ↔ R.readout () k p.erase e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd := actualCanonicalFirstKLiteralHit_eventually_agrees 0 0 0 0
  have hr := h 0 0 0 0
  have ht := Filter.eventually_gt_atTop (Tuple.threshold 0 0 0)
  obtain ⟨n, hD, hR, hN⟩ := (hd.and (hr.and ht)).exists
  have hz := (hR hN () (identityAvoider n) trivial).mpr trivial
  exact (hD hN () (identityAvoider n) trivial).mp hz

private def singletonDirect : Indecomposable false 1 :=
  ⟨identityAvoider 1, by rintro ⟨cut, hc, ht, _⟩; omega⟩

private def singletonTuple : Tuple 1 1 1 :=
  (⟨false, .inl ⟨0, singletonDirect⟩⟩, ())

private theorem singleton_hits : tupleHits singletonTuple.erase 0 := by
  apply Or.inl
  change false = false ∧ hitsDiagonal singletonDirect.val.val 0
  refine ⟨rfl, ⟨0, ?_⟩⟩
  have h : singletonDirect.val.val (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [h, sub_self]

private def skewSingleton : Indecomposable true 1 :=
  ⟨identityAvoider 1, by rintro ⟨cut, hc, ht, _⟩; omega⟩

private def skewTuple : Tuple 1 1 1 :=
  (⟨true, .inl ⟨0, skewSingleton⟩⟩, ())

private theorem skew_not_hits : ¬ tupleHits skewTuple.erase 0 := by
  change ¬ ((true = false ∧ _) ∨ False)
  simp

def family : Registration arena (type_of% @actualCanonicalFirstKLiteralHit_eventually_agrees) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualCanonicalFirstKLiteralHit_eventually_agrees, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩
    · intro a; exact nomatch a
  dependence := by
    intro i
    refine ⟨(1 : ℕ), singletonTuple.erase, skewTuple.erase, ?_⟩
    intro h
    change tupleHits singletonTuple.erase = tupleHits skewTuple.erase at h
    have hh := congrFun h (0 : ℤ)
    exact skew_not_hits (hh ▸ singleton_hits)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualCanonicalFirstKLiteralHit_eventually_agrees) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => tupleHits p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","body","body","body","body","body","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
