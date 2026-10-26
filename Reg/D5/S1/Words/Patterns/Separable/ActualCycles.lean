import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.ActualCycles
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.CutFactorization
open _root_.D5.S1.Words.Patterns.Separable.StableEndpointCodes
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => nhds z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ K H k n (large : Tuple.threshold K H k < n)
      (first last : Tuple K H k) (π : Avoider n),
      first.Event n large π → last.Event n large π → first = last) ∧
    (∀ K H k n (large : Tuple.threshold K H k < n) (tuple : Tuple K H k),
      0 < n - tuple.size ∧
      Nat.card {π : Avoider n // tuple.Event n large π} =
        Nat.card (Avoider (n - tuple.size)) ∧
      actualMass n (tuple.Event n large) =
        (Nat.card (Avoider (n - tuple.size)) : ℝ) / Nat.card (Avoider n)) ∧
    (∀ K H k (tuple : Tuple K H k),
      Tendsto tuple.probability atTop (R.readout () () (rho ^ tuple.size))) ∧
    (∀ K H k n (large : Tuple.threshold K H k < n),
      Nat.card {π : Avoider n // Success K H k n large π} =
        ∑ tuple : Tuple K H k, Nat.card (Avoider (n - tuple.size))) ∧
    (∀ K H k n, actualMass n (Failed K H k n) = 1 - successProbability K H k n) ∧
    (∀ K H k, Tendsto (successProbability K H k) atTop
      (𝓝 (∑ tuple : Tuple K H k, rho ^ tuple.size))) ∧
    (∀ k (ε : ℝ), 0 < ε →
      ∃ K H N : ℕ, ∀ n ≥ N, actualMass n (Failed K H k n) < ε) ∧
    (∀ k (tuple : UnboundedTuple k),
      ∃ K H : ℕ, ∃ bounded : Tuple K H k, bounded.erase = tuple ∧
        Tendsto bounded.probability atTop (𝓝 (rho ^ tuple.size))) ∧
    (∀ K H n (large : H * K + max (2 * K) 1 < n) (π : Avoider n),
      (∃ c : Family K H, (history c.stable n (by omega)).Event π) ↔ FirstSuccess K H n π)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact Filter.atTop_neBot.ne (Filter.tendsto_bot_right_iff.mp (law.2.2.1 0 0 0 ()))

def family : Registration arena (type_of% @actual_complete_cycles) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_complete_cycles, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    exact nhds_injective.ne (by norm_num)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_complete_cycles) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycles.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.ActualCycles.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => nhds z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.ActualCycles
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Words.Patterns.Separable.ActualCycles
