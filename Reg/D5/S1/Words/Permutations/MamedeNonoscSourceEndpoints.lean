import D5.S1.Words.Permutations.MamedeNonoscSourceEndpoints
import Reg.Support.DependentFamily

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeNonoscSourceEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.MamedeNonoscSourceEndpoints

abbrev signature : Signature where
  Params := Nat
  State _ := List Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [1, 2, 1, 3, 2]) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n m M : Nat) (σ : Equiv.Perm (Fin (n + 1))) (a : List Nat)
      (_ha : singletonWord n σ a) (_hmem : m ∈ a) (_hMem : M ∈ a)
      (_hm : 1 ≤ m) (_hmM : m ≤ M) (_hMn : M ≤ n)
      (_hb : ∀ k ∈ a, m ≤ k ∧ k ≤ M)
      (_hmax : σ (position n (M + 1)) = position n m)
      (_hnon : ¬ oscillation (r.readout () n a)),
    m < M ∧ ∃ i j, m < i ∧ i < M ∧ m < j ∧ j < M ∧
      σ (position n m) = position n (j + 1) ∧
      σ (position n i) = position n (M + 1) ∧
      (∀ x : Fin (n + 1),
        x.val + 1 < m ∨ M + 1 < x.val + 1 → σ x = x)

theorem rejected_law : ¬ arena.Law rejected := by
  have hr : reducedWord 1 [1] := by
    refine ⟨by simp [validWord], ?_⟩
    intro v _ he
    cases v with
    | nil => revert he; decide
    | cons k v => simp
  intro h
  have hh := h 1 1 1 (wordProduct 1 [1]) [1]
    ⟨hr, by simp [consecutive], rfl⟩ (by simp) (by simp)
    (by decide) (by decide) (by decide) (by simp) (by decide)
    (by simp [rejected, realize, oscillation, spikes, internalSpikes,
      segmentLengths, weakIncreasing])
  omega

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨0, [], [1], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_orientation_strict_endpoints, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem first_orientation_strict_endpoints in arena
  readout via (realize signature (fun _ _ w => w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeNonoscSourceEndpoints
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "domain", "arg", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S1.Words.Permutations.MamedeNonoscSourceEndpoints
