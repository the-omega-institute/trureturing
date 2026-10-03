import D5.S1.Words.Permutations.MamedeExtremalOrientation
import Reg.Support.DependentFamily

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeExtremalOrientation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.MamedeExtremalOrientation

abbrev signature : Signature where
  Params := Nat
  State _ := List Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Equiv.Perm (Fin (n + 1))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n w => wordProduct n w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n : Nat) (w : List Nat)
      (_hr : reducedWord n w) (_hc : consecutive w) (_hne : w ≠ []),
    let σ := r.readout () n w
    ∃ m M, 1 ≤ m ∧ m ≤ M ∧ M ≤ n ∧ m ∈ w ∧ M ∈ w ∧
      (∀ k ∈ w, m ≤ k ∧ k ≤ M) ∧
      (∀ x : Fin (n + 1), x.val + 1 < m ∨ M + 1 < x.val + 1 → σ x = x) ∧
      ((σ (position n m) = position n (M + 1) ∧
        ∃ p q, w = p ++ descending M m ++ q ∧
          (∀ k ∈ p, k < M) ∧ (∀ k ∈ q, m < k)) ∨
       (σ (position n (M + 1)) = position n m ∧
        ∃ p q, w = p ++ ascending m M ++ q ∧
          (∀ k ∈ p, m < k) ∧ (∀ k ∈ q, k < M)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : reducedWord 1 [1] := by
    refine ⟨by simp [validWord], ?_⟩
    intro v _ he
    cases v with
    | nil => revert he; decide
    | cons k v => simp
  obtain ⟨m, M, hm, hmM, hMn, _, _, _, _, he⟩ :=
    h 1 [1] hr (by simp [consecutive]) (by simp)
  have hm' : m = 1 := by omega
  have hM' : M = 1 := by omega
  subst m M
  rcases he with ⟨he, _⟩ | ⟨he, _⟩ <;> revert he <;> decide

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
  exact ⟨1, [], [1], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨extremal_orientation, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem extremal_orientation in arena
  readout via (realize signature
    (fun _ n w => wordProduct n w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeExtremalOrientation
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S1.Words.Permutations.MamedeExtremalOrientation
