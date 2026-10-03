import D5.S1.Words.Permutations.MamedeOrderFreeFiber
import Reg.Support.DependentFamily

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeOrderFreeFiber
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.MamedeOrderFreeFiber

private theorem sample_reduced : reducedWord 4 [2, 1, 2, 3, 4, 3] := by
  refine ⟨by simp [validWord], ?_⟩
  intro v hv hp
  by_contra hn
  have hl : v.length ≤ 5 := by simp only [List.length_cons, List.length_nil] at hn; omega
  rcases v with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, tail⟩⟩⟩⟩⟩⟩
  · revert hp; decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    interval_cases a <;> revert hp <;> decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    obtain ⟨hb0, hb1⟩ := hv b (by simp)
    interval_cases a <;> interval_cases b <;> revert hp <;> decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    obtain ⟨hb0, hb1⟩ := hv b (by simp)
    obtain ⟨hc0, hc1⟩ := hv c (by simp)
    interval_cases a <;> interval_cases b <;> interval_cases c <;> revert hp <;> decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    obtain ⟨hb0, hb1⟩ := hv b (by simp)
    obtain ⟨hc0, hc1⟩ := hv c (by simp)
    obtain ⟨hd0, hd1⟩ := hv d (by simp)
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      interval_cases d <;> revert hp <;> decide
  · obtain ⟨ha0, ha1⟩ := hv a (by simp)
    obtain ⟨hb0, hb1⟩ := hv b (by simp)
    obtain ⟨hc0, hc1⟩ := hv c (by simp)
    obtain ⟨hd0, hd1⟩ := hv d (by simp)
    obtain ⟨he0, he1⟩ := hv e (by simp)
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      interval_cases d <;> interval_cases e <;> revert hp <;> decide
  · simp only [List.length_cons] at hl
    omega

private theorem sample_endpoints :
    let σ := wordProduct 4 [2, 1, 2, 3, 4, 3]
    σ (position 4 5) = position 4 1 ∧
    σ (position 4 1) = position 4 3 ∧
    σ (position 4 3) = position 4 5 ∧
    (∀ k : Fin 5, k.val + 1 < 1 ∨ 5 < k.val + 1 → σ k = k) := by
  decide

abbrev signature : Signature where
  Params := Unit
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
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law t := ∀ (n m M i j : Nat) (σ : Equiv.Perm (Fin (n + 1)))
      (_hm : 1 ≤ m) (_hmj : m < j) (_hji : j < i) (_hiM : i < M) (_hMn : M ≤ n)
      (_hmax : σ (position n (M + 1)) = position n m)
      (_hj : σ (position n m) = position n (j + 1))
      (_hi : σ (position n i) = position n (M + 1))
      (_hfixed : ∀ k : Fin (n + 1),
        k.val + 1 < m ∨ M + 1 < k.val + 1 → σ k = k)
      (a b : List Nat) (_ha : singletonWord n σ a) (_hb : singletonWord n σ b),
      t.readout () () a = b

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let a : List Nat := [2, 1, 2, 3, 4, 3]
  let σ := wordProduct 4 a
  have hs := sample_endpoints
  have ha : singletonWord 4 σ a :=
    ⟨sample_reduced, by simp [a, consecutive], rfl⟩
  have hfalse := h 4 1 4 3 2 σ
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    a a ha ha
  contradiction

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
  exact ⟨(), [], [0], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨singleton_fiber_unique_of_j_lt_i, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem singleton_fiber_unique_of_j_lt_i in arena
  readout via (realize signature (fun _ _ w => w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeOrderFreeFiber
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 15 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S1.Words.Permutations.MamedeOrderFreeFiber
