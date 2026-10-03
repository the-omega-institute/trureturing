import D5.S1.Words.Permutations.MamedeFactorSeparation
import Reg.Support.DependentFamily

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeFactorSeparation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.MamedeFactorSeparation

-- An inhabited j<i source with both outer subwords empty.
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
  Law t := ∀ (n m M i j : Nat) (a b p q r s : List Nat)
      (_hm : 1 ≤ m) (_hmj : m < j) (_hji : j < i) (_hiM : i < M) (_hMn : M ≤ n)
      (_ha : reducedWord n a) (_hb : reducedWord n b)
      (_hca : consecutive a) (_hcb : consecutive b)
      (_he : wordProduct n a = wordProduct n b)
      (_hshape : sourceShape m M i j a p q)
      (_hshape' : sourceShape m M i j b r s), t.readout () () a = b

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : sourceShape 1 4 3 2 [2, 1, 2, 3, 4, 3] [] [] := by
    exact ⟨rfl, by simp, by simp⟩
  have := h 4 1 4 3 2 [2, 1, 2, 3, 4, 3] [2, 1, 2, 3, 4, 3] [] [] [] []
    (by decide) (by decide) (by decide) (by decide) (by decide)
    sample_reduced sample_reduced (by simp [consecutive]) (by simp [consecutive])
    rfl hs hs
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
  variation := ⟨source_shape_unique_of_j_lt_i, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem source_shape_unique_of_j_lt_i in arena
  readout via (realize signature (fun _ _ w => w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeFactorSeparation
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S1.Words.Permutations.MamedeFactorSeparation
