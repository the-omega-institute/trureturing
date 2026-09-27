import D5.S1.Words.Permutations.MamedeDeletionEquiv
import Reg.Support.DependentFamily

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeDeletionEquiv
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv

-- A nonoscillating source with i = j and empty outer words witnesses nonvacuity.
private theorem sample_reduced : reducedWord 3 [2, 1, 2, 3, 2] := by
  refine ⟨by simp [validWord], ?_⟩
  intro v hv hp
  by_contra hn
  have hl : v.length ≤ 4 := by simp only [List.length_cons, List.length_nil] at hn; omega
  rcases v with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩
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
  · simp only [List.length_cons] at hl
    omega

private theorem sample_hs : exactSourceHypotheses 3 1 3 2 2
    (wordProduct 3 [2, 1, 2, 3, 2]) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · decide
  · exact ⟨[2, 1, 2, 3, 2], ⟨sample_reduced, by simp [consecutive], rfl⟩,
      by simp [oscillation, spikes, internalSpikes, segmentLengths, weakIncreasing]⟩

abbrev signature : Signature where
  Params := Σ _ : Nat, Σ _ : Nat, List Nat
  State _ := List Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => imageWord p.1 p.2.1 p.2.2 q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n m M i j : Nat) (σ : Equiv.Perm (Fin (n + 1)))
      (_hs : exactSourceHypotheses n m M i j σ),
    ∃ e : {a : List Nat // singletonWord n σ a} ≃
        {b : List Nat // singletonWord n
          (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b},
      ∀ (a : {a : List Nat // singletonWord n σ a}) (p q : List Nat),
        sourceShape m M i j a.val p q →
          (e a).val = r.readout () ⟨i, j, p⟩ q ∧
          a.val.length = (e a).val.length + (deletedExcursion m M i).length ∧
          0 < (deletedExcursion m M i).length

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, he⟩ := h 3 1 3 2 2 _ sample_hs
  let a : {w : List Nat // singletonWord 3
      (wordProduct 3 [2, 1, 2, 3, 2]) w} :=
    ⟨[2, 1, 2, 3, 2], sample_reduced, by simp [consecutive], rfl⟩
  have hshape : sourceShape 1 3 2 2 a.val [] [] := by
    exact ⟨rfl, by simp, by simp⟩
  obtain ⟨hword, hlength, _⟩ := he a [] [] hshape
  change (e a).val = [] at hword
  rw [hword] at hlength
  norm_num [a, deletedExcursion, descending, ascending] at hlength

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
  exact ⟨⟨2, 2, []⟩, [], [0], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_deletion_equiv, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem source_deletion_equiv in arena
  readout via (realize signature
    (fun _ p q => imageWord p.1 p.2.1 p.2.2 q) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeDeletionEquiv
    coordinates := #[3, 4, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S1.Words.Permutations.MamedeDeletionEquiv
