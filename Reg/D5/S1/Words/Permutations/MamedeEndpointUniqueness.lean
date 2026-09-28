import D5.S1.Words.Permutations.MamedeEndpointUniqueness
import Reg.Support.DependentFamily

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeEndpointUniqueness
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.MamedeEndpointUniqueness

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
  realize signature (fun _ n _ => wordProduct n [2, 1]) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n k : Nat) (a b : List Nat)
      (_ha : reducedWord n a) (_hb : reducedWord n b)
      (_hca : consecutive a) (_hcb : consecutive b)
      (_he : r.readout () n a = wordProduct n b)
      (_hend : (a.head? = some k ∧ b.head? = some k) ∨
        (a.getLast? = some k ∧ b.getLast? = some k))
      (_hext : (∀ t ∈ a, t ≤ k) ∧ (∀ t ∈ b, t ≤ k) ∨
        (∀ t ∈ a, k ≤ t) ∧ (∀ t ∈ b, k ≤ t)), a = b

theorem rejected_law : ¬ arena.Law rejected := by
  have ha : reducedWord 2 [2] := by
    refine ⟨by simp [validWord], ?_⟩
    intro v _ he
    cases v with
    | nil => revert he; decide
    | cons k v => simp
  have hb : reducedWord 2 [2, 1] := by
    refine ⟨by simp [validWord], ?_⟩
    intro v hv he
    cases v with
    | nil => revert he; decide
    | cons k v =>
      cases v with
      | nil =>
        obtain ⟨hk1, hk2⟩ := hv k (by simp)
        interval_cases k <;> revert he <;> decide
      | cons l v => simp
  intro h
  have := h 2 2 [2] [2, 1] ha hb (by simp [consecutive])
    (by simp [consecutive]) rfl (Or.inl ⟨rfl, rfl⟩)
    (Or.inl ⟨by simp, by simp⟩)
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
  exact ⟨1, [], [1], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨extremal_endpoint_unique, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem extremal_endpoint_unique in arena
  readout via (realize signature
    (fun _ n w => wordProduct n w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeEndpointUniqueness
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

namespace MaximumPeel

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
  realize signature (fun _ n _ => (1 : Equiv.Perm (Fin (n + 1)))) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n M : Nat) (a : List Nat)
      (_hr : reducedWord n (M :: a)) (_hc : consecutive (M :: a))
      (_hb : ∀ k ∈ M :: a, k ≤ M),
    ∃ i q, 1 ≤ i ∧ i ≤ M ∧ M :: a = descending M i ++ q ∧
      (∀ k ∈ q, i < k) ∧
      r.readout () n (M :: a) (position n i) = position n (M + 1)

theorem rejected_law : ¬ arena.Law rejected := by
  have hr : reducedWord 1 [1] := by
    refine ⟨by simp [validWord], ?_⟩
    intro v _ he
    cases v with
    | nil => revert he; decide
    | cons k v => simp
  intro h
  obtain ⟨i, _, hi, hiM, _, _, he⟩ :=
    h 1 1 [] hr (by simp [consecutive]) (by simp)
  have hii : i = 1 := by omega
  subst i
  have hne : position 1 1 ≠ position 1 2 := by decide
  apply hne
  change (1 : Equiv.Perm (Fin 2)) (position 1 1) = position 1 2 at he
  simpa using he

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
  variation := ⟨maximum_peel, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem maximum_peel in arena
  readout via (realize signature
    (fun _ n w => wordProduct n w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeEndpointUniqueness
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration

end MaximumPeel

namespace EndpointOscillation

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
  realize signature (fun _ _ w => segmentLengths (spikes w)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [1, 2, 1]) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n k : Nat) (w : List Nat)
      (_hr : reducedWord n w) (_hc : consecutive w)
      (_hend : w.head? = some k ∨ w.getLast? = some k)
      (_hext : (∀ t ∈ w, t ≤ k) ∨ (∀ t ∈ w, k ≤ t)),
    let lengths := r.readout () n w
    weakIncreasing lengths ∨ weakIncreasing lengths.reverse

theorem rejected_law : ¬ arena.Law rejected := by
  have hr : reducedWord 1 [1] := by
    refine ⟨by simp [validWord], ?_⟩
    intro v _ he
    cases v with
    | nil => revert he; decide
    | cons k v => simp
  intro h
  have hh := h 1 1 [1] hr (by simp [consecutive]) (Or.inl rfl) (Or.inl (by simp))
  simp [rejected, realize, weakIncreasing] at hh

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
  exact ⟨0, [], [1, 2], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨extremal_endpoint_oscillation, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem extremal_endpoint_oscillation in arena
  readout via (realize signature
    (fun _ _ w => segmentLengths (spikes w)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeEndpointUniqueness
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

end EndpointOscillation

end Reg.D5.S1.Words.Permutations.MamedeEndpointUniqueness
