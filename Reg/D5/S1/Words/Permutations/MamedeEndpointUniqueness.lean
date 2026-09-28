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

namespace SymmetricExcursion

private theorem sample_reduced : reducedWord 3 [2, 3, 2, 1, 2, 3] := by
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
  Params := Σ _ : Nat, Σ _ : Nat, Σ _ : Nat, List Nat
  State _ := List Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [2]) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n m M : Nat) (p q : List Nat)
      (_hm : 1 ≤ m) (_hmM : m < M) (_hMn : M ≤ n)
      (_hp : ∀ k ∈ p, m < k ∧ k < M)
      (_hq : ∀ k ∈ q, m < k ∧ k < M)
      (_hr : reducedWord n
        (p ++ (descending M m ++ (List.range (M - m)).map (m + 1 + ·)) ++ q))
      (_hc : consecutive
        (p ++ (descending M m ++ (List.range (M - m)).map (m + 1 + ·)) ++ q)),
    p = [] ∨ r.readout () ⟨n, m, M, p⟩ q = []

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 1 3 [2] [] (by decide) (by decide) (by decide)
    (by simp) (by simp) (by change reducedWord 3 [2, 3, 2, 1, 2, 3]; exact sample_reduced)
    (by change consecutive [2, 3, 2, 1, 2, 3]; simp [consecutive])
  simp [rejected, realize] at hh

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
  exact ⟨⟨0, 0, 0, []⟩, [], [1], by decide⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨symmetric_excursion_outer_empty, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem symmetric_excursion_outer_empty in arena
  readout via (realize signature
    (fun _ _ q => q) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeEndpointUniqueness
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end SymmetricExcursion

namespace OppositeExtremalMaps

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
  Law r := ∀ (n m M : Nat) (sigma : Equiv.Perm (Fin (n + 1))) (a : List Nat)
      (_ha : singletonWord n sigma a) (_hmem : m ∈ a) (_hMem : M ∈ a)
      (_hm : 1 ≤ m) (_hmM : m ≤ M) (_hMn : M ≤ n)
      (_hb : ∀ k ∈ a, m ≤ k ∧ k ≤ M)
      (_hmax : sigma (position n (M + 1)) = position n m)
      (_hmin : sigma (position n m) = position n (M + 1)),
    oscillation (r.readout () n a)

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
    (by decide) (by decide) (by decide) (by simp) (by decide) (by decide)
  simp [rejected, realize, oscillation, spikes, internalSpikes,
    segmentLengths, weakIncreasing] at hh

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
  variation := ⟨opposite_extremal_maps_oscillation, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem opposite_extremal_maps_oscillation in arena
  readout via (realize signature (fun _ _ w => w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeEndpointUniqueness
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end OppositeExtremalMaps

namespace WordReversal

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
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n : Nat) (σ : Equiv.Perm (Fin (n + 1))) (w : List Nat),
    (singletonWord n σ⁻¹ w.reverse ↔ singletonWord n σ w) ∧
      (oscillation (r.readout () n w).reverse ↔ oscillation w)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 1 [1, 2, 1, 3, 2]).2
  simp [rejected, realize, oscillation, spikes, internalSpikes,
    segmentLengths, weakIncreasing] at hh

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
  variation := ⟨word_reversal_invariants, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem word_reversal_invariants in arena
  readout via (realize signature (fun _ _ w => w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Permutations.MamedeEndpointUniqueness
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

end WordReversal

end Reg.D5.S1.Words.Permutations.MamedeEndpointUniqueness
