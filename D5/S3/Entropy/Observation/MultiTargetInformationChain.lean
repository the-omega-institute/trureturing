/- GID: D5/S3/Entropy/Observation/MultiTargetInformationChain
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/MultiTargetInformationChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Multi-target information cost is order-invariant and obeys the chain rule. -/

import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.NamingWindow.FutureWordInformationChain
import D5.S3.Entropy.Relabeling.InjectiveInvariance

/- Library-search audit trail (2026-08-27):
   * Pinned-Mathlib searches for finite Shannon entropy, conditional entropy, permutation
     invariance, and an iterated chain rule found no theorem on finite real-valued mass functions.
   * Repository searches found the exact two-variable theorem `entropy_chain_rule` and the exact
     recursive theorem `future_word_information_chain`; both are imported and applied below.
   * `CompletionInformationChainDecomposition` specializes the recursion to one dynamical
     observation alphabet. It does not state the arbitrary heterogeneous target-family or
     permutation result formalized here.
   * Body-shape searches found no public D5 coordinate-to-future-word equivalence, lifted target
     permutation, or ordered completion law. The definitions below construct those objects from
     `Fin`, `Sum`, `Sigma`, `FutureWord`, and the canonical deterministic `pushforward`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.MultiTargetInformationChain

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.NamingWindow.FutureWordInformationChain
open D5.S3.Entropy.Relabeling.InjectiveInvariance
open scoped BigOperators

universe u v w

/-- The canonical equivalence between a finite coordinate vector and the recursively nested
future-word carrier used by the finite entropy chain rule. -/
def futureWordCoordinates (O : Type u) :
    (n : Nat) -> (Fin (n + 1) -> O) ≃ FutureWord O n
  | 0 => Equiv.funUnique (Fin 1) O
  | n + 1 =>
      ((Fin.snocEquiv (fun _ : Fin (n + 2) => O)).symm.trans
        (Equiv.prodComm O (Fin (n + 1) -> O))).trans
          ((futureWordCoordinates O n).prodCongr (Equiv.refl O))

@[simp] theorem futureWordCoordinates_zero (O : Type u) (coordinates : Fin 1 -> O) :
    futureWordCoordinates O 0 coordinates = coordinates 0 := rfl

@[simp] theorem futureWordCoordinates_succ (O : Type u) (n : Nat)
    (coordinates : Fin (n + 2) -> O) :
    futureWordCoordinates O (n + 1) coordinates =
      (futureWordCoordinates O n (fun i => coordinates i.castSucc),
        coordinates (Fin.last (n + 1))) := rfl

/-- Extend a target permutation by a fixed initial coordinate reserved for the concept readout. -/
def extendTargetPermutation {n : Nat} (permutation : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 (fun i => (permutation i).succ)
  invFun := Fin.cases 0 (fun i => (permutation.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp

@[simp] theorem extendTargetPermutation_zero {n : Nat}
    (permutation : Equiv.Perm (Fin n)) :
    extendTargetPermutation permutation 0 = 0 := rfl

@[simp] theorem extendTargetPermutation_succ {n : Nat}
    (permutation : Equiv.Perm (Fin n)) (i : Fin n) :
    extendTargetPermutation permutation i.succ = (permutation i).succ := rfl

/-- The coordinate relabeling of a future word that fixes the concept coordinate and permutes all
target coordinates. -/
def completionWordPermutation (O : Type u) {n : Nat}
    (permutation : Equiv.Perm (Fin n)) : Equiv.Perm (FutureWord O n) :=
  (futureWordCoordinates O n).symm |>.trans
    ((Equiv.arrowCongr (extendTargetPermutation permutation).symm (Equiv.refl O)).trans
      (futureWordCoordinates O n))

/-- A concept followed by a permuted heterogeneous target family, with target values tagged by
their original indices in the dependent sum. -/
def orderedCompletionWord {n : Nat} {X : Type u} {B : Type v}
    {Y : Fin n -> Type w} (concept : X -> B) (targets : (i : Fin n) -> X -> Y i)
    (permutation : Equiv.Perm (Fin n)) (x : X) :
    FutureWord (B ⊕ Sigma Y) n :=
  futureWordCoordinates (B ⊕ Sigma Y) n
    (Fin.cases (Sum.inl (concept x))
      (fun i => Sum.inr ⟨permutation i, targets (permutation i) x⟩))

/-- The finite law of a concept followed by the target family in the selected order. -/
noncomputable def orderedCompletionLaw {n : Nat} {X : Type u} {B : Type v}
    {Y : Fin n -> Type w} [Fintype X] (mass : PMF X) (concept : X -> B)
    (targets : (i : Fin n) -> X -> Y i) (permutation : Equiv.Perm (Fin n)) :
    FutureWord (B ⊕ Sigma Y) n -> Real :=
  pushforward (orderedCompletionWord concept targets permutation)
    (fun x => (mass x).toReal)

private theorem pushforward_comp {X A B : Type*} [Fintype X] [Fintype A]
    (mass : X -> Real) (f : X -> A) (g : A -> B) :
    pushforward g (pushforward f mass) = pushforward (g ∘ f) mass := by
  classical
  funext b
  simp only [pushforward]
  calc
    (∑ a, if g a = b then ∑ x, if f x = a then mass x else 0 else 0) =
        ∑ a, ∑ x, if g a = b then (if f x = a then mass x else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : g a = b <;> simp [ha]
    _ = ∑ x, ∑ a, if g a = b then (if f x = a then mass x else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ x, if (g ∘ f) x = b then mass x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · simp

private theorem entropy_pushforward_injective {A B : Type*} [Fintype A] [Fintype B]
    (mass : A -> Real) (f : A -> B) (hf : Function.Injective f) :
    shannonEntropy (pushforward f mass) = shannonEntropy mass := by
  classical
  have hpushforward :
      pushforward f mass = Function.extend f mass (fun _ => 0) := by
    funext b
    by_cases hb : b ∈ Set.range f
    · rcases hb with ⟨a, rfl⟩
      rw [hf.extend_apply]
      simp only [pushforward]
      rw [Finset.sum_eq_single a]
      · simp
      · intro a' _ ha'
        simp [show f a' ≠ f a by exact fun h => ha' (hf h)]
      · simp
    · have hnone : Not (Exists fun a => f a = b) := hb
      rw [Function.extend_apply' _ _ _ hnone]
      simp only [pushforward]
      apply Finset.sum_eq_zero
      intro a _
      simp [show f a ≠ b by exact fun h => hb ⟨a, h⟩]
  rw [hpushforward]
  exact shannonEntropy_extend_injective hf mass

private theorem entropy_pushforward_injective_comp {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B] (mass : X -> Real) (f : X -> A)
    (g : A -> B) (hg : Function.Injective g) :
    shannonEntropy (pushforward (g ∘ f) mass) =
      shannonEntropy (pushforward f mass) := by
  rw [← pushforward_comp]
  exact entropy_pushforward_injective (pushforward f mass) g hg

private theorem marginal_pushforward_pair {X A B : Type*}
    [Fintype X] [Fintype B] (mass : X -> Real)
    (first : X -> A) (second : X -> B) :
    marginal (pushforward (fun x => (first x, second x)) mass) =
      pushforward first mass := by
  classical
  funext a
  simp only [marginal, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hfirst : first x = a
  · simp [hfirst]
  · simp [hfirst]

private theorem firstReadoutMarginal_pushforward_coordinates {X O : Type*}
    [Fintype X] [Fintype O] (mass : X -> Real) :
    ∀ (n : Nat) (coordinates : X -> Fin (n + 1) -> O),
      firstReadoutMarginal
          (pushforward (fun x => futureWordCoordinates O n (coordinates x)) mass) =
        pushforward (fun x => coordinates x 0) mass
  | 0, coordinates => by
      rfl
  | n + 1, coordinates => by
      rw [show
        (pushforward
            (fun x => futureWordCoordinates O (n + 1) (coordinates x)) mass) =
          pushforward
            (fun x =>
              (futureWordCoordinates O n (fun i => coordinates x i.castSucc),
                coordinates x (Fin.last (n + 1)))) mass by rfl]
      simp only [firstReadoutMarginal]
      rw [show
        marginal
            (pushforward
              (fun x =>
                (futureWordCoordinates O n (fun i => coordinates x i.castSucc),
                  coordinates x (Fin.last (n + 1)))) mass) =
          pushforward
            (fun x => futureWordCoordinates O n (fun i => coordinates x i.castSucc)) mass from
        marginal_pushforward_pair mass _ _]
      exact firstReadoutMarginal_pushforward_coordinates mass n
        (fun x i => coordinates x i.castSucc)

private theorem ordered_completion_word_permutation {n : Nat} {X : Type u} {B : Type v}
    {Y : Fin n -> Type w} (concept : X -> B) (targets : (i : Fin n) -> X -> Y i)
    (permutation : Equiv.Perm (Fin n)) :
    orderedCompletionWord concept targets permutation =
      completionWordPermutation (B ⊕ Sigma Y) permutation ∘
        orderedCompletionWord concept targets (Equiv.refl (Fin n)) := by
  funext x
  apply (futureWordCoordinates (B ⊕ Sigma Y) n).symm.injective
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [orderedCompletionWord, completionWordPermutation, Equiv.arrowCongr]
  · simp [orderedCompletionWord, completionWordPermutation, Equiv.arrowCongr]

private theorem ordered_completion_entropy_invariant {n : Nat}
    {X : Type u} {B : Type v} {Y : Fin n -> Type w}
    [Fintype X] [Fintype B] [∀ i, Fintype (Y i)]
    (mass : PMF X) (concept : X -> B) (targets : (i : Fin n) -> X -> Y i)
    (permutation : Equiv.Perm (Fin n)) :
    shannonEntropy (orderedCompletionLaw mass concept targets permutation) =
      shannonEntropy
        (orderedCompletionLaw mass concept targets (Equiv.refl (Fin n))) := by
  unfold orderedCompletionLaw
  rw [ordered_completion_word_permutation]
  exact entropy_pushforward_injective_comp (fun x => (mass x).toReal)
    (orderedCompletionWord concept targets (Equiv.refl (Fin n)))
    (completionWordPermutation (B ⊕ Sigma Y) permutation)
    (completionWordPermutation (B ⊕ Sigma Y) permutation).injective

private theorem ordered_completion_first_marginal {n : Nat}
    {X : Type u} {B : Type v} {Y : Fin n -> Type w}
    [Fintype X] [Fintype B] [∀ i, Fintype (Y i)]
    (mass : PMF X) (concept : X -> B) (targets : (i : Fin n) -> X -> Y i)
    (permutation : Equiv.Perm (Fin n)) :
    firstReadoutMarginal (orderedCompletionLaw mass concept targets permutation) =
      pushforward (fun x => Sum.inl (concept x) : X -> B ⊕ Sigma Y)
        (fun x => (mass x).toReal) := by
  unfold orderedCompletionLaw orderedCompletionWord
  exact firstReadoutMarginal_pushforward_coordinates (fun x => (mass x).toReal) n
    (fun x =>
      Fin.cases (Sum.inl (concept x) : B ⊕ Sigma Y)
        (fun i =>
          (Sum.inr ⟨permutation i, targets (permutation i) x⟩ : B ⊕ Sigma Y)))

/-- In a finite probability model, the total conditional information required to append a
heterogeneous target family to a concept is independent of target order. For every permutation it
is the sum of the conditional information of each target given the concept and all earlier targets
in that order. -/
theorem multi_target_information_chain {n : Nat} {X : Type u} {B : Type v}
    {Y : Fin n -> Type w} [Fintype X] [Fintype B] [∀ i, Fintype (Y i)]
    (mass : PMF X) (concept : X -> B) (targets : (i : Fin n) -> X -> Y i)
    (permutation : Equiv.Perm (Fin n)) :
    let canonicalLaw :=
      orderedCompletionLaw mass concept targets (Equiv.refl (Fin n))
    let permutedLaw := orderedCompletionLaw mass concept targets permutation
    shannonEntropy canonicalLaw - shannonEntropy (firstReadoutMarginal canonicalLaw) =
      ∑ k ∈ Finset.range n, prefixConditionalEntropy permutedLaw k := by
  dsimp only
  have hnonnegative :
      ∀ word, 0 ≤ orderedCompletionLaw mass concept targets permutation word := by
    intro word
    simp only [orderedCompletionLaw, pushforward]
    exact Finset.sum_nonneg fun x _ => by
      by_cases hword : orderedCompletionWord concept targets permutation x = word
      · simp [hword]
      · simp [hword]
  have hchain := future_word_information_chain n
    (orderedCompletionLaw mass concept targets permutation) hnonnegative
  have hentropy := ordered_completion_entropy_invariant mass concept targets permutation
  have hcanonicalMarginal := ordered_completion_first_marginal mass concept targets
    (Equiv.refl (Fin n))
  have hpermutedMarginal :=
    ordered_completion_first_marginal mass concept targets permutation
  rw [hpermutedMarginal] at hchain
  rw [hcanonicalMarginal]
  linarith [hentropy]

#print axioms multi_target_information_chain

end D5.S3.Entropy.Observation.MultiTargetInformationChain
