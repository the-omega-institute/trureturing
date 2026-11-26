/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum]
   utility: none
   digest: A translation conjugates chosen coordinate swaps to the generators of a permutation group. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Set

/-! The no-split alternative in the binary small-word argument uses the
ordinary affine cube action. A freely chosen complemented swap on each
edge of a coordinate star is conjugate by a single translation to the
corresponding ordinary swap. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSwapConjugation

open BalancedCriticalSpectrum (Q flip)

/-- Translation by a cube vertex, using coordinatewise addition over F₂. -/
abbrev translate {n : ℕ} (t x : Q n) : Q n := fun i => Bool.xor (t i) (x i)

theorem translate_involutive {n : ℕ} (t : Q n) :
    Function.Involutive (translate t) := by
  intro x
  funext i
  change Bool.xor (t i) (Bool.xor (t i) (x i)) = x i
  cases t i <;> cases x i <;> rfl

/-- For distinct `r,j`, exchange the two coordinates and optionally
complement both of them. All other coordinates are fixed. -/
def chosenSwap {n : ℕ} (r j : Fin n) (b : Bool) (x : Q n) : Q n :=
  fun i => if i = r then Bool.xor b (x j)
    else if i = j then Bool.xor b (x r) else x i

/-- The choice on each edge of the coordinate star is independent. Set
`t r = false` and `t j = b j`. The intertwining identity, together with
`translate_involutive`, gives simultaneous conjugation by `translate t`. -/
theorem exists_translation_conjugating_star_swaps {n : ℕ} (r : Fin n) (b : Q n) :
    ∃ t : Q n, t r = false ∧
      ∀ j : Fin n, j ≠ r → ∀ x : Q n,
        chosenSwap r j (b j) (translate t x) = translate t (x ∘ Equiv.swap r j) := by
  let t : Q n := fun i => if i = r then false else b i
  refine ⟨t, by simp [t], ?_⟩
  intro j hj x
  funext i
  by_cases hir : i = r
  · subst i
    cases hb : b j <;> cases hx : x j <;>
      simp [chosenSwap, translate, t, hj, hb, hx, Bool.xor]
  · by_cases hij : i = j
    · subst i
      cases hb : b j <;> cases hx : x r <;>
        simp [chosenSwap, translate, t, hj, hb, hx, Bool.xor]
    · simp only [chosenSwap, if_neg hir, if_neg hij, translate,
        Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hir hij]

/-- A complemented or ordinary swap either fixes the vertex or flips both
selected coordinates. The fixed vertices satisfy `x r = b xor x j`. -/
private theorem chosenSwap_eq {n : ℕ} {r j : Fin n} (hj : j ≠ r)
    (b : Bool) (x : Q n) :
    chosenSwap r j b x =
      if x r = Bool.xor b (x j) then x else flip (flip x r) j := by
  funext i
  by_cases hir : i = r
  · subst i
    cases b <;> cases hr : x r <;> cases hx : x j <;>
      simp [chosenSwap, BalancedCriticalSpectrum.flip, Bool.xor, hj.symm, hr, hx]
  · by_cases hij : i = j
    · subst i
      cases b <;> cases hr : x r <;> cases hx : x j <;>
        simp [chosenSwap, BalancedCriticalSpectrum.flip, Bool.xor, hj, hr, hx]
    · by_cases h : x r = Bool.xor b (x j) <;>
        simp [chosenSwap, BalancedCriticalSpectrum.flip, hir, hij, h]

/-- The ordinary swaps with one common coordinate generate every coordinate
permutation. The action here is by precomposition. -/
private theorem invariant_of_star_swaps {n : ℕ} {β : Type*} (r : Fin n) (f : Q n → β)
    (h : ∀ j : Fin n, j ≠ r → ∀ x : Q n, f (x ∘ Equiv.swap r j) = f x) :
    ∀ (σ : Equiv.Perm (Fin n)) (x : Q n), f (x ∘ σ) = f x := by
  have hmul (σ τ : Equiv.Perm (Fin n))
      (hs : ∀ x : Q n, f (x ∘ σ) = f x)
      (ht : ∀ x : Q n, f (x ∘ τ) = f x) :
      ∀ x : Q n, f (x ∘ (σ * τ : Equiv.Perm (Fin n))) = f x := by
    intro x
    change f ((x ∘ σ) ∘ τ) = f x
    exact (ht (x ∘ σ)).trans (hs x)
  have hswap (i j : Fin n) (hij : i ≠ j) :
      ∀ x : Q n, f (x ∘ Equiv.swap i j) = f x := by
    by_cases hi : i = r
    · subst i
      exact h j hij.symm
    · by_cases hj : j = r
      · subst j
        rw [Equiv.swap_comm i r]
        exact h i hij
      · have he : Equiv.swap i j =
            Equiv.swap r i * Equiv.swap r j * Equiv.swap r i := by
          rw [Equiv.swap_comm r j]
          exact (Equiv.swap_mul_swap_mul_swap (x := j) (y := r) (z := i) hj hij.symm).symm
        rw [he]
        exact hmul _ _ (hmul _ _ (h i hi) (h j hj)) (h i hi)
  intro σ
  refine Equiv.Perm.swap_induction_on
    (motive := fun τ => ∀ x : Q n, f (x ∘ τ) = f x) σ ?_ ?_
  · intro x
    rfl
  · intro τ i j hij hτ
    exact hmul _ _ (hswap i j hij) hτ

/-- For each pair of coordinates through `r`, suppose the unequal-bit
sections agree after a double flip, or the equal-bit sections agree after
a double flip. In the four-section notation these are respectively `b=c`
and `a=d`. Then one translation makes the function invariant under every
coordinate permutation. No kernel or parity assumption is necessary. -/
theorem exists_translation_perm_invariant_of_no_split {n : ℕ} {β : Type*}
    (r : Fin n) (f : Q n → β)
    (h : ∀ j : Fin n, j ≠ r →
      (∀ x : Q n, x r ≠ x j → f (flip (flip x r) j) = f x) ∨
      (∀ x : Q n, x r = x j → f (flip (flip x r) j) = f x)) :
    ∃ t : Q n, t r = false ∧
      ∀ (σ : Equiv.Perm (Fin n)) (x : Q n),
        f (translate t (x ∘ σ)) = f (translate t x) := by
  classical
  have hchoice (j : Fin n) (hj : j ≠ r) :
      ∃ b : Bool, ∀ x : Q n, f (chosenSwap r j b x) = f x := by
    rcases h j hj with hplain | hcomplement
    · refine ⟨false, ?_⟩
      intro x
      rw [chosenSwap_eq hj]
      cases hr : x r <;> cases hx : x j <;> simp [Bool.xor, hr, hx]
      all_goals exact hplain x (by simp [hr, hx])
    · refine ⟨true, ?_⟩
      intro x
      rw [chosenSwap_eq hj]
      cases hr : x r <;> cases hx : x j <;> simp [Bool.xor, hr, hx]
      all_goals exact hcomplement x (by simp [hr, hx])
  let b : Q n := fun j => if hj : j ≠ r then Classical.choose (hchoice j hj) else false
  have hb (j : Fin n) (hj : j ≠ r) (x : Q n) :
      f (chosenSwap r j (b j) x) = f x := by
    simpa only [b, dite_eq_left hj] using Classical.choose_spec (hchoice j hj) x
  obtain ⟨t, ht, hconj⟩ := exists_translation_conjugating_star_swaps r b
  refine ⟨t, ht, invariant_of_star_swaps r (fun x => f (translate t x)) ?_⟩
  intro j hj x
  rw [← hconj j hj x]
  exact hb j hj (translate t x)

private theorem perm_of_equal_card {n : ℕ} (s t : Finset (Fin n)) (h : s.card = t.card) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, i ∈ s ↔ σ i ∈ t := by
  classical
  let e₀ : (s : Set (Fin n)) ≃ (t : Set (Fin n)) :=
    s.equivFin.trans (t.equivFinOfCardEq h.symm).symm
  have hcompl : (sᶜ).card = (tᶜ).card := by simp [Finset.card_compl, h]
  let es : ((s : Set (Fin n))ᶜ : Set (Fin n)) ≃ (sᶜ : Finset (Fin n)) :=
    Equiv.subtypeEquivRight (fun i => by simp)
  let et : ((t : Set (Fin n))ᶜ : Set (Fin n)) ≃ (tᶜ : Finset (Fin n)) :=
    Equiv.subtypeEquivRight (fun i => by simp)
  let e₁ := (es.trans ((sᶜ).equivFin.trans ((tᶜ).equivFinOfCardEq hcompl.symm).symm)).trans et.symm
  let σ := ((Equiv.Set.sumCompl (s : Set (Fin n))).symm.trans (e₀.sumCongr e₁)).trans
    (Equiv.Set.sumCompl (t : Set (Fin n)))
  have hσ (x : (s : Set (Fin n))) : σ x = e₀ x := by
    simp only [σ, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem x.property,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
  refine ⟨σ, fun i => ⟨?_, ?_⟩⟩
  · intro hi
    exact (hσ ⟨i, hi⟩).symm ▸ (e₀ ⟨i, hi⟩).property
  · intro hi
    obtain ⟨x, hx⟩ := e₀.surjective (⟨σ i, hi⟩ : (t : Set (Fin n)))
    have he : σ x = σ i := (hσ x).trans (congrArg Subtype.val hx)
    exact (σ.injective he) ▸ x.property

/-- Under the no-split hypotheses one translated function is constant on
each Hamming layer of the cube. -/
theorem exists_translation_hamming_layer_constant {n : ℕ} {β : Type*}
    (r : Fin n) (f : Q n → β)
    (h : ∀ j : Fin n, j ≠ r →
      (∀ x : Q n, x r ≠ x j → f (flip (flip x r) j) = f x) ∨
      (∀ x : Q n, x r = x j → f (flip (flip x r) j) = f x)) :
    ∃ t : Q n, t r = false ∧ ∀ x y : Q n,
      ((Finset.univ.filter fun i => x i = true).card =
        (Finset.univ.filter fun i => y i = true).card) →
      f (translate t x) = f (translate t y) := by
  obtain ⟨t, ht, hinv⟩ := exists_translation_perm_invariant_of_no_split r f h
  refine ⟨t, ht, ?_⟩
  intro x y hc
  obtain ⟨σ, hσ⟩ := perm_of_equal_card _ _ hc
  have hxy : y ∘ σ = x := by
    funext i
    have h₁ : x i = true ↔ y (σ i) = true := by simpa using hσ i
    cases hxi : x i <;> cases hyi : y (σ i) <;> simp_all
  simpa only [hxy] using hinv σ y

#print axioms exists_translation_conjugating_star_swaps
#print axioms exists_translation_perm_invariant_of_no_split
#print axioms exists_translation_hamming_layer_constant

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSwapConjugation
