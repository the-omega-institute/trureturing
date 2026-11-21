/- GID: D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixHamming/ExactDimension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: The minimum binary Hamming dimension of the permutation prefix-set metric. -/

module

public import Mathlib.InformationTheory.Hamming
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! # Binary Hamming dimension of unordered permutation prefixes -/

public section

namespace D5.S3.Combinatorics.Graph.PrefixHamming

open Finset
open scoped BigOperators

set_option autoImplicit false

/-- The unordered set of entries in positions strictly below the supplied rank. -/
def prefixSet {n : ℕ} (p : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (univ.filter fun i : Fin n => i.val < k).image p

/-- Proper ranks exclude zero and the total size of the ground set. -/
abbrev Rank (n : ℕ) := {k : Fin n // 0 < k.val}

/-- At Rossi's scale each different proper unordered prefix contributes two. -/
def prefixDistance {n : ℕ} (p q : Equiv.Perm (Fin n)) : ℕ :=
  2 * (univ.filter fun k : Rank n => prefixSet p k.val.val ≠ prefixSet q k.val.val).card

private theorem mem_prefix {n k : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n) :
    x ∈ prefixSet p k ↔ (p.symm x).val < k := by
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    simpa using (mem_filter.mp hi).2
  · intro hx
    exact mem_image.mpr ⟨p.symm x, mem_filter.mpr ⟨mem_univ _, hx⟩, p.apply_symm_apply x⟩

private theorem placement {n k : ℕ} (A : Finset (Fin n)) (hA : A.card = k) :
    ∃ p : Equiv.Perm (Fin n), ∀ i, p i ∈ A ↔ i.val < k := by
  classical
  have hk : k ≤ n := by simpa [← hA] using A.card_le_univ
  have hC : Aᶜ.card = n - k := by rw [card_compl, hA, Fintype.card_fin]
  let split : Fin n ≃ Fin k ⊕ Fin (n - k) :=
    (Fin.castOrderIso (Nat.add_sub_of_le hk).symm).toEquiv.trans finSumFinEquiv.symm
  let join : Fin k ⊕ Fin (n - k) ≃ Fin n :=
    (Equiv.sumCongr (A.equivFinOfCardEq hA).symm (Aᶜ.equivFinOfCardEq hC).symm).trans
      ((Equiv.sumCongr (Equiv.refl A)
        (Equiv.subtypeEquivRight fun _ => mem_compl)).trans (Equiv.sumCompl (· ∈ A)))
  refine ⟨split.trans join, ?_⟩
  intro i
  have hi := split.symm_apply_apply i
  change join (split i) ∈ A ↔ i.val < k
  rcases h : split i with a | b <;> rw [h] at hi
  · subst i
    change (((A.equivFinOfCardEq hA).symm a : A) : Fin n) ∈ A ↔ a.val < k
    exact iff_of_true ((A.equivFinOfCardEq hA).symm a).property a.isLt
  · subst i
    change (((Aᶜ.equivFinOfCardEq hC).symm b : ↥(Aᶜ : Finset (Fin n))) : Fin n) ∈ A ↔ k + b.val < k
    have hc := ((Aᶜ.equivFinOfCardEq hC).symm b).property
    exact iff_of_false (mem_compl.mp hc) (by omega)

private theorem swap_mem {α : Type*} [DecidableEq α] (A : Finset α) {a b : α}
    (hab : a ∈ A ↔ b ∈ A) (x : α) : Equiv.swap a b x ∈ A ↔ x ∈ A := by
  by_cases ha : x = a
  · subst x
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hb : x = b
  · subst x
    simpa only [Equiv.swap_apply_right] using hab
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

private theorem placed_boundary {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (A : Finset (Fin n)) (hA : A.card = k) {a b : Fin n} (ha : a ∈ A) (hb : b ∉ A) :
    ∃ p : Equiv.Perm (Fin n),
      (∀ i, p i ∈ A ↔ i.val < k) ∧ p ⟨k - 1, by omega⟩ = a ∧ p ⟨k, hkn⟩ = b := by
  classical
  let l : Fin n := ⟨k - 1, by omega⟩
  let r : Fin n := ⟨k, hkn⟩
  obtain ⟨p, hp⟩ := placement A hA
  have hpl : p l ∈ A := (hp l).mpr (by dsimp [l]; omega)
  have hpr : p r ∉ A := fun hr => (Nat.lt_irrefl k) ((hp r).mp hr)
  let s := Equiv.swap (p l) a
  let t := Equiv.swap (p r) b
  have sr : s (p r) = p r :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hpr (h ▸ hpl)) (fun h => hpr (h ▸ ha))
  have ta : t a = a :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hpr (h ▸ ha)) (fun h => hb (h ▸ ha))
  refine ⟨(p.trans s).trans t, fun i => ?_, ?_, ?_⟩
  · change t (s (p i)) ∈ A ↔ i.val < k
    rw [swap_mem A (iff_of_false hpr hb), swap_mem A (iff_of_true hpl ha), hp]
  · change t (s (p l)) = a
    rw [Equiv.swap_apply_left, ta]
  · change t (s (p r)) = b
    rw [sr, Equiv.swap_apply_left]

private theorem adjacent_boundary_exchange {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (A : Finset (Fin n)) (hA : A.card = k) {a b : Fin n} (ha : a ∈ A) (hb : b ∉ A) :
    ∃ p : Equiv.Perm (Fin n),
      let q := (Equiv.swap (⟨k - 1, by omega⟩ : Fin n) ⟨k, hkn⟩).trans p
      prefixSet p k = A ∧ prefixSet q k = insert b (A.erase a) ∧
        ∀ j : ℕ, j ≠ k → prefixSet q j = prefixSet p j := by
  classical
  let l : Fin n := ⟨k - 1, by omega⟩
  let r : Fin n := ⟨k, hkn⟩
  let s := Equiv.swap l r
  have hl : l.val = k - 1 := rfl
  have hr : r.val = k := rfl
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  obtain ⟨p, hp, hlp, hrp⟩ := placed_boundary hk hkn A hA ha hb
  change p l = a at hlp
  change p r = b at hrp
  have hpa : p.symm a = l := p.symm_apply_eq.mpr hlp.symm
  have hpb : p.symm b = r := p.symm_apply_eq.mpr hrp.symm
  have inv (x : Fin n) : (s.trans p).symm x = s (p.symm x) := rfl
  refine ⟨p, ?_, ?_, ?_⟩
  · ext x
    rw [mem_prefix, ← hp, p.apply_symm_apply]
  · change prefixSet (s.trans p) k = _
    ext x
    rw [mem_prefix, inv, mem_insert, mem_erase]
    by_cases hxa : x = a
    · subst x
      rw [hpa, Equiv.swap_apply_left]
      simp [hr, hab]
    by_cases hxb : x = b
    · subst x
      rw [hpb, Equiv.swap_apply_right]
      simp [hl, show k - 1 < k by omega]
    have hxl : p.symm x ≠ l := fun h => hxa (p.symm_apply_eq.mp h |>.trans hlp)
    have hxr : p.symm x ≠ r := fun h => hxb (p.symm_apply_eq.mp h |>.trans hrp)
    rw [Equiv.swap_apply_of_ne_of_ne hxl hxr, ← hp, p.apply_symm_apply]
    simp [hxa, hxb]
  · intro j hj
    change prefixSet (s.trans p) j = prefixSet p j
    ext x
    rw [mem_prefix, mem_prefix, inv]
    generalize p.symm x = i
    by_cases hil : i = l
    · subst i
      rw [Equiv.swap_apply_left, hl, hr]
      omega
    by_cases hir : i = r
    · subst i
      rw [Equiv.swap_apply_right, hl, hr]
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hil hir]

private def intBit (b : Bool) : ℤ := if b then 1 else 0

private theorem bit_square_dist {ι : Type*} [Fintype ι] (x y : ι → Bool) :
    ((intBit ∘ x) - (intBit ∘ y)) ⬝ᵥ ((intBit ∘ x) - (intBit ∘ y)) =
      (hammingDist x y : ℤ) := by
  classical
  rw [hammingDist, card_eq_sum_ones, Nat.cast_sum, sum_filter, dotProduct]
  apply sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Function.comp_apply, Nat.cast_one]
  cases x i <;> cases y i <;> decide

private theorem twice_pairing {ι : Type*} [Fintype ι] (a b c d : ι → Bool) :
    2 * (((intBit ∘ a) - (intBit ∘ b)) ⬝ᵥ ((intBit ∘ c) - (intBit ∘ d))) =
      (hammingDist a d : ℤ) + hammingDist b c - hammingDist a c - hammingDist b d := by
  simp only [← bit_square_dist, dotProduct, Finset.mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib, Pi.sub_apply]
  apply sum_congr rfl
  intro i _
  ring

private theorem four_endpoint_pairing {α ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : α → ι → Bool) (g : α → κ → Bool)
    (h : ∀ a b, hammingDist (f a) (f b) = hammingDist (g a) (g b))
    (a b c d : α) :
    ((intBit ∘ f a) - (intBit ∘ f b)) ⬝ᵥ ((intBit ∘ f c) - (intBit ∘ f d)) =
      ((intBit ∘ g a) - (intBit ∘ g b)) ⬝ᵥ ((intBit ∘ g c) - (intBit ∘ g d)) := by
  have hf := twice_pairing (f a) (f b) (f c) (f d)
  rw [h, h, h, h, ← twice_pairing] at hf
  omega

private def endpointSum {α ι : Type*} (f : α → ι → Bool) (L : List (α × α)) : ι → ℤ :=
  (L.map fun e => (intBit ∘ f e.1) - (intBit ∘ f e.2)).sum

private theorem list_pairing {α ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : α → ι → Bool) (g : α → κ → Bool)
    (h : ∀ a b, hammingDist (f a) (f b) = hammingDist (g a) (g b))
    (L M : List (α × α)) :
    endpointSum f L ⬝ᵥ endpointSum f M = endpointSum g L ⬝ᵥ endpointSum g M := by
  have edge_list (e : α × α) (M : List (α × α)) :
      ((intBit ∘ f e.1) - (intBit ∘ f e.2)) ⬝ᵥ endpointSum f M =
        ((intBit ∘ g e.1) - (intBit ∘ g e.2)) ⬝ᵥ endpointSum g M := by
    induction M with
    | nil => simp [endpointSum]
    | cons t M ih =>
      simp only [endpointSum, List.map_cons, List.sum_cons, dotProduct_add] at ih ⊢
      rw [four_endpoint_pairing f g h, ih]
  induction L with
  | nil => simp [endpointSum]
  | cons t L ih =>
    have ht := edge_list t M
    simp only [endpointSum, List.map_cons, List.sum_cons, add_dotProduct] at ht ih ⊢
    rw [ht, ih]

#print axioms adjacent_boundary_exchange
#print axioms four_endpoint_pairing
#print axioms list_pairing

end D5.S3.Combinatorics.Graph.PrefixHamming
