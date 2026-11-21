/- GID: D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixHamming/ExactDimension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: The minimum binary Hamming dimension of the permutation prefix-set metric. -/

module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Finset.SymmDiff
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Abel
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import D5.S3.Combinatorics.Graph.DUFStructure
import Mathlib.Tactic.Ring

/-!
# Binary Hamming dimension of unordered permutation prefixes

Rossi's cut-set metric at scale two is the Hamming distance of the proper-prefix
incidence words. Adjacent exchanges and integer polarization recover a separate
coordinate lower bound for every proper rank in any realization. One-hot blocks
attain the bound, with a three-bit even-parity block for each four-symbol rank.
-/

public section

namespace D5.S3.Combinatorics.Graph.PrefixHamming

open Finset
open scoped BigOperators symmDiff

set_option autoImplicit false

/-- The unordered set of entries in positions strictly below the supplied rank. -/
@[expose] def prefixSet {n : ℕ} (p : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (univ.filter fun i : Fin n => i.val < k).image p

/-- Proper ranks exclude zero and the total size of the ground set. -/
abbrev Rank (n : ℕ) := {k : Fin n // 0 < k.val}

/-- At Rossi's scale each different proper unordered prefix contributes two. -/
@[expose] def prefixDistance {n : ℕ} (p q : Equiv.Perm (Fin n)) : ℕ :=
  2 * (univ.filter fun k : Rank n => prefixSet p k.val.val ≠ prefixSet q k.val.val).card

private theorem mem_prefix {n k : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n) :
    x ∈ prefixSet p k ↔ (p.symm x).val < k := by
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    simpa using (mem_filter.mp hi).2
  · intro hx
    exact mem_image.mpr ⟨p.symm x, mem_filter.mpr ⟨mem_univ _, hx⟩, p.apply_symm_apply x⟩

/- Arrange a prescribed set in the first block, then place the two exchanged entries. -/

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

/- Polarization transfers all pairings of sums of endpoint differences. -/

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

private theorem prefix_card {n k : ℕ} (p : Equiv.Perm (Fin n)) (hk : k < n) :
    (prefixSet p k).card = k := by
  rw [prefixSet, card_image_of_injective _ p.injective]
  have h : (univ.filter fun i : Fin n => i.val < k) = Iio (⟨k, hk⟩ : Fin n) := by
    ext i
    simp [Fin.lt_def]
  rw [h]
  exact Fin.card_Iio _

private abbrev Layer {n : ℕ} (k : Rank n) := {A : Finset (Fin n) // A.card = k.val.val}

private def rankPrefix {n : ℕ} (p : Equiv.Perm (Fin n)) (k : Rank n) : Layer k :=
  ⟨prefixSet p k.val.val, prefix_card p k.val.isLt⟩

private def oneHot {α : Type*} [DecidableEq α] (x : α) (i : α) : Bool := decide (i = x)

private theorem oneHot_dist {α : Type*} [Fintype α] [DecidableEq α] (x y : α) :
    hammingDist (oneHot x) (oneHot y) = if x = y then 0 else 2 := by
  by_cases h : x = y
  · subst y
    simp
  rw [ite_eq_right h, hammingDist]
  have he : (univ.filter fun i => oneHot x i ≠ oneHot y i) = {x, y} := by
    ext i
    by_cases hx : i = x <;> by_cases hy : i = y <;> simp_all [oneHot]
  rw [he]
  simp [h]

private theorem hamming_sigma {α : Type*} {β : α → Type*} [Fintype α] [∀ a, Fintype (β a)]
    (x y : Sigma β → Bool) :
    hammingDist x y = ∑ a, hammingDist (fun b => x ⟨a, b⟩) (fun b => y ⟨a, b⟩) := by
  simp only [hammingDist, card_eq_sum_ones, sum_filter]
  exact Fintype.sum_sigma _

private theorem distance_sum {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    prefixDistance p q = ∑ k : Rank n, if rankPrefix p k = rankPrefix q k then 0 else 2 := by
  rw [prefixDistance, card_eq_sum_ones, sum_filter, Finset.mul_sum]
  apply sum_congr rfl
  intro k _
  by_cases h : prefixSet p k.val.val = prefixSet q k.val.val
  · have h' : rankPrefix p k = rankPrefix q k := Subtype.ext h
    simp [h, h']
  · have h' : rankPrefix p k ≠ rankPrefix q k := fun he => h (congrArg Subtype.val he)
    simp [h, h']

private abbrev CutCoord (n : ℕ) := Σ k : Rank n, Layer k

private def incidence {n : ℕ} (p : Equiv.Perm (Fin n)) (z : CutCoord n) : Bool :=
  oneHot (rankPrefix p z.1) z.2

private theorem incidence_dist {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    hammingDist (incidence p) (incidence q) = prefixDistance p q := by
  rw [hamming_sigma, distance_sum]
  exact sum_congr rfl (fun k _ => oneHot_dist (rankPrefix p k) (rankPrefix q k))

private def basis {α : Type*} [DecidableEq α] (z : α) : α → ℤ := Pi.single z 1

private theorem basis_at {α : Type*} [DecidableEq α] (z w : α) :
    basis z w = intBit (oneHot z w) := by
  by_cases h : w = z <;> simp [basis, intBit, oneHot, h]

private theorem incidence_exchange {n : ℕ} {k : Rank n} {A B : Layer k}
    {p q : Equiv.Perm (Fin n)}
    (hp : prefixSet p k.val.val = A.val) (hq : prefixSet q k.val.val = B.val)
    (hr : ∀ j : ℕ, j ≠ k.val.val → prefixSet q j = prefixSet p j) :
    (intBit ∘ incidence q) - (intBit ∘ incidence p) =
      basis (⟨k, B⟩ : CutCoord n) - basis ⟨k, A⟩ := by
  funext z
  obtain ⟨j, D⟩ := z
  simp only [Pi.sub_apply, Function.comp_apply, incidence, basis_at]
  by_cases hj : j = k
  · subst j
    have hp' : rankPrefix p k = A := Subtype.ext hp
    have hq' : rankPrefix q k = B := Subtype.ext hq
    simp [hp', hq', oneHot]
  · have he : rankPrefix q j = rankPrefix p j :=
      Subtype.ext (hr j.val.val (fun he => hj (Subtype.ext (Fin.ext he))))
    have hB : (⟨j, D⟩ : CutCoord n) ≠ ⟨k, B⟩ := fun h => hj (congrArg Sigma.fst h)
    have hA : (⟨j, D⟩ : CutCoord n) ≠ ⟨k, A⟩ := fun h => hj (congrArg Sigma.fst h)
    simp [he, oneHot, intBit, hB, hA]

/- Along an exchange path the canonical incidence differences telescope. -/

private theorem exchange_path {n : ℕ} (k : Rank n) (A B : Layer k) :
    ∃ L : List (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)),
      endpointSum incidence L = basis (⟨k, B⟩ : CutCoord n) - basis ⟨k, A⟩ := by
  classical
  suffices go : ∀ m (S : Layer k), (S.val \ B.val).card = m →
      ∃ L : List (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)),
        endpointSum incidence L = basis (⟨k, B⟩ : CutCoord n) - basis ⟨k, S⟩ by
    exact go _ A rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S hm
    by_cases he : S = B
    · subst S
      exact ⟨[], by simp [endpointSum]⟩
    have h₁ : ¬ S.val ⊆ B.val := fun hs =>
      he (Subtype.ext (eq_of_subset_of_card_le hs (by rw [S.property, B.property])))
    have h₂ : ¬ B.val ⊆ S.val := fun hs =>
      he (Subtype.ext (eq_of_subset_of_card_le hs (by rw [S.property, B.property])).symm)
    obtain ⟨a, ha⟩ := sdiff_nonempty.mpr h₁
    obtain ⟨b, hb⟩ := sdiff_nonempty.mpr h₂
    rw [mem_sdiff] at ha hb
    let C : Layer k := ⟨insert b (S.val.erase a), by
      rw [card_insert_of_notMem (fun h => hb.2 (mem_erase.mp h).2), card_erase_of_mem ha.1]
      have := k.property
      rw [S.property]
      omega⟩
    have hdiff : C.val \ B.val = (S.val \ B.val).erase a := by
      ext x
      simp only [C, mem_sdiff, mem_insert, mem_erase]
      by_cases hx : x = b <;> simp_all [and_left_comm, and_comm]
    have hlt : (C.val \ B.val).card < m := by
      rw [hdiff, ← hm]
      exact card_erase_lt_of_mem (mem_sdiff.mpr ha)
    obtain ⟨L, hL⟩ := ih _ hlt C rfl
    obtain ⟨p, hp, hq, hr⟩ :=
      adjacent_boundary_exchange k.property k.val.isLt S.val S.property ha.1 hb.2
    let q := (Equiv.swap (⟨k.val.val - 1, by have := k.val.isLt; omega⟩ : Fin n) k.val).trans p
    have hx := incidence_exchange (k := k) (A := S) (B := C) (p := p) (q := q) hp hq hr
    refine ⟨(q, p) :: L, ?_⟩
    change ((intBit ∘ incidence q) - (intBit ∘ incidence p)) + endpointSum incidence L = _
    rw [hx, hL]
    abel

/- Norm-two integral vectors have two signed coordinates. -/

private def support {ι : Type*} [Fintype ι] (v : ι → ℤ) : Finset ι :=
  univ.filter fun i => v i ≠ 0

private theorem mem_support {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    i ∈ support v ↔ v i ≠ 0 := by
  simp [support]

private theorem support_of_norm_two {ι : Type*} [Fintype ι] (v : ι → ℤ)
    (hv : v ⬝ᵥ v = 2) :
    (support v).card = 2 ∧ ∀ i ∈ support v, v i = 1 ∨ v i = -1 := by
  classical
  rw [dotProduct] at hv
  have hs (i : ι) : v i * v i ≤ 2 := by
    rw [← hv]
    exact single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _) (mem_univ i)
  have hb (i : ι) : v i = 0 ∨ v i = 1 ∨ v i = -1 := by
    have hl : -1 ≤ v i := by
      by_contra! h
      have hh : 0 ≤ (-v i - 2) * (-v i + 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith only [hs i, hh]
    have hu : v i ≤ 1 := by
      by_contra! h
      have hh : 0 ≤ (v i - 2) * (v i + 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith only [hs i, hh]
    omega
  have hcount : ((support v).card : ℤ) = ∑ i, v i * v i := by
    rw [support, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro i _
    rcases hb i with h | h | h <;> simp [h]
  exact ⟨by exact_mod_cast hcount.trans hv, fun i hi =>
    (hb i).resolve_left ((mem_support v i).mp hi)⟩

private theorem pairing_on_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℤ) {x y : ι} (hxy : x ≠ y) (h : support u = {x, y}) :
    u ⬝ᵥ v = u x * v x + u y * v y := by
  have he : ∑ i ∈ support u, u i * v i = ∑ i, u i * v i := by
    apply sum_subset (subset_univ _)
    intro i _ hi
    have hz : u i = 0 := by simpa [mem_support] using hi
    simp [hz]
  rw [dotProduct, ← he, h, sum_insert (by simpa using hxy), sum_singleton]

private theorem one_pairing_support {ι : Type*} [Fintype ι]
    {u v : ι → ℤ} (hu : u ⬝ᵥ u = 2) (hv : v ⬝ᵥ v = 2) (h : u ⬝ᵥ v = 1) :
    ¬ Disjoint (support u) (support v) ∧ support u ≠ support v := by
  classical
  obtain ⟨hc, hsign⟩ := support_of_norm_two u hu
  obtain ⟨_, hsign'⟩ := support_of_norm_two v hv
  obtain ⟨x, y, hxy, hpair⟩ := card_eq_two.mp hc
  have hx : x ∈ support u := by simp [hpair]
  have hy : y ∈ support u := by simp [hpair]
  rw [pairing_on_pair u v hxy hpair] at h
  constructor
  · intro hd
    have hvx : v x = 0 := by simpa [mem_support] using fun h' => disjoint_left.mp hd hx h'
    have hvy : v y = 0 := by simpa [mem_support] using fun h' => disjoint_left.mp hd hy h'
    simp [hvx, hvy] at h
  · intro he
    have hx' : x ∈ support v := he ▸ hx
    have hy' : y ∈ support v := he ▸ hy
    rcases hsign x hx with hux | hux <;> rcases hsign y hy with huy | huy <;>
      rcases hsign' x hx' with hvx | hvx <;> rcases hsign' y hy' with hvy | hvy <;>
      norm_num [hux, huy, hvx, hvy] at h

private theorem zero_pairing_support {ι : Type*} [Fintype ι]
    {u v : ι → ℤ} (hu : u ⬝ᵥ u = 2) (hv : v ⬝ᵥ v = 2) (h : u ⬝ᵥ v = 0) :
    Disjoint (support u) (support v) ∨ support u = support v := by
  classical
  obtain ⟨x, y, hxy, hpair⟩ := card_eq_two.mp (support_of_norm_two u hu).1
  have hux : u x ≠ 0 := (mem_support u x).mp (by simp [hpair])
  have huy : u y ≠ 0 := (mem_support u y).mp (by simp [hpair])
  rw [pairing_on_pair u v hxy hpair] at h
  by_cases hx : v x = 0
  · have hy : v y = 0 := by
      simpa [hx, huy] using h
    refine Or.inl (disjoint_left.mpr ?_)
    intro i hi hi'
    rw [hpair, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (mem_support v _).mp hi' hx
    · exact (mem_support v _).mp hi' hy
  · have hy : v y ≠ 0 := by
      intro hy
      simp [hy, hx, hux] at h
    refine Or.inr (eq_of_subset_of_card_le ?_ ?_)
    · rw [hpair, insert_subset_iff, singleton_subset_iff]
      exact ⟨(mem_support v x).mpr hx, (mem_support v y).mpr hy⟩
    · rw [(support_of_norm_two u hu).1, (support_of_norm_two v hv).1]

private def supportUnion {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℤ) : Finset ι := univ.biUnion fun a => support (v a)

private theorem support_union_bound {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℤ) (hα : 2 ≤ Fintype.card α)
    (hn : ∀ a, v a ⬝ᵥ v a = 2) (hp : ∀ a b, a ≠ b → v a ⬝ᵥ v b = 1) :
    (if Fintype.card α = 3 then 3 else Fintype.card α + 1) ≤ (supportUnion v).card := by
  classical
  let F := univ.image fun a => support (v a)
  have hF : F.card = Fintype.card α := by
    rw [card_image_of_injective]
    · exact card_univ
    · intro a b he
      by_contra hab
      exact (one_pairing_support (hn a) (hn b) (hp a b hab)).2 he
  have hpair : ∀ s ∈ F, s.card = 2 := by
    intro s hs
    obtain ⟨a, _, rfl⟩ := mem_image.mp hs
    exact (support_of_norm_two _ (hn a)).1
  have hnonempty : F.Nonempty := card_pos.mp (by omega)
  have hi : DUFStructure.Intersecting F := by
    intro s hs t ht hd
    obtain ⟨a, _, rfl⟩ := mem_image.mp hs
    obtain ⟨b, _, rfl⟩ := mem_image.mp ht
    by_cases he : a = b
    · subst b
      have hz := disjoint_self.mp hd
      have hc := (support_of_norm_two _ (hn a)).1
      simp [hz] at hc
    · exact (one_pairing_support (hn a) (hn b) (hp a b he)).1 hd
  have memUnion (s : Finset ι) (hs : s ∈ F) : s ⊆ supportUnion v := by
    obtain ⟨a, _, rfl⟩ := mem_image.mp hs
    exact fun _ hi => mem_biUnion.mpr ⟨a, mem_univ _, hi⟩
  rcases DUFStructure.intersecting_classification F hpair hi hnonempty with
    ⟨c, A, hc, he, hA⟩ | ⟨T, hT, he⟩
  · have hs : insert c A ⊆ supportUnion v := by
      intro i hi
      have leaf (a : ι) (ha : a ∈ A) :
          ({c, a} : Finset ι) ⊆ supportUnion v :=
        memUnion _ (he ▸ mem_image.mpr ⟨a, ha, rfl⟩)
      rcases mem_insert.mp hi with rfl | hi
      · obtain ⟨a, ha⟩ := card_pos.mp (show 0 < A.card by omega)
        exact leaf a ha (mem_insert_self _ _)
      · exact leaf i hi (by simp)
    have hl := card_le_card hs
    rw [card_insert_of_notMem hc, hA, hF] at hl
    split <;> omega
  · have h₃ : Fintype.card α = 3 := by
      rw [he, card_powersetCard, hT] at hF
      exact hF.symm
    have hs : T ⊆ supportUnion v := by
      intro i hi
      obtain ⟨j, hj, hji⟩ := exists_mem_ne (show 1 < T.card by omega) i
      have hp : ({i, j} : Finset ι) ∈ F := by
        rw [he, mem_powersetCard]
        refine ⟨insert_subset_iff.mpr ⟨hi, singleton_subset_iff.mpr hj⟩, ?_⟩
        simp [hji.symm]
      exact memUnion _ hp (by simp)
    simpa [h₃, hT] using card_le_card hs

private def blockSize (m : ℕ) : ℕ := if m = 4 then 3 else m

private theorem choose_at_least_n {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases he : k = n
    · subst k
      rw [Nat.choose_succ_self_right]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [Nat.choose_succ_succ]
    have h₁ := ih (Nat.succ_pos j) (show j + 1 < n by omega)
    have h₂ := Nat.choose_pos (show j ≤ n by omega)
    omega

private theorem layer_card {n : ℕ} (k : Rank n) :
    Fintype.card (Layer k) = n.choose k.val.val := by
  simp [Layer]

private theorem layer_at_least_n {n : ℕ} (k : Rank n) : n ≤ Fintype.card (Layer k) := by
  rw [layer_card]
  exact choose_at_least_n k.property k.val.isLt

private theorem basis_pairing {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    basis a ⬝ᵥ basis b = if a = b then 1 else 0 := by
  unfold basis
  rw [single_dotProduct, one_mul]
  by_cases h : a = b <;> simp [h]

private theorem supports_disjoint {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (v : α → ι → ℤ) (w : β → ι → ℤ) (hβ : 1 < Fintype.card β)
    (hv : ∀ a, v a ⬝ᵥ v a = 2) (hw : ∀ b, w b ⬝ᵥ w b = 2)
    (hww : ∀ b c, b ≠ c → w b ⬝ᵥ w c = 1)
    (hvw : ∀ a b, v a ⬝ᵥ w b = 0) :
    Disjoint (supportUnion v) (supportUnion w) := by
  apply disjoint_left.mpr
  intro i hi hj
  obtain ⟨a, _, ha⟩ := mem_biUnion.mp hi
  obtain ⟨b, _, hb⟩ := mem_biUnion.mp hj
  have he : support (v a) = support (w b) :=
    (zero_pairing_support (hv a) (hw b) (hvw a b)).resolve_left
      (fun hd => disjoint_left.mp hd ha hb)
  obtain ⟨c, hcb⟩ := Fintype.exists_ne_of_one_lt_card hβ b
  obtain ⟨hd, hne⟩ := one_pairing_support (hw b) (hw c) (hww b c hcb.symm)
  rcases zero_pairing_support (hv a) (hw c) (hvw a c) with hc | hc
  · exact hd (he ▸ hc)
  · exact hne (he.symm.trans hc)

/- Transport the anchored incidence differences into an arbitrary realization. -/

private theorem dimension_lower {n d : ℕ} (hn : 3 ≤ n)
    (f : Equiv.Perm (Fin n) → Fin d → Bool)
    (hf : ∀ p q, hammingDist (f p) (f q) = prefixDistance p q) :
    (∑ k : Rank n, blockSize (Fintype.card (Layer k))) ≤ d := by
  classical
  let anchor (k : Rank n) := rankPrefix (Equiv.refl (Fin n)) k
  let Other (k : Rank n) := {A : Layer k // A ≠ anchor k}
  let path (k : Rank n) (A : Other k) := Classical.choose (exchange_path k (anchor k) A.val)
  let v (k : Rank n) (A : Other k) := endpointSum f (path k A)
  let e (k : Rank n) (A : Layer k) : CutCoord n := ⟨k, A⟩
  have he (k : Rank n) : Function.Injective (e k) := fun _ _ h => by simpa [e] using h
  have hd (p q : Equiv.Perm (Fin n)) :
      hammingDist (f p) (f q) = hammingDist (incidence p) (incidence q) :=
    (hf p q).trans (incidence_dist p q).symm
  have hpath (k : Rank n) (A : Other k) :
      endpointSum incidence (path k A) = basis (e k A.val) - basis (e k (anchor k)) :=
    Classical.choose_spec (exchange_path k (anchor k) A.val)
  have gram (k j : Rank n) (A : Other k) (B : Other j) :
      v k A ⬝ᵥ v j B =
      (basis (e k A.val) - basis (e k (anchor k))) ⬝ᵥ
        (basis (e j B.val) - basis (e j (anchor j))) := by
    change endpointSum f (path k A) ⬝ᵥ endpointSum f (path j B) = _
    rw [list_pairing f incidence hd, hpath, hpath]
  have hnrm (k : Rank n) (A : Other k) : v k A ⬝ᵥ v k A = 2 := by
    have hA : e k A.val ≠ e k (anchor k) := fun h => A.property (he k h)
    rw [gram, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    norm_num [basis_pairing, hA, Ne.symm hA]
  have hsame (k : Rank n) (A B : Other k) (hAB : A ≠ B) : v k A ⬝ᵥ v k B = 1 := by
    have hA : e k A.val ≠ e k (anchor k) := fun h => A.property (he k h)
    have hB : e k (anchor k) ≠ e k B.val := fun h => B.property (he k h.symm)
    have hAB' : e k A.val ≠ e k B.val := fun h => hAB (Subtype.ext (he k h))
    rw [gram, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    norm_num [basis_pairing, hA, hB, hAB']
  have hcross (k j : Rank n) (hkj : k ≠ j) (A : Other k) (B : Other j) :
      v k A ⬝ᵥ v j B = 0 := by
    have hk (a : Layer k) (b : Layer j) : e k a ≠ e j b := fun h => hkj (congrArg Sigma.fst h)
    rw [gram, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    norm_num [basis_pairing, hk]
  have ho (k : Rank n) : Fintype.card (Other k) = Fintype.card (Layer k) - 1 := by
    change Fintype.card {A : Layer k // ¬ A = anchor k} = _
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have h₂ (k : Rank n) : 2 ≤ Fintype.card (Other k) := by
    have := layer_at_least_n k
    rw [ho]
    omega
  let U (k : Rank n) := supportUnion (v k)
  have hU (k : Rank n) : blockSize (Fintype.card (Layer k)) ≤ (U k).card := by
    have h := support_union_bound (v k) (h₂ k) (hnrm k) (hsame k)
    have hc := layer_at_least_n k
    change _ ≤ (U k).card at h
    rw [ho] at h
    unfold blockSize
    split at h <;> split <;> omega
  have hdj : (↑(univ : Finset (Rank n)) : Set (Rank n)).PairwiseDisjoint U := by
    intro k _ j _ hkj
    exact supports_disjoint (v k) (v j) (by have := h₂ j; omega) (hnrm k) (hnrm j)
      (hsame j) (hcross k j hkj)
  calc
    _ ≤ ∑ k, (U k).card := sum_le_sum (fun k _ => hU k)
    _ = (univ.biUnion U).card := (card_biUnion hdj).symm
    _ ≤ d := by simpa using (univ.biUnion U).card_le_univ

/- A proper subset determines its rank by its cardinality. -/

private def properSubsets (n : ℕ) : Finset (Finset (Fin n)) :=
  (univ.erase ∅).erase univ

private theorem mem_properSubsets {n : ℕ} (A : Finset (Fin n)) :
    A ∈ properSubsets n ↔ A ≠ ∅ ∧ A ≠ univ := by
  simp [properSubsets, and_comm]

private theorem cutCoordinate_injective {n : ℕ} :
    Function.Injective (fun z : CutCoord n => z.2.val) := by
  rintro ⟨k, A⟩ ⟨j, B⟩ (h : A.val = B.val)
  have hkj : k = j := Subtype.ext (Fin.ext (by rw [← A.property, ← B.property, h]))
  subst j
  have hAB : A = B := Subtype.ext h
  subst B
  rfl

private noncomputable def properCutEquiv (n : ℕ) : CutCoord n ≃ properSubsets n := by
  refine Equiv.ofBijective (fun z => ⟨z.2.val, (mem_properSubsets _).mpr ⟨?_, ?_⟩⟩)
    ⟨fun _ _ h => cutCoordinate_injective (congrArg Subtype.val h), ?_⟩
  · intro h
    have hpos := z.1.property
    have hcard := z.2.property
    rw [h, card_empty] at hcard
    omega
  · intro h
    have hlt := z.1.val.isLt
    have hcard := z.2.property
    rw [h, card_univ, Fintype.card_fin] at hcard
    omega
  · intro A
    obtain ⟨hnonempty, hnotuniv⟩ := (mem_properSubsets _).mp A.property
    have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr hnonempty)
    have hlt : A.val.card < n := by
      have hc : A.val.card ≤ n := by simpa using A.val.card_le_univ
      apply lt_of_le_of_ne hc
      intro he
      apply hnotuniv
      apply eq_of_subset_of_card_le (subset_univ _)
      simp [he]
    exact ⟨⟨⟨⟨A.val.card, hlt⟩, hp⟩, ⟨A.val, rfl⟩⟩, rfl⟩

private theorem card_cutCoord {n : ℕ} (hn : 0 < n) : Fintype.card (CutCoord n) = 2 ^ n - 2 := by
  rw [Fintype.card_congr (properCutEquiv n), Fintype.card_coe, properSubsets]
  have hu : (univ : Finset (Fin n)) ≠ ∅ := by
    intro he
    have hcard : (univ : Finset (Fin n)).card = n := by simp
    rw [he, card_empty] at hcard
    omega
  rw [card_erase_of_mem (mem_erase.mpr ⟨hu, mem_univ _⟩), card_erase_of_mem (mem_univ _)]
  simp only [card_univ, Fintype.card_finset, Fintype.card_fin, Nat.sub_sub]

/-- The cut family of a permutation consists of its nonempty proper unordered prefixes. -/
@[expose] def cutFamily {n : ℕ} (p : Equiv.Perm (Fin n)) : Finset (Finset (Fin n)) :=
  univ.image fun k : Rank n => prefixSet p k.val.val

private theorem incidence_true_iff_cut {n : ℕ} (p : Equiv.Perm (Fin n)) (z : CutCoord n) :
    incidence p z = true ↔ z.2.val ∈ cutFamily p := by
  rw [cutFamily, mem_image]
  simp only [mem_univ, true_and, incidence, oneHot, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨z.1, (congrArg Subtype.val h).symm⟩
  · obtain ⟨j, hj⟩ := z
    rintro ⟨k, hk⟩
    have hn : k = j := cutCoordinate_injective
      (show (⟨k, rankPrefix p k⟩ : CutCoord n).2.val = (⟨j, hj⟩ : CutCoord n).2.val from hk)
      |> congrArg Sigma.fst
    subst k
    exact Subtype.ext hk.symm

/-- Rossi's scaled distance is the cardinality of the symmetric difference of cut families. -/
theorem prefix_distance_eq_cut_symmDiff {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    prefixDistance p q = (cutFamily p ∆ cutFamily q).card := by
  classical
  rw [← incidence_dist, hammingDist]
  have hmem (z : CutCoord n) :
      z ∈ (univ.filter fun i => incidence p i ≠ incidence q i) ↔
        z.2.val ∈ cutFamily p ∆ cutFamily q := by
    rw [mem_filter, mem_symmDiff, ← incidence_true_iff_cut, ← incidence_true_iff_cut]
    cases incidence p z <;> cases incidence q z <;> simp
  refine card_bij (fun z _ => z.2.val) (fun z hz => (hmem z).mp hz)
    (fun _ _ _ _ h => cutCoordinate_injective h) ?_
  intro A hA
  have repr (r : Equiv.Perm (Fin n)) (hAr : A ∈ cutFamily r) :
      ∃ z : CutCoord n, z.2.val = A := by
    obtain ⟨k, _, hk⟩ := mem_image.mp hAr
    exact ⟨⟨k, rankPrefix r k⟩, hk⟩
  have hex : ∃ z : CutCoord n, z.2.val = A := by
    rcases mem_symmDiff.mp hA with hl | hr
    · exact repr p hl.1
    · exact repr q hr.1
  obtain ⟨z, hz⟩ := hex
  exact ⟨z, (hmem z).mpr (hz.symm ▸ hA), hz⟩

/-- The threshold at scale two, with the two three-bit exceptions in rank four. -/
@[expose] def minimumDimension (n : ℕ) : ℕ := if n = 4 then 12 else 2 ^ n - 2

private theorem sum_blockSizes {n : ℕ} (hn : 3 ≤ n) :
    (∑ k : Rank n, blockSize (Fintype.card (Layer k))) = minimumDimension n := by
  by_cases he : n = 4
  · subst n
    simp_rw [layer_card]
    decide
  rw [minimumDimension, ite_eq_right he, ← card_cutCoord (by omega : 0 < n), Fintype.card_sigma]
  apply sum_congr rfl
  intro k _
  have hc : Fintype.card (Layer k) ≠ 4 := by
    by_cases h₃ : n = 3
    · subst n
      have hpos := k.property
      have hlt := k.val.isLt
      rw [layer_card]
      have hk : k.val.val = 1 ∨ k.val.val = 2 := by omega
      rcases hk with hk | hk <;> rw [hk] <;> decide
    · have := layer_at_least_n k
      omega
  exact ite_eq_right hc

private theorem hamming_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x y : κ → Bool) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  rw [hammingDist, hammingDist]
  exact card_bijective e e.bijective (fun i => by simp)

/- The four even-parity triples are pairwise at Hamming distance two. -/

private def parityCode : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false], ![false, true, true], ![true, false, true], ![true, true, false]]

private theorem parityCode_dist (a b : Fin 4) :
    hammingDist (parityCode a) (parityCode b) = if a = b then 0 else 2 := by
  revert a b
  decide

private noncomputable def blockWord {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) : Fin (blockSize (Fintype.card α)) → Bool :=
  if h : Fintype.card α = 4 then
    parityCode (Fintype.equivFinOfCardEq h a) ∘
      (Fin.castOrderIso (show blockSize (Fintype.card α) = 3 by simp [blockSize, h])).toEquiv
  else
    oneHot (Fintype.equivFinOfCardEq (show Fintype.card α = blockSize (Fintype.card α) by
      simp [blockSize, h]) a)

private theorem blockWord_dist {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    hammingDist (blockWord a) (blockWord b) = if a = b then 0 else 2 := by
  by_cases h : Fintype.card α = 4
  · rw [blockWord, blockWord, dite_eq_left h, dite_eq_left h, hamming_reindex, parityCode_dist]
    simp only [Equiv.apply_eq_iff_eq]
  · rw [blockWord, blockWord, dite_eq_right h, dite_eq_right h, oneHot_dist]
    simp only [Equiv.apply_eq_iff_eq]

private def pad {a d : ℕ} (x : Fin a → Bool) (j : Fin d) : Bool :=
  if h : j.val < a then x ⟨j.val, h⟩ else false

private theorem pad_dist {a d : ℕ} (had : a ≤ d) (x y : Fin a → Bool) :
    hammingDist (pad x : Fin d → Bool) (pad y) = hammingDist x y := by
  symm
  rw [hammingDist, hammingDist]
  refine card_bij (fun i _ => Fin.castLE had i) ?_ (fun _ _ _ _ h => Fin.castLE_injective _ h) ?_
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    change pad x (Fin.castLE had i) ≠ pad y (Fin.castLE had i)
    simpa [pad, i.isLt] using hi
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    by_cases h : j.val < a
    · refine ⟨⟨j.val, h⟩, ?_, Fin.ext rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      simpa [pad, h] using hj
    · simp [pad, h] at hj

private noncomputable def blockEncoding {n : ℕ} (p : Equiv.Perm (Fin n))
    (z : Σ k : Rank n, Fin (blockSize (Fintype.card (Layer k)))) : Bool :=
  blockWord (rankPrefix p z.1) z.2

private theorem dimension_upper {n d : ℕ} (hn : 3 ≤ n) (hd : minimumDimension n ≤ d) :
    ∃ f : Equiv.Perm (Fin n) → Fin d → Bool,
      ∀ p q, hammingDist (f p) (f q) = prefixDistance p q := by
  let C := Σ k : Rank n, Fin (blockSize (Fintype.card (Layer k)))
  have hc : Fintype.card C = minimumDimension n := by
    change Fintype.card (Σ k : Rank n, Fin (blockSize (Fintype.card (Layer k)))) = _
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using sum_blockSizes hn
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun p => pad (blockEncoding p ∘ e), fun p q => ?_⟩
  rw [pad_dist hd, hamming_reindex, hamming_sigma, distance_sum]
  exact sum_congr rfl (fun k _ => blockWord_dist (rankPrefix p k) (rankPrefix q k))

/-- The least dimension of a unit-Hamming cube that realizes Rossi's scaled prefix metric. -/
theorem minimum_hamming_dimension (n d : ℕ) (hn : 3 ≤ n) :
    (∃ f : Equiv.Perm (Fin n) → Fin d → Bool,
      ∀ p q, hammingDist (f p) (f q) =
        2 * (univ.filter fun k : Rank n => prefixSet p k.val.val ≠ prefixSet q k.val.val).card) ↔
      (if n = 4 then 12 else 2 ^ n - 2) ≤ d := by
  change (∃ f : Equiv.Perm (Fin n) → Fin d → Bool,
    ∀ p q, hammingDist (f p) (f q) = prefixDistance p q) ↔ minimumDimension n ≤ d
  constructor
  · rintro ⟨f, hf⟩
    rw [← sum_blockSizes hn]
    exact dimension_lower hn f hf
  · exact dimension_upper hn

end D5.S3.Combinatorics.Graph.PrefixHamming
