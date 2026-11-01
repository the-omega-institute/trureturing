/- GID: D5/S3/Quantum/Magic/AffinePartitionFlagMaximum
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/AffinePartitionFlagMaximum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The flag partition maximizes squared sizes of affine parts outside the origin. -/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Digits.Defs

/-! Affine partitions of the punctured vector space in the conjecture of Heimendahl,
Heinrich and Gross, arXiv:2011.11651v3. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Magic.AffinePartitionFlagMaximum

open scoped BigOperators

/-- The standard finite vector space. -/
abbrev vector (p n : ℕ) := Fin n → ZMod p

/-- Nonempty affine parts, disjoint from one another, covering exactly the nonzero vectors. -/
def isAffinePartition (p n : ℕ) [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n))) : Prop :=
  (∀ k ∈ parts, (k : Set (vector p n)).Nonempty) ∧
  (∀ k ∈ parts, ∀ l ∈ parts, k ≠ l →
    Disjoint (k : Set (vector p n)) (l : Set (vector p n))) ∧
  ∀ v : vector p n, v ≠ 0 ↔ ∃ k ∈ parts, v ∈ k

/-- The objective in the affine partition problem. -/
def sqSum {p n : ℕ} [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n))) : ℕ :=
  ∑ k ∈ parts, Nat.card k ^ 2

/-- A coordinate cell with all earlier coordinates zero. -/
def flagCell (p n : ℕ) [Fact p.Prime] (i : Fin n) (x : ZMod p) :
    AffineSubspace (ZMod p) (vector p n) where
  carrier := {v | (∀ j < i, v j = 0) ∧ v i = x}
  smul_vsub_vadd_mem' c a b d ha hb hd := by
    constructor
    · intro j hj
      change c * (a j - b j) + d j = 0
      rw [ha.1 j hj, hb.1 j hj, hd.1 j hj]
      simp
    · change c * (a i - b i) + d i = x
      rw [ha.2, hb.2, hd.2]
      simp

/-- All flag cells with nonzero distinguished coordinate. -/
def flagPartition (p n : ℕ) [Fact p.Prime] :
    Finset (AffineSubspace (ZMod p) (vector p n)) := by
  classical
  exact Finset.univ.image
    (fun a : Fin n × {x : ZMod p // x ≠ 0} => flagCell p n a.1 a.2.1)

/-- The value of the flag partition, with dimensions in increasing order. -/
def flagValue (p n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (p - 1) * p ^ (2 * k)

private def radix (p s : ℕ) : ℕ := Nat.ofDigits (p ^ 2) (Nat.digits p s)

private lemma radix_zero (p : ℕ) : radix p 0 = 0 := by
  change Nat.ofDigits (p ^ 2) (Nat.digits p 0) = 0
  rw [Nat.digits_zero, Nat.ofDigits_nil]

private lemma radix_step {p : ℕ} (hp : 2 ≤ p) (s : ℕ) :
    radix p s = s % p + p ^ 2 * radix p (s / p) := by
  by_cases hs : s = 0
  · subst s
    simp [radix_zero]
  · change Nat.ofDigits (p ^ 2) (Nat.digits p s) =
      s % p + p ^ 2 * Nat.ofDigits (p ^ 2) (Nat.digits p (s / p))
    rw [Nat.digits_def' (by omega) (Nat.pos_of_ne_zero hs), Nat.ofDigits_cons]

private lemma radix_affine {p : ℕ} (hp : 2 ≤ p) (q r : ℕ) (hr : r < p) :
    radix p (p * q + r) = r + p ^ 2 * radix p q := by
  rw [radix_step hp]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div (show 0 < p by omega),
    Nat.div_eq_of_lt hr]

private lemma radix_one {p : ℕ} (hp : 2 ≤ p) (s : ℕ) (hs : 1 ≤ s) :
    1 + radix p (s - 1) ≤ radix p s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    have hd := Nat.mod_add_div s p
    have hrlt := Nat.mod_lt s (show 0 < p by omega)
    by_cases hr : s % p = 0
    · have hq : 1 ≤ s / p := by
        by_contra hn
        have hz : s / p = 0 := Nat.lt_one_iff.mp (lt_of_not_ge hn)
        rw [hr, hz] at hd
        simp at hd
        omega
      have hi := ih (s / p) (Nat.div_lt_self (by omega) (by omega)) hq
      have he : s - 1 = p * (s / p - 1) + (p - 1) := by
        have hqeq := Nat.sub_add_cancel hq
        have hpeq := Nat.sub_add_cancel (show 1 ≤ p by omega)
        have hseq := Nat.sub_add_cancel hs
        nlinarith
      rw [he, radix_affine hp _ _ (by omega), radix_step hp s, hr, zero_add]
      have hm := Nat.mul_le_mul_left (p ^ 2) hi
      have hpp : p ≤ p ^ 2 := Nat.le_self_pow (by decide) p
      have hpeq := Nat.sub_add_cancel (show 1 ≤ p by omega)
      nlinarith
    · have he : s - 1 = p * (s / p) + (s % p - 1) := by omega
      rw [he, radix_affine hp _ _ (by omega), radix_step hp s]
      omega

private lemma radix_power {p : ℕ} (hp : 2 ≤ p) (k s : ℕ) (hs : p ^ k ≤ s) :
    p ^ (2 * k) + radix p (s - p ^ k) ≤ radix p s := by
  induction k generalizing s with
  | zero => simpa using radix_one hp s hs
  | succ k ih =>
    have hq : p ^ k ≤ s / p :=
      (Nat.le_div_iff_mul_le (show 0 < p by omega)).2 (by simpa [pow_succ] using hs)
    have he : s - p ^ (k + 1) = p * (s / p - p ^ k) + s % p := by
      have hd := Nat.mod_add_div s p
      have hm := Nat.mul_sub_left_distrib p (s / p) (p ^ k)
      have hle := Nat.mul_le_mul_left p hq
      rw [pow_succ, Nat.mul_comm (p ^ k) p]
      omega
    rw [he, radix_affine hp _ _ (Nat.mod_lt _ (by omega)), radix_step hp s]
    have hi := Nat.mul_le_mul_left (p ^ 2) (ih (s / p) hq)
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    nlinarith

private lemma power_family_bound {p : ℕ} (hp : 2 ≤ p) {a : Type*}
    (t : Finset a) (size : a → ℕ) (hs : ∀ x ∈ t, ∃ k, size x = p ^ k) :
    ∑ x ∈ t, size x ^ 2 ≤ radix p (∑ x ∈ t, size x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [radix_zero]
  | @insert a t ha ih =>
    have hi := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨k, hk⟩ := hs a (Finset.mem_insert_self a t)
    have hpow : size a ^ 2 = p ^ (2 * k) := by
      rw [hk, ← pow_mul, Nat.mul_comm k 2]
    have hh := radix_power hp k (size a + ∑ x ∈ t, size x) (by omega)
    rw [← hk, Nat.add_sub_cancel_left] at hh
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    omega

private lemma radix_value {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    radix p (p ^ n - 1) = flagValue p n := by
  induction n with
  | zero => exact radix_zero p
  | succ n ih =>
    have he : p ^ (n + 1) - 1 = p * (p ^ n - 1) + (p - 1) := by
      have hpow := Nat.one_le_pow n p (by omega)
      have hn := Nat.sub_add_cancel hpow
      have hh := Nat.sub_add_cancel (show 1 ≤ p by omega)
      apply (Nat.sub_eq_iff_eq_add (Nat.one_le_pow (n + 1) p (by omega))).2
      rw [pow_succ]
      nlinarith
    rw [he, radix_affine hp _ _ (by omega), ih]
    change (p - 1) + p ^ 2 * (∑ k ∈ Finset.range n, (p - 1) * p ^ (2 * k)) =
      ∑ k ∈ Finset.range (n + 1), (p - 1) * p ^ (2 * k)
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, mul_one]
    rw [Finset.mul_sum, Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    ring

private lemma affine_card {p n : ℕ} [Fact p.Prime]
    (k : AffineSubspace (ZMod p) (vector p n)) (hk : (k : Set (vector p n)).Nonempty) :
    Nat.card k = p ^ Module.finrank (ZMod p) k.direction := by
  obtain ⟨v, hv⟩ := hk
  have : Nonempty k := ⟨⟨v, hv⟩⟩
  rw [← Nat.card_congr (Equiv.vaddConst (⟨v, hv⟩ : k)),
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

private lemma partition_card {p n : ℕ} [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n)))
    (hparts : isAffinePartition p n parts) :
    ∑ k ∈ parts, Nat.card k = p ^ n - 1 := by
  classical
  let f := fun k : AffineSubspace (ZMod p) (vector p n) => (k : Set (vector p n)).toFinset
  have hd : (parts : Set _).PairwiseDisjoint f := by
    intro k hk l hl hkl
    apply Finset.disjoint_left.mpr
    intro v hvk hvl
    exact Set.disjoint_left.mp (hparts.2.1 k hk l hl hkl)
      (by simpa [f] using hvk) (by simpa [f] using hvl)
  have hu : parts.biUnion f = Finset.univ.erase 0 := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    simpa [f] using (hparts.2.2 v).symm
  calc
    ∑ k ∈ parts, Nat.card k = ∑ k ∈ parts, (f k).card := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [f, Set.toFinset_card, Nat.card_eq_fintype_card]
    _ = (parts.biUnion f).card := (Finset.card_biUnion hd).symm
    _ = p ^ n - 1 := by simp [hu, ZMod.card]

private lemma flag_cell_card {p n : ℕ} [Fact p.Prime] (i : Fin n) (x : ZMod p) :
    Nat.card (flagCell p n i x) = p ^ (n - 1 - i.val) := by
  classical
  let e : flagCell p n i x ≃ ({j : Fin n // i < j} → ZMod p) :=
    { toFun := fun v j => v.1 j.1
      invFun := fun w => ⟨fun j => if h : i < j then w ⟨j, h⟩ else
          if j = i then x else 0, by
        constructor
        · intro j hj
          simp [not_lt_of_ge (le_of_lt hj), ne_of_lt hj]
        · simp⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext j
        change (if h : i < j then v.1 j else if j = i then x else 0) = v.1 j
        by_cases h : i < j
        · simp [h]
        · by_cases he : j = i
          · subst j
            simpa using v.2.2.symm
          · simp only [h, he, dite_false, ite_false]
            exact (v.2.1 j (lt_of_le_of_ne (le_of_not_gt h) he)).symm
      right_inv := by
        intro w
        funext j
        simp [j.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  congr 1
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_subtype (Finset.Ioi i) (fun j => Finset.mem_Ioi)]
  exact Fin.card_Ioi i

private lemma flag_center {p n : ℕ} [Fact p.Prime] (i : Fin n) (x : ZMod p) :
    (Pi.single i x : vector p n) ∈ flagCell p n i x := by
  constructor
  · intro j hj
    simp [Pi.single_eq_of_ne (ne_of_lt hj)]
  · simp

private lemma flag_indices_of_mem {p n : ℕ} [Fact p.Prime]
    (a b : Fin n × {x : ZMod p // x ≠ 0}) (v : vector p n)
    (ha : v ∈ flagCell p n a.1 a.2.1) (hb : v ∈ flagCell p n b.1 b.2.1) : a = b := by
  have hi : a.1 = b.1 := by
    apply le_antisymm
    · by_contra h
      exact b.2.2 (hb.2.symm.trans (ha.1 b.1 (lt_of_not_ge h)))
    · by_contra h
      exact a.2.2 (ha.2.symm.trans (hb.1 a.1 (lt_of_not_ge h)))
  apply Prod.ext hi
  apply Subtype.ext
  exact ha.2.symm.trans (by simpa [hi] using hb.2)

private lemma flag_index_injective {p n : ℕ} [Fact p.Prime] :
    Function.Injective
      (fun a : Fin n × {x : ZMod p // x ≠ 0} => flagCell p n a.1 a.2.1) := by
  intro a b hab
  apply flag_indices_of_mem a b (Pi.single a.1 a.2.1) (flag_center _ _)
  change flagCell p n a.1 a.2.1 = flagCell p n b.1 b.2.1 at hab
  rw [← hab]
  exact flag_center _ _

private lemma flag_partition {p n : ℕ} [Fact p.Prime] :
    isAffinePartition p n (flagPartition p n) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨_, flag_center a.1 a.2.1⟩
  · intro k hk l hl hkl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    apply Set.disjoint_left.mpr
    intro v hva hvb
    exact hkl (congrArg (fun a => flagCell p n a.1 a.2.1)
      (flag_indices_of_mem a b v hva hvb))
  · intro v
    constructor
    · intro hv
      have hex : ∃ j : Fin n, v j ≠ 0 := Function.ne_iff.mp hv
      let nz := Finset.univ.filter (fun j : Fin n => v j ≠ 0)
      have hnz : nz.Nonempty := by
        simpa only [nz, Finset.filter_nonempty_iff, Finset.mem_univ, true_and] using hex
      let i := nz.min' hnz
      have hi : v i ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem nz hnz)).2
      refine ⟨flagCell p n i (v i), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(i, ⟨v i, hi⟩), Finset.mem_univ _, rfl⟩
      · refine ⟨?_, rfl⟩
        intro j hj
        by_contra hzero
        have hle : i ≤ j := Finset.min'_le nz j (by simp [nz, hzero])
        exact not_le_of_gt hj hle
    · rintro ⟨k, hk, hv⟩ hzero
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      exact a.2.2 (hv.2.symm.trans (by simp [hzero]))

private lemma flag_sum {p n : ℕ} [Fact p.Prime] :
    sqSum (flagPartition p n) = flagValue p n := by
  classical
  change (∑ k ∈ Finset.univ.image
    (fun a : Fin n × {x : ZMod p // x ≠ 0} => flagCell p n a.1 a.2.1),
      Nat.card k ^ 2) = flagValue p n
  rw [Finset.sum_image (fun a _ b _ h => flag_index_injective h)]
  simp_rw [flag_cell_card]
  rw [Fintype.sum_prod_type]
  have hc : Fintype.card {x : ZMod p // x ≠ 0} = p - 1 := by
    simp [Fintype.card_subtype_compl]
  simp only [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (p - 1) * (p ^ (n - 1 - i)) ^ 2)]
  change (∑ i ∈ Finset.range n, (p - 1) * (p ^ (n - 1 - i)) ^ 2) = _
  simp_rw [← pow_mul, Nat.mul_comm _ 2]
  exact Finset.sum_range_reflect (fun k => (p - 1) * p ^ (2 * k)) n

private lemma partition_bound {p n : ℕ} [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n)))
    (hparts : isAffinePartition p n parts) : sqSum parts ≤ flagValue p n := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h := power_family_bound hp parts (fun k => Nat.card k)
    (fun k hk => ⟨_, affine_card k (hparts.1 k hk)⟩)
  rw [partition_card parts hparts, radix_value hp] at h
  exact h

/-- The flag partition attains the maximum over every affine partition of the punctured space. -/
def claim : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ),
    isAffinePartition p n (flagPartition p n) ∧
    sqSum (flagPartition p n) = flagValue p n ∧
    ∀ parts, isAffinePartition p n parts → sqSum parts ≤ flagValue p n

/-- The affine partition flag maximum conjecture. -/
theorem result : claim := by
  intro p hp n
  exact ⟨flag_partition, flag_sum, fun parts hparts => partition_bound parts hparts⟩

end D5.S3.Quantum.Magic.AffinePartitionFlagMaximum
