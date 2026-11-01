/- GID: D5/S3/Quantum/Magic/AffinePartitionFlagMaximum
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/AffinePartitionFlagMaximum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The flag partition maximizes squared sizes of affine parts outside the origin. -/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! Affine partitions of the punctured vector space in the conjecture of Heimendahl,
Heinrich and Gross, arXiv:2011.11651v3. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Magic.AffinePartitionFlagMaximum

open scoped BigOperators

/-- The standard finite vector space. -/
def vector (p n : ℕ) := Fin n → ZMod p

/-- Nonempty affine parts, disjoint from one another, covering exactly the nonzero vectors. -/
def isAffinePartition (p n : ℕ) [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n))) : Prop :=
  (∀ k ∈ parts, (k : Set (vector p n)).Nonempty) ∧
  (∀ k ∈ parts, ∀ l ∈ parts, k ≠ l → Disjoint (k : Set _) (l : Set _)) ∧
  ∀ v : vector p n, v ≠ 0 ↔ ∃ k ∈ parts, v ∈ k

/-- The objective in the affine partition problem. -/
def sqSum {p n : ℕ} [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n))) : ℕ :=
  ∑ k ∈ parts, Nat.card k ^ 2

/-- A flag cell, fixing the first nonzero coordinate and its value. -/
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
  simp [radix]

private lemma radix_step {p : ℕ} (hp : 2 ≤ p) (s : ℕ) :
    radix p s = s % p + p ^ 2 * radix p (s / p) := by
  sorry

private lemma radix_affine {p : ℕ} (hp : 2 ≤ p) (q r : ℕ) (hr : r < p) :
    radix p (p * q + r) = r + p ^ 2 * radix p q := by
  sorry

private lemma radix_one {p : ℕ} (hp : 2 ≤ p) (s : ℕ) (hs : 1 ≤ s) :
    1 + radix p (s - 1) ≤ radix p s := by
  sorry

private lemma radix_power {p : ℕ} (hp : 2 ≤ p) (k s : ℕ) (hs : p ^ k ≤ s) :
    p ^ (2 * k) + radix p (s - p ^ k) ≤ radix p s := by
  sorry

private lemma power_family_bound {p : ℕ} (hp : 2 ≤ p) {a : Type*}
    (t : Finset a) (size : a → ℕ) (hs : ∀ x ∈ t, ∃ k, size x = p ^ k) :
    ∑ x ∈ t, size x ^ 2 ≤ radix p (∑ x ∈ t, size x) := by
  sorry

private lemma radix_value {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    radix p (p ^ n - 1) = flagValue p n := by
  sorry

private lemma affine_card {p n : ℕ} [Fact p.Prime]
    (k : AffineSubspace (ZMod p) (vector p n)) (hk : (k : Set _).Nonempty) :
    Nat.card k = p ^ Module.finrank (ZMod p) k.direction := by
  sorry

private lemma partition_card {p n : ℕ} [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n)))
    (hparts : isAffinePartition p n parts) :
    ∑ k ∈ parts, Nat.card k = p ^ n - 1 := by
  sorry

private lemma flag_cell_card {p n : ℕ} [Fact p.Prime] (i : Fin n) (x : ZMod p) :
    Nat.card (flagCell p n i x) = p ^ (n - 1 - i.val) := by
  sorry

private lemma flag_index_injective {p n : ℕ} [Fact p.Prime] :
    Function.Injective
      (fun a : Fin n × {x : ZMod p // x ≠ 0} => flagCell p n a.1 a.2.1) := by
  sorry

private lemma flag_partition {p n : ℕ} [Fact p.Prime] :
    isAffinePartition p n (flagPartition p n) := by
  sorry

private lemma flag_sum {p n : ℕ} [Fact p.Prime] :
    sqSum (flagPartition p n) = flagValue p n := by
  sorry

private lemma partition_bound {p n : ℕ} [Fact p.Prime]
    (parts : Finset (AffineSubspace (ZMod p) (vector p n)))
    (hparts : isAffinePartition p n parts) : sqSum parts ≤ flagValue p n := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h := power_family_bound hp parts (fun k => Nat.card k)
    (fun k hk => ⟨_, affine_card k (hparts.1 k hk)⟩)
  simpa only [sqSum, partition_card parts hparts, radix_value hp] using h

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
