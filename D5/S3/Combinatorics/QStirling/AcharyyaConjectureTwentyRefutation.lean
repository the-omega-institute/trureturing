/- GID: D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation
   mirror-E: none(waiver:kernel-checked-refutation-probe)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.claim; result=D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.result; claim=D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.claim
   digest: Complement followed by full standardization need not satisfy the pointwise identity. -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Sort
import Mathlib.Tactic.NormNum

/-!
# Acharyya's pointwise Conjecture 20

Source: arXiv:2404.14439v1, Definitions 7, 12, 13 and Lemma 19.
The journal version is DOI 10.61091/ars162-14, Conjecture 3.16.
Only the universal pointwise identity is the target. The following generating
function equality is a separate unresolved assertion.

Blocks are finite sets of signed integers, indexed from zero. On admissible
inputs the default empty block and default minimum are never used at a valid
index. Standardization orients every nonzero pair and then sorts all pairs by
their absolute minimum, retaining the zero block.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.QStirling.AcharyyaConjectureTwentyRefutation

/-- An ordered list of signed blocks; admissibility is imposed by `Standard`. -/
abbrev Blocks := List (Finset ℤ)

/-- Zero-based block access, with an empty default outside the list. -/
def block (pi : Blocks) (i : ℕ) : Finset ℤ := pi[i]?.getD ∅

/-- The minimum of the absolute values; the empty-set default is irrelevant. -/
def minAbs (S : Finset ℤ) : ℕ := (S.image Int.natAbs).min.untopD 0

/-- The maximum of the absolute values. -/
def maxAbs (S : Finset ℤ) : ℕ := S.sup Int.natAbs

/-- Negate every signed letter of a block. -/
def negate (S : Finset ℤ) : Finset ℤ := S.image fun z => -z

/-- All source conditions for membership in S_B(<n>,k), including standard order. -/
def Standard (n k : ℕ) (pi : Blocks) : Prop :=
  pi.length = 2 * k + 1 ∧
  (∀ i ∈ Finset.range pi.length, (block pi i).Nonempty) ∧
  (∀ i ∈ Finset.range pi.length, ∀ j ∈ Finset.range pi.length,
    i ≠ j → Disjoint (block pi i) (block pi j)) ∧
  ((Finset.range pi.length).biUnion (block pi) = Finset.Icc (-(n : ℤ)) (n : ℤ)) ∧
  0 ∈ block pi 0 ∧ negate (block pi 0) = block pi 0 ∧
  (∀ r ∈ Finset.range k, block pi (2 * r + 2) = negate (block pi (2 * r + 1))) ∧
  (∀ r ∈ Finset.range k, (minAbs (block pi (2 * r + 2)) : ℤ) ∈
    block pi (2 * r + 2)) ∧
  minAbs (block pi 0) = 0 ∧
  (∀ r ∈ Finset.range (k + 1), ∀ t ∈ Finset.range (k + 1), r < t →
    minAbs (block pi (2 * r)) < minAbs (block pi (2 * t)))

/-- Definition 13: signed complement fixes zero and preserves the sign. -/
def complementLetter (n : ℕ) (z : ℤ) : ℤ :=
  if z = 0 then 0 else if 0 < z then (n : ℤ) + 1 - z else -((n : ℤ) + 1 + z)

/-- Complement every letter, retaining the original block order. -/
def complement (n : ℕ) (pi : Blocks) : Blocks :=
  pi.map fun S => S.image (complementLetter n)

/-- Orient a paired odd/even block so that its positive absolute minimum is even. -/
def orient (A B : Finset ℤ) : Finset ℤ × Finset ℤ :=
  if (minAbs A : ℤ) ∈ A then (B, A) else (A, B)

/-- Full standardization: orient every pair, then sort pairs by their common minimum. -/
def standardize (k : ℕ) (pi : Blocks) : Blocks :=
  let pairs := (List.range k).map fun r =>
    orient (block pi (2 * r + 1)) (block pi (2 * r + 2))
  let ordered := pairs.mergeSort fun p q => minAbs p.2 ≤ minAbs q.2
  block pi 0 :: ordered.flatMap (fun p => [p.1, p.2])

/-- Lemma 19's map on the entire original domain, with no witness-specific branch. -/
def f (n k : ℕ) (pi : Blocks) : Blocks := standardize k (complement n pi)

/-- Every possible (signed letter, target-block index) pair. -/
def candidates (pi : Blocks) : Finset (ℤ × ℕ) :=
  ((Finset.range pi.length).biUnion (block pi)).product (Finset.range pi.length)

/-- Definition 12(1), with a signed comparison and the inclusive lower bound. -/
def rosPairs (pi : Blocks) : Finset (ℤ × ℕ) :=
  (candidates pi).filter fun p =>
    (∃ i ∈ Finset.range p.2, p.1 ∈ block pi i) ∧
      (minAbs (block pi p.2) : ℤ) ≤ p.1

/-- Definition 12(4), including positivity and the inclusive upper bound. -/
def rcbPairs (pi : Blocks) : Finset (ℤ × ℕ) :=
  (candidates pi).filter fun p =>
    (∃ i ∈ Finset.range p.2, p.1 ∈ block pi i) ∧
      0 < p.1 ∧ p.1 ≤ (maxAbs (block pi p.2) : ℤ)

/-- The source right-opener-smaller statistic. -/
def ros (pi : Blocks) : ℕ := (rosPairs pi).card

/-- The source right-closer-bigger statistic. -/
def rcb (pi : Blocks) : ℕ := (rcbPairs pi).card

/-- The full original universal pointwise assertion, over all source parameters. -/
def claim : Prop :=
  ∀ n k : ℕ, ∀ pi : Blocks, Standard n k pi →
    rcb (f n k pi) = ros pi + k * (k - 1)

/-- The original-domain partition 0 / (-1,2,3) / (1,-2,-3). -/
def witness : Blocks := [{0}, {-1, 2, 3}, {1, -2, -3}]

/-- The full universal identity is contradicted inside its original domain. -/
theorem result : ¬ claim := by
  intro h
  have hp : Standard 3 1 witness := by decide +kernel
  have hros : rosPairs witness = {(2, 2), (3, 2)} := by decide +kernel
  have hrcb : rcbPairs (f 3 1 witness) = {(3, 2)} := by decide +kernel
  have hh := h 3 1 witness hp
  change (rcbPairs (f 3 1 witness)).card = (rosPairs witness).card + 1 * (1 - 1) at hh
  rw [hros, hrcb] at hh
  norm_num at hh

#check claim
#check result
#print axioms result

end D5.S3.Combinatorics.QStirling.AcharyyaConjectureTwentyRefutation
