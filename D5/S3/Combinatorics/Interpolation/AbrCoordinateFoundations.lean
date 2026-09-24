/- GID: D5/S3/Combinatorics/Interpolation/AbrCoordinateFoundations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrCoordinateFoundations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable exponent order and coordinate data for ABR straightening. -/

import D5.S1.Words.Patterns.Separable.CutFactorization
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
This module defines the stable decreasing-exponent order, the ABR dominance
order, and the coordinate operations shared by the straightening argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening

open scoped BigOperators
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization

/-- The ABR index permutation: exponents decrease, and original labels
increase when exponents are equal. -/
def indexPerm {n : Nat} (a : Fin n →₀ Nat) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (a i))

/-- The number of descents weakly to the right of a position. -/
def suffixHeight {n : Nat} (pi : Equiv.Perm (Fin n)) (i : Fin n) : Nat :=
  Finset.univ.sum fun j => if i <= j then descentAt pi j else 0

/-- The exponent vector of the ABR descent monomial. -/
def descentExponent {n : Nat} (pi : Equiv.Perm (Fin n)) : Fin n →₀ Nat :=
  Finsupp.equivFunOnFinite.symm (fun x => suffixHeight pi (pi.symm x))

/-- The ABR descent monomial attached to a permutation. -/
def descentMonomial {n : Nat} (pi : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) Rat :=
  monomial (descentExponent pi) 1

/-- Residual exponent after removing the descent monomial, read in stable
decreasing-exponent order. -/
def residual {n : Nat} (a : Fin n →₀ Nat) (i : Fin n) : Nat :=
  a (indexPerm a i) - suffixHeight (indexPerm a) i

/-- Sum of the first `k` parts of the decreasing exponent rearrangement. -/
def prefixWeight {n : Nat} (a : Fin n →₀ Nat) (k : Nat) : Nat :=
  (Finset.univ.filter fun i : Fin n => i.val < k).sum fun i => a (indexPerm a i)

/-- Dominance on equal-size exponent partitions, in the direction used by
ABR: `a` is below `b` if every initial sum of `a` is bounded by that of `b`. -/
def DominatedBy {n : Nat} (a b : Fin n →₀ Nat) : Prop :=
  (∑ x, a x) = ∑ x, b x ∧
    forall k : Nat, prefixWeight a k <= prefixWeight b k

/-- Inversion count of a permutation, used in reverse inside an equal
exponent-partition block. -/
def inversionCount {n : Nat} (pi : Equiv.Perm (Fin n)) : Nat :=
  ((Finset.univ.product Finset.univ).filter fun p => p.1 < p.2 ∧ pi p.2 < pi p.1).card

/-- Inversions of the stable decreasing sort, expressed on coordinate labels. -/
def exponentInversionCount {n : Nat} (a : Fin n →₀ Nat) : Nat :=
  ((Finset.univ.product Finset.univ).filter fun p => p.1 < p.2 ∧ a p.1 < a p.2).card

/-- The strict ABR order: strict dominance first; for equal exponent
partitions, the stable permutation with more inversions is lower. -/
def AbrLower {n : Nat} (a b : Fin n →₀ Nat) : Prop :=
  (DominatedBy a b ∧ ¬ DominatedBy b a) ∨
    ((fun i => a (indexPerm a i)) = (fun i => b (indexPerm b i)) ∧
      inversionCount (indexPerm b) < inversionCount (indexPerm a))

/-- Squarefree exponent supported on a finite coordinate set. -/
def subsetExponent {n : Nat} (t : Finset (Fin n)) : Fin n →₀ Nat :=
  Finsupp.indicator t (fun _ _ => 1)

/-- The first `h` coordinates in the stable decreasing-exponent order. -/
def initialSet {n : Nat} (a : Fin n →₀ Nat) (h : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun x => ((indexPerm a).symm x).val < h

/-- Coordinates at exponent level `v` that receive a squarefree increment. -/
def levelSelection {n : Nat} (a : Fin n →₀ Nat)
    (t : Finset (Fin n)) (v : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun x => a x = v ∧ x ∈ t

/-- Number of coordinates whose exponent is at least `v`. -/
def highCount {n : Nat} (a : Fin n →₀ Nat) (v : Nat) : Nat :=
  (Finset.univ.filter fun x => v <= a x).card

/-- Add one to the first `h` coordinates in stable order. -/
def leadExponent {n : Nat} (a : Fin n →₀ Nat) (h : Nat) : Fin n →₀ Nat :=
  a + subsetExponent (initialSet a h)

/-- Substitute the elementary symmetric polynomials into a coefficient
polynomial. -/
def esymmSubstitution {n : Nat} :
    MvPolynomial (Fin n) Rat →+* MvPolynomial (Fin n) Rat :=
  (MvPolynomial.aeval
    (fun k : Fin n => MvPolynomial.esymm (Fin n) Rat (k.val + 1))).toRingHom

theorem inversionCount_indexPerm {n : Nat} (a : Fin n →₀ Nat) :
    inversionCount (indexPerm a) = exponentInversionCount a := by
  classical
  have hanti : Antitone (fun i => a (indexPerm a i)) :=
    fun i j hij =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hij
  have htie : ∀ {i j : Fin n}, i < j ->
      a (indexPerm a i) = a (indexPerm a j) ->
      indexPerm a i < indexPerm a j := by
    intro i j hij heq
    have hsort : indexPerm a =
        Tuple.sort (fun x : Fin n => OrderDual.toDual (a x)) := rfl
    exact (Tuple.eq_sort_iff.mp hsort).2 i j hij heq
  let source := (Finset.univ.product Finset.univ).filter fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ indexPerm a p.2 < indexPerm a p.1
  let target := (Finset.univ.product Finset.univ).filter fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ a p.1 < a p.2
  change source.card = target.card
  apply Finset.card_bij
      (fun p _ => (indexPerm a p.2, indexPerm a p.1))
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨_, hp⟩
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      hp.2, ?_⟩
    have hle := hanti hp.1.le
    exact lt_of_le_of_ne hle fun heq =>
      (htie hp.1 heq.symm).not_gt hp.2
  · intro p hp q hq heq
    injection heq with h2 h1
    exact Prod.ext ((indexPerm a).injective h1) ((indexPerm a).injective h2)
  · intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨_, hp⟩
    let i := (indexPerm a).symm p.2
    let j := (indexPerm a).symm p.1
    have hij : i < j := by
      have hne : i ≠ j := by
        intro heq
        have hpEq : p.2 = p.1 := (indexPerm a).symm.injective heq
        exact hp.1.ne hpEq.symm
      by_contra h
      have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hne.symm
      have hle := hanti hji.le
      simp only [i, j, Equiv.apply_symm_apply] at hle
      omega
    refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        hij, ?_⟩
      simpa [i, j] using hp.1
    · simp [i, j]

theorem mem_initialSet_of_exponent_lt {n : Nat} (a : Fin n →₀ Nat)
    (h : Nat) {x y : Fin n} (hxy : a x < a y) (hx : x ∈ initialSet a h) :
    y ∈ initialSet a h := by
  have hanti : Antitone (fun i => a (indexPerm a i)) :=
    fun i j hij =>
      Tuple.monotone_sort (fun z : Fin n => OrderDual.toDual (a z)) hij
  simp only [initialSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx ⊢
  have hpos : (indexPerm a).symm y < (indexPerm a).symm x := by
    by_contra hnot
    have hle : (indexPerm a).symm x <= (indexPerm a).symm y := le_of_not_gt hnot
    have ha := hanti hle
    have hayx : a y <= a x := by simpa using ha
    omega
  exact lt_of_lt_of_le (Fin.mk_lt_mk.mp hpos) hx.le

theorem mem_initialSet_of_tie_lt {n : Nat} (a : Fin n →₀ Nat)
    (h : Nat) {x y : Fin n} (hxy : x < y) (heq : a x = a y)
    (hy : y ∈ initialSet a h) : x ∈ initialSet a h := by
  simp only [initialSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hy ⊢
  have hpos : (indexPerm a).symm x < (indexPerm a).symm y := by
    by_contra hnot
    have hne : (indexPerm a).symm y ≠ (indexPerm a).symm x := by
      intro hpositions
      have hlabels : y = x := (indexPerm a).injective (by simpa using hpositions)
      exact hxy.ne hlabels.symm
    have hyx : (indexPerm a).symm y < (indexPerm a).symm x :=
      lt_of_le_of_ne (le_of_not_gt hnot) hne
    have heq' :
        a (indexPerm a ((indexPerm a).symm y)) =
          a (indexPerm a ((indexPerm a).symm x)) := by
      simpa using heq.symm
    have hsort : indexPerm a =
        Tuple.sort (fun z : Fin n => OrderDual.toDual (a z)) := rfl
    have htie := (Tuple.eq_sort_iff.mp hsort).2 _ _ hyx heq'
    have hyx' : y < x := by simpa using htie
    exact hxy.not_gt hyx'
  exact lt_trans (Fin.mk_lt_mk.mp hpos) hy

end D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
