/- GID: D5/S3/Combinatorics/Interpolation/AbrCoordinateBoxStraightening
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrCoordinateBoxStraightening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: ABR descent straightening preserves a coordinate box in multivariate polynomials. -/

import D5.S1.Words.Patterns.Separable.CutFactorization
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
This module formalizes the descent-monomial straightening argument of
Adin--Brenti--Roichman, Sections 3.1--3.4.  The filtration used here is the
coordinate box: every variable exponent is bounded independently.  In
particular, the maximum descent exponent is the number of descents; its total
degree is the major index and is not used as the box bound.

Source: R. M. Adin, F. Brenti, Y. Roichman, Trans. Amer. Math. Soc. 357
(2005), DOI 10.1090/S0002-9947-04-03494-4, Claim 3.1 through Lemma 3.5.
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
  Finset.univ.sum fun j => if i ≤ j then descentAt pi j else 0

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
    forall k : Nat, prefixWeight a k ≤ prefixWeight b k

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
  (Finset.univ.filter fun x => v ≤ a x).card

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
  have htie : ∀ {i j : Fin n}, i < j →
      a (indexPerm a i) = a (indexPerm a j) →
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

theorem subsetExponent_injective {n : Nat} :
    Function.Injective (subsetExponent (n := n)) := by
  intro s t h
  ext x
  have hx := congrArg (fun u : Fin n →₀ Nat => u x) h
  simp only [subsetExponent, Finsupp.indicator_apply] at hx
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp_all

theorem highCount_add_subsetExponent {n : Nat} (a : Fin n →₀ Nat)
    (t : Finset (Fin n)) (v : Nat) :
    highCount (a + subsetExponent t) (v + 1) =
      highCount a (v + 1) + (levelSelection a t v).card := by
  classical
  unfold highCount levelSelection
  rw [show (Finset.univ.filter fun x : Fin n =>
        v + 1 ≤ (a + subsetExponent t) x).card =
      ∑ x, if v + 1 ≤ (a + subsetExponent t) x then 1 else 0 by simp]
  rw [show (Finset.univ.filter fun x : Fin n => v + 1 ≤ a x).card =
      ∑ x, if v + 1 ≤ a x then 1 else 0 by simp]
  rw [show (Finset.univ.filter fun x : Fin n => a x = v ∧ x ∈ t).card =
      ∑ x, if a x = v ∧ x ∈ t then 1 else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finsupp.add_apply, subsetExponent, Finsupp.indicator_apply]
  by_cases hx : x ∈ t
  · rcases lt_trichotomy (a x) v with hav | hav | hav
    · have hle : ¬v ≤ a x := by omega
      have hsucc : ¬v + 1 ≤ a x + 1 := by omega
      have hlt : ¬v < a x := by omega
      have hne : a x ≠ v := by omega
      simp [hx, hle, hsucc, hlt, hne]
    · subst v
      simp [hx]
    · have hle : v ≤ a x := hav.le
      have hsucc : v + 1 ≤ a x := hav
      have hne : a x ≠ v := hav.ne'
      simp [hx, hle, hsucc, hne]
  · simp [hx]

theorem highCount_eq_of_sorted_eq {n : Nat} {a b : Fin n →₀ Nat}
    (hsorted : (fun i => a (indexPerm a i)) = fun i => b (indexPerm b i))
    (v : Nat) : highCount a v = highCount b v := by
  classical
  unfold highCount
  rw [show (Finset.univ.filter fun x : Fin n => v ≤ a x).card =
      ∑ x, if v ≤ a x then 1 else 0 by simp]
  rw [show (Finset.univ.filter fun x : Fin n => v ≤ b x).card =
      ∑ x, if v ≤ b x then 1 else 0 by simp]
  calc
    (∑ x, if v ≤ a x then 1 else 0) =
        ∑ i, if v ≤ a (indexPerm a i) then 1 else 0 := by
          symm
          exact Fintype.sum_equiv (indexPerm a)
            (fun i => if v ≤ a (indexPerm a i) then 1 else 0)
            (fun x => if v ≤ a x then 1 else 0) (fun _ => rfl)
    _ = ∑ i, if v ≤ b (indexPerm b i) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [congrFun hsorted i]
    _ = ∑ x, if v ≤ b x then 1 else 0 := by
          exact Fintype.sum_equiv (indexPerm b)
            (fun i => if v ≤ b (indexPerm b i) then 1 else 0)
            (fun x => if v ≤ b x then 1 else 0) (fun _ => rfl)

/-- Equality of sorted exponent partitions fixes how many coordinates are
incremented at every original exponent level. -/
theorem card_levelSelection_eq_of_sorted_eq {n h : Nat} (a : Fin n →₀ Nat)
    (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    (v : Nat) :
    (levelSelection a t v).card = (levelSelection a (initialSet a h) v).card := by
  have hc := highCount_eq_of_sorted_eq hsorted (v + 1)
  rw [highCount_add_subsetExponent, leadExponent,
    highCount_add_subsetExponent] at hc
  omega

theorem subsetExponent_eq_sum_single {n : Nat} (t : Finset (Fin n)) :
    subsetExponent t = ∑ x ∈ t, Finsupp.single x 1 := by
  classical
  ext x
  simp only [subsetExponent, Finsupp.indicator_apply]
  rw [Finsupp.finsetSum_apply]
  simp_rw [Finsupp.single_apply]
  by_cases hx : x ∈ t <;> simp [hx]

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
    have hle : (indexPerm a).symm x ≤ (indexPerm a).symm y := le_of_not_gt hnot
    have ha := hanti hle
    have hayx : a y ≤ a x := by simpa using ha
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

theorem exists_initial_mismatch_of_selected_mismatch {n h : Nat}
    (a : Fin n →₀ Nat) (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    {x : Fin n} (hxt : x ∈ t) (hxi : x ∉ initialSet a h) :
    ∃ y, a y = a x ∧ y ∈ initialSet a h ∧ y ∉ t := by
  classical
  let A := levelSelection a t (a x)
  let B := levelSelection a (initialSet a h) (a x)
  have hcard : A.card = B.card :=
    card_levelSelection_eq_of_sorted_eq a t hsorted (a x)
  have hxA : x ∈ A := by simp [A, levelSelection, hxt]
  have hxB : x ∉ B := by
    intro hxB
    exact hxi (by simpa [B, levelSelection] using hxB)
  have hnsub : ¬B ⊆ A := by
    intro hsub
    have heq : B = A := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hxB (heq.symm ▸ hxA)
  obtain ⟨y, hyB, hyA⟩ := Finset.not_subset.mp hnsub
  simp only [B, A, levelSelection, Finset.mem_filter, Finset.mem_univ,
    true_and] at hyB hyA
  exact ⟨y, hyB.1, hyB.2, fun hyt => hyA ⟨hyB.1, hyt⟩⟩

theorem exists_selected_mismatch_of_initial_mismatch {n h : Nat}
    (a : Fin n →₀ Nat) (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    {x : Fin n} (hxi : x ∈ initialSet a h) (hxt : x ∉ t) :
    ∃ y, a y = a x ∧ y ∈ t ∧ y ∉ initialSet a h := by
  classical
  let A := levelSelection a t (a x)
  let B := levelSelection a (initialSet a h) (a x)
  have hcard : A.card = B.card :=
    card_levelSelection_eq_of_sorted_eq a t hsorted (a x)
  have hxB : x ∈ B := by
    dsimp only [B]
    rw [levelSelection]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hxi⟩
  have hxA : x ∉ A := by simp [A, levelSelection, hxt]
  have hnsub : ¬A ⊆ B := by
    intro hsub
    have heq : A = B := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hxA (heq.symm ▸ hxB)
  obtain ⟨y, hyA, hyB⟩ := Finset.not_subset.mp hnsub
  simp only [A, B, levelSelection, Finset.mem_filter, Finset.mem_univ,
    true_and] at hyA hyB
  exact ⟨y, hyA.1, hyA.2, fun hyi => hyB ⟨hyA.1, hyi⟩⟩

theorem exists_exchange_pair_at_mismatch {n h : Nat}
    (a : Fin n →₀ Nat) (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    {x : Fin n} (hx : (x ∈ t) ≠ (x ∈ initialSet a h)) :
    ∃ p m, a p = a x ∧ a m = a x ∧
      p ∈ t ∧ p ∉ initialSet a h ∧
      m ∈ initialSet a h ∧ m ∉ t := by
  classical
  by_cases hxt : x ∈ t
  · have hxi : x ∉ initialSet a h := by
      intro hmem
      exact hx (propext ⟨fun _ => hmem, fun _ => hxt⟩)
    obtain ⟨m, hma, hmi, hmt⟩ :=
      exists_initial_mismatch_of_selected_mismatch a t hsorted hxt hxi
    exact ⟨x, m, rfl, hma, hxt, hxi, hmi, hmt⟩
  · have hxi : x ∈ initialSet a h := by
      by_contra hni
      exact hx (propext ⟨fun hmem => (hxt hmem).elim, fun hmem => (hni hmem).elim⟩)
    obtain ⟨p, hpa, hpt, hpi⟩ :=
      exists_selected_mismatch_of_initial_mismatch a t hsorted hxi hxt
    exact ⟨p, x, hpa, rfl, hpt, hpi, hxi, hxt⟩

/-- Equal sorted exponent partitions confine every non-greedy exchange to
one exponent level, the boundary block in ABR Lemma 3.2. -/
theorem exponent_eq_of_membership_mismatch {n h : Nat}
    (a : Fin n →₀ Nat) (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    {x y : Fin n}
    (hx : (x ∈ t) ≠ (x ∈ initialSet a h))
    (hy : (y ∈ t) ≠ (y ∈ initialSet a h)) : a x = a y := by
  obtain ⟨px, mx, hpx, hmx, hpxt, hpxi, hmxi, hmxt⟩ :=
    exists_exchange_pair_at_mismatch a t hsorted hx
  obtain ⟨py, my, hpy, hmy, hpyt, hpyi, hmyi, hmyt⟩ :=
    exists_exchange_pair_at_mismatch a t hsorted hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact hpyi (mem_initialSet_of_exponent_lt a h
      (hmx.trans_lt (hxy.trans_eq hpy.symm)) hmxi)
  · exact hpxi (mem_initialSet_of_exponent_lt a h
      (hmy.trans_lt (hyx.trans_eq hpx.symm)) hmyi)

theorem card_initialSet {n : Nat} (a : Fin n →₀ Nat) {h : Nat} (hh : h ≤ n) :
    (initialSet a h).card = h := by
  classical
  let e := indexPerm a
  have himage : initialSet a h =
      (Finset.univ.filter fun i : Fin n => i.val < h).image e := by
    ext x
    simp only [initialSet, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, e]
    constructor
    · intro hx
      exact ⟨(indexPerm a).symm x, hx, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [himage, Finset.card_image_of_injective _ e.injective]
  simpa [Nat.min_eq_right hh] using (Fin.card_filter_val_lt (n := n) (m := h))

theorem card_initialSet_general {n : Nat} (a : Fin n →₀ Nat) (h : Nat) :
    (initialSet a h).card = min n h := by
  classical
  let e := indexPerm a
  have himage : initialSet a h =
      (Finset.univ.filter fun i : Fin n => i.val < h).image e := by
    ext x
    simp only [initialSet, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, e]
    constructor
    · intro hx
      exact ⟨(indexPerm a).symm x, hx, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [himage, Finset.card_image_of_injective _ e.injective]
  exact Fin.card_filter_val_lt

@[simp]
theorem leadExponent_at_perm {n : Nat} (a : Fin n →₀ Nat) (h : Nat) (i : Fin n) :
    leadExponent a h (indexPerm a i) = a (indexPerm a i) + if i.val < h then 1 else 0 := by
  classical
  simp [leadExponent, subsetExponent, Finsupp.indicator_apply, initialSet]

/-- Adding to a stable initial segment preserves the stable index permutation.
This is the order-preservation assertion in ABR Lemma 3.3 for one factor. -/
theorem indexPerm_leadExponent {n : Nat} (a : Fin n →₀ Nat) (h : Nat) :
    indexPerm (leadExponent a h) = indexPerm a := by
  have hanti : Antitone (fun i => a (indexPerm a i)) :=
    fun i j hij =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hij
  have htie : ∀ {i j : Fin n}, i < j →
      a (indexPerm a i) = a (indexPerm a j) →
      indexPerm a i < indexPerm a j := by
    intro i j hij heq
    have hsort : indexPerm a =
        Tuple.sort (fun x : Fin n => OrderDual.toDual (a x)) := rfl
    exact (Tuple.eq_sort_iff.mp hsort).2 i j hij heq
  symm
  apply Tuple.eq_sort_iff.mpr
  constructor
  · intro i j hij
    change leadExponent a h (indexPerm a j) ≤
      leadExponent a h (indexPerm a i)
    rw [leadExponent_at_perm, leadExponent_at_perm]
    have ha : a (indexPerm a j) ≤ a (indexPerm a i) :=
      hanti hij
    by_cases hi : i.val < h <;> by_cases hj : j.val < h <;> simp [hi, hj] <;> omega
  · intro i j hij heq
    have ha : a (indexPerm a j) ≤ a (indexPerm a i) :=
      hanti hij.le
    change leadExponent a h (indexPerm a i) =
      leadExponent a h (indexPerm a j) at heq
    rw [leadExponent_at_perm, leadExponent_at_perm] at heq
    by_cases hi : i.val < h
    · by_cases hj : j.val < h
      · apply htie hij
        simp [hi, hj] at heq
        omega
      · simp [hi, hj] at heq
        omega
    · have hj : ¬ j.val < h := by omega
      apply htie hij
      simp [hi, hj] at heq
      omega

theorem fin_val_le_orderEmbedding {k n : Nat} (e : Fin k ↪o Fin n) (i : Fin k) :
    i.val ≤ (e i).val := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i hi =>
          simpa using! lt_of_le_of_lt hi (e.strictMono Fin.castSucc_lt_succ)

theorem prefixWeight_eq_sum_fin {n k : Nat} (a : Fin n →₀ Nat) (hk : k ≤ n) :
    prefixWeight a k =
      ∑ i : Fin k, a (indexPerm a (Fin.castLE hk i)) := by
  classical
  have hset : (Finset.univ.filter fun i : Fin n => i.val < k) =
      Finset.univ.image (Fin.castLE hk) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [prefixWeight, hset, Finset.sum_image]
  exact (Fin.castLE_injective hk).injOn

/-- The first `k` stable positions maximize the exponent sum among all
`k`-element coordinate sets. -/
theorem sum_le_prefixWeight {n : Nat} (a : Fin n →₀ Nat)
    (s : Finset (Fin n)) :
    (∑ x ∈ s, a x) ≤ prefixWeight a s.card := by
  classical
  have hanti : Antitone (fun i => a (indexPerm a i)) :=
    fun i j hij =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hij
  let pi := indexPerm a
  let positions := s.image pi.symm
  have hcard : positions.card = s.card := by
    exact Finset.card_image_of_injective s pi.symm.injective
  let e : Fin s.card ↪o Fin n := positions.orderEmbOfFin hcard
  have hrewrite : (∑ x ∈ s, a x) = ∑ j ∈ positions, a (pi j) := by
    calc
      (∑ x ∈ s, a x) = ∑ x ∈ s, a (pi (pi.symm x)) := by simp [pi]
      _ = ∑ j ∈ positions, a (pi j) := by
        symm
        simpa [positions] using
          (Finset.sum_image (s := s) (f := fun j => a (pi j)) pi.symm.injective)
  have henum : (∑ j ∈ positions, a (pi j)) =
      ∑ i : Fin s.card, a (pi (e i)) := by
    calc
      (∑ j ∈ positions, a (pi j)) =
          ∑ j : positions, a (pi j.1) :=
        (Finset.sum_attach positions (fun j => a (pi j))).symm
      _ = ∑ i : Fin s.card, a (pi (e i)) := by
        simpa [e] using
          ((positions.orderIsoOfFin hcard).toEquiv.sum_comp
            (fun j : positions => a (pi j.1))).symm
  have hsle : s.card ≤ n := by simpa using Finset.card_le_univ s
  rw [hrewrite, henum, prefixWeight_eq_sum_fin a hsle]
  apply Finset.sum_le_sum
  intro i _
  apply hanti
  exact Fin.mk_le_mk.mpr (fin_val_le_orderEmbedding e i)

theorem sum_subsetExponent_eq_card_inter {n : Nat} (s t : Finset (Fin n)) :
    (∑ x ∈ s, subsetExponent t x) = (s ∩ t).card := by
  classical
  simp [subsetExponent, Finsupp.indicator_apply, Finset.card_inter]

theorem prefixWeight_min_left {n : Nat} (a : Fin n →₀ Nat) (k : Nat) :
    prefixWeight a (min n k) = prefixWeight a k := by
  classical
  unfold prefixWeight
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem prefixWeight_eq_sum_initialSet {n : Nat} (a : Fin n →₀ Nat) (k : Nat) :
    prefixWeight a k = ∑ x ∈ initialSet a k, a x := by
  classical
  have hset : initialSet a k =
      (Finset.univ.filter fun i : Fin n => i.val < k).image (indexPerm a) := by
    ext x
    simp only [initialSet, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨(indexPerm a).symm x, hx, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [prefixWeight, hset, Finset.sum_image]
  exact (indexPerm a).injective.injOn

theorem prefixWeight_leadExponent {n : Nat} (a : Fin n →₀ Nat) (h k : Nat) :
    prefixWeight (leadExponent a h) k =
      prefixWeight a k + min (min n k) h := by
  classical
  unfold prefixWeight
  rw [indexPerm_leadExponent]
  simp_rw [leadExponent_at_perm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show min (min n k) h = min n (min k h) by omega,
    ← Fin.card_filter_val_lt]
  rw [← Finset.card_filter]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- Every squarefree summand in the one-factor expansion is dominated by the
stable initial-segment leader. -/
theorem oneFactor_dominatedBy {n h : Nat} (a : Fin n →₀ Nat)
    (t : Finset (Fin n)) (ht : t.card = h) :
    DominatedBy (a + subsetExponent t) (leadExponent a h) := by
  classical
  constructor
  · have hh : h ≤ n := by
      rw [← ht]
      simpa using Finset.card_le_univ t
    change (Finset.univ.sum fun x : Fin n =>
        a x + subsetExponent t x) =
      (Finset.univ.sum fun x : Fin n =>
        a x + subsetExponent (initialSet a h) x)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_subsetExponent_eq_card_inter, sum_subsetExponent_eq_card_inter]
    simp [ht, card_initialSet a hh]
  · intro k
    let s := initialSet (a + subsetExponent t) k
    have hscard : s.card = min n k := card_initialSet_general _ _
    have ha : (∑ x ∈ s, a x) ≤ prefixWeight a s.card :=
      sum_le_prefixWeight a s
    have hinter : (s ∩ t).card ≤ min s.card t.card := by
      exact le_min
        (Finset.card_le_card Finset.inter_subset_left)
        (Finset.card_le_card Finset.inter_subset_right)
    rw [prefixWeight_eq_sum_initialSet, prefixWeight_leadExponent]
    change (s.sum fun i => a i + subsetExponent t i) ≤ _
    rw [Finset.sum_add_distrib, sum_subsetExponent_eq_card_inter]
    rw [ht, hscard] at hinter
    rw [hscard, prefixWeight_min_left] at ha
    omega

/-- If a squarefree summand has the leader's sorted exponent partition but
uses a different subset, its stable index permutation has strictly more
inversions.  This is the equal-partition clause of ABR Lemma 3.2. -/
theorem inversionCount_indexPerm_lt_of_sorted_eq {n h : Nat}
    (a : Fin n →₀ Nat) (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    (hne : t ≠ initialSet a h) :
    inversionCount (indexPerm (leadExponent a h)) <
      inversionCount (indexPerm (a + subsetExponent t)) := by
  classical
  rw [inversionCount_indexPerm, inversionCount_indexPerm]
  let leaderPairs := (Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ leadExponent a h p.1 < leadExponent a h p.2)
  let termPairs := (Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (a + subsetExponent t) p.1 < (a + subsetExponent t) p.2)
  change leaderPairs.card < termPairs.card
  have hbase {x y : Fin n} (hxy : x < y)
      (hlt : leadExponent a h x < leadExponent a h y) : a x < a y := by
    by_contra hnot
    have hayx : a y ≤ a x := le_of_not_gt hnot
    by_cases heq : a x = a y
    · by_cases hxi : x ∈ initialSet a h
      · by_cases hyi : y ∈ initialSet a h <;>
          simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hxi, hyi, heq] at hlt
      · have hyi : y ∉ initialSet a h := by
          intro hyi
          exact hxi (mem_initialSet_of_tie_lt a h hxy heq hyi)
        simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hxi, hyi, heq] at hlt
    · have hayx' : a y < a x := lt_of_le_of_ne hayx (Ne.symm heq)
      by_cases hxi : x ∈ initialSet a h <;>
        by_cases hyi : y ∈ initialSet a h <;>
          simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hxi, hyi] at hlt <;> omega
  have hsubset : leaderPairs ⊆ termPairs := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hpuniv, hxy, hleader⟩
    refine ⟨hpuniv, hxy, ?_⟩
    have hab : a p.1 < a p.2 := hbase hxy hleader
    by_cases hxt : p.1 ∈ t
    · by_cases hyt : p.2 ∈ t
      · simp [subsetExponent, Finsupp.indicator_apply, hxt, hyt]
        exact hab
      · simp [subsetExponent, Finsupp.indicator_apply, hxt, hyt]
        by_contra hnot
        have hsucc : a p.2 = a p.1 + 1 := by omega
        by_cases hxi : p.1 ∈ initialSet a h
        · have hyi : p.2 ∈ initialSet a h :=
            mem_initialSet_of_exponent_lt a h hab hxi
          obtain ⟨q, hqa, hqt, hqi⟩ :=
            exists_selected_mismatch_of_initial_mismatch a t hsorted hyi hyt
          exact hqi (mem_initialSet_of_exponent_lt a h
            (hab.trans_eq hqa.symm) hxi)
        · have hxmis : (p.1 ∈ t) ≠ (p.1 ∈ initialSet a h) := by
            simp [hxt, hxi]
          obtain ⟨q, hqa, hqi, hqt⟩ :=
            exists_initial_mismatch_of_selected_mismatch a t hsorted hxt hxi
          have hyi : p.2 ∈ initialSet a h :=
            mem_initialSet_of_exponent_lt a h (hqa.trans_lt hab) hqi
          have hymis : (p.2 ∈ t) ≠ (p.2 ∈ initialSet a h) := by
            simp [hyt, hyi]
          have heq := exponent_eq_of_membership_mismatch a t hsorted hxmis hymis
          omega
    · by_cases hyt : p.2 ∈ t <;>
        simp [subsetExponent, Finsupp.indicator_apply, hxt, hyt] <;> omega
  have hmismatch : ∃ x : Fin n,
      ¬ (x ∈ t ↔ x ∈ initialSet a h) := by
    by_contra hnone
    push_neg at hnone
    apply hne
    ext x
    exact hnone x
  obtain ⟨x, hx⟩ := hmismatch
  have hxne : (x ∈ t) ≠ (x ∈ initialSet a h) := by
    intro heq
    apply hx
    rw [heq]
  obtain ⟨p, m, hpa, hma, hpt, hpi, hmi, hmt⟩ :=
    exists_exchange_pair_at_mismatch a t hsorted hxne
  have hmp : m < p := by
    by_contra hnot
    have hnepm : p ≠ m := by
      intro heq
      exact hmt (heq ▸ hpt)
    have hpm : p < m := lt_of_le_of_ne (le_of_not_gt hnot) hnepm
    exact hpi (mem_initialSet_of_tie_lt a h hpm (hpa.trans hma.symm) hmi)
  have hwitnessTerm : (m, p) ∈ termPairs := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      hmp, ?_⟩
    simp [subsetExponent, Finsupp.indicator_apply, hpt, hmt, hpa, hma]
  have hwitnessLeader : (m, p) ∉ leaderPairs := by
    rw [Finset.mem_filter]
    simp only [Finset.mem_product, Finset.mem_univ, and_self, not_and]
    intro _
    simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hpi, hmi, hpa, hma]
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset hsubset).mpr
      ⟨(m, p), hwitnessTerm, hwitnessLeader⟩)

/-- Every nonleader squarefree summand is strictly below the stable leader in
the ABR dominance/reverse-inversion order. -/
theorem oneFactor_abrLower {n h : Nat} (a : Fin n →₀ Nat)
    (t : Finset (Fin n)) (ht : t.card = h)
    (hne : t ≠ initialSet a h) :
    AbrLower (a + subsetExponent t) (leadExponent a h) := by
  have hprefixStep (u : Fin n →₀ Nat) (i : Fin n) :
      prefixWeight u (i.val + 1) =
        prefixWeight u i.val + u (indexPerm u i) := by
    have hsucc : i.val + 1 ≤ n := i.isLt
    have hval : i.val ≤ n := le_trans (Nat.le_succ _) hsucc
    rw [prefixWeight_eq_sum_fin u hsucc, prefixWeight_eq_sum_fin u hval,
      Fin.sum_univ_castSucc]
    congr
  have hdom := oneFactor_dominatedBy a t ht
  by_cases hreverse : DominatedBy (leadExponent a h) (a + subsetExponent t)
  · right
    have hsorted :
        (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
          fun i => leadExponent a h (indexPerm (leadExponent a h) i) := by
      funext i
      have hprefix :
          prefixWeight (a + subsetExponent t) i.val =
            prefixWeight (leadExponent a h) i.val :=
        le_antisymm (hdom.2 i.val) (hreverse.2 i.val)
      have hprefixSucc :
          prefixWeight (a + subsetExponent t) (i.val + 1) =
            prefixWeight (leadExponent a h) (i.val + 1) :=
        le_antisymm (hdom.2 (i.val + 1)) (hreverse.2 (i.val + 1))
      rw [hprefixStep, hprefixStep, hprefix] at hprefixSucc
      omega
    exact ⟨hsorted, inversionCount_indexPerm_lt_of_sorted_eq a t hsorted hne⟩
  · exact Or.inl ⟨hdom, hreverse⟩

/-- The all-height ABR leader occurs in the one-factor expansion. -/
theorem initialSet_mem_powersetCard {n h : Nat} (a : Fin n →₀ Nat) (hh : h ≤ n) :
    initialSet a h ∈ Finset.univ.powersetCard h := by
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, card_initialSet a hh⟩

end D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
