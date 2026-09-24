/- GID: D5/S3/Combinatorics/Interpolation/AbrResidualPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrResidualPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: ABR residual exponents form the partition that reconstructs each monomial. -/

import D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening

/-!
This module formalizes Claim 3.1 of Adin--Brenti--Roichman: after subtracting
the descent exponents in stable decreasing-exponent order, the residual is a
nonnegative weakly decreasing partition.  Its column heights are the
elementary-symmetric factors used by the straightening iteration.

Source: R. M. Adin, F. Brenti, Y. Roichman, Trans. Amer. Math. Soc. 357
(2005), DOI 10.1090/S0002-9947-04-03494-4, Claim 3.1 and Lemma 3.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrResidualPartition

open scoped BigOperators
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening

theorem suffixHeight_antitone {n : Nat} (pi : Equiv.Perm (Fin n)) :
    Antitone (suffixHeight pi) := by
  intro i j hij
  unfold suffixHeight
  apply Finset.sum_le_sum
  intro k _
  by_cases hjk : j <= k
  · simp [hjk, hij.trans hjk]
  · simp [hjk]

theorem descentAt_indexPerm_eq_one_implies {n : Nat} (a : Fin n →₀ Nat)
    (i : Fin n) (hi : descentAt (indexPerm a) i = 1) :
    ∃ hnext : i.val + 1 < n,
      a (indexPerm a ⟨i.val + 1, hnext⟩) < a (indexPerm a i) := by
  have hanti : Antitone (fun j => a (indexPerm a j)) :=
    fun j k hjk =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hjk
  unfold descentAt at hi
  split at hi
  next hnext =>
    split at hi
    next hdescent =>
      refine ⟨hnext, ?_⟩
      have hpos : i ≤ (⟨i.val + 1, hnext⟩ : Fin n) :=
        Fin.mk_le_mk.mpr (Nat.le_succ _)
      have hposStrict : i < (⟨i.val + 1, hnext⟩ : Fin n) :=
        Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)
      have hle := hanti hpos
      have hsort : indexPerm a =
          Tuple.sort (fun x : Fin n => OrderDual.toDual (a x)) := rfl
      exact lt_of_le_of_ne hle fun heq =>
        ((Tuple.eq_sort_iff.mp hsort).2 _ _ hposStrict heq.symm).not_gt hdescent
    next _ => omega
  next _ => omega

theorem suffixHeight_indexPerm_le_exponent {n : Nat} (a : Fin n →₀ Nat)
    (i : Fin n) : suffixHeight (indexPerm a) i ≤ a (indexPerm a i) := by
  classical
  have suffixSplit (pi : Equiv.Perm (Fin n)) (j : Fin n)
      (hj : j.val + 1 < n) :
      suffixHeight pi j = descentAt pi j + suffixHeight pi ⟨j.val + 1, hj⟩ := by
    unfold suffixHeight
    calc
      (Finset.univ.sum fun k : Fin n => if j ≤ k then descentAt pi k else 0) =
          Finset.univ.sum fun k : Fin n =>
            (if k = j then descentAt pi j else 0) +
              (if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          have hnle : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ j := by
            intro hle
            have hval := Fin.mk_le_mk.mp hle
            omega
          simp [hnle]
        · by_cases hjk : j ≤ k
          · have hsucc : (⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              apply Fin.mk_le_mk.mpr
              have hjk' := Fin.mk_le_mk.mp hjk
              have hval : j.val ≠ k.val := fun h => hkj (Fin.ext h.symm)
              omega
            simp [hkj, hjk, hsucc]
          · have hsucc : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              intro h
              exact hjk (le_trans (Fin.mk_le_mk.mpr (Nat.le_succ _)) h)
            simp [hkj, hjk, hsucc]
      _ = (Finset.univ.sum fun k : Fin n => if k = j then descentAt pi j else 0) +
          Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        rw [Finset.sum_add_distrib]
      _ = descentAt pi j + Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        simp
  have hanti : Antitone (fun j => a (indexPerm a j)) :=
    fun j k hjk =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hjk
  by_cases hnext : i.val + 1 < n
  · have ih := suffixHeight_indexPerm_le_exponent a ⟨i.val + 1, hnext⟩
    rw [suffixSplit (indexPerm a) i hnext]
    by_cases hd : descentAt (indexPerm a) i = 0
    · rw [hd, zero_add]
      exact ih.trans (hanti (Fin.mk_le_mk.mpr (Nat.le_succ _)))
    · have hdle : descentAt (indexPerm a) i ≤ 1 := by
        unfold descentAt
        split <;> split <;> simp
      have hdone : descentAt (indexPerm a) i = 1 := by omega
      obtain ⟨hnext', hstrict⟩ := descentAt_indexPerm_eq_one_implies a i hdone
      have ih' := suffixHeight_indexPerm_le_exponent a ⟨i.val + 1, hnext'⟩
      have hsuffixEq : suffixHeight (indexPerm a) ⟨i.val + 1, hnext⟩ =
          suffixHeight (indexPerm a) ⟨i.val + 1, hnext'⟩ := by
        congr
      rw [hdone]
      rw [hsuffixEq]
      omega
  · have hilast : ∀ j : Fin n, i ≤ j → j = i := by
      intro j hij
      apply Fin.ext
      simp only [Fin.le_iff_val_le_val] at hij
      have hj := j.isLt
      omega
    unfold suffixHeight
    have hzero : (Finset.univ.sum fun j : Fin n =>
        if i ≤ j then descentAt (indexPerm a) j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hij : i ≤ j
      · have hji : j = i := hilast j hij
        subst j
        unfold descentAt
        simp [hnext]
      · simp [hij]
    rw [hzero]
    exact Nat.zero_le _
termination_by n - i.val
decreasing_by
  all_goals omega

/-- ABR Claim 3.1: the residual exponents are weakly decreasing in stable
index order. -/
theorem residual_antitone {n : Nat} (a : Fin n →₀ Nat) :
    Antitone (residual a) := by
  classical
  have suffixSplit (pi : Equiv.Perm (Fin n)) (j : Fin n)
      (hj : j.val + 1 < n) :
      suffixHeight pi j = descentAt pi j + suffixHeight pi ⟨j.val + 1, hj⟩ := by
    unfold suffixHeight
    calc
      (Finset.univ.sum fun k : Fin n => if j ≤ k then descentAt pi k else 0) =
          Finset.univ.sum fun k : Fin n =>
            (if k = j then descentAt pi j else 0) +
              (if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          have hnle : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ j := by
            intro hle
            have hval := Fin.mk_le_mk.mp hle
            omega
          simp [hnle]
        · by_cases hjk : j ≤ k
          · have hsucc : (⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              apply Fin.mk_le_mk.mpr
              have hjk' := Fin.mk_le_mk.mp hjk
              have hval : j.val ≠ k.val := fun h => hkj (Fin.ext h.symm)
              omega
            simp [hkj, hjk, hsucc]
          · have hsucc : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              intro h
              exact hjk (le_trans (Fin.mk_le_mk.mpr (Nat.le_succ _)) h)
            simp [hkj, hjk, hsucc]
      _ = (Finset.univ.sum fun k : Fin n => if k = j then descentAt pi j else 0) +
          Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        rw [Finset.sum_add_distrib]
      _ = descentAt pi j + Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        simp
  cases n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n =>
      have hanti : Antitone (fun j => a (indexPerm a j)) :=
        fun j k hjk =>
          Tuple.monotone_sort
            (fun x : Fin (n + 1) => OrderDual.toDual (a x)) hjk
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      have hnext : i.castSucc.val + 1 < n + 1 := by
        rw [Fin.val_castSucc]
        omega
      have hright : (⟨i.castSucc.val + 1, hnext⟩ : Fin (n + 1)) = i.succ :=
        Fin.ext rfl
      have hsuffix := suffixSplit (indexPerm a) i.castSucc hnext
      rw [hright] at hsuffix
      have hrightBound := suffixHeight_indexPerm_le_exponent a i.succ
      have hcast : i.castSucc ≤ i.succ :=
        Fin.mk_le_mk.mpr (Nat.le_succ _)
      have hleftOrder := hanti hcast
      by_cases hd : descentAt (indexPerm a) i.castSucc = 0
      · rw [hd, zero_add] at hsuffix
        unfold AbrCoordinateBoxStraightening.residual
        rw [hsuffix]
        exact Nat.sub_le_sub_right hleftOrder _
      · have hdle : descentAt (indexPerm a) i.castSucc ≤ 1 := by
          unfold descentAt
          split <;> split <;> simp
        have hdone : descentAt (indexPerm a) i.castSucc = 1 := by omega
        obtain ⟨hnext', hstrict⟩ :=
          descentAt_indexPerm_eq_one_implies a i.castSucc hdone
        have hsame : (⟨i.castSucc.val + 1, hnext'⟩ : Fin (n + 1)) = i.succ :=
          Fin.ext rfl
        rw [hsame] at hstrict
        unfold AbrCoordinateBoxStraightening.residual
        omega

/-- The height of residual Ferrers column `k`. -/
def columnHeight {n : Nat} (a : Fin n →₀ Nat) (k : Nat) : Nat :=
  (Finset.univ.filter fun i : Fin n => k < residual a i).card

/-- The largest coordinate exponent. -/
def maxExponent {n : Nat} (a : Fin n →₀ Nat) : Nat :=
  Finset.univ.sup a

/-- The number of nonempty columns of the residual partition. -/
def residualDepth {n : Nat} (a : Fin n →₀ Nat) : Nat :=
  Finset.univ.sup (residual a)

/-- Starting with the descent exponent, add the residual Ferrers columns in
order. -/
def greedyExponent {n : Nat} (a : Fin n →₀ Nat) : Nat → Fin n →₀ Nat
  | 0 => descentExponent (indexPerm a)
  | k + 1 => leadExponent (greedyExponent a k) (columnHeight a k)

/-- An antitone residual partition has each column supported on an initial
segment of stable positions. -/
theorem lt_columnHeight_iff {n : Nat} (a : Fin n →₀ Nat) (k : Nat)
    (i : Fin n) : i.val < columnHeight a k ↔ k < residual a i := by
  classical
  let s := Finset.univ.filter fun j : Fin n => k < residual a j
  have hs : s = Finset.univ.filter fun j : Fin n => k < residual a j := rfl
  constructor
  · intro hi
    by_contra hki
    have hsubset : s ⊆ Finset.Iio i := by
      intro j hj
      rw [hs, Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hnot
      have hij : i ≤ j := le_of_not_gt hnot
      have hres := residual_antitone a hij
      omega
    have hcard := Finset.card_le_card hsubset
    have hIio : (Finset.Iio i).card = i.val := by simp
    change i.val < s.card at hi
    omega
  · intro hki
    have hsubset : Finset.Iic i ⊆ s := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      rw [hs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le hki (residual_antitone a hj)⟩
    have hcard := Finset.card_le_card hsubset
    have hIic : (Finset.Iic i).card = i.val + 1 := by simp
    change i.val < s.card
    omega

theorem perm_lt_of_lt_of_suffixHeight_eq {n : Nat} (pi : Equiv.Perm (Fin n))
    (i j : Fin n) (hij : i < j)
    (heq : suffixHeight pi i = suffixHeight pi j) : pi i < pi j := by
  classical
  have suffixSplit (rho : Equiv.Perm (Fin n)) (k : Fin n)
      (hk : k.val + 1 < n) :
      suffixHeight rho k = descentAt rho k + suffixHeight rho ⟨k.val + 1, hk⟩ := by
    unfold suffixHeight
    calc
      (Finset.univ.sum fun l : Fin n => if k ≤ l then descentAt rho l else 0) =
          Finset.univ.sum fun l : Fin n =>
            (if l = k then descentAt rho k else 0) +
              (if (⟨k.val + 1, hk⟩ : Fin n) ≤ l then descentAt rho l else 0) := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases hlk : l = k
        · subst l
          have hnle : ¬(⟨k.val + 1, hk⟩ : Fin n) ≤ k := by
            intro hle
            have hval := Fin.mk_le_mk.mp hle
            omega
          simp [hnle]
        · by_cases hkl : k ≤ l
          · have hsucc : (⟨k.val + 1, hk⟩ : Fin n) ≤ l := by
              apply Fin.mk_le_mk.mpr
              have hkl' := Fin.mk_le_mk.mp hkl
              have hval : k.val ≠ l.val := fun h => hlk (Fin.ext h.symm)
              omega
            simp [hlk, hkl, hsucc]
          · have hsucc : ¬(⟨k.val + 1, hk⟩ : Fin n) ≤ l := by
              intro h
              exact hkl (le_trans (Fin.mk_le_mk.mpr (Nat.le_succ _)) h)
            simp [hlk, hkl, hsucc]
      _ = (Finset.univ.sum fun l : Fin n => if l = k then descentAt rho k else 0) +
          Finset.univ.sum fun l : Fin n =>
            if (⟨k.val + 1, hk⟩ : Fin n) ≤ l then descentAt rho l else 0 := by
        rw [Finset.sum_add_distrib]
      _ = descentAt rho k + Finset.univ.sum fun l : Fin n =>
            if (⟨k.val + 1, hk⟩ : Fin n) ≤ l then descentAt rho l else 0 := by
        simp
  have hnext : i.val + 1 < n := by
    have hj := j.isLt
    have hij' := Fin.mk_lt_mk.mp hij
    omega
  let next : Fin n := ⟨i.val + 1, hnext⟩
  have hinext : i < next := Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)
  have hnextj : next ≤ j := Fin.mk_le_mk.mpr (by
    have := Fin.mk_lt_mk.mp hij
    omega)
  have hsplit := suffixSplit pi i hnext
  have htail := suffixHeight_antitone pi hnextj
  change suffixHeight pi j ≤ suffixHeight pi ⟨i.val + 1, hnext⟩ at htail
  have hdescent : descentAt pi i = 0 := by omega
  have hnextEq : suffixHeight pi next = suffixHeight pi j := by
    change suffixHeight pi ⟨i.val + 1, hnext⟩ = suffixHeight pi j
    omega
  have hadj : pi i < pi next := by
    by_contra hnot
    have hne : pi next ≠ pi i := fun h =>
      hinext.ne' (pi.injective h)
    have hrev : pi next < pi i := lt_of_le_of_ne (le_of_not_gt hnot) hne
    unfold descentAt at hdescent
    simp [hnext, next, hrev] at hdescent
  by_cases hnj : next = j
  · simpa [hnj] using hadj
  · exact hadj.trans (perm_lt_of_lt_of_suffixHeight_eq pi next j
      (lt_of_le_of_ne hnextj hnj) hnextEq)
termination_by j.val - i.val
decreasing_by
  omega

/-- The descent exponent of a stable sorting permutation has that same stable
index permutation. -/
theorem indexPerm_descentExponent {n : Nat} (a : Fin n →₀ Nat) :
    indexPerm (descentExponent (indexPerm a)) = indexPerm a := by
  let pi := indexPerm a
  change Tuple.sort (fun i => OrderDual.toDual (descentExponent pi i)) = pi
  symm
  apply Tuple.eq_sort_iff.mpr
  constructor
  · intro i j hij
    change descentExponent pi (pi j) ≤ descentExponent pi (pi i)
    simpa [descentExponent] using suffixHeight_antitone pi hij
  · intro i j hij heq
    change OrderDual.toDual (descentExponent pi (pi i)) =
      OrderDual.toDual (descentExponent pi (pi j)) at heq
    have heq' : suffixHeight pi i = suffixHeight pi j := by
      simpa [descentExponent] using heq
    exact perm_lt_of_lt_of_suffixHeight_eq pi i j hij heq'

theorem indexPerm_greedyExponent {n : Nat} (a : Fin n →₀ Nat) (k : Nat) :
    indexPerm (greedyExponent a k) = indexPerm a := by
  induction k with
  | zero => exact indexPerm_descentExponent a
  | succ k ih =>
      rw [greedyExponent, indexPerm_leadExponent, ih]

/-- After `k` greedy columns, each stable coordinate contains its descent
height plus the first `k` cells of its residual row. -/
theorem greedyExponent_at_perm {n : Nat} (a : Fin n →₀ Nat) (k : Nat)
    (i : Fin n) :
    greedyExponent a k (indexPerm a i) =
      suffixHeight (indexPerm a) i + min k (residual a i) := by
  induction k with
  | zero => simp [greedyExponent, descentExponent]
  | succ k ih =>
      rw [greedyExponent]
      conv_lhs => rw [← indexPerm_greedyExponent a k]
      simp only [leadExponent, Finsupp.add_apply, subsetExponent,
        Finsupp.indicator_apply, initialSet, Finset.mem_filter, Finset.mem_univ,
        Equiv.symm_apply_apply, true_and]
      rw [indexPerm_greedyExponent, ih]
      by_cases hk : k < residual a i
      · rw [dif_pos ((lt_columnHeight_iff a k i).mpr hk)]
        omega
      · rw [dif_neg ((lt_columnHeight_iff a k i).not.mpr hk)]
        omega

theorem columnHeight_pos_of_lt_residualDepth {n : Nat} (a : Fin n →₀ Nat)
    {k : Nat} (hk : k < residualDepth a) : 0 < columnHeight a k := by
  by_contra hzero
  have hcard : columnHeight a k = 0 := Nat.eq_zero_of_not_pos hzero
  have hempty : (Finset.univ.filter fun i : Fin n => k < residual a i) = ∅ := by
    exact Finset.card_eq_zero.mp hcard
  have hdepth : residualDepth a ≤ k := by
    unfold residualDepth
    apply Finset.sup_le
    intro i _
    by_contra hi
    have himem : i ∈ Finset.univ.filter fun j : Fin n => k < residual a j := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by omega⟩
    rw [hempty] at himem
    exact Finset.notMem_empty i himem
  omega

/-- All residual columns reconstruct the original exponent vector. -/
theorem greedyExponent_residualDepth {n : Nat} (a : Fin n →₀ Nat) :
    greedyExponent a (residualDepth a) = a := by
  apply Finsupp.ext
  intro x
  let i := (indexPerm a).symm x
  have hbound := suffixHeight_indexPerm_le_exponent a i
  have hres : residual a i ≤ residualDepth a :=
    Finset.le_sup (Finset.mem_univ i)
  rw [← (indexPerm a).apply_symm_apply x]
  rw [greedyExponent_at_perm]
  rw [min_eq_right hres]
  unfold AbrCoordinateBoxStraightening.residual
  exact Nat.add_sub_of_le hbound

theorem maxExponent_eq_at_zero {n : Nat} (hn : 0 < n) (a : Fin n →₀ Nat) :
    maxExponent a = a (indexPerm a ⟨0, hn⟩) := by
  have hanti : Antitone (fun i => a (indexPerm a i)) :=
    fun i j hij =>
      Tuple.monotone_sort (fun y : Fin n => OrderDual.toDual (a y)) hij
  apply le_antisymm
  · unfold maxExponent
    apply Finset.sup_le
    intro x _
    have hx : (⟨0, hn⟩ : Fin n) ≤ (indexPerm a).symm x :=
      Fin.mk_le_mk.mpr (Nat.zero_le _)
    simpa using hanti hx
  · unfold maxExponent
    exact Finset.le_sup (Finset.mem_univ _)

/-- ABR's complement factor count: the number of residual columns is the
largest coordinate exponent minus the number of descents. -/
theorem residualDepth_eq_maxExponent_sub_descents {n : Nat} (hn : 0 < n)
    (a : Fin n →₀ Nat) :
    residualDepth a = maxExponent a - descents (indexPerm a) := by
  have hdepth : residualDepth a = residual a ⟨0, hn⟩ := by
    apply le_antisymm
    · unfold residualDepth
      apply Finset.sup_le
      intro i _
      exact residual_antitone a (Fin.mk_le_mk.mpr (Nat.zero_le _))
    · unfold residualDepth
      exact Finset.le_sup (Finset.mem_univ _)
  rw [hdepth, maxExponent_eq_at_zero hn]
  unfold AbrCoordinateBoxStraightening.residual
  have hzero : suffixHeight (indexPerm a) ⟨0, hn⟩ = descents (indexPerm a) := by
    unfold suffixHeight descents
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos]
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  rw [hzero]

#print axioms residual_antitone
#print axioms greedyExponent_residualDepth
#print axioms residualDepth_eq_maxExponent_sub_descents

end D5.S3.Combinatorics.Interpolation.AbrResidualPartition
