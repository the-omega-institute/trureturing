/- GID: D5/S3/Combinatorics/Interpolation/AbrCoordinateExchange
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrCoordinateExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable boundary exchanges for one-factor ABR straightening. -/

import D5.S3.Combinatorics.Interpolation.AbrCoordinateFoundations

/-!
Equal sorted exponent partitions differ only by exchanges inside one stable
boundary block.  This module also proves that adding the stable initial segment
preserves the index permutation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening

open scoped BigOperators
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization

theorem exists_initial_mismatch_of_selected_mismatch {n h : Nat}
    (a : Fin n →₀ Nat) (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    {x : Fin n} (hxt : x ∈ t) (hxi : x ∉ initialSet a h) :
    ∃ y, a y = a x ∧ y ∈ initialSet a h ∧ y ∉ t := by
  classical
  have hhighCountAdd (u : Fin n →₀ Nat) (s : Finset (Fin n)) (v : Nat) :
      highCount (u + subsetExponent s) (v + 1) =
        highCount u (v + 1) + (levelSelection u s v).card := by
    unfold highCount levelSelection
    rw [show (Finset.univ.filter fun z : Fin n =>
          v + 1 ≤ (u + subsetExponent s) z).card =
        ∑ z, if v + 1 ≤ (u + subsetExponent s) z then 1 else 0 by simp]
    rw [show (Finset.univ.filter fun z : Fin n => v + 1 ≤ u z).card =
        ∑ z, if v + 1 ≤ u z then 1 else 0 by simp]
    rw [show (Finset.univ.filter fun z : Fin n => u z = v ∧ z ∈ s).card =
        ∑ z, if u z = v ∧ z ∈ s then 1 else 0 by simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    simp only [Finsupp.add_apply, subsetExponent, Finsupp.indicator_apply]
    by_cases hz : z ∈ s
    · rcases lt_trichotomy (u z) v with huv | huv | huv
      · have hle : ¬v ≤ u z := by omega
        have hsucc : ¬v + 1 ≤ u z + 1 := by omega
        have hlt : ¬v < u z := by omega
        have hne : u z ≠ v := by omega
        simp [hz, hle, hsucc, hlt, hne]
      · subst v
        simp [hz]
      · have hle : v ≤ u z := huv.le
        have hsucc : v + 1 ≤ u z := huv
        have hne : u z ≠ v := huv.ne'
        simp [hz, hle, hsucc, hne]
    · simp [hz]
  have hhighCountEq {u v : Fin n →₀ Nat}
      (hsorted' : (fun i => u (indexPerm u i)) = fun i => v (indexPerm v i))
      (w : Nat) : highCount u w = highCount v w := by
    unfold highCount
    rw [show (Finset.univ.filter fun z : Fin n => w ≤ u z).card =
        ∑ z, if w ≤ u z then 1 else 0 by simp]
    rw [show (Finset.univ.filter fun z : Fin n => w ≤ v z).card =
        ∑ z, if w ≤ v z then 1 else 0 by simp]
    calc
      (∑ z, if w ≤ u z then 1 else 0) =
          ∑ i, if w ≤ u (indexPerm u i) then 1 else 0 := by
            symm
            exact Fintype.sum_equiv (indexPerm u)
              (fun i => if w ≤ u (indexPerm u i) then 1 else 0)
              (fun z => if w ≤ u z then 1 else 0) (fun _ => rfl)
      _ = ∑ i, if w ≤ v (indexPerm v i) then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [congrFun hsorted' i]
      _ = ∑ z, if w ≤ v z then 1 else 0 := by
            exact Fintype.sum_equiv (indexPerm v)
              (fun i => if w ≤ v (indexPerm v i) then 1 else 0)
              (fun z => if w ≤ v z then 1 else 0) (fun _ => rfl)
  let A := levelSelection a t (a x)
  let B := levelSelection a (initialSet a h) (a x)
  have hc := hhighCountEq hsorted (a x + 1)
  rw [hhighCountAdd, leadExponent, hhighCountAdd] at hc
  have hcard : A.card = B.card := by simpa [A, B] using (show
    (levelSelection a t (a x)).card =
      (levelSelection a (initialSet a h) (a x)).card by omega)
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
  have hhighCountAdd (u : Fin n →₀ Nat) (s : Finset (Fin n)) (v : Nat) :
      highCount (u + subsetExponent s) (v + 1) =
        highCount u (v + 1) + (levelSelection u s v).card := by
    unfold highCount levelSelection
    rw [show (Finset.univ.filter fun z : Fin n =>
          v + 1 ≤ (u + subsetExponent s) z).card =
        ∑ z, if v + 1 ≤ (u + subsetExponent s) z then 1 else 0 by simp]
    rw [show (Finset.univ.filter fun z : Fin n => v + 1 ≤ u z).card =
        ∑ z, if v + 1 ≤ u z then 1 else 0 by simp]
    rw [show (Finset.univ.filter fun z : Fin n => u z = v ∧ z ∈ s).card =
        ∑ z, if u z = v ∧ z ∈ s then 1 else 0 by simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    simp only [Finsupp.add_apply, subsetExponent, Finsupp.indicator_apply]
    by_cases hz : z ∈ s
    · rcases lt_trichotomy (u z) v with huv | huv | huv
      · have hle : ¬v ≤ u z := by omega
        have hsucc : ¬v + 1 ≤ u z + 1 := by omega
        have hlt : ¬v < u z := by omega
        have hne : u z ≠ v := by omega
        simp [hz, hle, hsucc, hlt, hne]
      · subst v
        simp [hz]
      · have hle : v ≤ u z := huv.le
        have hsucc : v + 1 ≤ u z := huv
        have hne : u z ≠ v := huv.ne'
        simp [hz, hle, hsucc, hne]
    · simp [hz]
  have hhighCountEq {u v : Fin n →₀ Nat}
      (hsorted' : (fun i => u (indexPerm u i)) = fun i => v (indexPerm v i))
      (w : Nat) : highCount u w = highCount v w := by
    unfold highCount
    rw [show (Finset.univ.filter fun z : Fin n => w ≤ u z).card =
        ∑ z, if w ≤ u z then 1 else 0 by simp]
    rw [show (Finset.univ.filter fun z : Fin n => w ≤ v z).card =
        ∑ z, if w ≤ v z then 1 else 0 by simp]
    calc
      (∑ z, if w ≤ u z then 1 else 0) =
          ∑ i, if w ≤ u (indexPerm u i) then 1 else 0 := by
            symm
            exact Fintype.sum_equiv (indexPerm u)
              (fun i => if w ≤ u (indexPerm u i) then 1 else 0)
              (fun z => if w ≤ u z then 1 else 0) (fun _ => rfl)
      _ = ∑ i, if w ≤ v (indexPerm v i) then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [congrFun hsorted' i]
      _ = ∑ z, if w ≤ v z then 1 else 0 := by
            exact Fintype.sum_equiv (indexPerm v)
              (fun i => if w ≤ v (indexPerm v i) then 1 else 0)
              (fun z => if w ≤ v z then 1 else 0) (fun _ => rfl)
  let A := levelSelection a t (a x)
  let B := levelSelection a (initialSet a h) (a x)
  have hc := hhighCountEq hsorted (a x + 1)
  rw [hhighCountAdd, leadExponent, hhighCountAdd] at hc
  have hcard : A.card = B.card := by simpa [A, B] using (show
    (levelSelection a t (a x)).card =
      (levelSelection a (initialSet a h) (a x)).card by omega)
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
  classical
  have exchange (z : Fin n) (hz : (z ∈ t) ≠ (z ∈ initialSet a h)) :
      ∃ p m, a p = a z ∧ a m = a z ∧
        p ∈ t ∧ p ∉ initialSet a h ∧
        m ∈ initialSet a h ∧ m ∉ t := by
    by_cases hzt : z ∈ t
    · have hzi : z ∉ initialSet a h := by
        intro hmem
        exact hz (propext ⟨fun _ => hmem, fun _ => hzt⟩)
      obtain ⟨m, hma, hmi, hmt⟩ :=
        exists_initial_mismatch_of_selected_mismatch a t hsorted hzt hzi
      exact ⟨z, m, rfl, hma, hzt, hzi, hmi, hmt⟩
    · have hzi : z ∈ initialSet a h := by
        by_contra hni
        exact hz (propext ⟨fun hmem => (hzt hmem).elim,
          fun hmem => (hni hmem).elim⟩)
      obtain ⟨p, hpa, hpt, hpi⟩ :=
        exists_selected_mismatch_of_initial_mismatch a t hsorted hzi hzt
      exact ⟨p, z, hpa, rfl, hpt, hpi, hzi, hzt⟩
  obtain ⟨px, mx, hpx, hmx, _hpxt, hpxi, hmxi, _hmxt⟩ := exchange x hx
  obtain ⟨py, my, hpy, hmy, _hpyt, hpyi, hmyi, _hmyt⟩ := exchange y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact hpyi (mem_initialSet_of_exponent_lt a h
      (hmx.trans_lt (hxy.trans_eq hpy.symm)) hmxi)
  · exact hpxi (mem_initialSet_of_exponent_lt a h
      (hmy.trans_lt (hyx.trans_eq hpx.symm)) hmyi)

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
    simp only [leadExponent, Finsupp.add_apply, subsetExponent,
      Finsupp.indicator_apply, initialSet, Finset.mem_filter, Finset.mem_univ,
      Equiv.symm_apply_apply, true_and]
    have ha : a (indexPerm a j) ≤ a (indexPerm a i) := hanti hij
    by_cases hi : i.val < h <;> by_cases hj : j.val < h <;> simp [hi, hj] <;> omega
  · intro i j hij heq
    have ha : a (indexPerm a j) ≤ a (indexPerm a i) := hanti hij.le
    change leadExponent a h (indexPerm a i) =
      leadExponent a h (indexPerm a j) at heq
    simp only [leadExponent, Finsupp.add_apply, subsetExponent,
      Finsupp.indicator_apply, initialSet, Finset.mem_filter, Finset.mem_univ,
      Equiv.symm_apply_apply, true_and] at heq
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

end D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
