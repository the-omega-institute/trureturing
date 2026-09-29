/- GID: D5/S3/Fourier/CharacterSelection/TriangleDefectStability
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/TriangleDefectStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered triangle defects count anchored edge repairs and bound the best anchor. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.TriangleDefectStability

universe u v

/-- The number of ordered edges on which the potential anchored at `r` disagrees with `a`. -/
noncomputable def edgeDefects {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] (a : V → V → A) (r : V) : ℕ := by
  classical
  exact ∑ i : V, ∑ j : V, if a i j ≠ a r j - a r i then 1 else 0

/-- The number of ordered triples with nonzero oriented triangle sum. -/
noncomputable def triangleDefects {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] (a : V → V → A) : ℕ := by
  classical
  exact ∑ r : V, ∑ i : V, ∑ j : V,
    if a r i + a i j + a j r ≠ 0 then 1 else 0

/-- The number of ordered edges on which a potential disagrees with `a`. -/
noncomputable def potentialErrors {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] (a : V → V → A) (p : V → A) : ℕ := by
  classical
  exact ∑ i : V, ∑ j : V, if a i j ≠ p j - p i then 1 else 0

/-- Ordered triangle incidence, minimum anchored repair, and a universal error bound. -/
theorem triangle_defects_incidence_repair_and_error_bound
    {V : Type u} {A : Type v} [Fintype V] [Nonempty V] [AddCommGroup A]
    (a : V → V → A)
    (hdiag : ∀ i, a i i = 0)
    (hskew : ∀ i j, a j i = -a i j) :
    (∑ r : V, edgeDefects a r) = triangleDefects a ∧
      (∃ r : V, Fintype.card V * edgeDefects a r ≤ triangleDefects a) ∧
      ∀ p : V → A,
        triangleDefects a ≤ 3 * (Fintype.card V - 2) * potentialErrors a p := by
  classical
  have incidence : (∑ r : V, edgeDefects a r) = triangleDefects a := by
    simp only [edgeDefects, triangleDefects]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hid : a r i + a i j + a j r = a i j - (a r j - a r i) := by
      rw [hskew r j]
      abel
    simp only [hid, sub_ne_zero]
  refine ⟨incidence, ?_, ?_⟩
  obtain ⟨r, _, hr⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V) (edgeDefects a)
      Finset.univ_nonempty
  refine ⟨r, ?_⟩
  rw [← incidence]
  simpa using
    (Finset.card_nsmul_le_sum (Finset.univ : Finset V) (edgeDefects a)
      (edgeDefects a r) (fun i _ => hr i (Finset.mem_univ i)))
  intro p
  let err (i j : V) : ℕ := if a i j ≠ p j - p i then 1 else 0
  let distinct (r i j : V) : Prop := r ≠ i ∧ i ≠ j ∧ j ≠ r
  have count_third (i j : V) (hij : i ≠ j) :
      (∑ r : V, if r ≠ i ∧ r ≠ j then (1 : ℕ) else 0) = Fintype.card V - 2 := by
    have hcard : 2 ≤ Fintype.card V := by
      have h : 1 < (Finset.univ : Finset V).card :=
        Finset.one_lt_card_iff.mpr ⟨i, j, Finset.mem_univ _, Finset.mem_univ _, hij⟩
      simp only [Finset.card_univ] at h
      omega
    rw [← Finset.card_filter]
    have hf : (Finset.univ.filter (fun r : V => r ≠ i ∧ r ≠ j)) =
        ((Finset.univ : Finset V).erase i).erase j := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [hf, Finset.card_erase_of_mem (by simp [hij.symm]),
      Finset.card_erase_of_mem (by simp), Finset.card_univ]
    omega
  have triangle_bound (r i j : V) :
      (if a r i + a i j + a j r ≠ 0 then 1 else 0) ≤
        (if distinct r i j then err r i + err i j + err j r else 0) := by
    by_cases hd : distinct r i j
    · simp only [if_pos hd]
      by_cases hri : a r i ≠ p i - p r
      · simp [err, hri]; split_ifs <;> omega
      by_cases hij : a i j ≠ p j - p i
      · simp [err, hij]; split_ifs <;> omega
      by_cases hjr : a j r ≠ p r - p j
      · simp [err, hjr]; split_ifs <;> omega
      have hz : a r i + a i j + a j r = 0 := by
        simp only [not_ne_iff] at hri hij hjr
        rw [hri, hij, hjr]
        abel
      simp [hz]
    · have hz : a r i + a i j + a j r = 0 := by
        simp only [distinct, not_and_or, not_ne_iff] at hd
        rcases hd with h | h | h
        · subst i
          rw [hdiag, hskew]
          abel
        · subst j
          rw [hdiag, hskew]
          abel
        · subst r
          rw [hdiag, hskew]
          abel
      simp [hd, hz]
  have hsum : triangleDefects a ≤
      ∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err r i + err i j + err j r else 0 := by
    unfold triangleDefects
    exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => triangle_bound r i j)))
  have count_edges (f : V → V → ℕ) (hdiagf : ∀ i, f i i = 0) :
      (∑ i : V, ∑ j : V, ∑ r : V,
        if distinct r i j then f i j else 0) =
        (Fintype.card V - 2) * (∑ i : V, ∑ j : V, f i j) := by
    calc
      _ = ∑ i : V, ∑ j : V, (Fintype.card V - 2) * f i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j
          simp [distinct, hdiagf]
        · have hc := count_third i j hij
          calc
            (∑ r : V, if distinct r i j then f i j else 0) =
                (∑ r : V, if r ≠ i ∧ r ≠ j then f i j else 0) := by
                  apply Finset.sum_congr rfl
                  intro r _
                  have : distinct r i j ↔ r ≠ i ∧ r ≠ j := by
                    simp [distinct, hij, ne_comm, and_comm]
                  simp only [this]
            _ = (∑ r : V, if r ≠ i ∧ r ≠ j then (1 : ℕ) else 0) * f i j := by
                  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
            _ = (Fintype.card V - 2) * f i j := by rw [hc]
      _ = (Fintype.card V - 2) * (∑ i : V, ∑ j : V, f i j) := by
        simp only [Finset.mul_sum]
  have herrdiag (i : V) : err i i = 0 := by
    simp [err, hdiag]
  have hfirst :
      (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err r i else 0) =
        (Fintype.card V - 2) * potentialErrors a p := by
    have h := count_edges err herrdiag
    have heq : (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err r i else 0) =
        (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct j r i then err r i else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp [distinct, and_comm, and_assoc]
    rw [heq, h]
    rfl
  have hmiddle :
      (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err i j else 0) =
        (Fintype.card V - 2) * potentialErrors a p := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ r : V,
          if distinct r i j then err i j else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
      _ = (Fintype.card V - 2) * potentialErrors a p := by
            rw [count_edges err herrdiag]
            rfl
  have hlast :
      (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err j r else 0) =
        (Fintype.card V - 2) * potentialErrors a p := by
    calc
      _ = ∑ j : V, ∑ r : V, ∑ i : V,
          if distinct r i j then err j r else 0 := by
            conv_lhs =>
              arg 2
              ext r
              rw [Finset.sum_comm]
            exact Finset.sum_comm
      _ = ∑ j : V, ∑ r : V, ∑ i : V,
          if distinct i j r then err j r else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro i _
            simp [distinct, and_comm, and_left_comm, and_assoc]
      _ = (Fintype.card V - 2) * potentialErrors a p := by
            rw [count_edges err herrdiag]
            rfl
  have hsplit :
      (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err r i + err i j + err j r else 0) =
      (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err r i else 0) +
      (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err i j else 0) +
      (∑ r : V, ∑ i : V, ∑ j : V,
        if distinct r i j then err j r else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> omega
  rw [hsplit, hfirst, hmiddle, hlast] at hsum
  rw [mul_assoc]
  omega

#print axioms triangle_defects_incidence_repair_and_error_bound

end D5.S3.Fourier.CharacterSelection.TriangleDefectStability
