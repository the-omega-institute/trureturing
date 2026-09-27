/- GID: D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tetrahedral defects count anchored triangle repairs and detect exact edge cochains. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair

universe u v

/-- The ordered triangles on which the edge cochain anchored at `r` fails to reproduce `F`. -/
noncomputable def faceErrors {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] (F : V → V → V → A) (r : V) : ℕ := by
  classical
  exact ∑ i : V, ∑ j : V, ∑ k : V,
    if F i j k ≠ F r j k - F r i k + F r i j then 1 else 0

/-- The number of ordered quadruples with a nonzero tetrahedral coboundary. -/
noncomputable def tetraDefects {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] (F : V → V → V → A) : ℕ := by
  classical
  exact ∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
    if F i j k - F r j k + F r i k - F r i j ≠ 0 then 1 else 0

/-- The ordered triangles on which an edge cochain fails to reproduce `F`. -/
noncomputable def edgeErrors {V : Type u} {A : Type v}
    [Fintype V] [AddCommGroup A] (F : V → V → V → A) (edge : V → V → A) : ℕ := by
  classical
  exact ∑ i : V, ∑ j : V, ∑ k : V,
    if F i j k ≠ edge j k - edge i k + edge i j then 1 else 0

/-- A degree-two cochain on a complete ordered simplex has a quantitatively
controlled anchored edge reconstruction. Its tetrahedral coboundary vanishes
exactly when an edge cochain reproduces every triangle value. -/
theorem tetra_defects_incidence_repair_and_exactness
    {V : Type u} {A : Type v} [Fintype V] [Nonempty V] [AddCommGroup A]
    (F : V → V → V → A) :
    (∑ r : V, faceErrors F r) = tetraDefects F ∧
      (∃ r : V, Fintype.card V * faceErrors F r ≤ tetraDefects F) ∧
      (∀ edge : V → V → A,
        tetraDefects F ≤ 4 * Fintype.card V * edgeErrors F edge) ∧
      ((∀ r i j k, F i j k - F r j k + F r i k - F r i j = 0) ↔
        ∃ edge : V → V → A, ∀ i j k,
          F i j k = edge j k - edge i k + edge i j) := by
  classical
  have incidence : (∑ r : V, faceErrors F r) = tetraDefects F := by
    simp only [faceErrors, tetraDefects]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hd : F i j k - F r j k + F r i k - F r i j =
        F i j k - (F r j k - F r i k + F r i j) := by
      abel
    simp only [hd, sub_ne_zero]
  refine ⟨incidence, ?_, ?_, ?_⟩
  · obtain ⟨r, _, hr⟩ :=
      Finset.exists_min_image (Finset.univ : Finset V) (faceErrors F)
        Finset.univ_nonempty
    refine ⟨r, ?_⟩
    rw [← incidence]
    simpa using
      (Finset.card_nsmul_le_sum (Finset.univ : Finset V) (faceErrors F)
        (faceErrors F r) (fun i _ => hr i (Finset.mem_univ i)))
  · intro edge
    let err (i j k : V) : ℕ :=
      if F i j k ≠ edge j k - edge i k + edge i j then 1 else 0
    have face_bound (r i j k : V) :
        (if F i j k - F r j k + F r i k - F r i j ≠ 0 then 1 else 0) ≤
          err i j k + err r j k + err r i k + err r i j := by
      by_cases hijk : F i j k ≠ edge j k - edge i k + edge i j
      · simp [err, hijk]
        split_ifs <;> omega
      by_cases hrjk : F r j k ≠ edge j k - edge r k + edge r j
      · simp [err, hrjk]
        split_ifs <;> omega
      by_cases hrik : F r i k ≠ edge i k - edge r k + edge r i
      · simp [err, hrik]
        split_ifs <;> omega
      by_cases hrij : F r i j ≠ edge i j - edge r j + edge r i
      · simp [err, hrij]
        split_ifs <;> omega
      have hz : F i j k - F r j k + F r i k - F r i j = 0 := by
        simp only [not_ne_iff] at hijk hrjk hrik hrij
        rw [hijk, hrjk, hrik, hrij]
        abel
      simp [hz, err]
    have hsum : tetraDefects F ≤
        ∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
          (err i j k + err r j k + err r i k + err r i j) := by
      unfold tetraDefects
      exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
          face_bound r i j k))))
    have hfirst :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err i j k) =
          Fintype.card V * edgeErrors F edge := by
      simp [Finset.sum_const, Finset.card_univ, edgeErrors, err]
    have hsecond :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err r j k) =
          Fintype.card V * edgeErrors F edge := by
      calc
        _ = ∑ i : V, ∑ r : V, ∑ j : V, ∑ k : V, err r j k := by
          rw [Finset.sum_comm]
        _ = Fintype.card V * edgeErrors F edge := by
          simp [Finset.sum_const, Finset.card_univ, edgeErrors, err]
    have hthird :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err r i k) =
          Fintype.card V * edgeErrors F edge := by
      calc
        _ = ∑ r : V, ∑ i : V, ∑ k : V, ∑ j : V, err r i k := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = Fintype.card V * edgeErrors F edge := by
          simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum, edgeErrors, err]
    have hfourth :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err r i j) =
          Fintype.card V * edgeErrors F edge := by
      simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum, edgeErrors, err]
    have hsplit :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
          (err i j k + err r j k + err r i k + err r i j)) =
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err i j k) +
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err r j k) +
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err r i k) +
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, err r i j) := by
      simp only [Finset.sum_add_distrib]
    rw [hsplit, hfirst, hsecond, hthird, hfourth] at hsum
    calc
      tetraDefects F ≤
          Fintype.card V * edgeErrors F edge +
          Fintype.card V * edgeErrors F edge +
          Fintype.card V * edgeErrors F edge +
          Fintype.card V * edgeErrors F edge := hsum
      _ = 4 * Fintype.card V * edgeErrors F edge := by ring
  · constructor
    · intro h
      let r : V := Classical.choice (inferInstance : Nonempty V)
      refine ⟨fun i j => F r i j, ?_⟩
      intro i j k
      have hd : F i j k - (F r j k - F r i k + F r i j) = 0 := by
        calc
          _ = F i j k - F r j k + F r i k - F r i j := by abel
          _ = 0 := h r i j k
      exact sub_eq_zero.mp hd
    · rintro ⟨edge, h⟩ r i j k
      rw [h i j k, h r j k, h r i k, h r i j]
      abel

#print axioms tetra_defects_incidence_repair_and_exactness

end D5.S3.Fourier.CharacterSelection.SimplexTwoCochainRepair
