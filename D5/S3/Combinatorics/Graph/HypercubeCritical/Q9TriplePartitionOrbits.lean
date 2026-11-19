import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe

/-! Intersection matrices for two partitions of the nine coordinates into triples. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TriplePartitionOrbits

open Finset

/-- Representatives for the intersection matrices up to relabeling both partitions. -/
def representatives : Fin 5 → Fin 3 → Fin 3 → Fin 4 :=
  ![![![0, 0, 3], ![0, 3, 0], ![3, 0, 0]],
    ![![0, 0, 3], ![1, 2, 0], ![2, 1, 0]],
    ![![0, 1, 2], ![1, 1, 1], ![2, 1, 0]],
    ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]],
    ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]]

private def rows : Fin 10 → Fin 3 → Fin 4 :=
  ![![0, 0, 3], ![0, 1, 2], ![0, 2, 1], ![0, 3, 0], ![1, 0, 2],
    ![1, 1, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0], ![3, 0, 0]]

private theorem row_in_list (r : Fin 3 → Fin 4)
    (hr : (r 0).val + (r 1).val + (r 2).val = 3) : ∃ i, rows i = r := by
  have h : ∀ (a b c : Fin 4), a.val + b.val + c.val = 3 → ∃ i, rows i = ![a, b, c] := by
    decide +kernel
  obtain ⟨i, hi⟩ := h (r 0) (r 1) (r 2) hr
  refine ⟨i, hi.trans ?_⟩
  funext j
  fin_cases j <;> rfl

private def columnTotal (m : Fin 3 → Fin 3 → Fin 4) (j : Fin 3) : Nat :=
  (m 0 j).val + (m 1 j).val + (m 2 j).val

private def classified (m : Fin 3 → Fin 3 → Fin 4) : Prop :=
  ∃ k : Fin 5, ∃ p q : Equiv.Perm (Fin 3), ∀ i j,
    m (p i) (q j) = representatives k i j

private instance (m : Fin 3 → Fin 3 → Fin 4) : Decidable (classified m) :=
  inferInstanceAs (Decidable (∃ k : Fin 5, ∃ p q : Equiv.Perm (Fin 3), ∀ i j,
    m (p i) (q j) = representatives k i j))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem classify_rows :
    ∀ (a b c : Fin 10), (∀ j, columnTotal ![rows a, rows b, rows c] j = 3) →
      classified ![rows a, rows b, rows c] := by
  decide +kernel

/-- The nine intersection sizes of two triple partitions reduce to one of five
matrices by permuting the labels of the two partitions independently. -/
theorem classify_intersection_matrix (m : Fin 3 → Fin 3 → Fin 4)
    (hrow : ∀ i, (m i 0).val + (m i 1).val + (m i 2).val = 3)
    (hcol : ∀ j, (m 0 j).val + (m 1 j).val + (m 2 j).val = 3) :
    ∃ k : Fin 5, ∃ p q : Equiv.Perm (Fin 3), ∀ i j,
      m (p i) (q j) = representatives k i j := by
  obtain ⟨a, ha⟩ := row_in_list (m 0) (hrow 0)
  obtain ⟨b, hb⟩ := row_in_list (m 1) (hrow 1)
  obtain ⟨c, hc⟩ := row_in_list (m 2) (hrow 2)
  have he : ![rows a, rows b, rows c] = m := by
    funext i
    fin_cases i <;> first | exact ha | exact hb | exact hc
  have h := classify_rows a b c
  rw [he] at h
  exact h hcol

#print axioms classify_intersection_matrix

/-- The first labels in each representative partition pair. -/
def standardLabels : Fin 9 → Fin 3 := ![0, 0, 0, 1, 1, 1, 2, 2, 2]

/-- Second labels realizing the five intersection matrices with the standard first
partition. -/
def secondLabels : Fin 5 → Fin 9 → Fin 3 :=
  ![![2, 2, 2, 1, 1, 1, 0, 0, 0], ![2, 2, 2, 0, 1, 1, 0, 0, 1],
    ![1, 2, 2, 0, 1, 2, 0, 0, 1], ![1, 2, 2, 0, 1, 1, 0, 0, 2],
    ![0, 1, 2, 0, 1, 2, 0, 1, 2]]

private theorem representative_counts : ∀ (k : Fin 5) (i j : Fin 3),
    (univ.filter (fun a => standardLabels a = i ∧ secondLabels k a = j)).card =
      (representatives k i j).val := by
  decide +kernel

/-- After independent relabeling of the triples and a common coordinate
permutation, two partitions of nine coordinates into triples have one of five
representative pairs. -/
theorem classify_triple_partitions (first second : Fin 9 → Fin 3)
    (hfirst : ∀ i, (univ.filter (fun a => first a = i)).card = 3)
    (hsecond : ∀ j, (univ.filter (fun a => second a = j)).card = 3) :
    ∃ (k : Fin 5) (p q : Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 9)), ∀ a,
      first (σ a) = p (standardLabels a) ∧ second (σ a) = q (secondLabels k a) := by
  let overlap (i j : Fin 3) := (univ.filter (fun a => first a = i ∧ second a = j)).card
  have hle (i j : Fin 3) : overlap i j ≤ 3 := by
    rw [← hfirst i]
    exact card_le_card (filter_subset_filter _ (fun _ h => h.1))
  let m (i j : Fin 3) : Fin 4 := ⟨overlap i j, Nat.lt_succ_of_le (hle i j)⟩
  have hrow (i : Fin 3) : (m i 0).val + (m i 1).val + (m i 2).val = 3 := by
    have h := card_eq_sum_card_fiberwise (f := second)
      (s := univ.filter (fun a => first a = i)) (t := univ) (by simp)
    simpa [Fin.sum_univ_three, filter_filter, hfirst, m, overlap, and_comm] using h.symm
  have hcol (j : Fin 3) : (m 0 j).val + (m 1 j).val + (m 2 j).val = 3 := by
    have h := card_eq_sum_card_fiberwise (f := first)
      (s := univ.filter (fun a => second a = j)) (t := univ) (by simp)
    simpa [Fin.sum_univ_three, filter_filter, hsecond, m, overlap, and_comm] using h.symm
  obtain ⟨k, p, q, hmatrix⟩ := classify_intersection_matrix m hrow hcol
  let f (a : Fin 9) := (standardLabels a, secondLabels k a)
  let g (a : Fin 9) := (p.symm (first a), q.symm (second a))
  obtain ⟨σ, hσ⟩ := exists_perm_of_coordinate_color_counts f g (by
    rintro ⟨i, j⟩
    have hcard := congrArg Fin.val (hmatrix i j)
    rw [← representative_counts] at hcard
    simpa [f, g, Prod.mk.injEq, Equiv.symm_apply_eq] using hcard.symm)
  refine ⟨k, p, q, σ, fun a => ?_⟩
  simpa [f, g, Prod.mk.injEq, Equiv.symm_apply_eq] using hσ a

#print axioms classify_triple_partitions

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TriplePartitionOrbits
