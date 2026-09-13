/- GID: D5/S1/Digit/Admissibility/FiniteProductThresholdPruning
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/FiniteProductThresholdPruning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every feasible finite capacity vector admits a bounded reduction preserving its product threshold. -/

import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.WellFounded

set_option autoImplicit false

namespace D5.S1.Digit.Admissibility.FiniteProductThresholdPruning

open scoped BigOperators

/-- Every finite capacity vector reaching a threshold of at least two has a feasible vector
that is no larger in any coordinate, whose entries are below the threshold, whose positive
support is bounded by the binary ceiling logarithm, and whose state count is less than twice
the threshold. -/
theorem exists_threshold_pruning (k q : ℕ) (hq : 2 ≤ q) (A : Fin k → ℕ)
    (hQ : q ≤ ∏ i, (A i + 1)) :
    ∃ a : Fin k → ℕ,
      (∀ i, a i ≤ A i) ∧
      q ≤ (∏ i, (a i + 1)) ∧
      (∀ i, a i ≤ q - 1) ∧
      (Finset.univ.filter (fun i => 0 < a i)).card ≤ Nat.clog 2 q ∧
      (∏ i, (a i + 1)) < 2 * q := by
  classical
  let C := {a : Fin k → ℕ // (∀ i, a i ≤ A i) ∧ q ≤ ∏ i, (a i + 1)}
  have : Nonempty C := ⟨⟨A, (fun _ => le_rfl), hQ⟩⟩
  let m : C := Function.argmin (fun a : C => ∑ i, a.val i)
  let a : Fin k → ℕ := m.val
  have ha : (∀ i, a i ≤ A i) ∧ q ≤ ∏ i, (a i + 1) := m.property
  have hminimal (b : Fin k → ℕ) (hb : ∀ i, b i ≤ a i)
      (hlt : ∃ i, b i < a i) : (∏ i, (b i + 1)) < q := by
    by_contra! hfeasible
    let c : C := ⟨b, (fun i => (hb i).trans (ha.1 i)), hfeasible⟩
    have hmin : (∑ i, a i) ≤ ∑ i, b i :=
      Function.argmin_le (fun c : C => ∑ i, c.val i) c
    have hsum : (∑ i, b i) < ∑ i, a i := by
      apply Finset.sum_lt_sum (fun i _ => hb i)
      obtain ⟨i, hi⟩ := hlt
      exact ⟨i, Finset.mem_univ _, hi⟩
    omega
  have hlower (i : Fin k) (t : ℕ) (ht : t < a i) :
      (t + 1) * (∏ j ∈ Finset.univ.erase i, (a j + 1)) < q := by
    let b := Function.update a i t
    have hb : ∀ j, b j ≤ a j := by
      intro j
      by_cases hji : j = i
      · subst j; simpa [b] using ht.le
      · simp [b, hji]
    have hlt := hminimal b hb ⟨i, by simpa [b] using ht⟩
    have hprod : (∏ j, (b j + 1)) =
        (t + 1) * (∏ j ∈ Finset.univ.erase i, (a j + 1)) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => b j + 1) (Finset.mem_univ i)]
      simp only [b, Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      simp [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rwa [hprod] at hlt
  have hcap (i : Fin k) : a i ≤ q - 1 := by
    by_contra! hi
    have h := hlower i (q - 1) hi
    have hR : 1 ≤ ∏ j ∈ Finset.univ.erase i, (a j + 1) :=
      Finset.one_le_prod' (fun j _ => Nat.succ_le_succ (Nat.zero_le _))
    have hmul := Nat.mul_le_mul_left q hR
    have hqsub : q - 1 + 1 = q := by omega
    rw [hqsub] at h
    omega
  let S := Finset.univ.filter (fun i => 0 < a i)
  have hS : S.Nonempty := by
    by_contra hempty
    have hz : ∀ i, a i = 0 := by
      intro i
      have hi : i ∉ S := fun hi => hempty ⟨i, hi⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      omega
    have := ha.2
    simp only [hz, zero_add, Finset.prod_const_one] at this
    omega
  obtain ⟨i, hi⟩ := hS
  have hai : 0 < a i := (Finset.mem_filter.mp hi).2
  have hdelete : (∏ j ∈ Finset.univ.erase i, (a j + 1)) < q := by
    simpa using hlower i 0 hai
  have hsupport : S.card ≤ Nat.clog 2 q := by
    by_contra! hc
    have hpow : 2 ^ (S.erase i).card ≤ ∏ j ∈ S.erase i, (a j + 1) := by
      apply Finset.pow_card_le_prod
      intro j hj
      have hjpos := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
      omega
    have hsubset : S.erase i ⊆ Finset.univ.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩
    have hprod := Finset.prod_le_prod_of_subset_of_one_le' hsubset
      (fun j _ _ => Nat.succ_le_succ (Nat.zero_le (a j)))
    have hcard : Nat.clog 2 q ≤ (S.erase i).card := by
      rw [Finset.card_erase_of_mem hi]
      omega
    have hpowq := (Nat.le_pow_clog (by decide : 1 < 2) q).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) hcard)
    exact (not_lt_of_ge (hpowq.trans (hpow.trans hprod))) hdelete
  have hdec : a i * (∏ j ∈ Finset.univ.erase i, (a j + 1)) < q := by
    have h := hlower i (a i - 1) (by omega)
    simpa only [Nat.sub_add_cancel hai] using h
  have htwice : a i + 1 ≤ 2 * a i := by omega
  have hbound : (∏ j, (a j + 1)) < 2 * q := by
    calc
      (∏ j, (a j + 1)) = (a i + 1) * ∏ j ∈ Finset.univ.erase i, (a j + 1) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
      _ ≤ (2 * a i) * ∏ j ∈ Finset.univ.erase i, (a j + 1) :=
        Nat.mul_le_mul_right _ htwice
      _ = 2 * (a i * ∏ j ∈ Finset.univ.erase i, (a j + 1)) := Nat.mul_assoc _ _ _
      _ < 2 * q := Nat.mul_lt_mul_of_pos_left hdec (by decide)
  exact ⟨a, ha.1, ha.2, hcap, hsupport, hbound⟩

#print axioms exists_threshold_pruning

end D5.S1.Digit.Admissibility.FiniteProductThresholdPruning
