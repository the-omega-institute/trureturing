/- GID: D5/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded irrational discrepancy excludes repetition, and finite two-sided edge presentations yield periodic points. -/

/- admission_basis: escape-witness
   no_positive_period_of_irrational_discrepancy uses the repeated-block sum
   and nonzero one-period discrepancy to violate the uniform bound.
   exists_periodic_point_of_finite_edge_presentation extracts an actual
   positive-length closed edge walk and checks its integer-modulo seam.
   MeyerovitchYoungQ62 uses the first estimate to exclude periods and the
   second construction to exclude all finite two-sided presentations. -/

import Mathlib.Algebra.Ring.Periodic
import Mathlib.NumberTheory.Real.Irrational

/-! Periodicity lemmas for Meyerovitch–Young, Question 6.2 (arXiv:2603.21449v1).
Both statements use the integer indexing of Eq. (19). -/

set_option autoImplicit false

open scoped BigOperators

namespace BiInfinitePayoffPeriodicity

private theorem sum_range_mul_of_periodic {f : ℕ → ℕ} {p : ℕ}
    (hf : Function.Periodic f p) (k : ℕ) :
    (∑ j ∈ Finset.range (k * p), f j) = k * (∑ j ∈ Finset.range p, f j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hshift :
          (∑ j ∈ Finset.range p, f (k * p + j)) = ∑ j ∈ Finset.range p, f j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.add_comm (k * p) j]
        exact hf.nat_mul k j
      simp only [Nat.succ_mul, Finset.sum_range_add f (k * p) p, ih, hshift]

/-- A bi-infinite binary word with uniformly bounded window discrepancy at an
irrational slope has no positive integer period. -/
theorem no_positive_period_of_irrational_discrepancy (a : ℤ → Bool) {α : ℝ}
    (hα : Irrational α)
    (hdiscrepancy : ∀ (i : ℤ) (n : ℕ), 2 ≤ n →
      |(∑ j ∈ Finset.range n, ((a (i + (j : ℤ))).toNat : ℝ)) - (n : ℝ) * α| ≤ 7) :
    ¬ ∃ period : ℤ, 0 < period ∧ Function.Periodic a period := by
  rintro ⟨period, hperiod, hper⟩
  let p : ℕ := period.toNat
  have hcast : (p : ℤ) = period := Int.toNat_of_nonneg hperiod.le
  have hp : 0 < p := by
    apply Int.natCast_pos.mp
    rw [hcast]
    exact hperiod
  let f : ℕ → ℕ := fun j => (a (j : ℤ)).toNat
  have hf : Function.Periodic f p := by
    intro j
    simpa only [f, Nat.cast_add, hcast] using congrArg Bool.toNat (hper (j : ℤ))
  let c : ℕ := ∑ j ∈ Finset.range p, f j
  -- A zero discrepancy over one period would express the slope as c / p.
  have hdelta_ne : (c : ℝ) - (p : ℝ) * α ≠ 0 := by
    intro hzero
    have hp_real : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
    have hratio : α = (c : ℝ) / (p : ℝ) := by
      apply (eq_div_iff hp_real.ne').2
      calc
        α * (p : ℝ) = (p : ℝ) * α := mul_comm _ _
        _ = (c : ℝ) := (sub_eq_zero.mp hzero).symm
    exact hα.ne_rational (c : ℤ) (p : ℤ) (by simpa only [Int.cast_natCast] using hratio)
  have hdelta_pos := abs_pos.mpr hdelta_ne
  obtain ⟨m, hm⟩ := exists_nat_gt ((7 : ℝ) / |(c : ℝ) - (p : ℝ) * α|)
  let k : ℕ := m + 2
  have hmk : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (by dsimp [k]; omega)
  have hlarge : 7 < (k : ℝ) * |(c : ℝ) - (p : ℝ) * α| :=
    (div_lt_iff₀ hdelta_pos).mp (hm.trans_le hmk)
  have hlength : 2 ≤ k * p := by
    calc
      2 ≤ k := by dsimp [k]; omega
      _ = k * 1 := (Nat.mul_one k).symm
      _ ≤ k * p := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hp)
  have hbound : |(∑ j ∈ Finset.range (k * p), (f j : ℝ)) -
      ((k * p : ℕ) : ℝ) * α| ≤ 7 := by
    simpa only [f, zero_add] using hdiscrepancy 0 (k * p) hlength
  have hblocks : (∑ j ∈ Finset.range (k * p), f j) = k * c :=
    sum_range_mul_of_periodic hf k
  rw [← Nat.cast_sum (Finset.range (k * p)) f, hblocks] at hbound
  have hscaled : (k : ℝ) * |(c : ℝ) - (p : ℝ) * α| ≤ 7 := by
    simpa only [Nat.cast_mul, mul_assoc, ← mul_sub, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))] using hbound
  exact (not_lt_of_ge hscaled) hlarge

/-- A nonempty shift presented by the edge labels of all bi-infinite walks
of a finite directed multigraph contains a point of positive integer period. -/
theorem exists_periodic_point_of_finite_edge_presentation
    {Vertex Edge Alphabet : Type*} [Finite Vertex] [Finite Edge]
    (source target : Edge → Vertex) (label : Edge → Alphabet)
    (S : Set (ℤ → Alphabet))
    (hS : ∀ x : ℤ → Alphabet, x ∈ S ↔
      ∃ walk : ℤ → Edge, (∀ i : ℤ, target (walk i) = source (walk (i + 1))) ∧
        ∀ i : ℤ, label (walk i) = x i)
    (hne : S.Nonempty) :
    ∃ x ∈ S, ∃ p : ℤ, 0 < p ∧ Function.Periodic x p := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨walk, hwalk, _⟩ := (hS x).mp hx
  obtain ⟨m, n, hne_indices, hsame⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun j : ℕ => source (walk (j : ℤ)))
  have hloop : ∃ i j : ℤ, i < j ∧ source (walk i) = source (walk j) := by
    rcases lt_or_gt_of_ne hne_indices with hlt | hgt
    · exact ⟨(m : ℤ), (n : ℤ), Int.ofNat_lt.mpr hlt, hsame⟩
    · exact ⟨(n : ℤ), (m : ℤ), Int.ofNat_lt.mpr hgt, hsame.symm⟩
  obtain ⟨i, j, hij, hclose⟩ := hloop
  let p : ℤ := j - i
  have hp : 0 < p := sub_pos.mpr hij
  have hendpoint : i + p = j := by dsimp [p]; omega
  let loop : ℤ → Edge := fun n => walk (i + n % p)
  have hloop_walk : ∀ n : ℤ, target (loop n) = source (loop (n + 1)) := by
    intro n
    change target (walk (i + n % p)) = source (walk (i + (n + 1) % p))
    have hrem_nonneg : 0 ≤ n % p := Int.emod_nonneg n hp.ne'
    have hrem_lt : n % p < p := Int.emod_lt_of_pos n hp
    rw [← Int.emod_add_emod n p 1]
    by_cases hbefore : n % p + 1 < p
    · rw [Int.emod_eq_of_lt (by omega) hbefore]
      simpa only [add_assoc] using hwalk (i + n % p)
    · have hlast : n % p + 1 = p := by omega
      rw [hlast, Int.emod_self, add_zero]
      calc
        target (walk (i + n % p)) = source (walk (i + n % p + 1)) :=
          hwalk (i + n % p)
        _ = source (walk j) := by rw [add_assoc, hlast, hendpoint]
        _ = source (walk i) := hclose.symm
  refine ⟨fun n => label (loop n), (hS _).mpr ⟨loop, hloop_walk, fun _ => rfl⟩,
    p, hp, ?_⟩
  intro n
  change label (walk (i + (n + p) % p)) = label (walk (i + n % p))
  rw [Int.add_emod_right]

end BiInfinitePayoffPeriodicity
