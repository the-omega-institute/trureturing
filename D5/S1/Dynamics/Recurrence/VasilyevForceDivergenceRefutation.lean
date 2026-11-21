/- GID: D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation
   generality: I
   mirror-B: D5/B/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.claim; result=D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.result; claim=D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.claim
   digest: A force-divergent set of positive integers contains no whole all-up tail. -/

import Mathlib.Data.Finset.Max
import Mathlib.Dynamics.PeriodicPts.Defs

/-! An infinite spaced omission set gives a counterexample to Vasilyev's Question 7.7. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Recurrence.VasilyevForceDivergenceRefutation

open Function
open scoped Function

/-- The positive vertices of the up-down graph. -/
def P : Set ℕ := {x | 0 < x}

/-- The up step, written using natural division. -/
def U (x : ℕ) : ℕ := (3 * x + 1) / 2

/-- The down step, written using natural division. -/
def D (x : ℕ) : ℕ := (x + 1) / 2

/-- The step chooses up at vertices in `S` and down at all other vertices. -/
noncomputable def T (S : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact if x ∈ S then U x else D x

/-- Every positive-vertex superset has a positive orbit that never enters a periodic cycle. -/
def ForceDivergent (A : Set ℕ) : Prop :=
  ∀ S : Set ℕ, S ⊆ P → A ⊆ S →
    ∃ x : ℕ, x ∈ P ∧ ¬ ∃ t : ℕ, (T S)^[t] x ∈ periodicPts (T S)

/-- A complete forward up orbit, including its starting vertex, lies in the set. -/
def ContainsTail (A : Set ℕ) : Prop :=
  ∃ y : ℕ, y ∈ P ∧ ∀ k : ℕ, U^[k] y ∈ A

/-- Vasilyev's Question 7.7 asserts this implication for every set of positive vertices. -/
def claim : Prop :=
  ∀ A : Set ℕ, A ⊆ P → ForceDivergent A → ContainsTail A

private theorem up_gt {x : ℕ} (hx : 0 < x) : x < U x := by
  unfold U
  omega

private theorem up_iterate_ge {x : ℕ} (hx : 0 < x) (k : ℕ) : x + k ≤ U^[k] x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    have hpos : 0 < U^[k] x := by omega
    have hup := up_gt hpos
    omega

/-- The seed determines the spacing, and the successors meet the up orbits in order. -/
private def b : ℕ → ℕ
  | 0 => 3
  | n + 1 => U^[2 * b n] (n + 1)

private def omitted : Set ℕ := Set.range (fun n => b (n + 1))

private def witness : Set ℕ := P \ omitted

private theorem b_spacing (n : ℕ) : 2 * b n < b (n + 1) := by
  have h := up_iterate_ge (x := n + 1) (Nat.succ_pos n) (2 * b n)
  rw [b]
  omega

private theorem b_strictMono : StrictMono b :=
  strictMono_nat_of_lt_succ fun n => (by have h := b_spacing n; omega)

private theorem gap_subset_witness {n x : ℕ} (hl : b n < x) (hr : x < b (n + 1)) :
    x ∈ witness := by
  refine ⟨(Nat.zero_le (b n)).trans_lt hl, ?_⟩
  rintro ⟨i, hi⟩
  by_cases h : i + 1 ≤ n
  · exact (not_le_of_gt hl) (hi ▸ b_strictMono.monotone h)
  · have h' : n + 1 ≤ i + 1 := by omega
    exact (not_le_of_gt hr) (hi ▸ b_strictMono.monotone h')

private theorem no_tail : ¬ ContainsTail witness := by
  rintro ⟨y, hy, hall⟩
  change 0 < y at hy
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = n + 1 := ⟨y - 1, by omega⟩
  exact (hall (2 * b n)).2 ⟨n, rfl⟩

private theorem up_rounding (x : ℕ) : 3 * x ≤ 2 * U x ∧ 2 * U x ≤ 3 * x + 1 := by
  unfold U
  omega

private theorem down_rounding (x : ℕ) : x ≤ 2 * D x ∧ 2 * D x ≤ x + 1 := by
  unfold D
  omega

private theorem gap_visits (n : ℕ) :
    b n < D (b (n + 1)) ∧
      D (b (n + 1)) < U (D (b (n + 1))) ∧ U (D (b (n + 1))) < b (n + 1) := by
  have spacing := b_spacing n
  have seed : 3 ≤ b n := b_strictMono.monotone (Nat.zero_le n)
  have roundingD := down_rounding (b (n + 1))
  have roundingU := up_rounding (D (b (n + 1)))
  have hpos : 0 < D (b (n + 1)) := by omega
  exact ⟨by omega, up_gt hpos, by omega⟩

/-- An up step or a down-up-up block strictly increases the endpoint. -/
private theorem increasing_block {S : Set ℕ} (hAS : witness ⊆ S) {x : ℕ} (hx : 0 < x) :
    ∃ k : ℕ, x < (T S)^[k] x := by
  classical
  by_cases hs : x ∈ S
  · refine ⟨1, ?_⟩
    simpa [T, hs] using up_gt hx
  · have hxB : x ∈ omitted := by
      by_contra h
      exact hs (hAS ⟨hx, h⟩)
    obtain ⟨n, rfl⟩ := hxB
    obtain ⟨hl, hm, hr⟩ := gap_visits n
    have hD := hAS (gap_subset_witness hl (hm.trans hr))
    have hUD := hAS (gap_subset_witness (hl.trans hm) hr)
    refine ⟨3, ?_⟩
    change b (n + 1) < T S (T S (T S (b (n + 1))))
    simp only [T, ite_eq_right hs, ite_eq_left hD, ite_eq_left hUD]
    have hd := (down_rounding (b (n + 1))).1
    have hu₁ := (up_rounding (D (b (n + 1)))).1
    have hu₂ := (up_rounding (U (D (b (n + 1))))).1
    omega

private theorem blocks_reach {S : Set ℕ} (hAS : witness ⊆ S) {x : ℕ} (hx : 0 < x)
    (j : ℕ) : ∃ t : ℕ, x + j ≤ (T S)^[t] x := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨t, ht⟩ := ih
    have hpos : 0 < (T S)^[t] x := by omega
    obtain ⟨k, hk⟩ := increasing_block hAS hpos
    refine ⟨k + t, ?_⟩
    rw [iterate_add_apply]
    omega

/-- Every eventually periodic orbit is bounded by a value in its initial segment. -/
private theorem eventually_periodic_bounded {f : ℕ → ℕ} {x : ℕ}
    (h : ∃ t : ℕ, f^[t] x ∈ periodicPts f) : ∃ M : ℕ, ∀ n : ℕ, f^[n] x ≤ M := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨p, hp, hperiod⟩ := mem_periodicPts.mp ht
  have segment : ∀ n : ℕ, ∃ i < t + p, f^[i] x = f^[n] x := by
    intro n
    by_cases hn : n < t
    · exact ⟨n, by omega, rfl⟩
    · refine ⟨(n - t) % p + t, ?_, ?_⟩
      · have hmod := Nat.mod_lt (n - t) hp
        omega
      · rw [iterate_add_apply, hperiod.iterate_mod_apply, ← iterate_add_apply,
          Nat.sub_add_cancel (Nat.le_of_not_gt hn)]
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.range (t + p))
    (fun k => f^[k] x) (Finset.nonempty_range_iff.mpr (by omega))
  refine ⟨f^[i] x, fun n => ?_⟩
  obtain ⟨j, hj, heq⟩ := segment n
  rw [← heq]
  exact hmax j (Finset.mem_range.mpr hj)

private theorem all_positive_not_eventually_periodic {S : Set ℕ} (hAS : witness ⊆ S)
    {x : ℕ} (hx : 0 < x) : ¬ ∃ t : ℕ, (T S)^[t] x ∈ periodicPts (T S) := by
  intro h
  obtain ⟨M, hM⟩ := eventually_periodic_bounded h
  obtain ⟨t, ht⟩ := blocks_reach hAS hx M
  have hb := hM t
  omega

private theorem force_divergent : ForceDivergent witness := by
  intro S _ hAS
  exact ⟨1, Nat.one_pos, all_positive_not_eventually_periodic hAS Nat.one_pos⟩

/-- The same set is force-divergent and fails to contain any all-up tail. -/
theorem result : ¬ claim := by
  intro h
  exact no_tail (h witness (fun _ hx => hx.1) force_divergent)

end D5.S1.Dynamics.Recurrence.VasilyevForceDivergenceRefutation
