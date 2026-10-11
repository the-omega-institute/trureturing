/- GID: D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: none
   digest: Stage endpoints and the lower-density bound for the eleven-adic interval construction. -/

import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationDensity

def M (k : ℕ) : ℕ := (11 ^ k + 1) / 2

def stage (k : ℕ) : Set ℕ :=
  Set.Icc (2 * M k) (3 * M k - 1) ∪
    Set.Icc (6 * M k - 2) (11 * M k - 5)

def S : Set ℕ := {1} ∪ {x | ∃ k, x ∈ stage k}

private theorem M_zero : M 0 = 1 := by norm_num [M]

private theorem power_odd (k : ℕ) : 11 ^ k % 2 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih => simp [pow_succ, Nat.mul_mod, ih]

theorem twice_M (k : ℕ) : 2 * M k = 11 ^ k + 1 := by
  have h := power_odd k
  have hd := Nat.mod_add_div (11 ^ k) 2
  unfold M
  omega

theorem M_pos (k : ℕ) : 0 < M k := by
  have h : 0 < 11 ^ k := pow_pos (by decide) _
  unfold M
  omega

theorem M_step (k : ℕ) : M (k + 1) = 11 * M k - 5 := by
  have h := twice_M k
  have hn := twice_M (k + 1)
  have hp : 0 < 11 ^ k := pow_pos (by decide) _
  rw [pow_succ] at hn
  omega

theorem M_strictMono : StrictMono M := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [M_step]
  have h := M_pos k
  omega

theorem stage_bounds {k x : ℕ} (hx : x ∈ stage k) :
    2 * M k ≤ x ∧ x ≤ M (k + 1) := by
  have h := M_pos k
  rw [M_step]
  rcases hx with hx | hx <;> simp only [Set.mem_Icc] at hx <;> omega

theorem S_pos {x : ℕ} (hx : x ∈ S) : 0 < x := by
  rcases hx with hx | ⟨k, hx⟩
  · simp only [Set.mem_singleton_iff] at hx
    omega
  · have hb := stage_bounds hx
    have hp := M_pos k
    omega

private def initialSegment : ℕ → Finset ℕ
  | 0 => {1}
  | k + 1 => initialSegment k ∪ Finset.Icc (2 * M k) (3 * M k - 1) ∪
      Finset.Icc (6 * M k - 2) (11 * M k - 5)

private theorem initialSegment_bounds (k : ℕ) {x : ℕ} (hx : x ∈ initialSegment k) :
    x ∈ S ∧ 1 ≤ x ∧ x ≤ M k := by
  induction k with
  | zero => simp only [initialSegment, Finset.mem_singleton] at hx; subst x; simp [S, M_zero]
  | succ k ih =>
    simp only [initialSegment, Finset.mem_union, Finset.mem_Icc] at hx
    rcases hx with (hx | hx) | hx
    · have hb := ih hx
      exact ⟨hb.1, hb.2.1, hb.2.2.trans (M_strictMono.monotone (Nat.le_succ k))⟩
    · have hs : x ∈ stage k := Or.inl hx
      exact ⟨Or.inr ⟨k, hs⟩, Nat.succ_le_of_lt (S_pos (Or.inr ⟨k, hs⟩)), (stage_bounds hs).2⟩
    · have hs : x ∈ stage k := Or.inr hx
      exact ⟨Or.inr ⟨k, hs⟩, Nat.succ_le_of_lt (S_pos (Or.inr ⟨k, hs⟩)), (stage_bounds hs).2⟩

private theorem initialSegment_card (k : ℕ) : 5 * (initialSegment k).card ≥ 3 * M k + 2 := by
  induction k with
  | zero => simp [initialSegment, M_zero]
  | succ k ih =>
    have hp := M_pos k
    have hdis0 : Disjoint (initialSegment k) (Finset.Icc (2 * M k) (3 * M k - 1)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hb := (initialSegment_bounds k hx).2.2
      simp only [Finset.mem_Icc] at hy
      omega
    have hdis1 : Disjoint (initialSegment k ∪ Finset.Icc (2 * M k) (3 * M k - 1))
        (Finset.Icc (6 * M k - 2) (11 * M k - 5)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      simp only [Finset.mem_union, Finset.mem_Icc] at hx hy
      rcases hx with hx | hx
      · have hb := (initialSegment_bounds k hx).2.2; omega
      · omega
    rw [initialSegment, Finset.card_union_of_disjoint hdis1, Finset.card_union_of_disjoint hdis0,
      Nat.card_Icc, Nat.card_Icc, M_step]
    omega

private def partialSegment (k n : ℕ) : Finset ℕ :=
  initialSegment k ∪ Finset.Icc (2 * M k) (min n (3 * M k - 1)) ∪
    Finset.Icc (6 * M k - 2) (min n (11 * M k - 5))

private theorem partialSegment_subset (k n : ℕ) (hn : M k ≤ n) :
    (partialSegment k n : Set ℕ) ⊆ S ∩ Set.Icc 1 n := by
  intro x hx
  simp only [partialSegment, Finset.mem_coe, Finset.mem_union, Finset.mem_Icc] at hx
  rcases hx with (hx | hx) | hx
  · have hb := initialSegment_bounds k hx
    exact ⟨hb.1, hb.2.1, hb.2.2.trans hn⟩
  · have hs : x ∈ S := Or.inr ⟨k, Or.inl ⟨hx.1, hx.2.trans (min_le_right _ _)⟩⟩
    exact ⟨hs, Nat.succ_le_of_lt (S_pos hs), hx.2.trans (min_le_left _ _)⟩
  · have hs : x ∈ S := Or.inr ⟨k, Or.inr ⟨hx.1, hx.2.trans (min_le_right _ _)⟩⟩
    exact ⟨hs, Nat.succ_le_of_lt (S_pos hs), hx.2.trans (min_le_left _ _)⟩

private theorem partialSegment_card (k n : ℕ) :
    (partialSegment k n).card = (initialSegment k).card +
      (min n (3 * M k - 1) + 1 - 2 * M k) +
      (min n (11 * M k - 5) + 1 - (6 * M k - 2)) := by
  have hp := M_pos k
  have hdis0 : Disjoint (initialSegment k)
      (Finset.Icc (2 * M k) (min n (3 * M k - 1))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hb := (initialSegment_bounds k hx).2.2
    simp only [Finset.mem_Icc] at hy
    omega
  have hdis1 : Disjoint
      (initialSegment k ∪ Finset.Icc (2 * M k) (min n (3 * M k - 1)))
      (Finset.Icc (6 * M k - 2) (min n (11 * M k - 5))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_union, Finset.mem_Icc] at hx hy
    rcases hx with hx | hx
    · have hb := (initialSegment_bounds k hx).2.2; omega
    · have hmin := min_le_right n (3 * M k - 1); omega
  rw [partialSegment, Finset.card_union_of_disjoint hdis1,
    Finset.card_union_of_disjoint hdis0, Nat.card_Icc, Nat.card_Icc]

private theorem withinStage_bound (k n : ℕ) (hlo : M k ≤ n) (hhi : n ≤ M (k + 1)) :
    15 * (S ∩ Set.Icc 1 n).ncard ≥ 4 * n := by
  have hsub := Set.ncard_le_ncard (partialSegment_subset k n hlo)
    ((Set.finite_Icc 1 n).subset Set.inter_subset_right)
  rw [Set.ncard_coe_finset, partialSegment_card] at hsub
  have hp := M_pos k
  have hc := initialSegment_card k
  rw [M_step] at hhi
  omega

private theorem densityBound (n : ℕ) (hn : 1 ≤ n) :
    15 * (S ∩ Set.Icc 1 n).ncard ≥ 4 * n := by
  have hex : ∃ k, n ≤ M (k + 1) := by
    use n
    exact (Nat.le_succ n).trans (M_strictMono.id_le (n + 1))
  let k := Nat.find hex
  have hhi : n ≤ M (k + 1) := Nat.find_spec hex
  have hlo : M k ≤ n := by
    cases hk : k with
    | zero => rw [M_zero]; exact hn
    | succ j =>
      have hf := Nat.find_min hex (show j < Nat.find hex by change j < k; omega)
      change ¬ n ≤ M (j + 1) at hf
      omega
  exact withinStage_bound k n hlo hhi

/-- Lower density uses the source's counts in `[1,n]`, divided by `n`, and the
`atTop` liminf of that real sequence. -/
theorem lowerDensityBound :
    (4 / 15 : ℝ) ≤ Filter.liminf
      (fun n : ℕ => ((S ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop := by
  have hu : ∀ n : ℕ, ((S ∩ Set.Icc 1 n).ncard : ℝ) / n ≤ 1 := by
    intro n
    have hb := Set.ncard_le_ncard (Set.inter_subset_right : S ∩ Set.Icc 1 n ⊆ Set.Icc 1 n)
    rw [Set.ncard_Icc_nat] at hb
    have hbReal : ((S ∩ Set.Icc 1 n).ncard : ℝ) ≤ n := by
      exact_mod_cast (show (S ∩ Set.Icc 1 n).ncard ≤ n by omega)
    by_cases hn : n = 0
    · simp [hn]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hbReal
  apply Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le Filter.atTop hu)
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hb := densityBound n hn
  have hbReal : (4 : ℝ) * n ≤ 15 * ((S ∩ Set.Icc 1 n).ncard : ℝ) := by exact_mod_cast hb
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))).mpr
  nlinarith

end D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationDensity
