/- GID: D5/S0/Tower/Tribonacci/Survivor
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Survivor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tribonacci-name grid distance has a sharp normalized bound on its hull. -/

import D5.S0.Tower.Tribonacci.Gaps
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-08-16):
   * Repository search found the frozen Tribonacci grid enumeration, strict
     order, exact three-gap spectrum, and the analogous golden survivor proof.
   * Pinned mathlib provides `Metric.le_infDist` and
     `Metric.infDist_le_dist_of_mem`, but no finite ordered-grid midpoint
     extremality theorem or result combining `Metric.infDist` with `Set.range`.
   * Loogle and LeanSearch returned only the generic infimum-distance API; no
     exact normalized Tribonacci-grid bound was found. Reservoir's package
     search endpoint returned no usable exact match, so no third-party package
     was introduced. -/

namespace D5.S0.Tower.Tribonacci.Survivor

open D5.S0.Tower.Tribonacci.Gaps
open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant

/-- The level-`Q` Tribonacci grid is the image of its increasing enumeration. -/
def tribonacciNameGrid (Q : Nat) : Set Real :=
  Set.range (indexedNameValue Q)

/-- Indexed and intrinsic Tribonacci names determine the same real grid. -/
theorem tribonacciNameGrid_eq_nameValue_range (Q : Nat) :
    tribonacciNameGrid Q = Set.range (tribonacciNameValue Q) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨tribonacciIndexEquiv Q i, rfl⟩
  · rintro ⟨name, rfl⟩
    refine ⟨(tribonacciIndexEquiv Q).symm name, ?_⟩
    simp [indexedNameValue]

/-- Distance to the level-`Q` Tribonacci grid, normalized by `t^Q`. -/
noncomputable def tribonacciSurvivor (Q : Nat) (x : Real) : Real :=
  t ^ (Q : Int) * Metric.infDist x (tribonacciNameGrid Q)

/-- The left endpoint index of an adjacent Tribonacci-grid gap. -/
def tribonacciGapLeft (Q : Nat) (i : Fin (tribonacci (Q + 2) - 1)) :
    Fin (tribonacci (Q + 2)) :=
  ⟨i.1, by have := i.2; omega⟩

/-- The right endpoint index of an adjacent Tribonacci-grid gap. -/
def tribonacciGapRight (Q : Nat) (i : Fin (tribonacci (Q + 2) - 1)) :
    Fin (tribonacci (Q + 2)) :=
  ⟨i.1 + 1, by have := i.2; omega⟩

/-- The natural hull of the finite grid, tiled by adjacent closed cells. -/
def tribonacciNameHull (Q : Nat) : Set Real :=
  ⋃ i : Fin (tribonacci (Q + 2) - 1),
    Set.Icc (indexedNameValue Q (tribonacciGapLeft Q i))
      (indexedNameValue Q (tribonacciGapRight Q i))

/-- Every hull point has normalized grid distance at most one half. -/
theorem tribonacciSurvivor_le_half (Q : Nat) (x : Real) (hQ : 3 ≤ Q)
    (hx : x ∈ tribonacciNameHull Q) :
    tribonacciSurvivor Q x ≤ 1 / 2 := by
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  let a := indexedNameValue Q (tribonacciGapLeft Q i)
  let b := indexedNameValue Q (tribonacciGapRight Q i)
  have hgap_mem : b - a ∈ adjacentGapSpectrum Q := by
    rw [adjacentGapSpectrum, Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rfl
  rw [adjacent_gap_spectrum Q hQ] at hgap_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hgap_mem
  have ha_mem : a ∈ tribonacciNameGrid Q :=
    ⟨tribonacciGapLeft Q i, rfl⟩
  have hb_mem : b ∈ tribonacciNameGrid Q :=
    ⟨tribonacciGapRight Q i, rfl⟩
  have hinf : Metric.infDist x (tribonacciNameGrid Q) ≤ (b - a) / 2 := by
    by_cases hleft : x ≤ (a + b) / 2
    · calc
        Metric.infDist x (tribonacciNameGrid Q) ≤ dist x a :=
          Metric.infDist_le_dist_of_mem ha_mem
        _ = x - a := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxi.1)]
        _ ≤ (b - a) / 2 := by linarith
    · have hright : (a + b) / 2 ≤ x := le_of_not_ge hleft
      calc
        Metric.infDist x (tribonacciNameGrid Q) ≤ dist x b :=
          Metric.infDist_le_dist_of_mem hb_mem
        _ = b - x := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxi.2)]
          ring
        _ ≤ (b - a) / 2 := by linarith
  rcases tribonacci_gap_lengths_order Q with ⟨hsmall, hcombined⟩
  have hgap_le : b - a ≤ t ^ (-(Q : Int)) := by
    rcases hgap_mem with hlarge | hsmallGap | hcombinedGap
    · exact hlarge.le
    · rw [hsmallGap]
      exact hsmall.le.trans hcombined.le
    · exact hcombinedGap.le.trans hcombined.le
  have hscale_nonneg : 0 ≤ t ^ (Q : Int) :=
    (zpow_pos tribonacciConstant_pos _).le
  have hcancel : t ^ (Q : Int) * t ^ (-(Q : Int)) = 1 := by
    rw [← zpow_add₀ tribonacciConstant_ne_zero]
    simp
  unfold tribonacciSurvivor
  calc
    t ^ (Q : Int) * Metric.infDist x (tribonacciNameGrid Q) ≤
        t ^ (Q : Int) * ((b - a) / 2) :=
      mul_le_mul_of_nonneg_left hinf hscale_nonneg
    _ ≤ t ^ (Q : Int) * (t ^ (-(Q : Int)) / 2) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hgap_le (by norm_num)) hscale_nonneg
    _ = 1 / 2 := by rw [← mul_div_assoc, hcancel]

/-- The index one exists at every positive Tribonacci level. -/
def tribonacciOneIndex (Q : Nat) (hQ : 1 ≤ Q) : Fin (tribonacci (Q + 2)) :=
  ⟨1, by
    by_cases hone : Q = 1
    · subst Q
      norm_num [tribonacci]
    by_cases htwo : Q = 2
    · subst Q
      norm_num [tribonacci]
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 3 := ⟨Q - 3, by omega⟩
    rw [tribonacci_count_split n]
    have hfirst : 0 < tribonacci (n + 4) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using tribonacci_level_pos (n + 2)
    have hsecond : 0 < tribonacci (n + 3) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using tribonacci_level_pos (n + 1)
    omega⟩

/-- The second indexed value at a positive level is exactly `t^-Q`. -/
theorem indexedNameValue_one (Q : Nat) (hQ : 1 ≤ Q) :
    indexedNameValue Q (tribonacciOneIndex Q hQ) = t ^ (-(Q : Int)) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hone : Q = 1
      · subst Q
        simp [tribonacciOneIndex]
      by_cases htwo : Q = 2
      · subst Q
        simp [tribonacciOneIndex]
      obtain ⟨n, rfl⟩ : ∃ n, Q = n + 3 := ⟨Q - 3, by omega⟩
      have hprev : 1 ≤ n + 2 := by omega
      have hi : (tribonacciOneIndex (n + 3) (by omega)).1 < tribonacci (n + 4) :=
        (tribonacciOneIndex (n + 2) hprev).2
      rw [indexedNameValue_lower n (tribonacciOneIndex (n + 3) (by omega)) hi]
      have hindex :
          (⟨(tribonacciOneIndex (n + 3) (by omega)).1, hi⟩ :
              Fin (tribonacci (n + 4))) = tribonacciOneIndex (n + 2) hprev := by
        apply Fin.ext
        rfl
      rw [hindex, ih (n + 2) (by omega) hprev, tribonacci_zpow_mul]
      congr 1
      push_cast
      omega

/-- The first adjacent gap at a level having the full three-gap spectrum. -/
def firstTribonacciGap (Q : Nat) (hQ : 3 ≤ Q) :
    Fin (tribonacci (Q + 2) - 1) :=
  ⟨0, by
    have hone := (tribonacciOneIndex Q (by omega)).2
    change 1 < tribonacci (Q + 2) at hone
    omega⟩

/-- The fixed first gap is a largest gap of exact length `t^-Q`. -/
theorem first_tribonacci_gap_value (Q : Nat) (hQ : 3 ≤ Q) :
    indexedNameValue Q (tribonacciGapRight Q (firstTribonacciGap Q hQ)) -
        indexedNameValue Q (tribonacciGapLeft Q (firstTribonacciGap Q hQ)) =
      t ^ (-(Q : Int)) := by
  have hleft : tribonacciGapLeft Q (firstTribonacciGap Q hQ) =
      (⟨0, tribonacci_level_pos Q⟩ : Fin (tribonacci (Q + 2))) := by
    apply Fin.ext
    rfl
  have hright : tribonacciGapRight Q (firstTribonacciGap Q hQ) =
      tribonacciOneIndex Q (by omega) := by
    apply Fin.ext
    rfl
  rw [hleft, hright, indexedNameValue_zero, indexedNameValue_one]
  ring

/-- The midpoint of the fixed first, hence largest, Tribonacci gap. -/
noncomputable def firstTribonacciMidpoint (Q : Nat) (hQ : 3 ≤ Q) : Real :=
  (indexedNameValue Q (tribonacciGapLeft Q (firstTribonacciGap Q hQ)) +
      indexedNameValue Q (tribonacciGapRight Q (firstTribonacciGap Q hQ))) / 2

/-- The explicit first-gap midpoint realizes the one-half upper bound. -/
theorem first_tribonacci_midpoint_realizes (Q : Nat) (hQ : 3 ≤ Q) :
    tribonacciSurvivor Q (firstTribonacciMidpoint Q hQ) = 1 / 2 := by
  let i := firstTribonacciGap Q hQ
  let a := indexedNameValue Q (tribonacciGapLeft Q i)
  let b := indexedNameValue Q (tribonacciGapRight Q i)
  have hgap : b - a = t ^ (-(Q : Int)) := by
    simpa [i, a, b] using first_tribonacci_gap_value Q hQ
  have hgap_pos : 0 < b - a := hgap.symm ▸ zpow_pos tribonacciConstant_pos _
  have hmid_mem : firstTribonacciMidpoint Q hQ ∈ tribonacciNameHull Q := by
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b
    constructor <;> linarith
  apply le_antisymm (tribonacciSurvivor_le_half Q _ hQ hmid_mem)
  have hgrid : (tribonacciNameGrid Q).Nonempty :=
    ⟨a, tribonacciGapLeft Q i, rfl⟩
  have hinf : (b - a) / 2 ≤
      Metric.infDist (firstTribonacciMidpoint Q hQ) (tribonacciNameGrid Q) := by
    rw [Metric.le_infDist hgrid]
    intro y hy
    rcases hy with ⟨j, rfl⟩
    by_cases hjleft : j ≤ tribonacciGapLeft Q i
    · have hy_le : indexedNameValue Q j ≤ a :=
        (indexed_nameValue_strictMono Q).monotone hjleft
      change (b - a) / 2 ≤ dist ((a + b) / 2) (indexedNameValue Q j)
      rw [Real.dist_eq, abs_of_nonneg]
      · linarith
      · linarith
    · have hright_le : tribonacciGapRight Q i ≤ j := by
        change i.1 + 1 ≤ j.1
        change ¬j.1 ≤ i.1 at hjleft
        omega
      have hb_le : b ≤ indexedNameValue Q j :=
        (indexed_nameValue_strictMono Q).monotone hright_le
      change (b - a) / 2 ≤ dist ((a + b) / 2) (indexedNameValue Q j)
      rw [Real.dist_eq, abs_of_nonpos]
      · linarith
      · linarith
  have hscale_pos : 0 < t ^ (Q : Int) := zpow_pos tribonacciConstant_pos _
  have hcancel : t ^ (Q : Int) * t ^ (-(Q : Int)) = 1 := by
    rw [← zpow_add₀ tribonacciConstant_ne_zero]
    simp
  unfold tribonacciSurvivor
  calc
    1 / 2 = t ^ (Q : Int) * ((b - a) / 2) := by
      rw [hgap, ← mul_div_assoc, hcancel]
    _ ≤ t ^ (Q : Int) *
        Metric.infDist (firstTribonacciMidpoint Q hQ) (tribonacciNameGrid Q) :=
      mul_le_mul_of_nonneg_left hinf hscale_pos.le

example :
    tribonacciSurvivor 3 (firstTribonacciMidpoint 3 (by norm_num)) = 1 / 2 := by
  norm_num [first_tribonacci_midpoint_realizes]

example :
    tribonacciSurvivor 4 (firstTribonacciMidpoint 4 (by norm_num)) = 1 / 2 := by
  norm_num [first_tribonacci_midpoint_realizes]

end D5.S0.Tower.Tribonacci.Survivor
