/- GID: D5/S0/Tower/MetricGeometry/GoldenSurvivor
   generality: I
   mirror-B: D5/B/S0/Tower/MetricGeometry/GoldenSurvivor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-name grid distance has an exact global normalized supremum on its hull. -/

import D5.S0.Tower.GoldenChampionPoint
import D5.S0.Tower.GoldenGaps
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-08-16):
   * Repository searches found the frozen `indexedNameValue`,
     `indexed_nameValue_strictMono`, `consecutive_nameValue_gap`, and
     `golden_champion_point_identity` declarations, but no distance carrier or
     global extremality theorem for the golden-name grid.
   * Loogle found `Metric.le_infDist` and the generic infimum-distance API, but
     no declaration mentioning both `Metric.infDist` and `Set.range`.
   * LeanSearch returned generic interval-distance, finite-separation, and
     diameter bounds, but no maximum-half-gap theorem for a finite ordered grid.
   * The Reservoir package catalogue exposed no package-specific exact match;
     the pinned mathlib API suffices for the proof below. -/

namespace D5.S0.Tower.MetricGeometry.GoldenSurvivor

open D5.S0.Conventions
open D5.S0.Tower.GoldenChampionPoint
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenNames

local notation "φ" => Real.goldenRatio

/-- The level-`Q` golden grid is the image of the frozen increasing enumeration. -/
def goldenNameGrid (Q : Nat) : Set Real :=
  Set.range (indexedNameValue Q)

/-- The indexed and intrinsic golden-name descriptions give the same grid. -/
theorem goldenNameGrid_eq_nameValue_range (Q : Nat) :
    goldenNameGrid Q = Set.range (nameValue Q) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨goldenNameEquiv Q i, rfl⟩
  · rintro ⟨name, rfl⟩
    refine ⟨(goldenNameEquiv Q).symm name, ?_⟩
    simp [indexedNameValue]

/-- The normalized distance from `x` to the level-`Q` golden-name grid. -/
noncomputable def goldenSurvivor (Q : Nat) (x : Real) : Real :=
  φ ^ (Q : Int) * Metric.infDist x (goldenNameGrid Q)

/-- The left endpoint index of an adjacent golden-grid gap. -/
def goldenGapLeft (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1)) :
    Fin (Nat.fib (Q + 2)) :=
  ⟨i.1, by have := i.2; omega⟩

/-- The right endpoint index of an adjacent golden-grid gap. -/
def goldenGapRight (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1)) :
    Fin (Nat.fib (Q + 2)) :=
  ⟨i.1 + 1, by have := i.2; omega⟩

/-- The natural hull of the finite grid, tiled by its adjacent closed cells. -/
def goldenNameHull (Q : Nat) : Set Real :=
  ⋃ i : Fin (Nat.fib (Q + 2) - 1),
    Set.Icc (indexedNameValue Q (goldenGapLeft Q i))
      (indexedNameValue Q (goldenGapRight Q i))

/-- The first adjacent gap, available at every positive level. -/
def firstGoldenGap (Q : Nat) (hQ : 1 ≤ Q) : Fin (Nat.fib (Q + 2) - 1) :=
  ⟨0, by
    have hmono := Nat.fib_mono (by omega : 3 ≤ Q + 2)
    norm_num [Nat.fib] at hmono ⊢
    omega⟩

/-- The midpoint of the first adjacent gap. -/
noncomputable def firstGoldenMidpoint (Q : Nat) (hQ : 1 ≤ Q) : Real :=
  (indexedNameValue Q (goldenGapLeft Q (firstGoldenGap Q hQ)) +
      indexedNameValue Q (goldenGapRight Q (firstGoldenGap Q hQ))) / 2

/-- The first indexed gap is the larger golden gap `phi^(-Q)`. -/
theorem first_golden_gap_value (Q : Nat) (hQ : 1 ≤ Q) :
    indexedNameValue Q (goldenGapRight Q (firstGoldenGap Q hQ)) -
        indexedNameValue Q (goldenGapLeft Q (firstGoldenGap Q hQ)) =
      φ ^ (-(Q : Int)) := by
  have hzero :
      indexedNameValue Q (goldenGapLeft Q (firstGoldenGap Q hQ)) = 0 := by
    change ((wdigits 0).map fun k : Nat ↦
      φ ^ ((k : Int) - ((Q + 2 : Nat) : Int))).sum = 0
    rw [show wdigits 0 = [] by
      symm
      apply wdigits_unique
      · exact List.IsZeckendorfRep_nil
      · rfl]
    rfl
  have hone :
      indexedNameValue Q (goldenGapRight Q (firstGoldenGap Q hQ)) =
        φ ^ (-(Q : Int)) := by
    change ((wdigits 1).map fun k : Nat ↦
      φ ^ ((k : Int) - ((Q + 2 : Nat) : Int))).sum = _
    rw [show wdigits 1 = [2] by
      symm
      apply wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 1
    push_cast
    omega
  rw [hone, hzero, sub_zero]

/-- Every point in the golden-grid hull has normalized distance at most one half. -/
theorem goldenSurvivor_le_half (Q : Nat) (x : Real) (hx : x ∈ goldenNameHull Q) :
    goldenSurvivor Q x ≤ 1 / 2 := by
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  let a := indexedNameValue Q (goldenGapLeft Q i)
  let b := indexedNameValue Q (goldenGapRight Q i)
  have hgap : b - a = φ ^ (-(Q : Int)) ∨
      b - a = φ ^ (-((Q + 1 : Nat) : Int)) := by
    simpa [a, b, goldenGapLeft, goldenGapRight] using
      consecutive_nameValue_gap Q i
  have ha_mem : a ∈ goldenNameGrid Q :=
    ⟨goldenGapLeft Q i, rfl⟩
  have hb_mem : b ∈ goldenNameGrid Q :=
    ⟨goldenGapRight Q i, rfl⟩
  have hinf : Metric.infDist x (goldenNameGrid Q) ≤ (b - a) / 2 := by
    by_cases hleft : x ≤ (a + b) / 2
    · calc
        Metric.infDist x (goldenNameGrid Q) ≤ dist x a :=
          Metric.infDist_le_dist_of_mem ha_mem
        _ = x - a := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxi.1)]
        _ ≤ (b - a) / 2 := by linarith
    · have hright : (a + b) / 2 ≤ x := le_of_not_ge hleft
      calc
        Metric.infDist x (goldenNameGrid Q) ≤ dist x b :=
          Metric.infDist_le_dist_of_mem hb_mem
        _ = b - x := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxi.2)]
          ring
        _ ≤ (b - a) / 2 := by linarith
  have hsmall_le :
      φ ^ (-((Q + 1 : Nat) : Int)) ≤ φ ^ (-(Q : Int)) := by
    apply zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le
    push_cast
    omega
  have hgap_le : b - a ≤ φ ^ (-(Q : Int)) := by
    rcases hgap with hgap | hgap
    · exact hgap.le
    · exact hgap.le.trans hsmall_le
  have hscale_nonneg : 0 ≤ φ ^ (Q : Int) :=
    (zpow_pos Real.goldenRatio_pos _).le
  have hcancel : φ ^ (Q : Int) * φ ^ (-(Q : Int)) = 1 := by
    rw [← zpow_add₀ Real.goldenRatio_ne_zero]
    simp
  unfold goldenSurvivor
  calc
    φ ^ (Q : Int) * Metric.infDist x (goldenNameGrid Q) ≤
        φ ^ (Q : Int) * ((b - a) / 2) :=
      mul_le_mul_of_nonneg_left hinf hscale_nonneg
    _ ≤ φ ^ (Q : Int) * (φ ^ (-(Q : Int)) / 2) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hgap_le (by norm_num))
        hscale_nonneg
    _ = 1 / 2 := by rw [← mul_div_assoc, hcancel]

/-- The first large-gap midpoint realizes the global one-half upper bound. -/
theorem first_golden_midpoint_realizes (Q : Nat) (hQ : 1 ≤ Q) :
    goldenSurvivor Q (firstGoldenMidpoint Q hQ) = 1 / 2 := by
  let i := firstGoldenGap Q hQ
  let a := indexedNameValue Q (goldenGapLeft Q i)
  let b := indexedNameValue Q (goldenGapRight Q i)
  have hgap : b - a = φ ^ (-(Q : Int)) := by
    simpa [i, a, b] using first_golden_gap_value Q hQ
  have hgap_pos : 0 < b - a := hgap.symm ▸ zpow_pos Real.goldenRatio_pos _
  have hmid_mem : firstGoldenMidpoint Q hQ ∈ goldenNameHull Q := by
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b
    constructor <;> linarith
  apply le_antisymm (goldenSurvivor_le_half Q _ hmid_mem)
  have hgrid : (goldenNameGrid Q).Nonempty := by
    exact ⟨a, goldenGapLeft Q i, rfl⟩
  have hinf : (b - a) / 2 ≤
      Metric.infDist (firstGoldenMidpoint Q hQ) (goldenNameGrid Q) := by
    rw [Metric.le_infDist hgrid]
    intro y hy
    rcases hy with ⟨j, rfl⟩
    by_cases hj : j = goldenGapLeft Q i
    · subst j
      change (b - a) / 2 ≤ dist ((a + b) / 2) a
      rw [Real.dist_eq, abs_of_nonneg]
      · ring_nf
        exact le_rfl
      · linarith
    · have hright_le : goldenGapRight Q i ≤ j := by
        change i.1 + 1 ≤ j.1
        have hleft_zero : i.1 = 0 := by rfl
        have hj_ne_zero : j.1 ≠ 0 := by
          intro hjzero
          apply hj
          apply Fin.ext
          change j.1 = i.1
          omega
        omega
      have hb_le : b ≤ indexedNameValue Q j :=
        (indexed_nameValue_strictMono Q).monotone hright_le
      change (b - a) / 2 ≤ dist ((a + b) / 2) (indexedNameValue Q j)
      rw [Real.dist_eq, abs_of_nonpos]
      · linarith
      · linarith
  have hscale_pos : 0 < φ ^ (Q : Int) := zpow_pos Real.goldenRatio_pos _
  have hcancel : φ ^ (Q : Int) * φ ^ (-(Q : Int)) = 1 := by
    rw [← zpow_add₀ Real.goldenRatio_ne_zero]
    simp
  unfold goldenSurvivor
  calc
    1 / 2 = φ ^ (Q : Int) * ((b - a) / 2) := by
      rw [hgap, ← mul_div_assoc, hcancel]
    _ ≤ φ ^ (Q : Int) *
        Metric.infDist (firstGoldenMidpoint Q hQ) (goldenNameGrid Q) :=
      mul_le_mul_of_nonneg_left hinf hscale_pos.le

/-- The global supremum of normalized golden-grid distance on the hull is one half. -/
theorem golden_survivor_global_sup (Q : Nat) (hQ : 1 ≤ Q) :
    sSup {r : Real | ∃ x ∈ goldenNameHull Q, r ≤ goldenSurvivor Q x} = 1 / 2 := by
  let S : Set Real :=
    {r | ∃ x ∈ goldenNameHull Q, r ≤ goldenSurvivor Q x}
  change sSup S = 1 / 2
  have hgap := first_golden_gap_value Q hQ
  have hmid_mem : firstGoldenMidpoint Q hQ ∈ goldenNameHull Q := by
    apply Set.mem_iUnion.mpr
    refine ⟨firstGoldenGap Q hQ, ?_⟩
    dsimp [firstGoldenMidpoint]
    have hpos : 0 < φ ^ (-(Q : Int)) := zpow_pos Real.goldenRatio_pos _
    constructor <;> nlinarith
  have hhalf_mem : (1 / 2 : Real) ∈ S := by
    exact ⟨firstGoldenMidpoint Q hQ, hmid_mem,
      (first_golden_midpoint_realizes Q hQ).ge⟩
  have hupper : ∀ r ∈ S, r ≤ (1 / 2 : Real) := by
    intro r hr
    rcases hr with ⟨x, hx, hr⟩
    exact hr.trans (goldenSurvivor_le_half Q x hx)
  exact le_antisymm
    (csSup_le ⟨1 / 2, hhalf_mem⟩ hupper)
    (le_csSup ⟨1 / 2, hupper⟩ hhalf_mem)

/-- The frozen closed-form golden champion point realizes the level-six global maximum. -/
theorem golden_champion_point_realizes :
    goldenSurvivor 6 ((13 / 2 : Real) - 4 * φ) = 1 / 2 := by
  have hQ : 1 ≤ (6 : Nat) := by omega
  have hzero :
      indexedNameValue 6 (goldenGapLeft 6 (firstGoldenGap 6 hQ)) = 0 := by
    change ((wdigits 0).map fun k : Nat ↦
      φ ^ ((k : Int) - (((6 : Nat) + 2 : Nat) : Int))).sum = 0
    rw [show wdigits 0 = [] by
      symm
      apply wdigits_unique
      · exact List.IsZeckendorfRep_nil
      · rfl]
    rfl
  have hmidpoint : firstGoldenMidpoint 6 hQ = φ ^ (-6 : Int) / 2 := by
    have hgap := first_golden_gap_value 6 hQ
    unfold firstGoldenMidpoint
    rw [hzero] at hgap ⊢
    norm_num at hgap
    rw [hgap]
    norm_num [zpow_neg]
  have hclosed : (13 / 2 : Real) - 4 * φ = φ ^ (-6 : Int) / 2 :=
    golden_champion_point_identity.1.trans golden_champion_point_identity.2
  rw [hclosed, ← hmidpoint]
  exact first_golden_midpoint_realizes 6 hQ

end D5.S0.Tower.MetricGeometry.GoldenSurvivor
