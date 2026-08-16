/- GID: D5/S0/Tower/Tribonacci/ChampionOrbit
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/ChampionOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A closed Tribonacci period-two point has its exact liminf survivor arm. -/

import D5.S0.Tower.Tribonacci.Substitution
import D5.S0.Tower.Tribonacci.Survivor

namespace D5.S0.Tower.Tribonacci.ChampionOrbit

open D5.S0.Tower.Tribonacci.Gaps
open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Substitution
open D5.S0.Tower.Tribonacci.Survivor
open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant

/-- The point selected by the period-two right-left gap itinerary `(ba)^infinity`. -/
noncomputable def tribonacciChampionPoint : Real :=
  (t ^ (-1 : Int) - t ^ (-2 : Int)) / 2

/- Library-search audit trail (2026-08-16):
   * Repository search found the frozen Tribonacci gap substitution, survivor
     carrier, strict grid order, and the golden phase-audit proof shape.
   * Pinned mathlib supplies `Metric.le_infDist`,
     `Metric.infDist_le_dist_of_mem`, `Filter.le_liminf_of_le`,
     `Filter.liminf_le_of_frequently_le`, and `Filter.frequently_atTop`.
   * Loogle confirmed the pinned liminf API. LeanSearch's public endpoint
     rejected the query method, and no third-party Tribonacci orbit theorem
     was found or introduced. -/

/-- An adjacent level gap records the normalized distances from a point to both endpoints. -/
def IsTribonacciOrbitGap (Q : Nat) (x leftArm rightArm : Real) : Prop :=
  ∃ i : Fin (tribonacci (Q + 2) - 1),
    x - indexedNameValue Q (tribonacciGapLeft Q i) =
        leftArm * t ^ (-(Q : Int)) ∧
      indexedNameValue Q (tribonacciGapRight Q i) - x =
        rightArm * t ^ (-(Q : Int))

theorem tribonacci_scale_succ (Q : Nat) :
    t ^ (-(Q : Int)) = t * t ^ (-((Q + 1 : Nat) : Int)) := by
  calc
    t ^ (-(Q : Int)) = t ^ ((1 : Int) + -((Q + 1 : Nat) : Int)) := by
      congr 1
      push_cast
      omega
    _ = t ^ (1 : Int) * t ^ (-((Q + 1 : Nat) : Int)) := by
      rw [zpow_add₀ tribonacciConstant_ne_zero]
    _ = t * t ^ (-((Q + 1 : Nat) : Int)) := by rw [zpow_one]

theorem tribonacci_champion_coordinate_sum :
    (t ^ 2 - t) / 2 + (1 - t ^ (-1 : Int)) / 2 = 1 := by
  rw [zpow_neg, zpow_one]
  field_simp [tribonacciConstant_ne_zero]
  nlinarith [tribonacciConstant_cubic]

theorem tribonacci_champion_low_to_middle :
    t * ((1 - t ^ (-1 : Int)) / 2) = (t - 1) / 2 := by
  rw [zpow_neg, zpow_one]
  field_simp [tribonacciConstant_ne_zero]

theorem tribonacci_champion_middle_to_large :
    t * ((t - 1) / 2) = (t ^ 2 - t) / 2 := by
  ring

theorem tribonacci_champion_large_branch :
    t * ((t ^ 2 - t) / 2) - 1 = (t - 1) / 2 := by
  nlinarith [tribonacciConstant_cubic]

theorem tribonacci_champion_large_complement :
    1 - (t ^ 2 - t) / 2 = (1 - t ^ (-1 : Int)) / 2 := by
  nlinarith [tribonacci_champion_coordinate_sum]

theorem tribonacci_champion_combined_ratio :
    t - 1 = t ^ (-1 : Int) + t ^ (-2 : Int) := by
  rw [zpow_neg, zpow_neg]
  norm_num only [zpow_ofNat, pow_one]
  field_simp [tribonacciConstant_ne_zero]
  nlinarith [tribonacciConstant_cubic]

theorem tribonacci_combined_scale (Q : Nat) :
    (t - 1) * t ^ (-(Q : Int)) =
      t ^ (-((Q + 1 : Nat) : Int)) +
        t ^ (-((Q + 2 : Nat) : Int)) := by
  rw [tribonacci_champion_combined_ratio, add_mul,
    tribonacci_zpow_mul, tribonacci_zpow_mul]
  congr 1 <;> push_cast <;> ring_nf

theorem tribonacci_champion_low_pos :
    0 < (1 - t ^ (-1 : Int)) / 2 := by
  have hinv : t ^ (-1 : Int) < 1 := by
    simpa [zpow_neg] using inv_lt_one_of_one_lt₀ one_lt_tribonacciConstant
  positivity

theorem tribonacci_champion_middle_pos : 0 < (t - 1) / 2 := by
  nlinarith [one_lt_tribonacciConstant]

theorem tribonacci_champion_large_pos : 0 < (t ^ 2 - t) / 2 := by
  have htpos := tribonacciConstant_pos
  nlinarith [one_lt_tribonacciConstant]

theorem tribonacci_champion_low_lt_middle :
    (1 - t ^ (-1 : Int)) / 2 < (t - 1) / 2 := by
  have hscale := tribonacci_champion_low_to_middle
  have hpos := tribonacci_champion_low_pos
  nlinarith [one_lt_tribonacciConstant]

theorem tribonacci_champion_middle_lt_large :
    (t - 1) / 2 < (t ^ 2 - t) / 2 := by
  have hscale := tribonacci_champion_middle_to_large
  have hpos := tribonacci_champion_middle_pos
  nlinarith [one_lt_tribonacciConstant]

theorem inserted_singleton_positions (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1))
    (j : Fin (tribonacci (Q + 3)))
    (hset : insertedNameIndices Q i = {j}) :
    (levelEmbedding Q (gapLeft Q i)).1 + 1 = j.1 ∧
      j.1 + 1 = (levelEmbedding Q (gapRight Q i)).1 := by
  have hj : j ∈ insertedNameIndices Q i := by
    rw [hset]
    simp
  have hjbounds :
      levelEmbedding Q (gapLeft Q i) < j ∧
        j < levelEmbedding Q (gapRight Q i) := by
    simpa only [insertedNameIndices, Finset.mem_Ioo] using hj
  have hcard : (insertedNameIndices Q i).card = 1 := by
    rw [hset]
    simp
  rw [insertedNameIndices, Fin.card_Ioo] at hcard
  constructor <;> omega

theorem tribonacci_large_gap_to_combined_gap (Q : Nat)
    (hgap : IsTribonacciOrbitGap Q tribonacciChampionPoint
      ((t ^ 2 - t) / 2) ((1 - t ^ (-1 : Int)) / 2)) :
    IsTribonacciOrbitGap (Q + 1) tribonacciChampionPoint
      ((t - 1) / 2) ((t - 1) / 2) := by
  rcases hgap with ⟨i, hleft, hright⟩
  change tribonacciChampionPoint - indexedNameValue Q (gapLeft Q i) =
    (t ^ 2 - t) / 2 * t ^ (-(Q : Int)) at hleft
  change indexedNameValue Q (gapRight Q i) - tribonacciChampionPoint =
    (1 - t ^ (-1 : Int)) / 2 * t ^ (-(Q : Int)) at hright
  have hlarge :
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        t ^ (-(Q : Int)) := by
    calc
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          (indexedNameValue Q (gapRight Q i) - tribonacciChampionPoint) +
            (tribonacciChampionPoint - indexedNameValue Q (gapLeft Q i)) := by ring
      _ = ((1 - t ^ (-1 : Int)) / 2 + (t ^ 2 - t) / 2) *
          t ^ (-(Q : Int)) := by rw [hleft, hright]; ring
      _ = t ^ (-(Q : Int)) := by
        rw [add_comm, tribonacci_champion_coordinate_sum]
        ring
  obtain ⟨j, hset, hjleft, hjright⟩ :=
    (tribonacci_gap_substitution Q i).2.1 hlarge
  have hpositions := inserted_singleton_positions Q i j hset
  let next : Fin (tribonacci ((Q + 1) + 2) - 1) :=
    ⟨j.1, by
      change j.1 < tribonacci (Q + 3) - 1
      have hrightpos := hpositions.2
      have hrightbound := (levelEmbedding Q (gapRight Q i)).2
      omega⟩
  have hnextLeft : tribonacciGapLeft (Q + 1) next = j := by
    apply Fin.ext
    rfl
  have hnextRight :
      tribonacciGapRight (Q + 1) next = levelEmbedding Q (gapRight Q i) := by
    apply Fin.ext
    exact hpositions.2
  refine ⟨next, ?_, ?_⟩
  · rw [hnextLeft]
    calc
      tribonacciChampionPoint - indexedNameValue (Q + 1) j =
          (tribonacciChampionPoint - indexedNameValue Q (gapLeft Q i)) -
            (indexedNameValue (Q + 1) j -
              indexedNameValue Q (gapLeft Q i)) := by ring
      _ = (t ^ 2 - t) / 2 * t ^ (-(Q : Int)) -
          t ^ (-((Q + 1 : Nat) : Int)) := by rw [hleft, hjleft]
      _ = (t * ((t ^ 2 - t) / 2) - 1) *
          t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_scale_succ Q]
        ring
      _ = (t - 1) / 2 * t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_champion_large_branch]
  · rw [hnextRight, levelEmbedding_value]
    calc
      indexedNameValue Q (gapRight Q i) - tribonacciChampionPoint =
          (1 - t ^ (-1 : Int)) / 2 * t ^ (-(Q : Int)) := hright
      _ = (t * ((1 - t ^ (-1 : Int)) / 2)) *
          t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_scale_succ Q]
        ring
      _ = (t - 1) / 2 * t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_champion_low_to_middle]

theorem tribonacci_combined_gap_to_large_gap (Q : Nat)
    (hgap : IsTribonacciOrbitGap Q tribonacciChampionPoint
      ((t - 1) / 2) ((t - 1) / 2)) :
    IsTribonacciOrbitGap (Q + 1) tribonacciChampionPoint
      ((t ^ 2 - t) / 2) ((1 - t ^ (-1 : Int)) / 2) := by
  rcases hgap with ⟨i, hleft, hright⟩
  change tribonacciChampionPoint - indexedNameValue Q (gapLeft Q i) =
    (t - 1) / 2 * t ^ (-(Q : Int)) at hleft
  change indexedNameValue Q (gapRight Q i) - tribonacciChampionPoint =
    (t - 1) / 2 * t ^ (-(Q : Int)) at hright
  have hcombined :
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        t ^ (-((Q + 1 : Nat) : Int)) +
          t ^ (-((Q + 2 : Nat) : Int)) := by
    calc
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          (indexedNameValue Q (gapRight Q i) - tribonacciChampionPoint) +
            (tribonacciChampionPoint - indexedNameValue Q (gapLeft Q i)) := by ring
      _ = (t - 1) * t ^ (-(Q : Int)) := by rw [hleft, hright]; ring
      _ = _ := tribonacci_combined_scale Q
  obtain ⟨j, hset, hjleft, hjright⟩ :=
    (tribonacci_gap_substitution Q i).2.2 hcombined
  have hpositions := inserted_singleton_positions Q i j hset
  let next : Fin (tribonacci ((Q + 1) + 2) - 1) :=
    ⟨(levelEmbedding Q (gapLeft Q i)).1, by
      change (levelEmbedding Q (gapLeft Q i)).1 < tribonacci (Q + 3) - 1
      have hjbound := j.2
      have hleftpos := hpositions.1
      omega⟩
  have hnextLeft :
      tribonacciGapLeft (Q + 1) next = levelEmbedding Q (gapLeft Q i) := by
    apply Fin.ext
    rfl
  have hnextRight : tribonacciGapRight (Q + 1) next = j := by
    apply Fin.ext
    exact hpositions.1
  refine ⟨next, ?_, ?_⟩
  · rw [hnextLeft, levelEmbedding_value]
    calc
      tribonacciChampionPoint - indexedNameValue Q (gapLeft Q i) =
          (t - 1) / 2 * t ^ (-(Q : Int)) := hleft
      _ = (t * ((t - 1) / 2)) *
          t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_scale_succ Q]
        ring
      _ = (t ^ 2 - t) / 2 * t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_champion_middle_to_large]
  · rw [hnextRight]
    calc
      indexedNameValue (Q + 1) j - tribonacciChampionPoint =
          (indexedNameValue (Q + 1) j - indexedNameValue Q (gapLeft Q i)) -
            (tribonacciChampionPoint - indexedNameValue Q (gapLeft Q i)) := by ring
      _ = t ^ (-((Q + 1 : Nat) : Int)) -
          (t - 1) / 2 * t ^ (-(Q : Int)) := by rw [hjleft, hleft]
      _ = (1 - t * ((t - 1) / 2)) *
          t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_scale_succ Q]
        ring
      _ = (1 - t ^ (-1 : Int)) / 2 *
          t ^ (-((Q + 1 : Nat) : Int)) := by
        rw [tribonacci_champion_middle_to_large]
        rw [tribonacci_champion_large_complement]

theorem tribonacci_champion_base_gap :
    IsTribonacciOrbitGap 3 tribonacciChampionPoint
      ((t ^ 2 - t) / 2) ((1 - t ^ (-1 : Int)) / 2) := by
  let i := firstTribonacciGap 3 (by omega)
  have hleftIndex : tribonacciGapLeft 3 i =
      (⟨0, tribonacci_level_pos 3⟩ : Fin (tribonacci 5)) := by
    apply Fin.ext
    rfl
  have hleftValue : indexedNameValue 3 (tribonacciGapLeft 3 i) = 0 := by
    rw [hleftIndex, indexedNameValue_zero]
  have hgap := first_tribonacci_gap_value 3 (by omega)
  have hgap' :
      indexedNameValue 3 (tribonacciGapRight 3 i) -
          indexedNameValue 3 (tribonacciGapLeft 3 i) = t ^ (-3 : Int) := by
    simpa [i] using hgap
  have hpoint : tribonacciChampionPoint =
      (t ^ 2 - t) / 2 * t ^ (-3 : Int) := by
    rw [tribonacciChampionPoint, zpow_neg, zpow_neg, zpow_neg]
    norm_num only [zpow_ofNat, pow_one]
    field_simp [tribonacciConstant_ne_zero]
  refine ⟨i, ?_, ?_⟩
  · rw [hleftValue, sub_zero]
    simpa using hpoint
  · calc
      indexedNameValue 3 (tribonacciGapRight 3 i) - tribonacciChampionPoint =
          (indexedNameValue 3 (tribonacciGapRight 3 i) -
            indexedNameValue 3 (tribonacciGapLeft 3 i)) -
              (tribonacciChampionPoint -
                indexedNameValue 3 (tribonacciGapLeft 3 i)) := by ring
      _ = t ^ (-3 : Int) - (t ^ 2 - t) / 2 * t ^ (-3 : Int) := by
        rw [hgap', hleftValue, sub_zero, hpoint]
      _ = (1 - t ^ (-1 : Int)) / 2 * t ^ (-3 : Int) := by
        rw [← tribonacci_champion_large_complement]
        ring

/-- The containing gap follows the right branch `b`, then the left branch `a`, forever. -/
theorem tribonacci_champion_gap_orbit (k : Nat) :
    IsTribonacciOrbitGap (2 * k + 3) tribonacciChampionPoint
        ((t ^ 2 - t) / 2) ((1 - t ^ (-1 : Int)) / 2) ∧
      IsTribonacciOrbitGap (2 * k + 4) tribonacciChampionPoint
        ((t - 1) / 2) ((t - 1) / 2) := by
  induction k with
  | zero =>
      have hlarge := tribonacci_champion_base_gap
      refine ⟨?_, ?_⟩
      · simpa using hlarge
      · simpa using tribonacci_large_gap_to_combined_gap 3 hlarge
  | succ k ih =>
      have hlarge := tribonacci_combined_gap_to_large_gap (2 * k + 4) ih.2
      have hcombined := tribonacci_large_gap_to_combined_gap (2 * k + 5) hlarge
      constructor
      · convert hlarge using 1
        all_goals omega
      · convert hcombined using 1
        all_goals omega

theorem tribonacciSurvivor_nonneg (Q : Nat) (x : Real) :
    0 ≤ tribonacciSurvivor Q x := by
  exact mul_nonneg (zpow_pos tribonacciConstant_pos _).le Metric.infDist_nonneg

theorem tribonacciSurvivor_eq_of_orbit_gap (Q : Nat) (x leftArm rightArm arm : Real)
    (hgap : IsTribonacciOrbitGap Q x leftArm rightArm)
    (hleftArm : 0 ≤ leftArm) (hrightArm : 0 ≤ rightArm)
    (harmLeft : arm ≤ leftArm) (harmRight : arm ≤ rightArm)
    (hnearest : arm = leftArm ∨ arm = rightArm) :
    tribonacciSurvivor Q x = arm := by
  rcases hgap with ⟨i, hleft, hright⟩
  let a := indexedNameValue Q (tribonacciGapLeft Q i)
  let b := indexedNameValue Q (tribonacciGapRight Q i)
  have hscale_nonneg : 0 ≤ t ^ (-(Q : Int)) :=
    (zpow_pos tribonacciConstant_pos _).le
  have hleft_nonneg : 0 ≤ x - a := by
    rw [show x - a = leftArm * t ^ (-(Q : Int)) by exact hleft]
    positivity
  have hright_nonneg : 0 ≤ b - x := by
    rw [show b - x = rightArm * t ^ (-(Q : Int)) by exact hright]
    positivity
  have hgrid : (tribonacciNameGrid Q).Nonempty :=
    ⟨a, tribonacciGapLeft Q i, rfl⟩
  have hlower : arm * t ^ (-(Q : Int)) ≤
      Metric.infDist x (tribonacciNameGrid Q) := by
    rw [Metric.le_infDist hgrid]
    intro y hy
    rcases hy with ⟨j, rfl⟩
    by_cases hjleft : j ≤ tribonacciGapLeft Q i
    · have hy_le : indexedNameValue Q j ≤ a :=
        (indexed_nameValue_strictMono Q).monotone hjleft
      have hy_x : indexedNameValue Q j ≤ x := hy_le.trans (sub_nonneg.mp hleft_nonneg)
      have hscaled := mul_le_mul_of_nonneg_right harmLeft hscale_nonneg
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy_x)]
      linarith
    · have hright_le : tribonacciGapRight Q i ≤ j := by
        change i.1 + 1 ≤ j.1
        change ¬j.1 ≤ i.1 at hjleft
        omega
      have hb_le : b ≤ indexedNameValue Q j :=
        (indexed_nameValue_strictMono Q).monotone hright_le
      have hx_y : x ≤ indexedNameValue Q j := (sub_nonneg.mp hright_nonneg).trans hb_le
      have hscaled := mul_le_mul_of_nonneg_right harmRight hscale_nonneg
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx_y)]
      linarith
  have hupper : Metric.infDist x (tribonacciNameGrid Q) ≤
      arm * t ^ (-(Q : Int)) := by
    rcases hnearest with hnear | hnear
    · calc
        Metric.infDist x (tribonacciNameGrid Q) ≤ dist x a :=
          Metric.infDist_le_dist_of_mem ⟨tribonacciGapLeft Q i, rfl⟩
        _ = x - a := by rw [Real.dist_eq, abs_of_nonneg hleft_nonneg]
        _ = arm * t ^ (-(Q : Int)) := by rw [hleft, hnear]
    · calc
        Metric.infDist x (tribonacciNameGrid Q) ≤ dist x b :=
          Metric.infDist_le_dist_of_mem ⟨tribonacciGapRight Q i, rfl⟩
        _ = b - x := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (sub_nonneg.mp hright_nonneg))]
          ring
        _ = arm * t ^ (-(Q : Int)) := by rw [hright, hnear]
  have hinf : Metric.infDist x (tribonacciNameGrid Q) =
      arm * t ^ (-(Q : Int)) := le_antisymm hupper hlower
  have hcancel : t ^ (Q : Int) * t ^ (-(Q : Int)) = 1 := by
    rw [← zpow_add₀ tribonacciConstant_ne_zero]
    simp
  unfold tribonacciSurvivor
  rw [hinf]
  calc
    t ^ (Q : Int) * (arm * t ^ (-(Q : Int))) =
        arm * (t ^ (Q : Int) * t ^ (-(Q : Int))) := by ring
    _ = arm := by rw [hcancel]; ring

/-- On every large-gap phase, the normalized arm is the source value. -/
theorem tribonacci_champion_survivor_odd (k : Nat) :
    tribonacciSurvivor (2 * k + 3) tribonacciChampionPoint =
      (1 - t ^ (-1 : Int)) / 2 := by
  apply tribonacciSurvivor_eq_of_orbit_gap
      (hgap := (tribonacci_champion_gap_orbit k).1)
  · exact tribonacci_champion_large_pos.le
  · exact tribonacci_champion_low_pos.le
  · exact tribonacci_champion_low_lt_middle.le.trans
      tribonacci_champion_middle_lt_large.le
  · exact le_rfl
  · exact Or.inr rfl

/-- On every intervening combined-gap phase, the point is the exact midpoint. -/
theorem tribonacci_champion_survivor_even (k : Nat) :
    tribonacciSurvivor (2 * k + 4) tribonacciChampionPoint = (t - 1) / 2 := by
  apply tribonacciSurvivor_eq_of_orbit_gap
      (hgap := (tribonacci_champion_gap_orbit k).2)
  · exact tribonacci_champion_middle_pos.le
  · exact tribonacci_champion_middle_pos.le
  · exact le_rfl
  · exact le_rfl
  · exact Or.inl rfl

/-- The period-two point has liminf arm `(1 - t^-1) / 2`, not the fixed-level half bound. -/
theorem tribonacci_champion_liminf :
    Filter.liminf (fun Q => tribonacciSurvivor Q tribonacciChampionPoint)
        Filter.atTop =
      (1 - t ^ (-1 : Int)) / 2 := by
  let low := (1 - t ^ (-1 : Int)) / 2
  let middle := (t - 1) / 2
  have hlow_middle : low ≤ middle := by
    exact tribonacci_champion_low_lt_middle.le
  have heventually_lower :
      ∀ᶠ Q in Filter.atTop,
        low ≤ tribonacciSurvivor Q tribonacciChampionPoint := by
    rw [Filter.eventually_atTop]
    refine ⟨3, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 3 := ⟨Q - 3, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [show 2 * k + 3 = 2 * k + 3 by rfl,
        tribonacci_champion_survivor_odd]
    · subst n
      rw [show (2 * k + 1) + 3 = 2 * k + 4 by omega,
        tribonacci_champion_survivor_even]
      exact hlow_middle
  have heventually_upper :
      ∀ᶠ Q in Filter.atTop,
        tribonacciSurvivor Q tribonacciChampionPoint ≤ middle := by
    rw [Filter.eventually_atTop]
    refine ⟨3, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 3 := ⟨Q - 3, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [show 2 * k + 3 = 2 * k + 3 by rfl,
        tribonacci_champion_survivor_odd]
      exact hlow_middle
    · subst n
      rw [show (2 * k + 1) + 3 = 2 * k + 4 by omega,
        tribonacci_champion_survivor_even]
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨2 * N + 3, by omega, ?_⟩
      rw [tribonacci_champion_survivor_odd]
    · exact ⟨low, heventually_lower⟩
  · exact Filter.le_liminf_of_le
      (Filter.IsBoundedUnder.isCoboundedUnder_ge ⟨middle, heventually_upper⟩)
      heventually_lower

example : tribonacciSurvivor 3 tribonacciChampionPoint =
    (1 - t ^ (-1 : Int)) / 2 := by
  have h := tribonacci_champion_survivor_odd 0
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example : tribonacciSurvivor 4 tribonacciChampionPoint = (t - 1) / 2 := by
  have h := tribonacci_champion_survivor_even 0
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example : tribonacciSurvivor 5 tribonacciChampionPoint =
    (1 - t ^ (-1 : Int)) / 2 := by
  have h := tribonacci_champion_survivor_odd 1
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example : tribonacciSurvivor 6 tribonacciChampionPoint = (t - 1) / 2 := by
  have h := tribonacci_champion_survivor_even 1
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example : tribonacciSurvivor 7 tribonacciChampionPoint =
    (1 - t ^ (-1 : Int)) / 2 := by
  have h := tribonacci_champion_survivor_odd 2
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example : tribonacciSurvivor 8 tribonacciChampionPoint = (t - 1) / 2 := by
  have h := tribonacci_champion_survivor_even 2
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

end D5.S0.Tower.Tribonacci.ChampionOrbit
