/- GID: D5/S1/Phase/LonelyRunnerFourteenOfTwenty
   generality: I
   mirror-B: D5/B/S1/Phase/LonelyRunnerFourteenOfTwenty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify a rational lonely time for every fourteen speeds chosen from one through twenty. -/

import Mathlib

namespace D5.S1.Phase.LonelyRunnerFourteenOfTwenty

/-- Distance to the nearest integer, expressed through the fractional part. -/
def torusDist (x : ℚ) : ℚ :=
  min (Int.fract x) (1 - Int.fract x)

private theorem fract_nat_mul_div (s a d : ℕ) :
    Int.fract ((s : ℚ) * ((a : ℚ) / (d : ℚ))) =
      (((s * a) % d : ℕ) : ℚ) / (d : ℚ) := by
  have h : (s : ℚ) * ((a : ℚ) / (d : ℚ)) = ((s * a : ℕ) : ℚ) / (d : ℚ) := by
    push_cast
    ring
  rw [h, Int.fract_div_natCast_eq_div_natCast_mod]

private theorem torusDist_nat_ratio_ge_iff_residue_window (s a d : ℕ) :
    (1 : ℚ) / 15 ≤ torusDist ((s : ℚ) * ((a : ℚ) / (d : ℚ))) ↔
      (1 : ℚ) / 15 ≤ (((s * a) % d : ℕ) : ℚ) / (d : ℚ) ∧
        (((s * a) % d : ℕ) : ℚ) / (d : ℚ) ≤ (14 : ℚ) / 15 := by
  rw [torusDist, fract_nat_mul_div, le_min_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨hlo, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨hlo, by linarith⟩

private theorem ratio_window_iff_nat_window (r d : ℕ) (hd : 0 < d) :
    ((1 : ℚ) / 15 ≤ (r : ℚ) / (d : ℚ) ∧
      (r : ℚ) / (d : ℚ) ≤ (14 : ℚ) / 15) ↔
      d ≤ 15 * r ∧ 15 * r ≤ 14 * d := by
  have hdq : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast hd
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : ((1 : ℚ) / 15) * (d : ℚ) ≤ (r : ℚ) :=
      (le_div_iff₀ hdq).mp hlo
    have hhi' : (r : ℚ) ≤ ((14 : ℚ) / 15) * (d : ℚ) :=
      (div_le_iff₀ hdq).mp hhi
    constructor
    · exact_mod_cast (show (d : ℚ) ≤ 15 * (r : ℚ) by linarith)
    · exact_mod_cast (show 15 * (r : ℚ) ≤ 14 * (d : ℚ) by linarith)
  · rintro ⟨hlo, hhi⟩
    have hlo' : (d : ℚ) ≤ 15 * (r : ℚ) := by
      exact_mod_cast hlo
    have hhi' : 15 * (r : ℚ) ≤ 14 * (d : ℚ) := by
      exact_mod_cast hhi
    constructor
    · apply (le_div_iff₀ hdq).mpr
      linarith
    · apply (div_le_iff₀ hdq).mpr
      linarith

/-- At a positive-denominator rational time, the lonely-runner bound is
equivalent to an exact natural-number residue window. -/
theorem torusDist_nat_ratio_ge_iff_nat_residue_window (s a d : ℕ) (hd : 0 < d) :
    (1 : ℚ) / 15 ≤ torusDist ((s : ℚ) * ((a : ℚ) / (d : ℚ))) ↔
      d ≤ 15 * ((s * a) % d) ∧ 15 * ((s * a) % d) ≤ 14 * d :=
  (torusDist_nat_ratio_ge_iff_residue_window s a d).trans
    (ratio_window_iff_nat_window ((s * a) % d) d hd)

/-- The available integer speeds from one through twenty. -/
def speedUniverse : Finset ℕ :=
  Finset.Icc 1 20

/-- The speeds safe at time `t` for the threshold `1 / 15`. -/
def safeMask (t : ℚ) : Finset ℕ :=
  speedUniverse.filter fun s => (1 : ℚ) / 15 ≤ torusDist ((s : ℚ) * t)

private theorem mem_safeMask_iff {t : ℚ} {s : ℕ} :
    s ∈ safeMask t ↔
      s ∈ speedUniverse ∧ (1 : ℚ) / 15 ≤ torusDist ((s : ℚ) * t) := by
  simp [safeMask]

private theorem safeMask_sound {t : ℚ} {s : ℕ} (hs : s ∈ safeMask t) :
    (1 : ℚ) / 15 ≤ torusDist ((s : ℚ) * t) :=
  (mem_safeMask_iff.mp hs).2

private def residueMask (a d : ℕ) : Finset ℕ :=
  speedUniverse.filter fun s =>
    d ≤ 15 * ((s * a) % d) ∧ 15 * ((s * a) % d) ≤ 14 * d

private theorem safeMask_nat_ratio_eq_residueMask (a d : ℕ) (hd : 0 < d) :
    safeMask ((a : ℚ) / (d : ℚ)) = residueMask a d := by
  ext s
  simp only [safeMask, residueMask, Finset.mem_filter]
  exact and_congr_right fun _ =>
    torusDist_nat_ratio_ge_iff_nat_residue_window s a d hd

/-- Fifteen rational times paired with their exact safe masks. -/
def certificate : List (ℚ × Finset ℕ) := [
  ((1 : ℚ) / 11, speedUniverse.erase 11),
  ((1 : ℚ) / 12, speedUniverse.erase 12),
  ((1 : ℚ) / 13, speedUniverse.erase 13),
  ((1 : ℚ) / 14, speedUniverse.erase 14),
  ((1 : ℚ) / 15, speedUniverse.erase 15),
  ((1 : ℚ) / 22, speedUniverse.erase 1),
  ((11 : ℚ) / 23, speedUniverse.erase 2),
  ((6 : ℚ) / 25, speedUniverse.erase 4),
  ((8 : ℚ) / 25, speedUniverse.erase 3),
  ((5 : ℚ) / 26, speedUniverse.erase 5),
  ((4 : ℚ) / 29, speedUniverse.erase 7),
  ((5 : ℚ) / 29, speedUniverse.erase 6),
  ((11 : ℚ) / 29, speedUniverse.erase 8),
  ((1 : ℚ) / 9, speedUniverse \ {9, 18}),
  ((1 : ℚ) / 10, speedUniverse \ {10, 20})
]

private theorem mask_1_11 : safeMask ((1 : ℚ) / 11) = speedUniverse.erase 11 := by
  calc
    _ = residueMask 1 11 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 11 (by norm_num)
    _ = _ := by decide

private theorem mask_1_12 : safeMask ((1 : ℚ) / 12) = speedUniverse.erase 12 := by
  calc
    _ = residueMask 1 12 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 12 (by norm_num)
    _ = _ := by decide

private theorem mask_1_13 : safeMask ((1 : ℚ) / 13) = speedUniverse.erase 13 := by
  calc
    _ = residueMask 1 13 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 13 (by norm_num)
    _ = _ := by decide

private theorem mask_1_14 : safeMask ((1 : ℚ) / 14) = speedUniverse.erase 14 := by
  calc
    _ = residueMask 1 14 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 14 (by norm_num)
    _ = _ := by decide

private theorem mask_1_15 : safeMask ((1 : ℚ) / 15) = speedUniverse.erase 15 := by
  calc
    _ = residueMask 1 15 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 15 (by norm_num)
    _ = _ := by decide

private theorem mask_1_22 : safeMask ((1 : ℚ) / 22) = speedUniverse.erase 1 := by
  calc
    _ = residueMask 1 22 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 22 (by norm_num)
    _ = _ := by decide

private theorem mask_11_23 : safeMask ((11 : ℚ) / 23) = speedUniverse.erase 2 := by
  calc
    _ = residueMask 11 23 := by
      simpa using safeMask_nat_ratio_eq_residueMask 11 23 (by norm_num)
    _ = _ := by decide

private theorem mask_6_25 : safeMask ((6 : ℚ) / 25) = speedUniverse.erase 4 := by
  calc
    _ = residueMask 6 25 := by
      simpa using safeMask_nat_ratio_eq_residueMask 6 25 (by norm_num)
    _ = _ := by decide

private theorem mask_8_25 : safeMask ((8 : ℚ) / 25) = speedUniverse.erase 3 := by
  calc
    _ = residueMask 8 25 := by
      simpa using safeMask_nat_ratio_eq_residueMask 8 25 (by norm_num)
    _ = _ := by decide

private theorem mask_5_26 : safeMask ((5 : ℚ) / 26) = speedUniverse.erase 5 := by
  calc
    _ = residueMask 5 26 := by
      simpa using safeMask_nat_ratio_eq_residueMask 5 26 (by norm_num)
    _ = _ := by decide

private theorem mask_4_29 : safeMask ((4 : ℚ) / 29) = speedUniverse.erase 7 := by
  calc
    _ = residueMask 4 29 := by
      simpa using safeMask_nat_ratio_eq_residueMask 4 29 (by norm_num)
    _ = _ := by decide

private theorem mask_5_29 : safeMask ((5 : ℚ) / 29) = speedUniverse.erase 6 := by
  calc
    _ = residueMask 5 29 := by
      simpa using safeMask_nat_ratio_eq_residueMask 5 29 (by norm_num)
    _ = _ := by decide

private theorem mask_11_29 : safeMask ((11 : ℚ) / 29) = speedUniverse.erase 8 := by
  calc
    _ = residueMask 11 29 := by
      simpa using safeMask_nat_ratio_eq_residueMask 11 29 (by norm_num)
    _ = _ := by decide

private theorem mask_1_9 : safeMask ((1 : ℚ) / 9) = speedUniverse \ {9, 18} := by
  calc
    _ = residueMask 1 9 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 9 (by norm_num)
    _ = _ := by decide

private theorem mask_1_10 : safeMask ((1 : ℚ) / 10) = speedUniverse \ {10, 20} := by
  calc
    _ = residueMask 1 10 := by
      simpa using safeMask_nat_ratio_eq_residueMask 1 10 (by norm_num)
    _ = _ := by decide

private theorem reflected_mask_certificate :
    safeMask ((1 : ℚ) / 11) = speedUniverse.erase 11 ∧
    safeMask ((1 : ℚ) / 12) = speedUniverse.erase 12 ∧
    safeMask ((1 : ℚ) / 13) = speedUniverse.erase 13 ∧
    safeMask ((1 : ℚ) / 14) = speedUniverse.erase 14 ∧
    safeMask ((1 : ℚ) / 15) = speedUniverse.erase 15 ∧
    safeMask ((1 : ℚ) / 22) = speedUniverse.erase 1 ∧
    safeMask ((11 : ℚ) / 23) = speedUniverse.erase 2 ∧
    safeMask ((6 : ℚ) / 25) = speedUniverse.erase 4 ∧
    safeMask ((8 : ℚ) / 25) = speedUniverse.erase 3 ∧
    safeMask ((5 : ℚ) / 26) = speedUniverse.erase 5 ∧
    safeMask ((4 : ℚ) / 29) = speedUniverse.erase 7 ∧
    safeMask ((5 : ℚ) / 29) = speedUniverse.erase 6 ∧
    safeMask ((11 : ℚ) / 29) = speedUniverse.erase 8 ∧
    safeMask ((1 : ℚ) / 9) = speedUniverse \ {9, 18} ∧
    safeMask ((1 : ℚ) / 10) = speedUniverse \ {10, 20} := by
  exact ⟨mask_1_11, mask_1_12, mask_1_13, mask_1_14, mask_1_15, mask_1_22,
    mask_11_23, mask_6_25, mask_8_25, mask_5_26, mask_4_29, mask_5_29,
    mask_11_29, mask_1_9, mask_1_10⟩

private def singletonUnsafeSpeeds : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15}

/-- The seven speeds not excluded by one of the thirteen singleton masks. -/
def residualSpeeds : Finset ℕ :=
  {9, 10, 16, 17, 18, 19, 20}

/-- The residual six-subsets containing one of the two excluded pairs. -/
def residualCoveredSixSubsets : Finset (Finset ℕ) :=
  (Finset.powersetCard 6 residualSpeeds).filter fun B =>
    decide ({9, 18} ⊆ B) || decide ({10, 20} ⊆ B)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem reflected_cover_certificate :
    Finset.powersetCard 6 residualSpeeds ⊆ residualCoveredSixSubsets := by
  unfold residualCoveredSixSubsets residualSpeeds
  decide

private theorem speedUniverse_card : speedUniverse.card = 20 := by
  decide

private theorem certificate_mask_exact {p : ℚ × Finset ℕ} (hp : p ∈ certificate) :
    safeMask p.1 = p.2 := by
  simp [certificate] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals subst p
  · simpa using mask_1_11
  · simpa using mask_1_12
  · simpa using mask_1_13
  · simpa using mask_1_14
  · simpa using mask_1_15
  · simpa using mask_1_22
  · simpa using mask_11_23
  · simpa using mask_6_25
  · simpa using mask_8_25
  · simpa using mask_5_26
  · simpa using mask_4_29
  · simpa using mask_5_29
  · simpa using mask_11_29
  · simpa using mask_1_9
  · simpa using mask_1_10

private theorem certificate_time_mem_unit {p : ℚ × Finset ℕ} (hp : p ∈ certificate) :
    p.1 ∈ Set.Icc (0 : ℚ) 1 := by
  simp [certificate] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals
    subst p
    norm_num

private theorem exists_certificate_cover {S : Finset ℕ}
    (hS : S ∈ Finset.powersetCard 14 speedUniverse) :
    ∃ p ∈ certificate, S ⊆ p.2 := by
  have hsub : S ⊆ speedUniverse := (Finset.mem_powersetCard.mp hS).1
  have hcard : S.card = 14 := (Finset.mem_powersetCard.mp hS).2
  by_cases hmiss : ∃ x ∈ singletonUnsafeSpeeds, x ∉ S
  · obtain ⟨x, hxSingle, hxS⟩ := hmiss
    have hxCases :
        x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨
          x = 8 ∨ x = 11 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 := by
      simpa [singletonUnsafeSpeeds] using hxSingle
    rcases hxCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨((1 : ℚ) / 22, speedUniverse.erase 1), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((11 : ℚ) / 23, speedUniverse.erase 2), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((8 : ℚ) / 25, speedUniverse.erase 3), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((6 : ℚ) / 25, speedUniverse.erase 4), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((5 : ℚ) / 26, speedUniverse.erase 5), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((5 : ℚ) / 29, speedUniverse.erase 6), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((4 : ℚ) / 29, speedUniverse.erase 7), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((11 : ℚ) / 29, speedUniverse.erase 8), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((1 : ℚ) / 11, speedUniverse.erase 11), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((1 : ℚ) / 12, speedUniverse.erase 12), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((1 : ℚ) / 13, speedUniverse.erase 13), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((1 : ℚ) / 14, speedUniverse.erase 14), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
    · exact ⟨((1 : ℚ) / 15, speedUniverse.erase 15), by simp [certificate],
        Finset.subset_erase.mpr ⟨hsub, hxS⟩⟩
  · have hSingletonSub : singletonUnsafeSpeeds ⊆ S := by
      intro x hx
      by_contra hnot
      exact hmiss ⟨x, hx, hnot⟩
    let B := speedUniverse \ S
    have hBsub : B ⊆ residualSpeeds := by
      intro x hxB
      have hxParts := Finset.mem_sdiff.mp hxB
      have hxNotSingle : x ∉ singletonUnsafeSpeeds := by
        intro hxSingle
        exact hxParts.2 (hSingletonSub hxSingle)
      simp [speedUniverse, singletonUnsafeSpeeds, residualSpeeds] at hxParts hxNotSingle ⊢
      omega
    have hBcard : B.card = 6 := by
      dsimp [B]
      rw [Finset.card_sdiff_of_subset hsub, speedUniverse_card, hcard]
    have hBmem : B ∈ Finset.powersetCard 6 residualSpeeds :=
      Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩
    have hBCovered : B ∈ residualCoveredSixSubsets := reflected_cover_certificate hBmem
    have hOr := (Finset.mem_filter.mp hBCovered).2
    change (decide ({9, 18} ⊆ B) || decide ({10, 20} ⊆ B)) = true at hOr
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hOr
    rcases hOr with hPair | hPair
    · have hSafe : S ⊆ speedUniverse \ {9, 18} := by
        intro x hxS
        refine Finset.mem_sdiff.mpr ⟨hsub hxS, ?_⟩
        intro hxPair
        exact (Finset.mem_sdiff.mp (hPair hxPair)).2 hxS
      exact ⟨((1 : ℚ) / 9, speedUniverse \ {9, 18}), by simp [certificate], hSafe⟩
    · have hSafe : S ⊆ speedUniverse \ {10, 20} := by
        intro x hxS
        refine Finset.mem_sdiff.mpr ⟨hsub hxS, ?_⟩
        intro hxPair
        exact (Finset.mem_sdiff.mp (hPair hxPair)).2 hxS
      exact ⟨((1 : ℚ) / 10, speedUniverse \ {10, 20}), by simp [certificate], hSafe⟩

private theorem certificate_covers_fourteen (S : Finset ℕ)
    (hsub : S ⊆ speedUniverse) (hcard : S.card = 14) :
    ∃ p ∈ certificate, S ⊆ p.2 := by
  apply exists_certificate_cover
  exact Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩

/-- The fifteen exact masks, the seven-case residual cover, and their universal
fourteen-speed consequence, packaged as the complete finite certificate. -/
theorem certificate_package :
    (safeMask ((1 : ℚ) / 11) = speedUniverse.erase 11 ∧
      safeMask ((1 : ℚ) / 12) = speedUniverse.erase 12 ∧
      safeMask ((1 : ℚ) / 13) = speedUniverse.erase 13 ∧
      safeMask ((1 : ℚ) / 14) = speedUniverse.erase 14 ∧
      safeMask ((1 : ℚ) / 15) = speedUniverse.erase 15 ∧
      safeMask ((1 : ℚ) / 22) = speedUniverse.erase 1 ∧
      safeMask ((11 : ℚ) / 23) = speedUniverse.erase 2 ∧
      safeMask ((6 : ℚ) / 25) = speedUniverse.erase 4 ∧
      safeMask ((8 : ℚ) / 25) = speedUniverse.erase 3 ∧
      safeMask ((5 : ℚ) / 26) = speedUniverse.erase 5 ∧
      safeMask ((4 : ℚ) / 29) = speedUniverse.erase 7 ∧
      safeMask ((5 : ℚ) / 29) = speedUniverse.erase 6 ∧
      safeMask ((11 : ℚ) / 29) = speedUniverse.erase 8 ∧
      safeMask ((1 : ℚ) / 9) = speedUniverse \ {9, 18} ∧
      safeMask ((1 : ℚ) / 10) = speedUniverse \ {10, 20}) ∧
    Finset.powersetCard 6 residualSpeeds ⊆ residualCoveredSixSubsets ∧
    ∀ S : Finset ℕ, S ⊆ speedUniverse → S.card = 14 →
      ∃ p ∈ certificate, S ⊆ p.2 := by
  exact ⟨reflected_mask_certificate, reflected_cover_certificate,
    certificate_covers_fourteen⟩

example : (Finset.Icc 1 14 : Finset ℕ) ⊆ speedUniverse ∧
    (Finset.Icc 1 14 : Finset ℕ).card = 14 := by
  decide

example : ∃ t : ℚ, t ∈ Set.Icc (0 : ℚ) 1 := by
  exact ⟨0, by norm_num⟩

/-- Every fourteen speeds chosen from one through twenty have a rational time
in `[0,1]` at which all fourteen torus distances are at least `1 / 15`. -/
theorem lonely_runner_fourteen_of_twenty (S : Finset ℕ)
    (hsub : S ⊆ speedUniverse) (hcard : S.card = 14) :
    ∃ t : ℚ, t ∈ Set.Icc (0 : ℚ) 1 ∧
      ∀ s ∈ S, (1 : ℚ) / 15 ≤ torusDist ((s : ℚ) * t) := by
  obtain ⟨p, hp, hpS⟩ := certificate_covers_fourteen S hsub hcard
  refine ⟨p.1, certificate_time_mem_unit hp, ?_⟩
  intro s hs
  apply safeMask_sound
  rw [certificate_mask_exact hp]
  exact hpS hs

#print axioms torusDist_nat_ratio_ge_iff_nat_residue_window
#print axioms certificate_package
#print axioms lonely_runner_fourteen_of_twenty

end D5.S1.Phase.LonelyRunnerFourteenOfTwenty
