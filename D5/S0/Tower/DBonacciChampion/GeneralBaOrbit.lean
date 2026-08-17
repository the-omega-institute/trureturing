/- GID: D5/S0/Tower/DBonacciChampion/GeneralBaOrbit
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciChampion/GeneralBaOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The universal ba fixed point generates every d-bonacci champion orbit and liminf. -/

import D5.S0.Tower.DBonacciGeneral.ChampionValue
import D5.S0.Tower.DBonacciGeneral.UniformBaseGap

namespace D5.S0.Tower.DBonacciChampion.GeneralBaOrbit

/- Library-search audit trail (2026-08-17):
   * Repository search found the general typed gap orbit, the uniform diagonal
     base gap, the general survivor evaluator, and the order-three, four, and
     five hand proofs. No unconditional all-order champion orbit was present.
   * Pinned mathlib supplies the elementary ordered-field and liminf lemmas
     used below; no external d-bonacci champion theorem was found. -/

/-- The two-refinement return map for the right-left word `ba`. -/
def baReturn (beta u : Real) : Real := beta * (beta * u - 1)

/-- The universal normalized left arm fixed by the `ba` return map. -/
noncomputable def baFixedPoint (beta : Real) : Real :=
  beta / (beta ^ 2 - 1)

/-- The fixed-point formula is exactly `beta / (beta^2 - 1)`. -/
theorem ba_fixed_point_formula (beta : Real) :
    baFixedPoint beta = beta / (beta ^ 2 - 1) := rfl

/-- Above one, the displayed arm is fixed by one complete `ba` return. -/
theorem ba_fixed_point (beta : Real) (hbeta : 1 < beta) :
    baReturn beta (baFixedPoint beta) = baFixedPoint beta := by
  have hden : beta ^ 2 - 1 ≠ 0 := by nlinarith
  unfold baReturn baFixedPoint
  field_simp [hden]
  ring

/-- Above one, the `ba` return has no other real fixed point. -/
theorem ba_fixed_point_iff (beta u : Real) (hbeta : 1 < beta) :
    baReturn beta u = u ↔ u = baFixedPoint beta := by
  have hden : beta ^ 2 - 1 ≠ 0 := by nlinarith
  constructor
  · intro hfixed
    unfold baReturn at hfixed
    unfold baFixedPoint
    apply (eq_div_iff hden).2
    nlinarith
  · rintro rfl
    exact ba_fixed_point beta hbeta

/-- The complementary arm of the fixed point is the corrected champion value. -/
theorem championValue_eq_one_sub_baFixedPoint (beta : Real) (hbeta : 1 < beta) :
    D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue beta =
      1 - baFixedPoint beta := by
  have hden : beta ^ 2 - 1 ≠ 0 := by nlinarith
  unfold D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue baFixedPoint
  field_simp [hden]
  ring

/-- The low arm on the `ba` orbit. -/
noncomputable def baLowArm (beta : Real) : Real :=
  D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue beta

/-- The left arm in the intervening predecessor-gap phase. -/
noncomputable def baMiddleLeft (beta : Real) : Real :=
  1 / (beta ^ 2 - 1)

/-- The right arm in the intervening predecessor-gap phase. -/
noncomputable def baMiddleRight (beta : Real) : Real :=
  beta * baLowArm beta

/-- The real point selected by the all-order `ba` orbit. -/
noncomputable def dbonacciChampionPoint (d : Nat) : Real :=
  baFixedPoint
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) *
    D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(d : Int))

theorem ba_fixed_point_add_lowArm (beta : Real) (hbeta : 1 < beta) :
    baFixedPoint beta + baLowArm beta = 1 := by
  rw [baLowArm, championValue_eq_one_sub_baFixedPoint beta hbeta]
  ring

theorem ba_large_branch (beta : Real) (hbeta : 1 < beta) :
    beta * baFixedPoint beta - 1 = baMiddleLeft beta := by
  have hden : beta ^ 2 - 1 ≠ 0 := by nlinarith
  unfold baFixedPoint baMiddleLeft
  field_simp [hden]
  ring

theorem ba_middle_branch (beta : Real) (hbeta : 1 < beta) :
    beta * baMiddleLeft beta = baFixedPoint beta := by
  have hden : beta ^ 2 - 1 ≠ 0 := by nlinarith
  unfold baMiddleLeft baFixedPoint
  field_simp [hden]

theorem ba_middle_complement (beta : Real) (hbeta : 1 < beta) :
    1 - beta * baMiddleLeft beta = baLowArm beta := by
  rw [ba_middle_branch beta hbeta]
  nlinarith [ba_fixed_point_add_lowArm beta hbeta]

theorem dbonacci_champion_denominator_pos (d : Nat) (hd : 3 <= d) :
    0 < D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ 2 - 1 := by
  nlinarith [D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d
    (by omega)]

theorem dbonacci_champion_lowArm_pos (d : Nat) (hd : 3 <= d) :
    0 < baLowArm
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  let beta := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d
  have hbeta : 1 < beta :=
    D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d (by omega)
  have hbphi : Real.goldenRatio < beta := by
    rw [← D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_two_eq_goldenRatio]
    exact D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_strictMonoOn
      (by norm_num) (by exact show 2 ≤ d by omega)
      (by exact show 2 < d by omega)
  have hproduct :
      0 < (beta - Real.goldenRatio) *
        (beta + Real.goldenRatio - 1) := by
    exact mul_pos (sub_pos.mpr hbphi)
      (by nlinarith [Real.one_lt_goldenRatio])
  have hnum : 0 < beta ^ 2 - beta - 1 := by
    nlinarith [Real.goldenRatio_sq]
  unfold baLowArm D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue
  exact div_pos hnum (dbonacci_champion_denominator_pos d hd)

theorem dbonacci_champion_middleLeft_pos (d : Nat) (hd : 3 <= d) :
    0 < baMiddleLeft
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  exact one_div_pos.mpr (dbonacci_champion_denominator_pos d hd)

theorem dbonacci_champion_lowArm_lt_middleLeft (d : Nat) (hd : 3 <= d) :
    baLowArm (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) <
      baMiddleLeft
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  let beta := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d
  have hden : 0 < beta ^ 2 - 1 := dbonacci_champion_denominator_pos d hd
  have hbeta : 1 < beta :=
    D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d (by omega)
  have hbeta_two : beta < 2 :=
    D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_lt_two d (by omega)
  unfold baLowArm baMiddleLeft
    D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue
  rw [div_lt_div_iff_of_pos_right hden]
  nlinarith

theorem dbonacci_champion_lowArm_lt_fixedPoint (d : Nat) (hd : 3 <= d) :
    baLowArm (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) <
      baFixedPoint
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  refine (dbonacci_champion_lowArm_lt_middleLeft d hd).trans ?_
  apply div_lt_div_of_pos_right
  · exact D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d
      (by omega)
  · exact dbonacci_champion_denominator_pos d hd

theorem dbonacci_champion_middleLeft_le_middleRight (d : Nat) (hd : 3 <= d) :
    baMiddleLeft
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) <=
      baMiddleRight
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  let beta := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d
  let t := D5.S0.Tower.Tribonacci.Values.tribonacciConstant
  have hbeta : 1 < beta :=
    D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d (by omega)
  have ht : 1 < t := D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant
  have ht_le : t <= beta := by
    by_cases heq : d = 3
    · subst d
      change t <= D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 3
      rw [D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant]
    · exact le_of_lt
        (by
          have hmono :=
            D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_strictMonoOn
              (show 3 ∈ Set.Ici (2 : Nat) by norm_num)
              (show d ∈ Set.Ici (2 : Nat) by
                exact show 2 ≤ d by omega)
              (by omega : 3 < d)
          rw [D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant]
            at hmono
          exact hmono)
  have hbquad : 0 < beta ^ 2 - beta := by nlinarith
  have hcross : 0 < beta * t - 1 := by
    nlinarith [mul_pos (lt_trans zero_lt_one hbeta) (lt_trans zero_lt_one ht)]
  have htquad : 0 < t ^ 2 - t := by nlinarith
  have hsecond :
      0 < beta ^ 2 + beta * t + t ^ 2 - beta - t - 1 := by
    nlinarith
  have hfactor :
      0 <= (beta - t) *
        (beta ^ 2 + beta * t + t ^ 2 - beta - t - 1) :=
    mul_nonneg (sub_nonneg.mpr ht_le) hsecond.le
  have hnum : 0 <= beta ^ 3 - beta ^ 2 - beta - 1 := by
    nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
  have hdifference :
      baMiddleRight beta - baMiddleLeft beta =
        (beta ^ 3 - beta ^ 2 - beta - 1) / (beta ^ 2 - 1) := by
    have hden := (dbonacci_champion_denominator_pos d hd).ne'
    unfold baMiddleRight baMiddleLeft baLowArm
      D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue
    field_simp [hden]
  rw [← sub_nonneg, hdifference]
  exact div_nonneg hnum (dbonacci_champion_denominator_pos d hd).le

/-- A typed orbit gap can be consumed by the general survivor evaluator. -/
theorem letterOrbitGap_to_orbitGap (d Q : Nat) (x : Real)
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d)
    (leftArm rightArm : Real)
    (hgap : D5.S0.Tower.DBonacci.OrbitAlgebra.IsDBonacciLetterOrbitGap
      d Q x letter leftArm rightArm) :
    D5.S0.Tower.DBonacci.ChampionOrbit.IsDBonacciOrbitGap
      d Q x letter.1 leftArm rightArm := by
  rcases hgap with ⟨i, hlength, hleft, hright⟩
  refine ⟨i, ?_, hleft, hright⟩
  simpa [D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength] using hlength

/-- Uniform base data and the closed scalar identities give the all-order `ba` gap orbit. -/
theorem dbonacci_champion_gap_orbit (d : Nat) (hd : 3 <= d) (k : Nat) :
    D5.S0.Tower.DBonacci.ChampionOrbit.IsDBonacciOrbitGap d (2 * k + d)
        (dbonacciChampionPoint d) (d - 1)
        (baFixedPoint
          (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d))
        (baLowArm
          (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d)) /\
      D5.S0.Tower.DBonacci.ChampionOrbit.IsDBonacciOrbitGap d (2 * k + d + 1)
        (dbonacciChampionPoint d) (d - 2)
        (baMiddleLeft
          (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d))
        (baMiddleRight
          (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d)) := by
  let beta := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d
  have hbeta : 1 < beta :=
    D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d (by omega)
  have hbase :=
    D5.S0.Tower.DBonacciGeneral.UniformBaseGap.diagonal_top_base_gap d hd
      (dbonacciChampionPoint d) (baFixedPoint beta) (baLowArm beta)
      (by rfl) (ba_fixed_point_add_lowArm beta hbeta)
  have htyped :=
    D5.S0.Tower.DBonacci.OrbitAlgebra.top_predecessor_period_two_orbit
      d d hd (dbonacciChampionPoint d) (baFixedPoint beta) (baLowArm beta)
      (baMiddleLeft beta) (baMiddleRight beta)
      (ba_large_branch beta hbeta)
      (by rfl)
      (ba_middle_branch beta hbeta)
      (ba_middle_complement beta hbeta) hbase k
  constructor
  · simpa [D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter] using
      letterOrbitGap_to_orbitGap d (2 * k + d) (dbonacciChampionPoint d)
        _ _ _ htyped.1
  · simpa [D5.S0.Tower.DBonacci.OrbitAlgebra.topPredecessorGapLetter] using
      letterOrbitGap_to_orbitGap d (2 * k + d + 1) (dbonacciChampionPoint d)
        _ _ _ htyped.2

theorem dbonacci_champion_survivor_even (d : Nat) (hd : 3 <= d) (k : Nat) :
    D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor d (2 * k + d)
        (dbonacciChampionPoint d) =
      baLowArm
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  apply D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciSurvivor_eq_of_orbit_gap
      d (2 * k + d) (by omega) (hgap := (dbonacci_champion_gap_orbit d hd k).1)
  · exact (div_pos
      (lt_trans zero_lt_one
        (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d
          (by omega)))
      (dbonacci_champion_denominator_pos d hd)).le
  · exact (dbonacci_champion_lowArm_pos d hd).le
  · exact (dbonacci_champion_lowArm_lt_fixedPoint d hd).le
  · exact le_rfl
  · exact Or.inr rfl

theorem dbonacci_champion_survivor_odd (d : Nat) (hd : 3 <= d) (k : Nat) :
    D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor d (2 * k + d + 1)
        (dbonacciChampionPoint d) =
      baMiddleLeft
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  apply D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciSurvivor_eq_of_orbit_gap
      d (2 * k + d + 1) (by omega)
      (hgap := (dbonacci_champion_gap_orbit d hd k).2)
  · exact (dbonacci_champion_middleLeft_pos d hd).le
  · exact mul_nonneg
      (zero_lt_one.trans
        (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot d
          (by omega))).le
      (dbonacci_champion_lowArm_pos d hd).le
  · exact le_rfl
  · exact dbonacci_champion_middleLeft_le_middleRight d hd
  · exact Or.inl rfl

/-- For every order at least three, the `ba` point has exact corrected liminf. -/
theorem dbonacci_champion_liminf (d : Nat) (hd : 3 <= d) :
    Filter.liminf
        (fun Q => D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor d Q
          (dbonacciChampionPoint d)) Filter.atTop =
      D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d) := by
  let beta := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d
  have hlow_middle : baLowArm beta <= baMiddleLeft beta :=
    (dbonacci_champion_lowArm_lt_middleLeft d hd).le
  have heventually_lower :
      ∀ᶠ Q in Filter.atTop,
        baLowArm beta <=
          D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor d Q
            (dbonacciChampionPoint d) := by
    rw [Filter.eventually_atTop]
    refine ⟨d, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + d := ⟨Q - d, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [dbonacci_champion_survivor_even d hd]
    · subst n
      rw [show (2 * k + 1) + d = 2 * k + d + 1 by omega,
        dbonacci_champion_survivor_odd d hd]
      exact hlow_middle
  have heventually_upper :
      ∀ᶠ Q in Filter.atTop,
        D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor d Q
            (dbonacciChampionPoint d) <= baMiddleLeft beta := by
    rw [Filter.eventually_atTop]
    refine ⟨d, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + d := ⟨Q - d, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [dbonacci_champion_survivor_even d hd]
      exact hlow_middle
    · subst n
      rw [show (2 * k + 1) + d = 2 * k + d + 1 by omega,
        dbonacci_champion_survivor_odd d hd]
  change Filter.liminf
      (fun Q => D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor d Q
        (dbonacciChampionPoint d)) Filter.atTop = baLowArm beta
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨2 * N + d, by omega, ?_⟩
      rw [dbonacci_champion_survivor_even d hd]
    · exact ⟨baLowArm beta, heventually_lower⟩
  · exact Filter.le_liminf_of_le
      (Filter.IsBoundedUnder.isCoboundedUnder_ge
        ⟨baMiddleLeft beta, heventually_upper⟩)
      heventually_lower

theorem dbonacciChampionPoint_three :
    dbonacciChampionPoint 3 =
      D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacciChampionPoint := by
  let t := D5.S0.Tower.Tribonacci.Values.tribonacciConstant
  have ht0 : t ≠ 0 :=
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero
  have htpos : 0 < t := zero_lt_one.trans
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant
  have hden : t ^ 2 - 1 ≠ 0 := by
    nlinarith [D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant]
  rw [dbonacciChampionPoint,
    D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant]
  unfold baFixedPoint D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacciChampionPoint
  rw [zpow_neg, zpow_neg, zpow_neg]
  norm_num only [zpow_ofNat, pow_one]
  field_simp [ht0, hden]
  all_goals
    have heq :
        2 / (t ^ 2 * (t ^ 2 - 1)) = (t - 1) / t ^ 2 := by
      field_simp [ht0, hden]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
    nlinarith [heq]

theorem dbonacciChampionPoint_four :
    dbonacciChampionPoint 4 =
      D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint := by
  let beta := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4
  have hbeta0 : beta ≠ 0 := ne_of_gt (lt_trans zero_lt_one
    (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot 4
      (by norm_num)))
  have hpow : beta * beta ^ (-4 : Int) = beta ^ (-3 : Int) := by
    calc
      beta * beta ^ (-4 : Int) = beta ^ (1 : Int) * beta ^ (-4 : Int) := by
        rw [zpow_one]
      _ = beta ^ ((1 : Int) + (-4 : Int)) := by rw [zpow_add₀ hbeta0]
      _ = beta ^ (-3 : Int) := by norm_num
  unfold dbonacciChampionPoint baFixedPoint
    D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint
  norm_num only [Nat.cast_ofNat]
  calc
    beta / (beta ^ 2 - 1) * beta ^ (-4 : Int) =
        (beta * beta ^ (-4 : Int)) / (beta ^ 2 - 1) := by ring
    _ = beta ^ (-3 : Int) / (beta ^ 2 - 1) := by rw [hpow]

theorem dbonacciChampionPoint_five :
    dbonacciChampionPoint 5 =
      D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.dbonacciFiveChampionPoint := by
  let beta := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 5
  have hbeta0 : beta ≠ 0 := ne_of_gt (lt_trans zero_lt_one
    (D5.S0.Tower.DBonacci.PerronRoot.one_lt_dbonacciPerronRoot 5
      (by norm_num)))
  have hpow : beta * beta ^ (-5 : Int) = beta ^ (-4 : Int) := by
    calc
      beta * beta ^ (-5 : Int) = beta ^ (1 : Int) * beta ^ (-5 : Int) := by
        rw [zpow_one]
      _ = beta ^ ((1 : Int) + (-5 : Int)) := by rw [zpow_add₀ hbeta0]
      _ = beta ^ (-4 : Int) := by norm_num
  unfold dbonacciChampionPoint baFixedPoint
    D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.dbonacciFiveChampionPoint
  norm_num only [Nat.cast_ofNat]
  calc
    beta / (beta ^ 2 - 1) * beta ^ (-5 : Int) =
        (beta * beta ^ (-5 : Int)) / (beta ^ 2 - 1) := by ring
    _ = beta ^ (-4 : Int) / (beta ^ 2 - 1) := by rw [hpow]

/-- The Tribonacci hand theorem is an order-three instance of the general result. -/
theorem tribonacci_champion_liminf_from_general :
    Filter.liminf
        (fun Q => D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor Q
          D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacciChampionPoint)
        Filter.atTop =
      D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant := by
  have hgeneral := dbonacci_champion_liminf 3 (by norm_num)
  rw [dbonacciChampionPoint_three] at hgeneral
  simpa only [D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor_three_eq_tribonacciSurvivor,
    D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant]
    using hgeneral

/-- The original order-four liminf statement follows from the general theorem. -/
theorem four_champion_liminf_from_general :
    Filter.liminf
        (fun Q => D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor 4 Q
          D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint)
        Filter.atTop =
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 -
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 - 1) /
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1) := by
  have hgeneral := dbonacci_champion_liminf 4 (by norm_num)
  rw [dbonacciChampionPoint_four] at hgeneral
  exact hgeneral

/-- The order-five hand theorem is likewise a direct instance. -/
theorem five_champion_liminf_from_general :
    Filter.liminf
        (fun Q => D5.S0.Tower.DBonacci.Survivor.dbonacciSurvivor 5 Q
          D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.dbonacciFiveChampionPoint)
        Filter.atTop =
      D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 5) := by
  have hgeneral := dbonacci_champion_liminf 5 (by norm_num)
  rw [dbonacciChampionPoint_five] at hgeneral
  exact hgeneral

end D5.S0.Tower.DBonacciChampion.GeneralBaOrbit
