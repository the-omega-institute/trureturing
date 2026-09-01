/- GID: D5/S0/Tower/DBonacciGeneral/UniformBaseGap
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/UniformBaseGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The diagonal d-bonacci layer has a uniform typed top-gap witness. -/

import D5.S0.Tower.DBonacci.OrbitAlgebra
import D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit
import D5.S0.Tower.Tribonacci.ChampionOrbit

namespace D5.S0.Tower.DBonacciGeneral.UniformBaseGap

/- Library-search audit trail (2026-08-17):
   * Repository search found the bounded-run prefix recursion and the three
     frozen order-specific base-gap proofs, but no diagonal cardinality or
     uniform second-index theorem.
   * Pinned mathlib supplies finite-sum, power, and integer-power algebra;
     no external d-bonacci base-gap construction was found or introduced. -/

theorem dbonacci_diagonal_cardinality (d : Nat) :
    D5.S0.Tower.DBonacci.Names.dbonacci d (d + 2) = 2 ^ d - 1 := by
  rw [D5.S0.Tower.DBonacci.Names.dbonacci_add_two_of_le d d le_rfl]
  have hsum : forall n : Nat, (Finset.range n).sum (fun i => 2 ^ i) = 2 ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        have hpow : 1 <= 2 ^ n :=
          one_le_pow_of_one_le' (by norm_num : 1 <= (2 : Nat)) n
        omega
  calc
    (Finset.univ : Finset (Fin d)).sum
          (fun i => D5.S0.Tower.DBonacci.Names.dbonacci d
            (d - d + i.1 + 2)) =
        (Finset.univ : Finset (Fin d)).sum (fun i => 2 ^ i.1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.sub_self, zero_add,
        D5.S0.Tower.DBonacci.Names.dbonacci_add_two_of_lt]
      exact i.2
    _ = (Finset.range d).sum (fun i => 2 ^ i) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = 2 ^ d - 1 := hsum d

theorem diagonal_cardinality_two_le (d : Nat) (hd : 2 <= d) :
    2 <= D5.S0.Tower.DBonacci.Names.dbonacci d (d + 2) := by
  rw [dbonacci_diagonal_cardinality]
  have hpow : 2 ^ 2 <= 2 ^ d := pow_le_pow_right' (by norm_num) hd
  norm_num at hpow
  omega

theorem short_full_budget_cardinality (maxTrue Q : Nat)
    (hQ : Q < maxTrue + 1) :
    Fintype.card
        (D5.S0.Tower.DBonacci.Names.BoundedRunName maxTrue maxTrue Q) =
      2 ^ Q := by
  rw [<- D5.S0.Tower.DBonacci.Names.dbonacci_name_card_eq_bounded maxTrue Q,
    D5.S0.Tower.DBonacci.Names.dbonacci_name_card_of_lt]
  exact hQ

theorem full_budget_cardinality_two_le (maxTrue Q : Nat)
    (hmax : 0 < maxTrue) (hQ : 0 < Q) (hshort : Q <= maxTrue + 1) :
    2 <= Fintype.card
      (D5.S0.Tower.DBonacci.Names.BoundedRunName maxTrue maxTrue Q) := by
  by_cases hlt : Q < maxTrue + 1
  · rw [short_full_budget_cardinality maxTrue Q hlt]
    have hpow : 2 ^ 1 <= 2 ^ Q :=
      pow_le_pow_right' (by norm_num) hQ
    norm_num at hpow
    exact hpow
  · have hQeq : Q = maxTrue + 1 := by omega
    subst Q
    rw [<- D5.S0.Tower.DBonacci.Names.dbonacci_name_card_eq_bounded,
      D5.S0.Tower.DBonacci.Names.dbonacci_name_card,
      dbonacci_diagonal_cardinality]
    have hpow : 2 ^ 2 <= 2 ^ (maxTrue + 1) :=
      pow_le_pow_right' (by norm_num) (by omega)
    norm_num at hpow
    omega

theorem bounded_full_budget_second_value (maxTrue Q : Nat)
    (hmax : 0 < maxTrue) (hQ : 0 < Q) (hshort : Q <= maxTrue + 1) :
    D5.S0.Tower.DBonacci.Values.boundedIndexedNameValue maxTrue maxTrue Q
        (⟨1, full_budget_cardinality_two_le maxTrue Q hmax hQ hshort⟩ :
          Fin (Fintype.card
            (D5.S0.Tower.DBonacci.Names.BoundedRunName maxTrue maxTrue Q))) =
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot
        (maxTrue + 1))⁻¹ ^ Q := by
  cases maxTrue with
  | zero => omega
  | succ maxTrue =>
      induction Q with
      | zero => omega
      | succ Q ih =>
          cases Q with
          | zero =>
              let i : Fin (Fintype.card
                  (D5.S0.Tower.DBonacci.Names.BoundedRunName
                    (maxTrue + 1) (maxTrue + 1) 1)) :=
                ⟨1, full_budget_cardinality_two_le (maxTrue + 1) 1
                  (by omega) (by omega) (by omega)⟩
              have hi : Fintype.card
                  (D5.S0.Tower.DBonacci.Names.BoundedRunName
                    (maxTrue + 1) (maxTrue + 1) 0) <= i.1 := by
                rw [short_full_budget_cardinality (maxTrue + 1) 0 (by omega)]
                simp [i]
              rw [show (⟨1, full_budget_cardinality_two_le (maxTrue + 1) 1
                    (by omega) (by omega) (by omega)⟩ :
                    Fin (Fintype.card
                      (D5.S0.Tower.DBonacci.Names.BoundedRunName
                        (maxTrue + 1) (maxTrue + 1) 1))) = i by rfl,
                D5.S0.Tower.DBonacci.Values.boundedIndexedNameValue_upper
                  (maxTrue + 1) maxTrue 0 i hi]
              have hcardZero : Fintype.card
                  (D5.S0.Tower.DBonacci.Names.BoundedRunName
                    (maxTrue + 1) (maxTrue + 1) 0) = 1 := by
                rw [short_full_budget_cardinality (maxTrue + 1) 0 (by omega)]
                norm_num
              have htailCard : Fintype.card
                  (D5.S0.Tower.DBonacci.Names.BoundedRunName
                    (maxTrue + 1) maxTrue 0) = 1 := by
                letI : Unique (D5.S0.Tower.DBonacci.Names.BoundedRunName
                    (maxTrue + 1) maxTrue 0) :=
                  { default := ⟨fun z => Fin.elim0 z, by rfl⟩
                    uniq := by
                      intro a
                      apply Subtype.ext
                      funext z
                      exact Fin.elim0 z }
                exact Fintype.card_unique
              have htailIndex :
                  (⟨i.1 - Fintype.card
                      (D5.S0.Tower.DBonacci.Names.BoundedRunName
                        (maxTrue + 1) (maxTrue + 1) 0), by
                    have htotal := i.2
                    change i.1 - Fintype.card
                        (D5.S0.Tower.DBonacci.Names.BoundedRunName
                          (maxTrue + 1) (maxTrue + 1) 0) <
                      Fintype.card
                        (D5.S0.Tower.DBonacci.Names.BoundedRunName
                          (maxTrue + 1) maxTrue 0)
                    simp only [i, hcardZero, htailCard]
                    norm_num⟩ : Fin (Fintype.card
                      (D5.S0.Tower.DBonacci.Names.BoundedRunName
                        (maxTrue + 1) maxTrue 0))) =
                    ⟨0, D5.S0.Tower.DBonacci.Values.bounded_run_level_pos
                      (maxTrue + 1) maxTrue 0⟩ := by
                apply Fin.ext
                simp [i, hcardZero]
              rw [htailIndex,
                D5.S0.Tower.DBonacci.Values.boundedIndexedNameValue_level_zero]
              simp
          | succ Q =>
              have hpreviousShort : Q + 1 < (maxTrue + 1) + 1 := by omega
              have hpreviousCard : 1 < Fintype.card
                  (D5.S0.Tower.DBonacci.Names.BoundedRunName
                    (maxTrue + 1) (maxTrue + 1) (Q + 1)) := by
                rw [short_full_budget_cardinality (maxTrue + 1) (Q + 1)
                  hpreviousShort]
                have hpow : 2 ^ 1 <= 2 ^ (Q + 1) :=
                  pow_le_pow_right' (by norm_num) (by omega)
                norm_num at hpow
                exact hpow
              let i : Fin (Fintype.card
                  (D5.S0.Tower.DBonacci.Names.BoundedRunName
                    (maxTrue + 1) (maxTrue + 1) (Q + 2))) :=
                ⟨1, full_budget_cardinality_two_le (maxTrue + 1) (Q + 2)
                  (by omega) (by omega) (by omega)⟩
              rw [show (⟨1, full_budget_cardinality_two_le (maxTrue + 1) (Q + 2)
                    (by omega) (by omega) (by omega)⟩ :
                    Fin (Fintype.card
                      (D5.S0.Tower.DBonacci.Names.BoundedRunName
                        (maxTrue + 1) (maxTrue + 1) (Q + 2)))) = i by rfl,
                D5.S0.Tower.DBonacci.Values.boundedIndexedNameValue_lower
                  (maxTrue + 1) maxTrue (Q + 1) i
                  (by simpa [i] using hpreviousCard)]
              rw [ih (by omega) (by omega)]
              simp [pow_succ, mul_assoc]
              ring

theorem diagonal_first_index_zero (d : Nat) (hd : 1 <= d) :
    D5.S0.Tower.DBonacci.Values.indexedNameValue d d
        ⟨0, D5.S0.Tower.DBonacci.Values.dbonacci_level_pos d d (by omega)⟩ = 0 := by
  cases d with
  | zero => omega
  | succ maxTrue =>
      rw [D5.S0.Tower.DBonacci.Values.indexedNameValue_succ_eq_bounded]
      have hindex :
          Fin.cast
              ((D5.S0.Tower.DBonacci.Names.dbonacci_name_card
                    (maxTrue + 1) (maxTrue + 1)).symm.trans
                (D5.S0.Tower.DBonacci.Names.dbonacci_name_card_eq_bounded
                  maxTrue (maxTrue + 1)))
              ⟨0, D5.S0.Tower.DBonacci.Values.dbonacci_level_pos
                (maxTrue + 1) (maxTrue + 1) (by omega)⟩ =
            (⟨0, D5.S0.Tower.DBonacci.Values.bounded_run_level_pos
                maxTrue maxTrue (maxTrue + 1)⟩ : Fin (Fintype.card
              (D5.S0.Tower.DBonacci.Names.BoundedRunName
                maxTrue maxTrue (maxTrue + 1)))) := by
        apply Fin.ext
        rfl
      rw [hindex,
        D5.S0.Tower.DBonacci.Values.boundedIndexedNameValue_zero]

theorem diagonal_first_index_one (d : Nat) (hd : 2 <= d) :
    D5.S0.Tower.DBonacci.Values.indexedNameValue d d
        ⟨1, diagonal_cardinality_two_le d hd⟩ =
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(d : Int)) := by
  cases d with
  | zero => omega
  | succ maxTrue =>
      rw [D5.S0.Tower.DBonacci.Values.indexedNameValue_succ_eq_bounded]
      have hindex :
          Fin.cast
              ((D5.S0.Tower.DBonacci.Names.dbonacci_name_card
                    (maxTrue + 1) (maxTrue + 1)).symm.trans
                (D5.S0.Tower.DBonacci.Names.dbonacci_name_card_eq_bounded
                  maxTrue (maxTrue + 1)))
              ⟨1, diagonal_cardinality_two_le (maxTrue + 1) (by omega)⟩ =
            (⟨1, full_budget_cardinality_two_le maxTrue (maxTrue + 1)
                (by omega) (by omega) le_rfl⟩ : Fin (Fintype.card
              (D5.S0.Tower.DBonacci.Names.BoundedRunName
                maxTrue maxTrue (maxTrue + 1)))) := by
        apply Fin.ext
        rfl
      rw [hindex,
        bounded_full_budget_second_value maxTrue (maxTrue + 1)
          (by omega) (by omega) le_rfl]
      rw [zpow_neg, zpow_natCast]
      exact inv_pow _ _

theorem diagonal_top_base_gap (d : Nat) (hd : 3 <= d)
    (x largeLeft lowArm : Real)
    (hpoint : x = largeLeft *
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(d : Int)))
    (harms : largeLeft + lowArm = 1) :
    D5.S0.Tower.DBonacci.OrbitAlgebra.IsDBonacciLetterOrbitGap d d x
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter d (by omega))
      largeLeft lowArm := by
  let i : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (d + 2) - 1) :=
    ⟨0, by
      have hcard := diagonal_cardinality_two_le d (by omega)
      omega⟩
  have hleft : D5.S0.Tower.DBonacci.Substitution.gapLeft d d i =
      ⟨0, D5.S0.Tower.DBonacci.Values.dbonacci_level_pos d d (by omega)⟩ := by
    apply Fin.ext
    rfl
  have hright : D5.S0.Tower.DBonacci.Substitution.gapRight d d i =
      ⟨1, diagonal_cardinality_two_le d (by omega)⟩ := by
    apply Fin.ext
    rfl
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [hleft, hright, diagonal_first_index_zero d (by omega),
      diagonal_first_index_one d (by omega), sub_zero]
    exact (D5.S0.Tower.DBonacci.OrbitAlgebra.top_gap_letter_length
      d d (by omega)).symm
  · rw [hleft, diagonal_first_index_zero d (by omega), sub_zero]
    exact hpoint
  · rw [hright, diagonal_first_index_one d (by omega), hpoint]
    calc
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^ (-(d : Int)) -
            largeLeft *
              D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
                (-(d : Int)) =
          (1 - largeLeft) *
            D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
              (-(d : Int)) := by ring
      _ = lowArm *
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot d ^
            (-(d : Int)) := by
        rw [show 1 - largeLeft = lowArm by linarith [harms]]

theorem tribonacci_champion_base_gap_typed :
    D5.S0.Tower.DBonacci.OrbitAlgebra.IsDBonacciLetterOrbitGap 3 3
      D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacciChampionPoint
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter 3 (by norm_num))
      ((D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ 2 -
          D5.S0.Tower.Tribonacci.Values.tribonacciConstant) / 2)
      ((1 - D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^
        (-1 : Int)) / 2) := by
  apply diagonal_top_base_gap 3 (by norm_num)
  · rw [D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant]
    rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacciChampionPoint,
      zpow_neg, zpow_neg, zpow_neg]
    norm_num only [zpow_ofNat, pow_one]
    field_simp [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero]
  · exact D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_coordinate_sum

theorem four_champion_base_gap_typed :
    D5.S0.Tower.DBonacci.OrbitAlgebra.IsDBonacciLetterOrbitGap 4 4
      D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter 4 (by norm_num))
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 /
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1))
      ((D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 -
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 - 1) /
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1)) := by
  apply diagonal_top_base_gap 4 (by norm_num)
  · exact D5.S0.Tower.DBonacci.ChampionOrbit.four_champion_point_scaled
  · exact D5.S0.Tower.DBonacci.ChampionOrbit.four_coordinate_sum

theorem five_champion_base_gap_typed :
    D5.S0.Tower.DBonacci.OrbitAlgebra.IsDBonacciLetterOrbitGap 5 5
      D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.dbonacciFiveChampionPoint
      (D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter 5 (by norm_num))
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 5 /
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 5 ^ 2 - 1))
      ((D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 5 ^ 2 -
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 5 - 1) /
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 5 ^ 2 - 1)) := by
  apply diagonal_top_base_gap 5 (by norm_num)
  · exact
      D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.five_champion_point_scaled
  · exact D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit.five_coordinate_sum

theorem four_champion_base_gap_reproved :
    D5.S0.Tower.DBonacci.ChampionOrbit.IsDBonacciOrbitGap 4 4
      D5.S0.Tower.DBonacci.ChampionOrbit.dbonacciFourChampionPoint 3
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 /
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1))
      ((D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 -
          D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 - 1) /
        (D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot 4 ^ 2 - 1)) := by
  rcases four_champion_base_gap_typed with ⟨i, hlength, hleft, hright⟩
  refine ⟨i, ?_, hleft, hright⟩
  simpa [D5.S0.Tower.DBonacci.GapAlphabet.gapLetterLength,
    D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter] using hlength

end D5.S0.Tower.DBonacciGeneral.UniformBaseGap
