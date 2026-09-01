/- GID: D5/S0/Tower/DBonacci/Gaps
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/Gaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: D-bonacci name values have min(d,Q) adjacent gaps, reaching d at level d. -/
import D5.S0.Tower.DBonacci.Values
namespace D5.S0.Tower.DBonacci.Gaps
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacci.Values
/-- The budget label carried by the terminal gap after reading `Q` digits. -/
def boundedTerminalFuel : (maxTrue fuel Q : Nat) -> Nat
  | _, fuel, 0 => fuel
  | maxTrue, 0, q + 1 => boundedTerminalFuel maxTrue maxTrue q
  | maxTrue, fuel + 1, q + 1 => boundedTerminalFuel maxTrue fuel q
termination_by _ _ Q => Q
/-- Gap labels in prefix order, with repetitions retained. -/
def boundedGapFuelList : (maxTrue fuel Q : Nat) -> List Nat
  | _, _, 0 => []
  | maxTrue, 0, q + 1 => boundedGapFuelList maxTrue maxTrue q
  | maxTrue, fuel + 1, q + 1 =>
      boundedGapFuelList maxTrue maxTrue q ++
        boundedTerminalFuel maxTrue maxTrue q ::
          boundedGapFuelList maxTrue fuel q
termination_by _ _ Q => Q
/-- Transparent counting used by the executable finite measurement table. -/
def countGapFuel (needle : Nat) : List Nat -> Nat
  | [] => 0
  | fuel :: fuels => (if fuel = needle then 1 else 0) + countGapFuel needle fuels
/-- Multiplicities by decreasing run residue in the actual adjacent-gap recursion. -/
def dbonacciGapMultiplicityProfile : (d Q : Nat) -> List Nat
  | 0, _ => []
  | maxTrue + 1, Q =>
      (List.range (maxTrue + 1)).map fun residue =>
        countGapFuel (maxTrue - residue) (boundedGapFuelList maxTrue maxTrue Q)
/-- The recursive label list has one entry for every adjacent pair. -/
theorem boundedGapFuelList_length (maxTrue fuel Q : Nat) (hfuel : fuel ≤ maxTrue) :
    (boundedGapFuelList maxTrue fuel Q).length =
      Fintype.card (BoundedRunName maxTrue fuel Q) - 1 := by
  induction Q generalizing fuel with
  | zero =>
      have hcard : Fintype.card (BoundedRunName maxTrue fuel 0) = 1 := by
        apply Fintype.card_eq_one_iff.mpr
        refine ⟨⟨fun i => Fin.elim0 i, by simp [runAdmissible]⟩, ?_⟩
        intro name
        apply Subtype.ext
        funext i; exact Fin.elim0 i
      simp [boundedGapFuelList, hcard]
  | succ Q ih =>
      cases fuel with
      | zero =>
          rw [boundedGapFuelList, ih maxTrue le_rfl,
            bounded_run_name_card_zero]
      | succ fuel =>
          rw [boundedGapFuelList, List.length_append, List.length_cons,
            ih maxTrue le_rfl, ih fuel (by omega),
            bounded_run_name_card_succ]
          have hleft := bounded_run_level_pos maxTrue maxTrue Q
          have hright := bounded_run_level_pos maxTrue fuel Q
          omega
example :
    [[dbonacciGapMultiplicityProfile 2 2, dbonacciGapMultiplicityProfile 2 3,
      dbonacciGapMultiplicityProfile 2 4, dbonacciGapMultiplicityProfile 2 5],
     [dbonacciGapMultiplicityProfile 3 2, dbonacciGapMultiplicityProfile 3 3,
      dbonacciGapMultiplicityProfile 3 4, dbonacciGapMultiplicityProfile 3 5],
     [dbonacciGapMultiplicityProfile 4 2, dbonacciGapMultiplicityProfile 4 3,
      dbonacciGapMultiplicityProfile 4 4, dbonacciGapMultiplicityProfile 4 5]] =
    [[[1, 1], [3, 1], [4, 3], [8, 4]],
     [[2, 1, 0], [3, 2, 1], [7, 3, 2], [13, 7, 3]],
     [[2, 1, 0, 0], [4, 2, 1, 0], [7, 4, 2, 1], [15, 7, 4, 2]]] := by
  norm_num [dbonacciGapMultiplicityProfile, boundedGapFuelList, boundedTerminalFuel,
    countGapFuel, List.range, List.range.loop, List.map]
/-- The endpoint attached to a run budget: the first `fuel+1` reciprocal powers. -/
noncomputable def dbonacciBudgetBound (d fuel : Nat) : Real :=
  ∑ i ∈ Finset.range (fuel + 1), (dbonacciPerronRoot d)⁻¹ ^ (i + 1)
theorem dbonacci_root_inv_pos (d : Nat) (hd : 2 ≤ d) :
    0 < (dbonacciPerronRoot d)⁻¹ :=
  inv_pos.mpr (lt_trans (by norm_num) (one_lt_dbonacciPerronRoot d hd))
theorem dbonacciBudgetBound_pos (d fuel : Nat) (hd : 2 ≤ d) :
    0 < dbonacciBudgetBound d fuel := by
  unfold dbonacciBudgetBound
  have hterm : 0 < (dbonacciPerronRoot d)⁻¹ ^ (0 + 1) :=
    pow_pos (dbonacci_root_inv_pos d hd) _
  exact Finset.sum_pos' (fun i _ => (pow_pos (dbonacci_root_inv_pos d hd) _).le)
    ⟨0, by simp, hterm⟩
theorem dbonacciBudgetBound_succ_add (d fuel : Nat) :
    dbonacciBudgetBound d (fuel + 1) = dbonacciBudgetBound d fuel +
      (dbonacciPerronRoot d)⁻¹ ^ (fuel + 2) := by
  unfold dbonacciBudgetBound
  rw [show fuel + 1 + 1 = (fuel + 1) + 1 by omega, Finset.sum_range_succ]
theorem dbonacciBudgetBound_succ (d fuel : Nat) :
    dbonacciBudgetBound d (fuel + 1) =
      (dbonacciPerronRoot d)⁻¹ +
        (dbonacciPerronRoot d)⁻¹ * dbonacciBudgetBound d fuel := by
  unfold dbonacciBudgetBound
  rw [show fuel + 1 + 1 = (fuel + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.zero_add, pow_one]
  have hshift :
      (∑ i ∈ Finset.range (fuel + 1),
          (dbonacciPerronRoot d)⁻¹ ^ (i + 1 + 1)) =
        ∑ i ∈ Finset.range (fuel + 1),
          (dbonacciPerronRoot d)⁻¹ * (dbonacciPerronRoot d)⁻¹ ^ (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ']
  rw [hshift, ← Finset.mul_sum]
  ring
/-- At full budget the endpoint is one, exactly the Perron reciprocal equation. -/
theorem dbonacciBudgetBound_full (d : Nat) (hd : 2 ≤ d) :
    dbonacciBudgetBound d (d - 1) = 1 := by
  rw [dbonacciBudgetBound]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
  exact dbonacciPerronRoot_reciprocalSum d hd
theorem dbonacciBudgetBound_strictMono (d : Nat) (hd : 2 ≤ d) :
    StrictMono (dbonacciBudgetBound d) := by
  apply strictMono_nat_of_lt_succ
  intro fuel
  rw [dbonacciBudgetBound_succ_add]
  exact lt_add_of_pos_right _ (pow_pos (dbonacci_root_inv_pos d hd) _)
/-- A label `fuel` at level `Q` denotes this real gap length. -/
noncomputable def dbonacciGapLength (d Q fuel : Nat) : Real :=
  (dbonacciPerronRoot d)⁻¹ ^ Q * dbonacciBudgetBound d fuel
theorem dbonacciGapLength_pos (d Q fuel : Nat) (hd : 2 ≤ d) :
    0 < dbonacciGapLength d Q fuel := by
  exact mul_pos (pow_pos (dbonacci_root_inv_pos d hd) _)
    (dbonacciBudgetBound_pos d fuel hd)
theorem dbonacciGapLength_scale (d Q fuel : Nat) :
    (dbonacciPerronRoot d)⁻¹ * dbonacciGapLength d Q fuel =
      dbonacciGapLength d (Q + 1) fuel := by
  unfold dbonacciGapLength
  rw [pow_succ']
  ring
theorem boundedTerminalFuel_le (maxTrue fuel Q : Nat) (hfuel : fuel ≤ maxTrue) :
    boundedTerminalFuel maxTrue fuel Q ≤ maxTrue := by
  induction Q generalizing fuel with
  | zero => simpa [boundedTerminalFuel] using hfuel
  | succ Q ih =>
      cases fuel with
      | zero => simpa [boundedTerminalFuel] using ih maxTrue le_rfl
      | succ fuel => simpa [boundedTerminalFuel] using ih fuel (by omega)
theorem boundedTerminalFuel_of_le (maxTrue fuel Q : Nat) (hQ : Q ≤ fuel) :
    boundedTerminalFuel maxTrue fuel Q = fuel - Q := by
  induction Q generalizing fuel with
  | zero => simp [boundedTerminalFuel]
  | succ Q ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [boundedTerminalFuel, ih fuel (by omega)]
          omega
/-- The final index in a nonempty bounded-run layer. -/
def boundedLastIndex (maxTrue fuel Q : Nat) :
    Fin (Fintype.card (BoundedRunName maxTrue fuel Q)) :=
  ⟨Fintype.card (BoundedRunName maxTrue fuel Q) - 1,
    Nat.sub_lt (bounded_run_level_pos maxTrue fuel Q) (by omega)⟩
/-- The distance from the final bounded-run value to its budget endpoint. -/
noncomputable def boundedTerminalGap (maxTrue fuel Q : Nat) : Real :=
  dbonacciBudgetBound (maxTrue + 1) fuel -
    boundedIndexedNameValue maxTrue fuel Q (boundedLastIndex maxTrue fuel Q)
/-- The difference at a specified adjacent bounded-run index. -/
noncomputable def boundedIndexedGap (maxTrue fuel Q : Nat)
    (i : Fin (Fintype.card (BoundedRunName maxTrue fuel Q) - 1)) : Real :=
  boundedIndexedNameValue maxTrue fuel Q
      ⟨i.1 + 1, by have := i.2; have := bounded_run_level_pos maxTrue fuel Q; omega⟩ -
    boundedIndexedNameValue maxTrue fuel Q
      ⟨i.1, by have := i.2; have := bounded_run_level_pos maxTrue fuel Q; omega⟩
/-- Labels possible in a bounded state; zero budget delays their first appearance by one level. -/
def BoundedGapLabelAllowed (maxTrue fuel Q label : Nat) : Prop :=
  label ≤ maxTrue ∧
    if fuel = 0 then maxTrue + 2 ≤ Q + label else maxTrue + 1 ≤ Q + label
/-- Adjacent gaps and the terminal gap obey the same finite-state recursion. -/
def BoundedGapInvariant (maxTrue fuel Q : Nat) : Prop :=
  (∀ k (hk : k + 1 < Fintype.card (BoundedRunName maxTrue fuel Q)),
      ∃ label, BoundedGapLabelAllowed maxTrue fuel Q label ∧
        boundedIndexedNameValue maxTrue fuel Q ⟨k + 1, hk⟩ -
          boundedIndexedNameValue maxTrue fuel Q
            ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩ =
          dbonacciGapLength (maxTrue + 1) Q label) ∧
    boundedTerminalGap maxTrue fuel Q =
      dbonacciGapLength (maxTrue + 1) Q
        (boundedTerminalFuel maxTrue fuel Q)
/-- The bounded-run automaton gives the adjacent and terminal gap invariant at every level. -/
theorem bounded_gap_invariant (maxTrue fuel Q : Nat)
    (hmax : 1 ≤ maxTrue) (hfuel : fuel ≤ maxTrue) :
    BoundedGapInvariant maxTrue fuel Q := by
  induction Q generalizing fuel with
  | zero =>
      have hcard : Fintype.card (BoundedRunName maxTrue fuel 0) = 1 := by
        apply Fintype.card_eq_one_iff.mpr
        refine ⟨⟨fun i => Fin.elim0 i, by simp [runAdmissible]⟩, ?_⟩
        intro name
        apply Subtype.ext
        funext i
        exact Fin.elim0 i
      constructor
      · intro k hk
        rw [hcard] at hk
        omega
      · have hlast : boundedLastIndex maxTrue fuel 0 =
            ⟨0, bounded_run_level_pos maxTrue fuel 0⟩ := by
          apply Fin.ext
          simp [boundedLastIndex, hcard]
        rw [boundedTerminalGap, hlast, boundedIndexedNameValue_level_zero]
        simp [dbonacciGapLength, boundedTerminalFuel]
  | succ q ih =>
      cases fuel with
      | zero =>
          have hfull := ih maxTrue le_rfl
          constructor
          · intro k hk
            have hkfull : k + 1 <
                Fintype.card (BoundedRunName maxTrue maxTrue q) := by
              calc
                k + 1 < Fintype.card (BoundedRunName maxTrue 0 (q + 1)) := hk
                _ = _ := bounded_run_name_card_zero maxTrue q
            obtain ⟨label, hlabel, hgap⟩ := hfull.1 k hkfull
            refine ⟨label, ?_, ?_⟩
            · unfold BoundedGapLabelAllowed at hlabel ⊢
              simp only [show maxTrue ≠ 0 by omega, ↓reduceIte] at hlabel
              simp only [↓reduceIte]
              omega
            · rw [boundedIndexedNameValue_zero_budget maxTrue q ⟨k + 1, hk⟩,
                boundedIndexedNameValue_zero_budget maxTrue q
                  ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩]
              have hright :
                  Fin.cast (bounded_run_name_card_zero maxTrue q) ⟨k + 1, hk⟩ =
                    ⟨k + 1, hkfull⟩ := by
                apply Fin.ext
                simp
              have hleft :
                  Fin.cast (bounded_run_name_card_zero maxTrue q)
                      ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩ =
                    ⟨k, lt_trans (Nat.lt_succ_self k) hkfull⟩ := by
                apply Fin.ext
                simp
              rw [hright, hleft]
              calc
                (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                      boundedIndexedNameValue maxTrue maxTrue q ⟨k + 1, hkfull⟩ -
                    (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                      boundedIndexedNameValue maxTrue maxTrue q
                        ⟨k, lt_trans (Nat.lt_succ_self k) hkfull⟩ =
                    (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                      (boundedIndexedNameValue maxTrue maxTrue q ⟨k + 1, hkfull⟩ -
                        boundedIndexedNameValue maxTrue maxTrue q
                          ⟨k, lt_trans (Nat.lt_succ_self k) hkfull⟩) := by ring
                _ = (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                    dbonacciGapLength (maxTrue + 1) q label := by rw [hgap]
                _ = dbonacciGapLength (maxTrue + 1) (q + 1) label :=
                  dbonacciGapLength_scale (maxTrue + 1) q label
          · have hlastCast :
                Fin.cast (bounded_run_name_card_zero maxTrue q)
                    (boundedLastIndex maxTrue 0 (q + 1)) =
                  boundedLastIndex maxTrue maxTrue q := by
              apply Fin.ext
              simp [boundedLastIndex]
              rw [bounded_run_name_card_zero maxTrue q]
            rw [boundedTerminalGap, boundedIndexedNameValue_zero_budget, hlastCast]
            rw [show dbonacciBudgetBound (maxTrue + 1) 0 =
                (dbonacciPerronRoot (maxTrue + 1))⁻¹ by
              simp [dbonacciBudgetBound]]
            have hterminal := hfull.2
            rw [boundedTerminalGap] at hterminal
            have hbudget : dbonacciBudgetBound (maxTrue + 1) maxTrue = 1 := by
              simpa using dbonacciBudgetBound_full (maxTrue + 1) (by omega)
            calc
              (dbonacciPerronRoot (maxTrue + 1))⁻¹ -
                    (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                      boundedIndexedNameValue maxTrue maxTrue q
                        (boundedLastIndex maxTrue maxTrue q) =
                  (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                    (dbonacciBudgetBound (maxTrue + 1) maxTrue -
                      boundedIndexedNameValue maxTrue maxTrue q
                        (boundedLastIndex maxTrue maxTrue q)) := by
                rw [hbudget]
                ring
              _ = (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                  dbonacciGapLength (maxTrue + 1) q
                    (boundedTerminalFuel maxTrue maxTrue q) := by rw [hterminal]
              _ = dbonacciGapLength (maxTrue + 1) (q + 1)
                  (boundedTerminalFuel maxTrue 0 (q + 1)) := by
                simpa [boundedTerminalFuel] using
                  dbonacciGapLength_scale (maxTrue + 1) q
                    (boundedTerminalFuel maxTrue maxTrue q)
      | succ fuel =>
          have hfuel' : fuel ≤ maxTrue := by omega
          have hfull := ih maxTrue le_rfl
          have hlower := ih fuel hfuel'
          let lowerCount := Fintype.card (BoundedRunName maxTrue maxTrue q)
          let upperCount := Fintype.card (BoundedRunName maxTrue fuel q)
          have htotal :
              Fintype.card (BoundedRunName maxTrue (fuel + 1) (q + 1)) =
                lowerCount + upperCount := by
            exact bounded_run_name_card_succ maxTrue fuel q
          constructor
          · intro k hk
            have hkTotal : k + 1 < lowerCount + upperCount := by
              rw [← htotal]
              exact hk
            by_cases hinsideLower : k + 1 < lowerCount
            · obtain ⟨label, hlabel, hgap⟩ := hfull.1 k hinsideLower
              refine ⟨label, ?_, ?_⟩
              · unfold BoundedGapLabelAllowed at hlabel ⊢
                simp only [show maxTrue ≠ 0 by omega, ↓reduceIte] at hlabel
                simp only [Nat.succ_ne_zero, ↓reduceIte]
                omega
              · rw [boundedIndexedNameValue_lower maxTrue fuel q ⟨k + 1, hk⟩
                    hinsideLower,
                  boundedIndexedNameValue_lower maxTrue fuel q
                    ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩
                      (by simpa using lt_trans (Nat.lt_succ_self k) hinsideLower)]
                calc
                  (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                        boundedIndexedNameValue maxTrue maxTrue q
                          ⟨k + 1, hinsideLower⟩ -
                      (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                        boundedIndexedNameValue maxTrue maxTrue q
                          ⟨k, lt_trans (Nat.lt_succ_self k) hinsideLower⟩ =
                      (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                        (boundedIndexedNameValue maxTrue maxTrue q
                            ⟨k + 1, hinsideLower⟩ -
                          boundedIndexedNameValue maxTrue maxTrue q
                            ⟨k, lt_trans (Nat.lt_succ_self k) hinsideLower⟩) := by ring
                  _ = (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                      dbonacciGapLength (maxTrue + 1) q label := by rw [hgap]
                  _ = dbonacciGapLength (maxTrue + 1) (q + 1) label :=
                    dbonacciGapLength_scale _ _ _
            · have hlowerLe : lowerCount ≤ k + 1 := Nat.le_of_not_gt hinsideLower
              by_cases hboundary : k + 1 = lowerCount
              · have hkLower : k < lowerCount := by omega
                have hrightUpper : lowerCount ≤ k + 1 := hlowerLe
                rw [boundedIndexedNameValue_lower maxTrue fuel q
                      ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩ hkLower,
                    boundedIndexedNameValue_upper maxTrue fuel q ⟨k + 1, hk⟩
                      hrightUpper]
                have hrightIndex :
                    (⟨k + 1 - lowerCount, by
                        dsimp [lowerCount, upperCount] at hkTotal ⊢
                        omega⟩ : Fin upperCount) =
                      ⟨0, by
                        dsimp [upperCount]
                        exact bounded_run_level_pos maxTrue fuel q⟩ := by
                  apply Fin.ext
                  simp [hboundary]
                have hleftIndex :
                    (⟨k, hkLower⟩ : Fin lowerCount) =
                      boundedLastIndex maxTrue maxTrue q := by
                  apply Fin.ext
                  simp [boundedLastIndex, lowerCount]
                  have := bounded_run_level_pos maxTrue maxTrue q
                  omega
                rw [hrightIndex, boundedIndexedNameValue_zero, hleftIndex]
                simp only [mul_zero, add_zero]
                have labelLe := boundedTerminalFuel_le maxTrue maxTrue q le_rfl
                have hterminal := hfull.2
                refine ⟨boundedTerminalFuel maxTrue maxTrue q, ?_, ?_⟩
                · unfold BoundedGapLabelAllowed
                  simp only [Nat.succ_ne_zero, ↓reduceIte]
                  refine ⟨labelLe, ?_⟩
                  by_cases hq : q ≤ maxTrue
                  · rw [boundedTerminalFuel_of_le maxTrue maxTrue q hq]
                    omega
                  · omega
                · rw [boundedTerminalGap] at hterminal
                  have hbudget : dbonacciBudgetBound (maxTrue + 1) maxTrue = 1 := by
                    simpa using dbonacciBudgetBound_full (maxTrue + 1) (by omega)
                  calc
                    (dbonacciPerronRoot (maxTrue + 1))⁻¹ -
                          (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                            boundedIndexedNameValue maxTrue maxTrue q
                              (boundedLastIndex maxTrue maxTrue q) =
                        (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                          (dbonacciBudgetBound (maxTrue + 1) maxTrue -
                            boundedIndexedNameValue maxTrue maxTrue q
                              (boundedLastIndex maxTrue maxTrue q)) := by
                      rw [hbudget]
                      ring
                    _ = (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                        dbonacciGapLength (maxTrue + 1) q
                          (boundedTerminalFuel maxTrue maxTrue q) := by rw [hterminal]
                    _ = dbonacciGapLength (maxTrue + 1) (q + 1)
                        (boundedTerminalFuel maxTrue maxTrue q) :=
                      dbonacciGapLength_scale _ _ _
              · have hkUpper : lowerCount ≤ k := by omega
                have hresBound : (k - lowerCount) + 1 < upperCount := by omega
                obtain ⟨label, hlabel, hgap⟩ :=
                  hlower.1 (k - lowerCount) hresBound
                refine ⟨label, ?_, ?_⟩
                · unfold BoundedGapLabelAllowed at hlabel ⊢
                  simp only [Nat.succ_ne_zero, ↓reduceIte]
                  split at hlabel <;> omega
                · rw [boundedIndexedNameValue_upper maxTrue fuel q ⟨k + 1, hk⟩
                      hlowerLe,
                    boundedIndexedNameValue_upper maxTrue fuel q
                      ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩ hkUpper]
                  have hrightIndex :
                      (⟨k + 1 - lowerCount, by
                          dsimp [lowerCount, upperCount] at hkTotal ⊢
                          omega⟩ : Fin upperCount) =
                        ⟨(k - lowerCount) + 1, hresBound⟩ := by
                    apply Fin.ext
                    change k + 1 - lowerCount = k - lowerCount + 1
                    omega
                  have hleftIndex :
                      (⟨k - lowerCount, by
                          dsimp [lowerCount, upperCount] at hkTotal ⊢
                          omega⟩ : Fin upperCount) =
                        ⟨k - lowerCount,
                          lt_trans (Nat.lt_succ_self (k - lowerCount)) hresBound⟩ := by
                    apply Fin.ext
                    simp
                  rw [hrightIndex, hleftIndex]
                  calc
                    (dbonacciPerronRoot (maxTrue + 1))⁻¹ +
                            (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                              boundedIndexedNameValue maxTrue fuel q
                                ⟨k - lowerCount + 1, hresBound⟩ -
                          ((dbonacciPerronRoot (maxTrue + 1))⁻¹ +
                            (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                              boundedIndexedNameValue maxTrue fuel q
                                ⟨k - lowerCount,
                                  lt_trans (Nat.lt_succ_self (k - lowerCount))
                                    hresBound⟩) =
                        (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                          (boundedIndexedNameValue maxTrue fuel q
                              ⟨k - lowerCount + 1, hresBound⟩ -
                            boundedIndexedNameValue maxTrue fuel q
                              ⟨k - lowerCount,
                                lt_trans (Nat.lt_succ_self (k - lowerCount))
                                  hresBound⟩) := by ring
                    _ = (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                        dbonacciGapLength (maxTrue + 1) q label := by rw [hgap]
                    _ = dbonacciGapLength (maxTrue + 1) (q + 1) label :=
                      dbonacciGapLength_scale _ _ _
          · have hlastUpper : lowerCount ≤
                (boundedLastIndex maxTrue (fuel + 1) (q + 1)).1 := by
              simp [boundedLastIndex]
              rw [htotal]
              have := bounded_run_level_pos maxTrue fuel q
              omega
            have hresIndex :
                (⟨(boundedLastIndex maxTrue (fuel + 1) (q + 1)).1 - lowerCount,
                    by
                      simp [boundedLastIndex]
                      rw [htotal]
                      have := bounded_run_level_pos maxTrue fuel q
                      omega⟩ : Fin upperCount) =
                  boundedLastIndex maxTrue fuel q := by
              apply Fin.ext
              simp [boundedLastIndex]
              rw [htotal]
              have := bounded_run_level_pos maxTrue fuel q
              omega
            rw [boundedTerminalGap,
              boundedIndexedNameValue_upper maxTrue fuel q
                (boundedLastIndex maxTrue (fuel + 1) (q + 1)) hlastUpper,
              hresIndex, dbonacciBudgetBound_succ]
            have hterminal := hlower.2
            rw [boundedTerminalGap] at hterminal
            calc
              (dbonacciPerronRoot (maxTrue + 1))⁻¹ +
                      (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                        dbonacciBudgetBound (maxTrue + 1) fuel -
                    ((dbonacciPerronRoot (maxTrue + 1))⁻¹ +
                      (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                        boundedIndexedNameValue maxTrue fuel q
                          (boundedLastIndex maxTrue fuel q)) =
                  (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                    (dbonacciBudgetBound (maxTrue + 1) fuel -
                      boundedIndexedNameValue maxTrue fuel q
                        (boundedLastIndex maxTrue fuel q)) := by ring
              _ = (dbonacciPerronRoot (maxTrue + 1))⁻¹ *
                  dbonacciGapLength (maxTrue + 1) q
                    (boundedTerminalFuel maxTrue fuel q) := by rw [hterminal]
              _ = dbonacciGapLength (maxTrue + 1) (q + 1)
                  (boundedTerminalFuel maxTrue (fuel + 1) (q + 1)) := by
                simpa [boundedTerminalFuel] using
                  dbonacciGapLength_scale (maxTrue + 1) q
                    (boundedTerminalFuel maxTrue fuel q)
/-- A label occurs when one adjacent full-budget index realizes its length. -/
def BoundedGapOccurs (maxTrue Q label : Nat) : Prop :=
  ∃ i : Fin (Fintype.card (BoundedRunName maxTrue maxTrue Q) - 1),
    boundedIndexedGap maxTrue maxTrue Q i =
      dbonacciGapLength (maxTrue + 1) Q label
/-- An occurring full-budget gap persists in the zero-prefix block one level higher. -/
theorem boundedGapOccurs_lower (maxTrue Q label : Nat) (hmax : 1 ≤ maxTrue)
    (hgap : BoundedGapOccurs maxTrue Q label) :
    BoundedGapOccurs maxTrue (Q + 1) label := by
  obtain ⟨fuel, rfl⟩ : ∃ fuel, maxTrue = fuel + 1 := ⟨maxTrue - 1, by omega⟩
  obtain ⟨i, hi⟩ := hgap
  have hiNext : i.1 + 1 <
      Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) Q) := by
    have := i.2
    have := bounded_run_level_pos (fuel + 1) (fuel + 1) Q
    omega
  have htotal := bounded_run_name_card_succ (fuel + 1) fuel Q
  let j : Fin
      (Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) (Q + 1)) - 1) :=
    ⟨i.1, by
      rw [htotal]
      have hupper := bounded_run_level_pos (fuel + 1) fuel Q
      omega⟩
  refine ⟨j, ?_⟩
  unfold boundedIndexedGap
  rw [boundedIndexedNameValue_lower (fuel + 1) fuel Q
      ⟨j.1 + 1, by
        dsimp [j]
        rw [htotal]
        have hupper := bounded_run_level_pos (fuel + 1) fuel Q
        omega⟩ (by simpa [j] using hiNext),
    boundedIndexedNameValue_lower (fuel + 1) fuel Q
      ⟨j.1, by
        dsimp [j]
        rw [htotal]
        have hupper := bounded_run_level_pos (fuel + 1) fuel Q
        omega⟩ (by have := hiNext; simp [j]; omega)]
  have hright :
      (⟨j.1 + 1, by simpa [j] using hiNext⟩ :
          Fin (Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) Q))) =
        ⟨i.1 + 1, hiNext⟩ := by
    apply Fin.ext
    simp [j]
  have hleft :
      (⟨j.1, by have := hiNext; simp [j]; omega⟩ :
          Fin (Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) Q))) =
        ⟨i.1, by have := hiNext; omega⟩ := by
    apply Fin.ext
    simp [j]
  rw [hright, hleft]
  unfold boundedIndexedGap at hi
  calc
    (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ *
          boundedIndexedNameValue (fuel + 1) (fuel + 1) Q ⟨i.1 + 1, hiNext⟩ -
        (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ *
          boundedIndexedNameValue (fuel + 1) (fuel + 1) Q
            ⟨i.1, by have := hiNext; omega⟩ =
      (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ *
        (boundedIndexedNameValue (fuel + 1) (fuel + 1) Q ⟨i.1 + 1, hiNext⟩ -
          boundedIndexedNameValue (fuel + 1) (fuel + 1) Q
            ⟨i.1, by have := hiNext; omega⟩) := by ring
    _ = (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ *
        dbonacciGapLength (fuel + 1 + 1) Q label := by rw [hi]
    _ = dbonacciGapLength (fuel + 1 + 1) (Q + 1) label :=
      dbonacciGapLength_scale _ _ _
/-- The boundary between the zero- and one-prefix blocks realizes the terminal label. -/
theorem boundedGapOccurs_boundary (maxTrue Q : Nat) (hmax : 1 ≤ maxTrue) :
    BoundedGapOccurs maxTrue (Q + 1) (boundedTerminalFuel maxTrue maxTrue Q) := by
  obtain ⟨fuel, rfl⟩ : ∃ fuel, maxTrue = fuel + 1 := ⟨maxTrue - 1, by omega⟩
  let lowerCount := Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) Q)
  let upperCount := Fintype.card (BoundedRunName (fuel + 1) fuel Q)
  have htotal :
      Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) (Q + 1)) =
        lowerCount + upperCount := bounded_run_name_card_succ (fuel + 1) fuel Q
  let i : Fin
      (Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) (Q + 1)) - 1) :=
    ⟨lowerCount - 1, by
      rw [htotal]
      have hlower := bounded_run_level_pos (fuel + 1) (fuel + 1) Q
      have hupper := bounded_run_level_pos (fuel + 1) fuel Q
      omega⟩
  refine ⟨i, ?_⟩
  have hiLeft : i.1 < lowerCount := by
    dsimp [i]
    exact Nat.sub_lt (by dsimp [lowerCount]; exact bounded_run_level_pos _ _ _) (by omega)
  have hiRight : lowerCount ≤ i.1 + 1 := by
    dsimp [i]
    have := bounded_run_level_pos (fuel + 1) (fuel + 1) Q
    dsimp [lowerCount] at ⊢
    omega
  have htotalNat :
      Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) (Q + 1)) =
        lowerCount + upperCount := htotal
  have hiLeftTotal :
      i.1 < Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) (Q + 1)) := by
    have hupper := bounded_run_level_pos (fuel + 1) fuel Q
    omega
  have hiRightTotal :
      i.1 + 1 < Fintype.card (BoundedRunName (fuel + 1) (fuel + 1) (Q + 1)) := by
    have hupper := bounded_run_level_pos (fuel + 1) fuel Q
    omega
  unfold boundedIndexedGap
  rw [boundedIndexedNameValue_lower (fuel + 1) fuel Q
        ⟨i.1, hiLeftTotal⟩ hiLeft,
      boundedIndexedNameValue_upper (fuel + 1) fuel Q
        ⟨i.1 + 1, hiRightTotal⟩ hiRight]
  have hrightIndex :
      (⟨i.1 + 1 - lowerCount, by
          dsimp [i, lowerCount, upperCount]
          have := bounded_run_level_pos (fuel + 1) fuel Q
          omega⟩ : Fin upperCount) =
        ⟨0, by dsimp [upperCount]; exact bounded_run_level_pos _ _ _⟩ := by
    apply Fin.ext
    dsimp [i]
    have := bounded_run_level_pos (fuel + 1) (fuel + 1) Q
    dsimp [lowerCount]
    omega
  have hleftIndex :
      (⟨i.1, hiLeft⟩ : Fin lowerCount) =
        boundedLastIndex (fuel + 1) (fuel + 1) Q := by
    apply Fin.ext
    simp [i, boundedLastIndex, lowerCount]
  rw [hrightIndex, boundedIndexedNameValue_zero, hleftIndex]
  simp only [mul_zero, add_zero]
  have hterminal := (bounded_gap_invariant (fuel + 1) (fuel + 1) Q
    (by omega) le_rfl).2
  rw [boundedTerminalGap] at hterminal
  have hbudget : dbonacciBudgetBound (fuel + 1 + 1) (fuel + 1) = 1 := by
    simpa [show fuel + 1 + 1 = fuel + 2 by omega] using
      dbonacciBudgetBound_full (fuel + 2) (by omega)
  calc
    (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ -
          (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ *
            boundedIndexedNameValue (fuel + 1) (fuel + 1) Q
              (boundedLastIndex (fuel + 1) (fuel + 1) Q) =
        (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ *
          (dbonacciBudgetBound (fuel + 1 + 1) (fuel + 1) -
            boundedIndexedNameValue (fuel + 1) (fuel + 1) Q
              (boundedLastIndex (fuel + 1) (fuel + 1) Q)) := by
      rw [hbudget]
      ring
    _ = (dbonacciPerronRoot (fuel + 1 + 1))⁻¹ *
        dbonacciGapLength (fuel + 1 + 1) Q
          (boundedTerminalFuel (fuel + 1) (fuel + 1) Q) := by rw [hterminal]
    _ = dbonacciGapLength (fuel + 1 + 1) (Q + 1)
        (boundedTerminalFuel (fuel + 1) (fuel + 1) Q) :=
      dbonacciGapLength_scale _ _ _
/-- Every label in `[d-Q,d)` is realized by an adjacent full-budget gap. -/
theorem boundedGapOccurs_of_mem_Ico (maxTrue Q label : Nat) (hmax : 1 ≤ maxTrue)
    (hlabel : label ∈ Finset.Ico (maxTrue + 1 - Q) (maxTrue + 1)) :
    BoundedGapOccurs maxTrue Q label := by
  induction Q with
  | zero => simp at hlabel
  | succ Q ih =>
      by_cases hold : label ∈ Finset.Ico (maxTrue + 1 - Q) (maxTrue + 1)
      · exact boundedGapOccurs_lower maxTrue Q label hmax (ih hold)
      · by_cases hQ : Q ≤ maxTrue
        · have hnew : label = maxTrue - Q := by
            simp only [Finset.mem_Ico] at hlabel hold
            omega
          rw [hnew, ← boundedTerminalFuel_of_le maxTrue maxTrue Q hQ]
          exact boundedGapOccurs_boundary maxTrue Q hmax
        · exfalso
          apply hold
          simp only [Finset.mem_Ico] at hlabel ⊢
          omega
/-- The finite set of differences between consecutive d-bonacci values. -/
noncomputable def adjacentGapSpectrum (d Q : Nat) : Finset Real :=
  match d with
  | 0 => ∅
  | maxTrue + 1 =>
      Finset.univ.image (boundedIndexedGap maxTrue maxTrue Q)
/-- The exact spectrum is indexed by the budget interval `[d-Q,d)`. -/
theorem adjacent_gap_spectrum (d Q : Nat) (hd : 2 ≤ d) :
    adjacentGapSpectrum d Q =
      (Finset.Ico (d - Q) d).image (dbonacciGapLength d Q) := by
  obtain ⟨maxTrue, rfl⟩ : ∃ maxTrue, d = maxTrue + 1 := ⟨d - 1, by omega⟩
  have hmax : 1 ≤ maxTrue := by omega
  ext gap
  constructor
  · intro hgap
    simp only [adjacentGapSpectrum, Finset.mem_image, Finset.mem_univ, true_and] at hgap
    obtain ⟨i, rfl⟩ := hgap
    obtain ⟨label, hlabel, hvalue⟩ :=
      (bounded_gap_invariant maxTrue maxTrue Q hmax le_rfl).1 i.1 (by
        have := i.2
        have := bounded_run_level_pos maxTrue maxTrue Q
        omega)
    rw [Finset.mem_image]
    refine ⟨label, ?_, ?_⟩
    · unfold BoundedGapLabelAllowed at hlabel
      simp only [show maxTrue ≠ 0 by omega, ↓reduceIte] at hlabel
      simp only [Finset.mem_Ico]
      omega
    · simpa [boundedIndexedGap] using hvalue.symm
  · intro hgap
    rw [Finset.mem_image] at hgap
    obtain ⟨label, hlabel, rfl⟩ := hgap
    obtain ⟨i, hi⟩ := boundedGapOccurs_of_mem_Ico maxTrue Q label hmax hlabel
    simp only [adjacentGapSpectrum, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, hi⟩
theorem dbonacciGapLength_strictMono (d Q : Nat) (hd : 2 ≤ d) :
    StrictMono (dbonacciGapLength d Q) := by
  intro left right hlr
  unfold dbonacciGapLength
  exact mul_lt_mul_of_pos_left
    (dbonacciBudgetBound_strictMono d hd hlr)
    (pow_pos (dbonacci_root_inv_pos d hd) _)
/-- The adjacent-gap spectrum has exactly `min d Q` elements. -/
theorem adjacent_gap_spectrum_card (d Q : Nat) (hd : 2 ≤ d) :
    (adjacentGapSpectrum d Q).card = min d Q := by
  rw [adjacent_gap_spectrum d Q hd,
    Finset.card_image_of_injective _ (dbonacciGapLength_strictMono d Q hd).injective]
  rw [Nat.card_Ico]
  omega
/-- The full `d`-length spectrum appears exactly at and above level `d`. -/
theorem adjacent_gap_spectrum_card_eq_order_iff (d Q : Nat) (hd : 2 ≤ d) :
    (adjacentGapSpectrum d Q).card = d ↔ d ≤ Q := by
  rw [adjacent_gap_spectrum_card d Q hd]
  omega
/-- Every consecutive indexed difference has one of the exact spectrum labels. -/
theorem consecutive_nameValue_gap (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1)) :
    ∃ label ∈ Finset.Ico (d - Q) d,
      indexedNameValue d Q
          ⟨i.1 + 1, by have := i.2; have := dbonacci_level_pos d Q (by omega); omega⟩ -
        indexedNameValue d Q
          ⟨i.1, by have := i.2; have := dbonacci_level_pos d Q (by omega); omega⟩ =
        dbonacciGapLength d Q label := by
  obtain ⟨maxTrue, rfl⟩ : ∃ maxTrue, d = maxTrue + 1 := ⟨d - 1, by omega⟩
  have hmax : 1 ≤ maxTrue := by omega
  let hcount : dbonacci (maxTrue + 1) (Q + 2) =
      Fintype.card (BoundedRunName maxTrue maxTrue Q) :=
    (dbonacci_name_card (maxTrue + 1) Q).symm.trans
      (dbonacci_name_card_eq_bounded maxTrue Q)
  have hiNext : i.1 + 1 < Fintype.card (BoundedRunName maxTrue maxTrue Q) := by
    have hi := i.2
    have hpos := dbonacci_level_pos (maxTrue + 1) Q (by omega)
    rw [← hcount]
    omega
  obtain ⟨label, hlabel, hgap⟩ :=
    (bounded_gap_invariant maxTrue maxTrue Q hmax le_rfl).1 i.1 hiNext
  refine ⟨label, ?_, ?_⟩
  · unfold BoundedGapLabelAllowed at hlabel
    simp only [show maxTrue ≠ 0 by omega, ↓reduceIte] at hlabel
    simp only [Finset.mem_Ico]
    omega
  · rw [indexedNameValue_succ_eq_bounded, indexedNameValue_succ_eq_bounded]
    have hright :
        Fin.cast hcount
            ⟨i.1 + 1, by
              have := i.2
              have := dbonacci_level_pos (maxTrue + 1) Q (by omega)
              omega⟩ =
          ⟨i.1 + 1, hiNext⟩ := by
      apply Fin.ext
      simp
    have hleft :
        Fin.cast hcount
            ⟨i.1, by
              have := i.2
              have := dbonacci_level_pos (maxTrue + 1) Q (by omega)
              omega⟩ =
          ⟨i.1, lt_trans (Nat.lt_succ_self i.1) hiNext⟩ := by
      apply Fin.ext
      simp
    rw [hright, hleft]
    exact hgap
/-- The canonical prefix enumeration has strictly increasing real values. -/
theorem indexed_nameValue_strictMono (d Q : Nat) (hd : 2 ≤ d) :
    StrictMono (indexedNameValue d Q) := by
  have hpos := dbonacci_level_pos d Q (by omega)
  have hcard : dbonacci d (Q + 2) - 1 + 1 = dbonacci d (Q + 2) := by omega
  let values : Fin (dbonacci d (Q + 2) - 1 + 1) -> Real := fun i =>
    indexedNameValue d Q (Fin.cast hcard i)
  have hvalues : StrictMono values := Fin.strictMono_iff_lt_succ.2 fun i => by
    have hleft : Fin.cast hcard i.castSucc =
        (⟨i.1, by have := i.2; omega⟩ : Fin (dbonacci d (Q + 2))) := by
      apply Fin.ext
      simp
    have hright : Fin.cast hcard i.succ =
        (⟨i.1 + 1, by have := i.2; omega⟩ : Fin (dbonacci d (Q + 2))) := by
      apply Fin.ext
      simp
    obtain ⟨label, _, hgap⟩ := consecutive_nameValue_gap d Q hd i
    have hgapPos := dbonacciGapLength_pos d Q label hd
    dsimp [values]
    rw [hleft, hright]
    nlinarith
  intro i j hij
  let i' : Fin (dbonacci d (Q + 2) - 1 + 1) := Fin.cast hcard.symm i
  let j' : Fin (dbonacci d (Q + 2) - 1 + 1) := Fin.cast hcard.symm j
  have hij' : i' < j' := hij
  simpa [values, i', j'] using hvalues hij'
/-- Distinct d-bonacci names have distinct real values for every meaningful order. -/
theorem dbonacciNameValue_injective (d Q : Nat) (hd : 2 ≤ d) :
    Function.Injective (dbonacciNameValue d Q) := by
  intro left right hvalue
  apply (dbonacciIndexEquiv d Q).symm.injective
  apply (indexed_nameValue_strictMono d Q hd).injective
  simpa [indexedNameValue] using hvalue
/-- All level-`Q` d-bonacci name values, listed increasingly. -/
noncomputable def sortedNameValues (d Q : Nat) : List Real :=
  List.ofFn (indexedNameValue d Q)
theorem sortedNameValues_sorted (d Q : Nat) (hd : 2 ≤ d) :
    (sortedNameValues d Q).SortedLT := by
  unfold sortedNameValues
  exact (List.pairwise_ofFn.mpr (indexed_nameValue_strictMono d Q hd)).sortedLT
theorem sortedNameValues_toFinset (d Q : Nat) :
    (sortedNameValues d Q).toFinset = Finset.univ.image (dbonacciNameValue d Q) := by
  ext value
  simp only [List.mem_toFinset, sortedNameValues, List.mem_ofFn, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨dbonacciIndexEquiv d Q i, by simpa [indexedNameValue] using hi⟩
  · rintro ⟨name, hname⟩
    refine ⟨(dbonacciIndexEquiv d Q).symm name, ?_⟩
    simpa [indexedNameValue] using hname
end D5.S0.Tower.DBonacci.Gaps
