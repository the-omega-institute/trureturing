/- GID: D5/S0/Tower/DBonacci/Survivor
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/Survivor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: D-bonacci name-grid distance has a common normalized survivor carrier. -/

import D5.S0.Tower.DBonacci.Values
import D5.S0.Tower.Tribonacci.Survivor

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen Tribonacci survivor carrier and the
     existing order-three root and word-value bridges.
   * Pinned mathlib provides `Metric.infDist_nonneg`, but no d-bonacci grid,
     admissible-word specialization, or normalized survivor theorem.
   * Loogle returned no d-bonacci result. LeanSearch's public API endpoint
     returned HTTP 404, so no third-party package was introduced. -/

namespace D5.S0.Tower.DBonacci.Survivor

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacci.Values

/-- The level-`Q` d-bonacci grid is the image of all admissible name values. -/
def dbonacciNameGrid (d Q : Nat) : Set Real :=
  Set.range (dbonacciNameValue d Q)

/-- Indexed and intrinsic d-bonacci names determine the same real grid. -/
theorem dbonacciNameGrid_eq_indexedNameValue_range (d Q : Nat) :
    dbonacciNameGrid d Q = Set.range (indexedNameValue d Q) := by
  ext x
  constructor
  · rintro ⟨name, rfl⟩
    refine ⟨(dbonacciIndexEquiv d Q).symm name, ?_⟩
    simp [indexedNameValue]
  · rintro ⟨i, rfl⟩
    exact ⟨dbonacciIndexEquiv d Q i, rfl⟩

/-- Distance to the level-`Q` d-bonacci grid, normalized by `beta_d^Q`. -/
noncomputable def dbonacciSurvivor (d Q : Nat) (x : Real) : Real :=
  (dbonacciPerronRoot d) ^ (Q : Int) * Metric.infDist x (dbonacciNameGrid d Q)

/-- The general order-three run automaton and the frozen Tribonacci predicate agree. -/
theorem dbonacciAdmissible_three_iff (Q : Nat) (word : Fin Q -> Bool) :
    DBonacciAdmissible 3 Q word ↔
      D5.S0.Tower.Tribonacci.Names.TribonacciAdmissible Q word := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      match Q with
      | 0 => simp [DBonacciAdmissible, runAdmissible,
          D5.S0.Tower.Tribonacci.Names.TribonacciAdmissible]
      | 1 => simp [DBonacciAdmissible, runAdmissible,
          D5.S0.Tower.Tribonacci.Names.TribonacciAdmissible]
      | 2 => simp [DBonacciAdmissible, runAdmissible,
          D5.S0.Tower.Tribonacci.Names.TribonacciAdmissible]
      | n + 3 =>
          let tail := Fin.tail word
          have hword : word = Fin.cons (word 0) tail :=
            (Fin.cons_self_tail word).symm
          rw [hword]
          cases hzero : word 0 with
          | false =>
              simpa [DBonacciAdmissible, runAdmissible, hzero,
                D5.S0.Tower.Tribonacci.Names.admissible_cons_false] using
                  ih (n + 2) (by omega) tail
          | true =>
              let tailTwo := Fin.tail tail
              have htail : tail = Fin.cons (tail 0) tailTwo :=
                (Fin.cons_self_tail tail).symm
              rw [htail]
              cases hone : tail 0 with
              | false =>
                  simpa [DBonacciAdmissible, runAdmissible, hzero, hone,
                    D5.S0.Tower.Tribonacci.Names.admissible_cons_true_false] using
                      ih (n + 1) (by omega) tailTwo
              | true =>
                  let tailThree := Fin.tail tailTwo
                  have htailTwo : tailTwo = Fin.cons (tailTwo 0) tailThree :=
                    (Fin.cons_self_tail tailTwo).symm
                  rw [htailTwo]
                  cases htwo : tailTwo 0 with
                  | false =>
                      simpa [DBonacciAdmissible, runAdmissible, hzero, hone, htwo,
                        D5.S0.Tower.Tribonacci.Names.admissible_cons_true_true_false] using
                            ih n (by omega) tailThree
                  | true =>
                      simp [DBonacciAdmissible, runAdmissible,
                        D5.S0.Tower.Tribonacci.Names.TribonacciAdmissible]

/-- Intrinsic order-three d-bonacci values and frozen Tribonacci values have one image. -/
theorem dbonacciNameGrid_three_eq_tribonacciNameGrid (Q : Nat) :
    dbonacciNameGrid 3 Q =
      D5.S0.Tower.Tribonacci.Survivor.tribonacciNameGrid Q := by
  rw [D5.S0.Tower.Tribonacci.Survivor.tribonacciNameGrid_eq_nameValue_range]
  ext x
  constructor
  · rintro ⟨dname, rfl⟩
    let tname : D5.S0.Tower.Tribonacci.Names.TribonacciName Q :=
      ⟨dname.1, (dbonacciAdmissible_three_iff Q dname.1).1 dname.2⟩
    refine ⟨tname, ?_⟩
    exact (dbonacciNameValue_three_eq_tribonacciNameValue Q dname tname rfl).symm
  · rintro ⟨tname, rfl⟩
    let dname : DBonacciName 3 Q :=
      ⟨tname.1, (dbonacciAdmissible_three_iff Q tname.1).2 tname.2⟩
    refine ⟨dname, ?_⟩
    exact dbonacciNameValue_three_eq_tribonacciNameValue Q dname tname rfl

/-- The general carrier specializes exactly to the frozen Tribonacci survivor. -/
theorem dbonacciSurvivor_three_eq_tribonacciSurvivor (Q : Nat) (x : Real) :
    dbonacciSurvivor 3 Q x =
      D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor Q x := by
  unfold dbonacciSurvivor D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor
  rw [dbonacciPerronRoot_three_eq_tribonacciConstant,
    dbonacciNameGrid_three_eq_tribonacciNameGrid]

/-- Every meaningful d-bonacci survivor value is nonnegative. -/
theorem dbonacciSurvivor_nonneg (d Q : Nat) (x : Real) (hd : 2 ≤ d) :
    0 ≤ dbonacciSurvivor d Q x := by
  unfold dbonacciSurvivor
  exact mul_nonneg
    (zpow_pos (zero_lt_one.trans (one_lt_dbonacciPerronRoot d hd)) _).le
    Metric.infDist_nonneg

end D5.S0.Tower.DBonacci.Survivor
