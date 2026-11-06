/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmComparison
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmComparison
   mirror-E: none(waiver:universal-actual-score-criterion)
   anchors: []
   utility: none
   digest: Exact strict failure criterion for the actual symmetric-ensemble comparison. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmClassification

/-!
The failure criterion is Theorem 3 of the verification note by Haobo Ma and
Wenlin Zhang (4 November 2026, CC BY 4.0 for that note only). Symmetric score
calculations are credited there to Hyunho Cha. The score supplier below proves
the formulas from the actual CFC score, so no scalar bridge is assumed.
Admission commitment: the complete strict failure iff with the actual optimal
active set, not only a sufficient condition inside one sign region.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.EquiprobablePgmComparison
open D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.EquiprobablePgmClassification
open D5.S3.Quantum.Measurement.EquiprobablePgmScores (symmetric_scores)
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore)

private theorem gap_criterion (q D b δ : ℝ) (hq : 0 < q) (hD : 0 < D) :
    2 * (4 * b ^ 2 / (3 * Real.sqrt D) + 2 * δ ^ 2 / (3 * D)) <
        2 * b ^ 2 / (3 * Real.sqrt q) ↔
      16 * q < D ∧
        2 * δ ^ 2 * Real.sqrt q /
          (Real.sqrt D * (Real.sqrt D - 4 * Real.sqrt q)) < b ^ 2 := by
  let Q := Real.sqrt q
  let T := Real.sqrt D
  have hQ : 0 < Q := Real.sqrt_pos.mpr hq
  have hT : 0 < T := Real.sqrt_pos.mpr hD
  have hQsq : Q ^ 2 = q := Real.sq_sqrt hq.le
  have hTsq : T ^ 2 = D := Real.sq_sqrt hD.le
  by_cases hbig : 16 * q < D
  · have hdiff : 0 < T - 4 * Q := by nlinarith [sq_nonneg (T - 4 * Q)]
    have hid : 2 * b ^ 2 / (3 * Q) -
        2 * (4 * b ^ 2 / (3 * T) + 2 * δ ^ 2 / (3 * D)) =
        (2 * (T - 4 * Q) / (3 * Q * T)) *
          (b ^ 2 - 2 * δ ^ 2 * Q / (T * (T - 4 * Q))) := by
      rw [← hTsq]
      field_simp
      ring
    have hfac : 0 < 2 * (T - 4 * Q) / (3 * Q * T) := by positivity
    change _ ↔ 16 * q < D ∧ 2 * δ ^ 2 * Q / (T * (T - 4 * Q)) < b ^ 2
    rw [and_iff_right hbig, ← sub_pos, hid, mul_pos_iff_of_pos_left hfac, sub_pos]
  · have hle : T ≤ 4 * Q := by nlinarith [sq_nonneg (T - 4 * Q)]
    have hcoh : 2 * b ^ 2 / (3 * Q) ≤ 8 * b ^ 2 / (3 * T) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 3 * Q)
        (by positivity : 0 < 3 * T)).mpr
      nlinarith [sq_nonneg b]
    have hpop : 0 ≤ 2 * δ ^ 2 / (3 * D) := by positivity
    have hn : ¬ 2 * (4 * b ^ 2 / (3 * T) + 2 * δ ^ 2 / (3 * D)) <
        2 * b ^ 2 / (3 * Q) := by
      intro h
      linarith
    exact iff_of_false hn (not_and_of_not_left _ hbig)

/-- Exact failure in the closed two-active region; either threshold equality
is nonfailure. The formulas remain actual matrix/CFC scores. -/
theorem pair_failure_iff (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) <
        pgmScore (rho a b c) {0, 1} - 1 / 3 ↔
      16 * (a * (1 - a)) < (2 * a + c) * (3 - 2 * a - c) ∧
        2 * (c - a) ^ 2 * Real.sqrt (a * (1 - a)) /
          (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) *
            (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) -
              4 * Real.sqrt (a * (1 - a)))) < b ^ 2 := by
  rw [(symmetric_scores a b c ha ha1 hc hc1).1,
    (symmetric_scores a b c ha ha1 hc hc1).2]
  exact gap_criterion _ _ _ _ (mul_pos ha (sub_pos.mpr ha1))
    (mul_pos (by positivity) (by linarith))

/-- The full active-set failure iff. It includes the closed pair region as an
essential conjunct; with three active effects the original comparison is equality. -/
theorem active_failure_iff (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hc : 0 < c) (hc1 : c < 1)
    (hd : 0 < a * (1 - a) - b ^ 2) :
    (∀ i, (rho a b c i).PosDef ∧ trace (rho a b c i) = 1) ∧
      (let A := Finset.univ.filter (fun i => optimalPovm a b c i ≠ 0)
       2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) <
           ((A.card : ℝ) - 1) * (pgmScore (rho a b c) A - 1 / 3) ↔
        |c - a| ≤ b ∧
          16 * (a * (1 - a)) < (2 * a + c) * (3 - 2 * a - c) ∧
          2 * (c - a) ^ 2 * Real.sqrt (a * (1 - a)) /
            (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) *
              (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) -
                4 * Real.sqrt (a * (1 - a)))) < b ^ 2) := by
  refine ⟨states_posDef a b c ha hc hc1 hd, ?_⟩
  dsimp only
  rw [(complete_classification a b c hb).2.2]
  by_cases hpair : |c - a| ≤ b
  · rw [if_pos hpair, and_iff_right hpair]
    norm_num only [Finset.card_pair (show (0 : Fin 3) ≠ 1 by decide),
      Nat.cast_ofNat, sub_self, sub_zero, one_mul, show (2 : ℝ) - 1 = 1 by norm_num]
    exact pair_failure_iff a b c ha ha1 hc hc1
  · simp [hpair]

end D5.S3.Quantum.Measurement.EquiprobablePgmComparison
