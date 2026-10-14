import Reg.Support.FibonacciL22
import Mathlib.Tactic.IntervalCases

namespace Reg.Support.FibonacciL22
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open Reg.Support.FibonacciQuadratic
open _root_.Set
open scoped Topology
noncomputable section

private theorem p_0 :
    ClosedExpanded theta h[0] (compose (P.drop 0) lo) ∧
    ClosedExpanded theta h[0] (compose (P.drop 0) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_1 :
    ClosedExpanded theta h[1] (compose (P.drop 1) lo) ∧
    ClosedExpanded theta h[1] (compose (P.drop 1) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_2 :
    ClosedExpanded theta h[2] (compose (P.drop 2) lo) ∧
    ClosedExpanded theta h[2] (compose (P.drop 2) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_3 :
    ClosedExpanded theta h[3] (compose (P.drop 3) lo) ∧
    ClosedExpanded theta h[3] (compose (P.drop 3) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_4 :
    ClosedExpanded theta h[4] (compose (P.drop 4) lo) ∧
    ClosedExpanded theta h[4] (compose (P.drop 4) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_5 :
    ClosedExpanded theta h[5] (compose (P.drop 5) lo) ∧
    ClosedExpanded theta h[5] (compose (P.drop 5) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_6 :
    ClosedExpanded theta h[6] (compose (P.drop 6) lo) ∧
    ClosedExpanded theta h[6] (compose (P.drop 6) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_7 :
    ClosedExpanded theta h[7] (compose (P.drop 7) lo) ∧
    ClosedExpanded theta h[7] (compose (P.drop 7) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_8 :
    ClosedExpanded theta h[8] (compose (P.drop 8) lo) ∧
    ClosedExpanded theta h[8] (compose (P.drop 8) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_9 :
    ClosedExpanded theta h[9] (compose (P.drop 9) lo) ∧
    ClosedExpanded theta h[9] (compose (P.drop 9) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_10 :
    ClosedExpanded theta h[10] (compose (P.drop 10) lo) ∧
    ClosedExpanded theta h[10] (compose (P.drop 10) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_11 :
    ClosedExpanded theta h[11] (compose (P.drop 11) lo) ∧
    ClosedExpanded theta h[11] (compose (P.drop 11) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_12 :
    ClosedExpanded theta h[12] (compose (P.drop 12) lo) ∧
    ClosedExpanded theta h[12] (compose (P.drop 12) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_13 :
    ClosedExpanded theta h[13] (compose (P.drop 13) lo) ∧
    ClosedExpanded theta h[13] (compose (P.drop 13) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_14 :
    ClosedExpanded theta h[14] (compose (P.drop 14) lo) ∧
    ClosedExpanded theta h[14] (compose (P.drop 14) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_15 :
    ClosedExpanded theta h[15] (compose (P.drop 15) lo) ∧
    ClosedExpanded theta h[15] (compose (P.drop 15) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_16 :
    ClosedExpanded theta h[16] (compose (P.drop 16) lo) ∧
    ClosedExpanded theta h[16] (compose (P.drop 16) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_17 :
    ClosedExpanded theta h[17] (compose (P.drop 17) lo) ∧
    ClosedExpanded theta h[17] (compose (P.drop 17) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_18 :
    ClosedExpanded theta h[18] (compose (P.drop 18) lo) ∧
    ClosedExpanded theta h[18] (compose (P.drop 18) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_19 :
    ClosedExpanded theta h[19] (compose (P.drop 19) lo) ∧
    ClosedExpanded theta h[19] (compose (P.drop 19) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_20 :
    ClosedExpanded theta h[20] (compose (P.drop 20) lo) ∧
    ClosedExpanded theta h[20] (compose (P.drop 20) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem p_21 :
    ClosedExpanded theta h[21] (compose (P.drop 21) lo) ∧
    ClosedExpanded theta h[21] (compose (P.drop 21) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [P, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

theorem numeric_high_P : EndpointCertificate theta lo hi P h := by
  intro r hr
  have hr' : r < 22 := by simpa [h] using hr
  interval_cases r
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_0.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_0.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_1.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_1.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_2.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_2.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_3.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_3.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_4.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_4.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_5.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_5.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_6.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_6.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_7.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_7.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_8.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_8.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_9.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_9.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_10.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_10.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_11.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_11.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_12.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_12.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_13.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_13.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_14.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_14.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_15.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_15.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_16.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_16.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_17.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_17.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_18.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_18.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_19.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_19.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_20.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_20.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp p_21.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp p_21.2⟩

private theorem r_0 :
    ClosedExpanded theta j[0] (compose (R.drop 0) lo) ∧
    ClosedExpanded theta j[0] (compose (R.drop 0) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_1 :
    ClosedExpanded theta j[1] (compose (R.drop 1) lo) ∧
    ClosedExpanded theta j[1] (compose (R.drop 1) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_2 :
    ClosedExpanded theta j[2] (compose (R.drop 2) lo) ∧
    ClosedExpanded theta j[2] (compose (R.drop 2) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_3 :
    ClosedExpanded theta j[3] (compose (R.drop 3) lo) ∧
    ClosedExpanded theta j[3] (compose (R.drop 3) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_4 :
    ClosedExpanded theta j[4] (compose (R.drop 4) lo) ∧
    ClosedExpanded theta j[4] (compose (R.drop 4) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_5 :
    ClosedExpanded theta j[5] (compose (R.drop 5) lo) ∧
    ClosedExpanded theta j[5] (compose (R.drop 5) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_6 :
    ClosedExpanded theta j[6] (compose (R.drop 6) lo) ∧
    ClosedExpanded theta j[6] (compose (R.drop 6) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_7 :
    ClosedExpanded theta j[7] (compose (R.drop 7) lo) ∧
    ClosedExpanded theta j[7] (compose (R.drop 7) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_8 :
    ClosedExpanded theta j[8] (compose (R.drop 8) lo) ∧
    ClosedExpanded theta j[8] (compose (R.drop 8) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_9 :
    ClosedExpanded theta j[9] (compose (R.drop 9) lo) ∧
    ClosedExpanded theta j[9] (compose (R.drop 9) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_10 :
    ClosedExpanded theta j[10] (compose (R.drop 10) lo) ∧
    ClosedExpanded theta j[10] (compose (R.drop 10) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_11 :
    ClosedExpanded theta j[11] (compose (R.drop 11) lo) ∧
    ClosedExpanded theta j[11] (compose (R.drop 11) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_12 :
    ClosedExpanded theta j[12] (compose (R.drop 12) lo) ∧
    ClosedExpanded theta j[12] (compose (R.drop 12) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_13 :
    ClosedExpanded theta j[13] (compose (R.drop 13) lo) ∧
    ClosedExpanded theta j[13] (compose (R.drop 13) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_14 :
    ClosedExpanded theta j[14] (compose (R.drop 14) lo) ∧
    ClosedExpanded theta j[14] (compose (R.drop 14) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_15 :
    ClosedExpanded theta j[15] (compose (R.drop 15) lo) ∧
    ClosedExpanded theta j[15] (compose (R.drop 15) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_16 :
    ClosedExpanded theta j[16] (compose (R.drop 16) lo) ∧
    ClosedExpanded theta j[16] (compose (R.drop 16) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_17 :
    ClosedExpanded theta j[17] (compose (R.drop 17) lo) ∧
    ClosedExpanded theta j[17] (compose (R.drop 17) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_18 :
    ClosedExpanded theta j[18] (compose (R.drop 18) lo) ∧
    ClosedExpanded theta j[18] (compose (R.drop 18) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_19 :
    ClosedExpanded theta j[19] (compose (R.drop 19) lo) ∧
    ClosedExpanded theta j[19] (compose (R.drop 19) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_20 :
    ClosedExpanded theta j[20] (compose (R.drop 20) lo) ∧
    ClosedExpanded theta j[20] (compose (R.drop 20) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem r_21 :
    ClosedExpanded theta j[21] (compose (R.drop 21) lo) ∧
    ClosedExpanded theta j[21] (compose (R.drop 21) hi) := by
  have bounds := t_bounds
  simp only [ClosedExpanded, InSupport, supportUpper, lo, hi, compose_eval]
  norm_num [R, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

theorem numeric_high_R : EndpointCertificate theta lo hi R j := by
  intro r hr
  have hr' : r < 22 := by simpa [j] using hr
  interval_cases r
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_0.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_0.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_1.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_1.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_2.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_2.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_3.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_3.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_4.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_4.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_5.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_5.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_6.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_6.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_7.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_7.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_8.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_8.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_9.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_9.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_10.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_10.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_11.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_11.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_12.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_12.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_13.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_13.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_14.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_14.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_15.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_15.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_16.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_16.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_17.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_17.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_18.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_18.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_19.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_19.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_20.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_20.2⟩
  · exact ⟨(expanded_distance_formula _ theta_bounds.1.le _ _).mp r_21.1,
      (expanded_distance_formula _ theta_bounds.1.le _ _).mp r_21.2⟩

end
end Reg.Support.FibonacciL22
