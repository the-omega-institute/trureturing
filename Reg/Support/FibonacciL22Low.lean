import Reg.Support.FibonacciL22High
import Mathlib.Tactic.IntervalCases

namespace Reg.Support.FibonacciL22
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open Reg.Support.FibonacciQuadratic
open _root_.Set
open scoped Topology
noncomputable section

private theorem q_0 :
    InSupport .G0 (compose (Q.drop 0) b) ∧
    cut h[0].val - theta < compose (Q.drop 0) b ∧
    compose (Q.drop 0) b < cut (h[0].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_1 :
    InSupport .G0 (compose (Q.drop 1) b) ∧
    cut h[1].val - theta < compose (Q.drop 1) b ∧
    compose (Q.drop 1) b < cut (h[1].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_2 :
    InSupport .G0 (compose (Q.drop 2) b) ∧
    cut h[2].val - theta < compose (Q.drop 2) b ∧
    compose (Q.drop 2) b < cut (h[2].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_3 :
    InSupport .G0 (compose (Q.drop 3) b) ∧
    cut h[3].val - theta < compose (Q.drop 3) b ∧
    compose (Q.drop 3) b < cut (h[3].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_4 :
    InSupport .G0 (compose (Q.drop 4) b) ∧
    cut h[4].val - theta < compose (Q.drop 4) b ∧
    compose (Q.drop 4) b < cut (h[4].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_5 :
    InSupport .G0 (compose (Q.drop 5) b) ∧
    cut h[5].val - theta < compose (Q.drop 5) b ∧
    compose (Q.drop 5) b < cut (h[5].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_6 :
    InSupport .G0 (compose (Q.drop 6) b) ∧
    cut h[6].val - theta < compose (Q.drop 6) b ∧
    compose (Q.drop 6) b < cut (h[6].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_7 :
    InSupport .G0 (compose (Q.drop 7) b) ∧
    cut h[7].val - theta < compose (Q.drop 7) b ∧
    compose (Q.drop 7) b < cut (h[7].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_8 :
    InSupport .G0 (compose (Q.drop 8) b) ∧
    cut h[8].val - theta < compose (Q.drop 8) b ∧
    compose (Q.drop 8) b < cut (h[8].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_9 :
    InSupport .G0 (compose (Q.drop 9) b) ∧
    cut h[9].val - theta < compose (Q.drop 9) b ∧
    compose (Q.drop 9) b < cut (h[9].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_10 :
    InSupport .G0 (compose (Q.drop 10) b) ∧
    cut h[10].val - theta < compose (Q.drop 10) b ∧
    compose (Q.drop 10) b < cut (h[10].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_11 :
    InSupport .G0 (compose (Q.drop 11) b) ∧
    cut h[11].val - theta < compose (Q.drop 11) b ∧
    compose (Q.drop 11) b < cut (h[11].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_12 :
    InSupport .G0 (compose (Q.drop 12) b) ∧
    cut h[12].val - theta < compose (Q.drop 12) b ∧
    compose (Q.drop 12) b < cut (h[12].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_13 :
    InSupport .G0 (compose (Q.drop 13) b) ∧
    cut h[13].val - theta < compose (Q.drop 13) b ∧
    compose (Q.drop 13) b < cut (h[13].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_14 :
    InSupport .G0 (compose (Q.drop 14) b) ∧
    cut h[14].val - theta < compose (Q.drop 14) b ∧
    compose (Q.drop 14) b < cut (h[14].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_15 :
    InSupport .G0 (compose (Q.drop 15) b) ∧
    cut h[15].val - theta < compose (Q.drop 15) b ∧
    compose (Q.drop 15) b < cut (h[15].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_16 :
    InSupport .G0 (compose (Q.drop 16) b) ∧
    cut h[16].val - theta < compose (Q.drop 16) b ∧
    compose (Q.drop 16) b < cut (h[16].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_17 :
    InSupport .G0 (compose (Q.drop 17) b) ∧
    cut h[17].val - theta < compose (Q.drop 17) b ∧
    compose (Q.drop 17) b < cut (h[17].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_18 :
    InSupport .G0 (compose (Q.drop 18) b) ∧
    cut h[18].val - theta < compose (Q.drop 18) b ∧
    compose (Q.drop 18) b < cut (h[18].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_19 :
    InSupport .G0 (compose (Q.drop 19) b) ∧
    cut h[19].val - theta < compose (Q.drop 19) b ∧
    compose (Q.drop 19) b < cut (h[19].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_20 :
    InSupport .G0 (compose (Q.drop 20) b) ∧
    cut h[20].val - theta < compose (Q.drop 20) b ∧
    compose (Q.drop 20) b < cut (h[20].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem q_21 :
    InSupport .G0 (compose (Q.drop 21) b) ∧
    cut h[21].val - theta < compose (Q.drop 21) b ∧
    compose (Q.drop 21) b < cut (h[21].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, h, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

private theorem v_13 :
    InSupport .G0 (compose (Q.drop 13) b) ∧
    cut j[13].val - theta < compose (Q.drop 13) b ∧
    compose (Q.drop 13) b < cut (j[13].val+1) + theta := by
  have bounds := t_bounds
  simp only [InSupport, supportUpper, b, compose_eval]
  norm_num [Q, j, composePair, step, shiftPair, eval, theta, cut, g, T2, lam, phi]
  repeat' constructor
  all_goals linarith [bounds.1,bounds.2]

theorem numeric_low (i : Bool) :
    ∀ r (hr : r < (W i).length),
      InSupport .G0 (compose (Q.drop r) b) ∧
      cut (W i)[r].val - theta < compose (Q.drop r) b ∧
      compose (Q.drop r) b < cut ((W i)[r].val+1) + theta := by
  intro r hr
  have hr' : r < 22 := by cases i <;> simpa [W, h, j] using hr
  cases i <;> interval_cases r
  · exact q_0
  · exact q_1
  · exact q_2
  · exact q_3
  · exact q_4
  · exact q_5
  · exact q_6
  · exact q_7
  · exact q_8
  · exact q_9
  · exact q_10
  · exact q_11
  · exact q_12
  · exact q_13
  · exact q_14
  · exact q_15
  · exact q_16
  · exact q_17
  · exact q_18
  · exact q_19
  · exact q_20
  · exact q_21
  · exact q_0
  · exact q_1
  · exact q_2
  · exact q_3
  · exact q_4
  · exact q_5
  · exact q_6
  · exact q_7
  · exact q_8
  · exact q_9
  · exact q_10
  · exact q_11
  · exact q_12
  · exact v_13
  · exact q_14
  · exact q_15
  · exact q_16
  · exact q_17
  · exact q_18
  · exact q_19
  · exact q_20
  · exact q_21

end
end Reg.Support.FibonacciL22
