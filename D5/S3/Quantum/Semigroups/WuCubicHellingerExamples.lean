import D5.S3.Quantum.Semigroups.WuCubicHellingerCut
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicHellingerExamples

open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate
open WuCubicHellingerCut (hellinger_deficit_bound)
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private cutA cutB c e gamma bias from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

/-- The focal spectrum at `r = 21 / 20` and displacement `1 / 1024` in
direction `(1, 1/2, 1/2, 0)` has zero angular loss. -/
private theorem focal_example_occupation_le (U : unitary Mat) :
    let r : ℝ := 21 / 20
    let m : ℝ := (20 / 21) ^ 2 + 1 / 1024
    let n : ℝ := 20 / 21 + 1 / 2048
    occupationDeficit r m n n ≤ normalizedDeficit r U m n n := by
  intro r m n
  let η : ℝ := 1 / 1000000000
  have hbound := hellinger_deficit_bound (r := r) (m := m) (n := n) (q := n) (η := η) U
    (by norm_num [r]) (by norm_num [m]) (by norm_num [m, n]) le_rfl (by norm_num [n])
  dsimp only at hbound
  refine le_trans ?_ (hbound ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals
    norm_num [r, m, n, η, cutEnergy, cutBias, matchedMixture, lowerCoeff, upperCoeff, longCoeff,
      crossCoeff, directedCoeff, cutA, cutB, c, e, gamma, bias, max_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The distinct middle levels at the same temperature give zero angular loss. -/
private theorem distinct_middle_occupation_le (U : unitary Mat) :
    let r : ℝ := 21 / 20
    let m : ℝ := (20 / 21) ^ 2 + 1 / 1024
    let n : ℝ := 20 / 21 - 1 / 4096
    let q : ℝ := 20 / 21 + 1 / 4096
    n < q ∧ occupationDeficit r m n q ≤ normalizedDeficit r U m n q := by
  intro r m n q
  let η : ℝ := 1 / 1000000
  refine ⟨by norm_num [n, q], ?_⟩
  have hbound := hellinger_deficit_bound (r := r) (m := m) (n := n) (q := q) (η := η) U
    (by norm_num [r]) (by norm_num [m]) (by norm_num [m, n]) (by norm_num [n, q])
    (by norm_num [q])
  dsimp only at hbound
  refine le_trans ?_ (hbound ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals
    norm_num [r, m, n, q, η, cutEnergy, cutBias, matchedMixture, lowerCoeff, upperCoeff, longCoeff,
      crossCoeff, directedCoeff, cutA, cutB, c, e, gamma, bias, max_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

#print axioms focal_example_occupation_le
#print axioms distinct_middle_occupation_le

end D5.S3.Quantum.Semigroups.WuCubicHellingerExamples
