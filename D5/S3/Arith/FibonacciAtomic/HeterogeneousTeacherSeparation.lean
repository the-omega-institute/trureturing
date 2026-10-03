/- GID: D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation
   mirror-E: none(waiver:unbounded-symbolic-estimate)
   anchors: []
   utility: none
   digest: Independent heterogeneous whole-window laws have a sharp uniform teacher separation. -/

import D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap
import D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation

open LiteralWindowEnd (Window first last)
open LegalPriorityTeacher (Input Roles)
open scoped BigOperators

/-- Real masses on the five actual windows at each position. No seam conditioning. -/
abbrev Laws (n : ℕ) := Fin n → Window → ℝ

/-- Every one of the five masses is at least rho and each position has total mass one. -/
def Admissible {n : ℕ} (rho : ℝ) (μ : Laws n) : Prop :=
  (∀ i a, rho ≤ μ i a) ∧ (∀ i, ∑ a, μ i a = 1)

/-- The frozen priority teacher on the three selected actual windows, as a real class value. -/
def classValue {n : ℕ} (t : Roles n) (w : Input n) : ℝ :=
  (GarbledPosteriorRootGap.teacher (m := 0) ![w t.p, w t.q, w t.r]).val

/-- Squared separation in the full heterogeneous product input law. -/
def distance {n : ℕ} (μ : Laws n) (t u : Roles n) : ℝ :=
  ∑ w : Input n, (∏ i, μ i (w i)) * (classValue t w - classValue u w) ^ 2

/-- The proposed sharp constant for the entire admissible heterogeneous class. -/
def gamma (rho : ℝ) : ℝ := 8 * rho ^ 2 * (1 - 2 * rho)

/-- A common law attaining the heterogeneous infimum; order is zero, low, middle, ends, high. -/
def extremal (rho : ℝ) : Window → ℝ
  | .zero | .middle => (1 - 3 * rho) / 2
  | .low | .ends | .high => rho

end D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
