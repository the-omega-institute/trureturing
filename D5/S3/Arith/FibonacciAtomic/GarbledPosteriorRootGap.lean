/- GID: D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A scalar root with an unrestricted affine softmax head has a uniform positive proper-risk gap for the garbled three-class window teacher. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S3.TotalVariation.Pinsker

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap

open LiteralWindowEnd
open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker
open scoped BigOperators

/-- Independent whole windows, including every tail word. -/
abbrev Input (m : ℕ) := Fin (m + 3) → Window

/-- The class is 1 at the first selected seam, 2 at the second seam only
when the first is absent, and 0 otherwise. -/
def teacher {m : ℕ} (x : Input m) : Fin 3 :=
  if last (x 0) && first (x 1) then 1
  else if last (x 1) && first (x 2) then 2 else 0

def mu : ℝ := (11 - 6 * Real.sqrt 2) / 12

def channel : Fin 3 → Fin 3 → ℝ := ![
  ![5 / 12, Real.sqrt 2 / 2 - 1 / 3, mu],
  ![7 / 24, 5 / 12, 7 / 24],
  ![mu, Real.sqrt 2 / 2 - 1 / 3, 5 / 12]]

def posterior {m : ℕ} (x : Input m) : Fin 3 → ℝ := channel (teacher x)

def uniformMass (m : ℕ) : ℝ := 1 / (5 : ℝ) ^ (m + 3)

def jointMass {m : ℕ} (x : Input m) (j : Fin 3) : ℝ :=
  uniformMass m * posterior x j

def mean {m : ℕ} (f : Input m → ℝ) : ℝ := uniformMass m * ∑ x, f x

/-- Every scalar root is allowed. A zero-dimensional root embeds by z = 0;
there is no restriction on trees, peaks, encodings, or internal parameters. -/
def softmax {m : ℕ} (z : Input m → ℝ) (u v : Fin 3 → ℝ)
    (x : Input m) (i : Fin 3) : ℝ :=
  Real.exp (u i * z x + v i) / ∑ j, Real.exp (u j * z x + v j)

def brierRisk {m : ℕ} (p : Input m → Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ j, jointMass x j * ∑ i, (p x i - if j = i then 1 else 0) ^ 2

def brierBayes (m : ℕ) : ℝ := mean (m := m) (fun x => 1 - ∑ i, posterior x i ^ 2)

def logRisk {m : ℕ} (p : Input m → Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ j, jointMass x j * (-Real.log (p x j))

def logBayes (m : ℕ) : ℝ :=
  mean (m := m) (fun x => -∑ j, posterior x j * Real.log (posterior x j))

def kappa : ℝ := mu ^ 2 * (Real.log (125 / 98 : ℝ)) ^ 2 / 1875

/-- The risk is scored under the joint law, with its own Bayes value.
The lower bound includes arbitrary scalar roots and free affine heads. -/
theorem result (m : ℕ) (z : Input m → ℝ) (u v : Fin 3 → ℝ) :
    kappa ≤ brierRisk (softmax z u v) - brierBayes m ∧
    kappa ≤ logRisk (softmax z u v) - logBayes m ∧
    kappa = (193 - 132 * Real.sqrt 2) / 270000 *
      (Real.log (125 / 98 : ℝ)) ^ 2 ∧
    0 < kappa := by
  sorry

#check Real.exp_pos
#check Real.log_div
#check Real.add_pow_le_pow_mul_pow_of_add_eq_one
#check Real.log_le_sub_one_of_pos
#check Real.one_sub_inv_le_log_of_pos
#check abs_real_inner_le_norm
#check inner_mul_le_norm_mul_norm
#check Finset.expect
#check Real.sq_sqrt
#check Real.sqrt_lt_sqrt
#check Real.lt_sqrt
#check Real.sqrt_two_gt_one
#print axioms result

end D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap
