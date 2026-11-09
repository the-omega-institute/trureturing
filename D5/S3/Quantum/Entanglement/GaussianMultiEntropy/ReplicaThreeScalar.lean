/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Strict balancing and squeezing of the replica-three scalar expression. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The scalar expression for replica order three. Positive real coordinates here
are a mathematical extension, not a claim about fractional bosonic modes.
The physical integral bridge is in `ReplicaThree`.

Scientific source: Haobo Ma and Wenlin Zhang, *An exact balancing law for
order-three Gaussian multi-entropy*, released note of 2026-11-04, CC BY 4.0.
The fully symmetric physical family and equal-party observation are due to
Camargo and Nishida; the majorization criterion is classical
(Marshall, Olkin and Arnold).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar

/-- The second elementary symmetric polynomial of the three labelled parties. -/
def pairSum (x y z : ℝ) : ℝ := x * y + x * z + y * z

/-- One labelled cut factor. The three factors remain distinct occurrences at ties. -/
def cut (k x y z : ℝ) : ℝ := 1 + k * x * (y + z)

/-- The replica-three scalar value, with nonnegative parameter `k`. -/
def value (k x y z : ℝ) : ℝ :=
  (2 * Real.log (1 + k * pairSum x y z) -
    (Real.log (cut k x y z) + Real.log (cut k y x z) + Real.log (cut k z x y))) / 12

private lemma cut_pos {k x y z : ℝ} (hk : 0 ≤ k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 < cut k x y z := by
  unfold cut
  positivity

private lemma main_pos {k x y z : ℝ} (hk : 0 ≤ k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 < 1 + k * pairSum x y z := by
  unfold pairSum
  positivity

/-- The logarithmic quotient form, on its full nonnegative scalar domain. -/
theorem value_eq_log_ratio (k x y z : ℝ) (hk : 0 ≤ k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    value k x y z = Real.log ((1 + k * pairSum x y z) ^ 2 /
      (cut k x y z * cut k y x z * cut k z x y)) / 12 := by
  have hA := cut_pos hk hx hy hz
  have hB := cut_pos hk hy hx hz
  have hC := cut_pos hk hz hx hy
  rw [Real.log_div (pow_ne_zero 2 (main_pos hk hx hy hz).ne')
    (mul_ne_zero (mul_ne_zero hA.ne' hB.ne') hC.ne'), Real.log_pow,
    Real.log_mul (mul_ne_zero hA.ne' hB.ne') hC.ne', Real.log_mul hA.ne' hB.ne']
  rfl

lemma value_swap (k x y z : ℝ) : value k x y z = value k y x z := by
  have hs : pairSum x y z = pairSum y x z := by unfold pairSum; ring
  have hc : cut k z x y = cut k z y x := by unfold cut; ring
  unfold value
  rw [hs, hc]
  ring

lemma value_cycle (k x y z : ℝ) : value k x y z = value k y z x := by
  unfold value pairSum cut
  have h1 : x * y + x * z + y * z = y * z + y * x + z * x := by ring
  rw [h1, show z + x = x + z by ring, show y + x = x + y by ring]
  ring

/-- At vacuum every scalar triple has value zero. -/
private lemma value_zero (x y z : ℝ) : value 0 x y z = 0 := by
  simp [value, cut]

private lemma denominator_excess (k x y z : ℝ) :
    cut k x y z * cut k y x z * cut k z x y - (1 + k * pairSum x y z) ^ 2 =
      k ^ 2 * x * y * z * ((x + y + z) +
        k * ((x + y + z) * pairSum x y z - x * y * z)) := by
  unfold cut pairSum
  ring

/-- Strict negativity holds for positive parties and positive squeezing parameter. -/
theorem value_neg (k x y z : ℝ) (hk : 0 < k)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : value k x y z < 0 := by
  rw [value_eq_log_ratio k x y z hk.le hx.le hy.le hz.le]
  apply div_neg_of_neg_of_pos _ (by norm_num)
  apply Real.log_neg
  · exact div_pos (sq_pos_of_pos (main_pos hk.le hx.le hy.le hz.le))
      (mul_pos (mul_pos (cut_pos hk.le hx.le hy.le hz.le)
        (cut_pos hk.le hy.le hx.le hz.le)) (cut_pos hk.le hz.le hx.le hy.le))
  · apply (div_lt_one (mul_pos (mul_pos (cut_pos hk.le hx.le hy.le hz.le)
        (cut_pos hk.le hy.le hx.le hz.le)) (cut_pos hk.le hz.le hx.le hy.le))).2
    have hS : 0 < (x + y + z) * pairSum x y z - x * y * z := by
      have he : (x + y + z) * pairSum x y z - x * y * z =
          x ^ 2 * y + x ^ 2 * z + x * y ^ 2 + x * z ^ 2 + y ^ 2 * z + y * z ^ 2 +
            2 * x * y * z := by unfold pairSum; ring
      rw [he]
      positivity
    have hp : 0 < k ^ 2 * x * y * z * ((x + y + z) +
        k * ((x + y + z) * pairSum x y z - x * y * z)) := by positivity
    linarith [denominator_excess k x y z]

private def parameterDerivative (k x y z : ℝ) : ℝ :=
  (2 * (pairSum x y z / (1 + k * pairSum x y z)) -
    (x * (y + z) / cut k x y z + y * (x + z) / cut k y x z +
      z * (x + y) / cut k z x y)) / 12

private lemma hasDerivAt_parameter (k x y z : ℝ) (hk : 0 ≤ k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    HasDerivAt (fun t => value t x y z) (parameterDerivative k x y z) k := by
  have hd (r : ℝ) (hr : 0 ≤ r) :
      HasDerivAt (fun t => Real.log (1 + t * r)) (r / (1 + k * r)) k := by
    have hne : 1 + k * r ≠ 0 := ne_of_gt (by positivity)
    simpa only [one_mul, id_eq] using
      (((hasDerivAt_id k).mul_const r).const_add 1).log hne
  have hs : 0 ≤ pairSum x y z := by unfold pairSum; positivity
  simpa only [value, parameterDerivative, cut, mul_assoc, Pi.add_apply, Pi.sub_apply] using
    (((hd (pairSum x y z) hs).const_mul 2).sub
      (((hd (x * (y + z)) (by positivity)).add
        (hd (y * (x + z)) (by positivity))).add
          (hd (z * (x + y)) (by positivity)))).div_const 12

private lemma parameterDerivative_neg (k x y z : ℝ) (hk : 0 < k)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : parameterDerivative k x y z < 0 := by
  have hA : x * (y + z) / (1 + k * pairSum x y z) < x * (y + z) / cut k x y z := by
    apply div_lt_div_of_pos_left (by positivity) (cut_pos hk.le hx.le hy.le hz.le)
    have h : 0 < k * (y * z) := mul_pos hk (mul_pos hy hz)
    dsimp [cut, pairSum]
    nlinarith
  have hB : y * (x + z) / (1 + k * pairSum x y z) < y * (x + z) / cut k y x z := by
    apply div_lt_div_of_pos_left (by positivity) (cut_pos hk.le hy.le hx.le hz.le)
    have h : 0 < k * (x * z) := mul_pos hk (mul_pos hx hz)
    dsimp [cut, pairSum]
    nlinarith
  have hC : z * (x + y) / (1 + k * pairSum x y z) < z * (x + y) / cut k z x y := by
    apply div_lt_div_of_pos_left (by positivity) (cut_pos hk.le hz.le hx.le hy.le)
    have h : 0 < k * (x * y) := mul_pos hk (mul_pos hx hy)
    dsimp [cut, pairSum]
    nlinarith
  have hsum : 2 * (pairSum x y z / (1 + k * pairSum x y z)) =
      x * (y + z) / (1 + k * pairSum x y z) +
        y * (x + z) / (1 + k * pairSum x y z) +
          z * (x + y) / (1 + k * pairSum x y z) := by
    unfold pairSum
    ring
  unfold parameterDerivative
  apply div_neg_of_neg_of_pos _ (by norm_num)
  linarith

/-- Increasing the squeezing parameter strictly decreases the value on the
whole nonnegative parameter ray. Its derivative at vacuum need not be negative. -/
private lemma strictAntiOn_parameter (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    StrictAntiOn (fun k => value k x y z) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
  · intro k hk
    exact (hasDerivAt_parameter k x y z hk hx.le hy.le hz.le).continuousAt.continuousWithinAt
  · intro k hk
    have hk' : 0 < k := by simpa only [interior_Ici, mem_Ioi] using hk
    rw [(hasDerivAt_parameter k x y z hk'.le hx.le hy.le hz.le).deriv]
    exact parameterDerivative_neg k x y z hk' hx hy hz

/-- Vacuum is zero for every positive scalar triple, and every strict increase
in the nonnegative squeezing parameter strictly lowers the value. -/
theorem parameter_behavior (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    value 0 x y z = 0 ∧ StrictAntiOn (fun k => value k x y z) (Ici 0) :=
  ⟨value_zero x y z, strictAntiOn_parameter x y z hx hy hz⟩

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
