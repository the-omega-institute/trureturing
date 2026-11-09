/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeBalancing
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeBalancing
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Strict balancing of the positive-real replica-three scalar extension. -/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar

/-!
Strict balancing for the scalar extension. Real coordinates are not fractional
physical modes. Scientific source: Haobo Ma then Wenlin Zhang, *An exact
balancing law for order-three Gaussian multi-entropy*, 2026-11-04, CC BY 4.0.
The physical family is due to Camargo and Nishida; classical majorization
criteria are due to Marshall, Olkin and Arnold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing

open ReplicaThreeScalar

private def pairDen (k u z p : ℝ) : ℝ :=
  (1 + k * p) ^ 2 + k * u * z * (1 + k * p) + k ^ 2 * p * z ^ 2

private def pairNum (k u z p : ℝ) : ℝ := (1 + k * (p + u * z)) ^ 2

private lemma pairDen_pos (k u z p : ℝ) (hk : 0 ≤ k) (hu : 0 ≤ u)
    (hz : 0 ≤ z) (hp : 0 ≤ p) : 0 < pairDen k u z p := by
  unfold pairDen
  have h : 0 < (1 + k * p) ^ 2 := sq_pos_of_pos (by positivity)
  positivity

private lemma pair_form (k x y z : ℝ) (hk : 0 ≤ k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    value k x y z = Real.log (pairNum k (x + y) z (x * y) /
      (pairDen k (x + y) z (x * y) * (1 + k * (x + y) * z))) / 12 := by
  rw [value_eq_log_ratio k x y z hk hx hy hz]
  congr 3
  · unfold pairSum pairNum
    ring
  · unfold pairDen cut
    ring

private lemma cross_difference (k u z p q : ℝ) :
    pairNum k u z p * pairDen k u z q - pairNum k u z q * pairDen k u z p =
      k ^ 2 * z * (q - p) *
        (u + z + k * u * (p + q + 2 * u * z + 2 * z ^ 2) +
          k ^ 2 * (u * p * q + z * p * (u ^ 2 - q) + z * q * u ^ 2 +
            u ^ 2 * z ^ 2 * (u + z))) := by
  unfold pairNum pairDen
  ring

private lemma pair_product_comparison (k x y x' y' z : ℝ) (hk : 0 < k)
    (hx : 0 < x) (hy : 0 < y) (hx' : 0 < x') (hy' : 0 < y') (hz : 0 < z)
    (hs : x' + y' = x + y) (hp : x * y < x' * y') :
    value k x' y' z < value k x y z := by
  rw [pair_form k x y z hk.le hx.le hy.le hz.le,
    pair_form k x' y' z hk.le hx'.le hy'.le hz.le, hs]
  apply div_lt_div_of_pos_right _ (by norm_num)
  apply Real.strictMonoOn_log
  · exact div_pos (sq_pos_of_pos (by positivity))
      (mul_pos (pairDen_pos k (x + y) z (x' * y') hk.le (by positivity) hz.le
        (by positivity)) (by positivity))
  · exact div_pos (sq_pos_of_pos (by positivity))
      (mul_pos (pairDen_pos k (x + y) z (x * y) hk.le (by positivity) hz.le
        (by positivity)) (by positivity))
  · apply (div_lt_div_iff₀
      (mul_pos (pairDen_pos k (x + y) z (x' * y') hk.le (by positivity) hz.le
        (by positivity)) (by positivity))
      (mul_pos (pairDen_pos k (x + y) z (x * y) hk.le (by positivity) hz.le
        (by positivity)) (by positivity))).2
    have hq : 0 ≤ (x + y) ^ 2 - x' * y' := by
      nlinarith [sq_nonneg x', sq_nonneg y', mul_pos hx' hy']
    have hbr : 0 < (x + y) + z + k * (x + y) *
        (x * y + x' * y' + 2 * (x + y) * z + 2 * z ^ 2) +
        k ^ 2 * ((x + y) * (x * y) * (x' * y') + z * (x * y) *
          ((x + y) ^ 2 - x' * y') + z * (x' * y') * (x + y) ^ 2 +
            (x + y) ^ 2 * z ^ 2 * ((x + y) + z)) := by positivity
    have hd := cross_difference k (x + y) z (x * y) (x' * y')
    have hdiff : 0 < pairNum k (x + y) z (x * y) * pairDen k (x + y) z (x' * y') -
        pairNum k (x + y) z (x' * y') * pairDen k (x + y) z (x * y) := by
      rw [hd]
      exact mul_pos (mul_pos (mul_pos (sq_pos_of_pos hk) hz) (sub_pos.mpr hp)) hbr
    nlinarith [mul_pos hdiff (show 0 < 1 + k * (x + y) * z by positivity)]

/-- Every proper convex mixing of unequal positive coordinates strictly lowers
the scalar value. The parameter and the third coordinate stay positive. -/
private theorem proper_pair_mixing (k x y z t : ℝ) (hk : 0 < k)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ht : 0 < t) (ht1 : t < 1) (hxy : x ≠ y) :
    value k ((1 - t) * x + t * y) (t * x + (1 - t) * y) z < value k x y z := by
  apply pair_product_comparison k x y _ _ z hk hx hy
    (by positivity) (by positivity) hz (by ring)
  have hs : 0 < (x - y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hi : 0 < t * (1 - t) * (x - y) ^ 2 := by positivity
  nlinarith

/-- Mixing two positive coordinates never increases the scalar expression.
Equality occurs exactly for the identity, the full swap, or an already tied
pair. Thus every proper mixing of unequal coordinates is strictly decreasing. -/
theorem pair_mixing (k x y z t : ℝ) (hk : 0 < k)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    value k ((1 - t) * x + t * y) (t * x + (1 - t) * y) z ≤ value k x y z ∧
      (value k ((1 - t) * x + t * y) (t * x + (1 - t) * y) z = value k x y z ↔
        t = 0 ∨ t = 1 ∨ x = y) := by
  by_cases h0 : t = 0
  · simp [h0]
  by_cases h1 : t = 1
  · simp [h1, value_swap]
  by_cases hxy : x = y
  · subst y
    have he : (1 - t) * x + t * x = x := by ring
    have he' : t * x + (1 - t) * x = x := by ring
    simp [he, he']
  have hlt := proper_pair_mixing k x y z t hk hx hy hz
    (lt_of_le_of_ne ht (Ne.symm h0)) (lt_of_le_of_ne ht1 h1) hxy
  exact ⟨hlt.le, iff_of_false hlt.ne (by simp [h0, h1, hxy])⟩

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing
