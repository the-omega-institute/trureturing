# Joint logarithm for the Robin clock

## Abstract

The joint Robin logarithm is nonzero on an explicit integer cone and has a cubic first-coordinate sensitivity bound.

**Definition 1.1 (The joint logarithm).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def omegaThree (h p q : ℝ) : ℝ := h * log (3 * p / (p + q)) - q * log (2 * p / (p + h))

**Theorem 1.2 (Nonvanishing in the positive integer cone).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem omegaThree_ne_zero {p h q : ℕ} (hh : 0 < h) (hp : h < p) (hlo : 11 * h < 7 * q) (hhi : 5 * q < 8 * h) : omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0

The rational cutoff separation bound is positive on the integer cone. Its logarithmic expression is the negative of the joint form.

**Theorem 1.3 (The first partial derivative).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_hasDerivAt_p`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_hasDerivAt_p` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem omegaThree_hasDerivAt_p {h p q : ℝ} (hp : 0 < p) (hh : 0 < h) (hq : 0 < q) : HasDerivAt (fun x : ℝ => omegaThree h x q) (-(h * q * (q - h) / (p * (p + h) * (p + q)))) p

**Theorem 1.4 (The second partial derivative).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_hasDerivAt_q`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_hasDerivAt_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem omegaThree_hasDerivAt_q {h p q : ℝ} (hp : 0 < p) (hh : 0 < h) (hq : 0 < q) : HasDerivAt (fun y : ℝ => omegaThree h p y) (-log 2 + log (1 + h / p) - h / (p + q)) q

**Theorem 1.5 (Sensitivity to the two label errors).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.abs_omegaThree_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.abs_omegaThree_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem abs_omegaThree_sub_le {h p q s r X : ℝ} (hh : 1 ≤ h) (hX : 4 ≤ X) (hs : X ≤ s) (hr₁ : 3 / 2 ≤ r) (hr₂ : r ≤ 2) (hp : |p - h * s| ≤ 1 / 2) (hq : |q - h * r| ≤ 1 / 2) : |omegaThree h p q - omegaThree h (h * s) (h * r)| ≤ 48 / X ^ 3 * |p - h * s| + 2 * |q - h * r|

Apply the mean value bound separately in each coordinate along the rectangle joining the two pairs. The first partial derivative scales as the inverse cube of X.

**Theorem 1.6 (Cancellation at the root phases).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_at_root_phases`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_at_root_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem omegaThree_at_root_phases {h L a b e₂ e₃ : ℝ} (hh : 0 < h) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (haEq : a + log (1 + a / L) = log 2 + e₂) (hbEq : b + log (1 + b / L) = log 3 + e₃) : omegaThree h (h * (L / a)) (h * (b / a)) = h * ((b / a) * e₂ - e₃)

The two positive logarithm arguments reduce to 3/(1+b/L) and 2/(1+a/L). Substituting the root equations cancels the linear offsets.

**Theorem 1.7 (Nonvanishing for signed integer labels).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_ne_zero_int`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_ne_zero_int` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem omegaThree_ne_zero_int {p h q : ℤ} (hh : 0 < h) (hp : h < p) (hlo : 11 * h < 7 * q) (hhi : 5 * q < 8 * h) : omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.abs_omegaThree_sub_le`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_at_root_phases`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_hasDerivAt_p`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_hasDerivAt_q`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_ne_zero`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm.omegaThree_ne_zero_int`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ExactCutoff/ExactRationalCutoffSeparation](ExactCutoff/ExactRationalCutoffSeparation.md)
