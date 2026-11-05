# Non-unital channel constraints imply the network bounds

## Abstract

The three real parameter constraints for the non-unital channel class imply both quadratic and quartic network bounds.

**Definition 1.1 (The parameter implication).**

$$\operatorname{claim} = (\forall (t: \mathbb{R}), \forall (\mathrm{l1}: \mathbb{R}), \forall (\mathrm{l3}: \mathbb{R}), (\left|\mathrm{l1}\right| \le 1) \Rightarrow ((\left|\mathrm{l3}\right| + \left|t\right| \le 1) \Rightarrow (((\mathrm{l1})^{2} + (t)^{2} \le (1 - \left|\mathrm{l3}\right|)^{2}) \Rightarrow (((\left|t\right| + \left|\mathrm{l3}\right|)^{2} + (\mathrm{l1})^{2} \le 1) \land (2 \cdot (t)^{2} \cdot (\mathrm{l1})^{2} + (\mathrm{l1})^{4} + (\left|t\right| + \left|\mathrm{l3}\right|)^{4} \le 1)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.claim` (`✓ std3`).

*Citation.* Kaushiki Mukherjee; Nirman Ganguly (2025). *Network nonlocality breaking channels*. URL: <https://arxiv.org/abs/2510.26417v1>.

*Commentary.*

For every real triple t, l1, l3, the three channel constraints imply both network bounds. In Network_Nonlocality.tex, Eq. (nu3), lines 211–215, supplies the hypotheses; Eq. (resnon1), lines 716–719, supplies the conclusions of the parameter implication. Theorem 3, lines 714–721, uses those conclusions as sufficient conditions for network nonlocality breaking. The observation in lines 733–734 asserts this parameter implication and motivates Conjecture 1. The proposition concerns real parameters; it does not itself assert a theorem about quantum channels.

**Theorem 1.2 (Both bounds follow from nonnegative remainders).**

$$\forall (t: \mathbb{R}), \forall (\mathrm{l1}: \mathbb{R}), \forall (\mathrm{l3}: \mathbb{R}), (\left|\mathrm{l1}\right| \le 1) \Rightarrow ((\left|\mathrm{l3}\right| + \left|t\right| \le 1) \Rightarrow (((\mathrm{l1})^{2} + (t)^{2} \le (1 - \left|\mathrm{l3}\right|)^{2}) \Rightarrow (((\left|t\right| + \left|\mathrm{l3}\right|)^{2} + (\mathrm{l1})^{2} \le 1) \land (2 \cdot (t)^{2} \cdot (\mathrm{l1})^{2} + (\mathrm{l1})^{4} + (\left|t\right| + \left|\mathrm{l3}\right|)^{4} \le 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.result` (`✓ std3`). ∎

*Resolves.* `Problems/mukherjee-ganguly-2025-non-unital-network-condition-implication` (proved) by `D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mukherjee-ganguly-2025-non-unital-network-condition-implication","declaration_gid":"D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kaushiki Mukherjee; Nirman Ganguly (2025). *Network nonlocality breaking channels*. URL: <https://arxiv.org/abs/2510.26417v1>.

*Commentary.*

Fix real t, l1, l3 satisfying the three hypotheses, and put:

$$
A = (\mathrm{l1})^{2}, x = \left|\mathrm{l3}\right|, y = \left|t\right|, u = x + y, D = (1 - x)^{2} - (y)^{2} - A
$$

Squares and absolute values give nonnegative A, x and y. The second hypothesis gives u at most one. Since the square of y equals the square of t, the third hypothesis gives nonnegative D. Expanding the first remainder gives:

$$
1 - (A + (u)^{2}) = D + 2 \cdot x \cdot (1 - u)
$$

Both terms on the right are nonnegative, because x is nonnegative and u is at most one. Thus A plus the square of u is at most one. It is also nonnegative, since A and the square of u are nonnegative. Next expand the second remainder:

$$
(A + (u)^{2})^{2} - ((A)^{2} + 2 \cdot (y)^{2} \cdot A + (u)^{4}) = 2 \cdot A \cdot x \cdot (x + 2 \cdot y)
$$

The product on the right is nonnegative because A, x and y are nonnegative. Squaring the bounds zero and one for A plus the square of u therefore yields:

$$
(A)^{2} + 2 \cdot (y)^{2} \cdot A + (u)^{4}\leq(A + (u)^{2})^{2}\leq1
$$

For the first conclusion, substitute A and u in the quadratic bound and commute x and y. For the second, substitute A, u, x and y in the quartic bound, replace the square of the absolute value of t by the square of t, and collect powers and products. These are the two required inequalities. The bound on the absolute value of l1 is unnecessary for these estimates; the second and third hypotheses suffice.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.result`
