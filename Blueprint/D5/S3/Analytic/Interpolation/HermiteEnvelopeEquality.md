# Equality in the Hermite envelope

## Abstract

The logarithmic Hermite bound is attained exactly at the moment nodes, with one upper coordinate when the variance is positive.

**Theorem 1.1 (Strict sign to the left of the double node).**

$$\forall x,L,H: \operatorname{Real}\left(\right), \forall g: \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right), (x < L \land L < H \land \operatorname{ContDiff}\left(\operatorname{Real}\left(\right), 3, g\right) \land \operatorname{g}\left(L\right) = 0 \land \operatorname{g}\left(H\right) = 0 \land \operatorname{deriv}\left(g, L\right) = 0 \land (\forall t \in (x,H), 0 < \operatorname{iteratedDeriv}\left(3, g, t\right))) \implies \operatorname{g}\left(x\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.negative_left_of_double_node` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x, L and H be real numbers with x less than L and L less than H. Let g be three times continuously differentiable on the real line. Suppose g vanishes at L and H, its derivative vanishes at L, and its third derivative is strictly positive throughout the open interval from x to H. Then g(x) is strictly negative. If g(x) were nonnegative, two mean value arguments would produce a nonnegative second derivative to the left of L. Two Rolle arguments produce a zero second derivative to the right of L, contradicting strict increase of the second derivative.

**Theorem 1.2 (Positive variance and the unique upper coordinate).**

$$\forall k: \operatorname{Nat}\left(\right), \forall x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), (2 \le k \land (\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{x}\left(i\right)) \land 0 < V) \implies ((\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{f}\left(\operatorname{x}\left(i\right)\right) = \operatorname{f}\left(H\right)+(k-1)\operatorname{f}\left(L\right) \iff (\forall i: \operatorname{Fin}\left(k\right), (\operatorname{x}\left(i\right) = L \lor \operatorname{x}\left(i\right) = H))) \land ((\forall i: \operatorname{Fin}\left(k\right), (\operatorname{x}\left(i\right) = L \lor \operatorname{x}\left(i\right) = H)) \implies (\exists j: \operatorname{Fin}\left(k\right), (\operatorname{x}\left(j\right) = H \land (\forall i: \operatorname{Fin}\left(k\right), i \neq j \implies \operatorname{x}\left(i\right) = L)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a natural number at least two and let x assign positive real coordinates to Fin k. Write m for their mean, V for their total squared deviation, r for the radius, and L and H for the two nodes.

$m = \frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k}, V = \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-m)^{2}, r = \sqrt{\frac{V}{k(k-1)}}, L = m-r, H = m+(k-1)r$

$\operatorname{f}\left(t\right) = \log(1-\exp(-t))$

If V is positive, the sum attains the envelope if and only if every coordinate equals L or H. For coordinates at these nodes, the first moment forces exactly one coordinate to equal H and every other coordinate to equal L.

Use the quadratic agreeing with f and its derivative at L and with f at H. Its sum is determined by the first two moments. At any positive coordinate below H other than the nodes, f is strictly below this quadratic: the interval remainder handles coordinates between the nodes, and the preceding strict sign handles coordinates to the left. The nonnegative differences sum to zero exactly when every difference is zero. Finally, counting the upper coordinates gives their count times H-L equal to H-L, so their count is one.

**Theorem 1.3 (Zero variance).**

$$\forall k: \operatorname{Nat}\left(\right), \forall x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), V = 0 \implies ((\forall i: \operatorname{Fin}\left(k\right), \operatorname{x}\left(i\right) = m) \land L = m \land H = m \land \sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{f}\left(\operatorname{x}\left(i\right)\right) = \operatorname{f}\left(H\right)+(k-1)\operatorname{f}\left(L\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_zero_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural k and real vector indexed by Fin k, use the same definitions of m, V, r, L and H. If V is zero, each nonnegative squared deviation is zero. Thus every coordinate equals m, both nodes equal m, and the logarithmic sum equals its envelope. This identity requires no positivity assumption.

**Theorem 1.4 (Attainment for every feasible pair of moments).**

$$\forall k: \operatorname{Nat}\left(\right), \forall m,V: \operatorname{Real}\left(\right), (2 \le k \land 0 < m \land 0 \le V \land V < k(k-1)(m)^{2}) \implies \exists x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), ((\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{x}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right) = km \land \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-m)^{2} = V \land \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right))^{2} = k(m)^{2}+V \land (\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{f}\left(\operatorname{x}\left(i\right)\right) = \operatorname{f}\left(H\right)+(k-1)\operatorname{f}\left(L\right)) \land (\exists j: \operatorname{Fin}\left(k\right), (\operatorname{x}\left(j\right) = H \land (\forall i: \operatorname{Fin}\left(k\right), i \neq j \implies \operatorname{x}\left(i\right) = L))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Now prescribe a natural k at least two and real parameters m and V satisfying m positive and zero at most V strictly less than k(k-1)m squared. Define r, L and H from these parameters as follows.

$r = \sqrt{\frac{V}{k(k-1)}}, L = m-r, H = m+(k-1)r$

There is a positive real vector whose first sum is km, whose total squared deviation about m is V, and whose square sum is km squared plus V. It attains the logarithmic envelope and has one distinguished coordinate H and all other coordinates L. When V is zero the nodes coincide, so the distinguished index need not be unique.

Choose index zero for H and put L at every other index. The radius is smaller than m, which proves positivity. Summing any function over this vector gives its value at H plus k-1 times its value at L. Applying this to the identity, centered square and square gives the required moments. The equality classification, including its zero variance case, then gives attainment. Together with the upper bound this proves optimality in the class of positive real vectors with the prescribed moments.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_equality`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_sharpness`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_zero_variance`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.negative_left_of_double_node`
- Dependency: [D5/S3/Analytic/Interpolation/HermiteMomentBounds](HermiteMomentBounds.md)
- Dependency: [D5/S3/Analytic/Interpolation/HermiteUpperEnvelope](HermiteUpperEnvelope.md)
- Dependency: [D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives](LogOneSubExpDerivatives.md)
