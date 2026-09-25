# Finite Calibration Sets for Rational Scalar Controls

## Abstract

Every finite set above the fixed threshold is exactly the calibration jet set of a strictly feasible rational scalar control with degree at most twice its cardinality.

The parameters a and delta are real, with 0 < a < 1, 0 < delta, delta < (1-a)/4, and delta < (1-a squared)/16. The last inequality is retained among the hypotheses although the scalar proof does not use it. The finite set S consists of arbitrary real nodes i satisfying a/(1-delta) < i < 1; its cardinality has no fixed upper bound.

The scalar parameters are L(a) = 1-a, lam(a,delta) = L(a)-delta, gamma(a,delta) = lam(a,delta)/(2 delta), and center(a,delta) = lam(a,delta)/L(a). The radius is the product of the square roots of a/lam(a,delta) and (1-p)/p. The energy at s is s squared plus gamma squared times the square of s + 1/s - 2. The required derivative is beta(p) = 1/(2 p (1-p)), taken with respect to p.

**Definition 1.1 (All scalar control requirements).**

$$\operatorname{FullControl}\left(a, delta, S, N, D\right) \iff \operatorname{natDegree}\left(N\right) \le 2 \operatorname{card}\left(S\right) \land \operatorname{natDegree}\left(D\right) \le 2 \operatorname{card}\left(S\right) \land (\forall p: \mathbb{R}, 0 < \operatorname{D}\left(p\right)) \land (\forall p \in \operatorname{Icc}\left(a, 1\right), (0 < \operatorname{s}\left(p\right) \land {\operatorname{radius}\left(a, delta, p\right)}^{2} \operatorname{energy}\left(a, delta, \operatorname{s}\left(p\right)\right) < 1)) \land \operatorname{AnalyticOnNhd}\left(\mathbb{R}, s, \operatorname{Ioo}\left(a, 1\right)\right) \land (\forall p \in \operatorname{Ioo}\left(a, 1\right), (\operatorname{s}\left(p\right) = 1 \land \operatorname{deriv}\left(s, p\right) = \operatorname{beta}\left(p\right)) \iff p \in S) \land (S = \emptyset \Rightarrow \forall p: \mathbb{R}, \operatorname{s}\left(p\right) = \operatorname{center}\left(a, delta\right))$$

*Formalization.* `D5/S3/Quantum/Information/FiniteCalibrationControl.FullControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here N and D are real polynomials and s(p) denotes N(p)/D(p). Both natural degrees are at most twice card S. D is strictly positive on the entire real line. For every p in the closed interval [a,1], s(p) is positive and radius squared times energy is strictly less than one, including both endpoints.

The quotient is real analytic in a neighborhood of every point of (a,1). At each point of that open interval, value one together with derivative beta(p) holds if and only if p belongs to S. This specifies the complete set of first jets. When S is empty, the quotient equals center(a,delta) at every real p.

**Theorem 1.2 (Every prescribed finite set is realized exactly).**

$$\forall a, delta: \mathbb{R}, S: \operatorname{Finset}\left(\mathbb{R}\right), (0 < a \land a < 1 \land 0 < delta \land delta < \frac{1 - a}{4} \land delta < \frac{1 - {a}^{2}}{16} \land (\forall i \in S, \frac{a}{1 - delta} < i \land i < 1)) \Rightarrow \exists N, D: \mathbb{R}[X], \operatorname{FullControl}\left(a, delta, S, N, D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiniteCalibrationControl.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be the nodal polynomial of S and let B_i be its Lagrange basis polynomials. The polynomial hermite(S) is one plus the sum of beta(i) times (X-i) times B_i squared. Its value is one and its derivative is beta(i) at every prescribed node.

For nonempty S the construction uses N = H + k center P squared and D = 1 + k P squared, with one positive real k. The center is strictly feasible throughout [a,1]. Convexity of the energy preserves feasibility as k increases. Pointwise eventual feasibility gives a directed open cover of the compact interval; compactness supplies a single k valid at every point. The polynomial degrees satisfy the stated bound.

Away from S, (H-1)/P squared is a sum of positive weights divided by p-i. Its derivative is strictly negative. At every additional root where s(p)=1, the derivative of s is therefore strictly negative, whereas beta(p) is positive on (a,1). Such roots cannot supply additional calibration jets. For empty S take N constant equal to the center and D=1; the center is strictly below one.

The conclusion concerns the rational scalar control and its complete calibration jet set. Constructing a completely positive, trace preserving processor, an actual pure-state program, its quantum Fisher information, and a minimum program dimension requires separate operator and state results. Those conclusions are not asserted here.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiniteCalibrationControl.FullControl`
- Truth anchor: `D5/S3/Quantum/Information/FiniteCalibrationControl.result`
