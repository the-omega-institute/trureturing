# Compact Integral Operators with a Continuous Kernel

## Abstract

For compact spaces X and Y, a finite measure on Y and a continuous kernel on X x Y with real or complex values, the integral operator of the kernel is a compact operator from the Lebesgue space of exponent at least one into the continuous functions on X.

**Theorem 1.1 (The integral operator of a continuous kernel is compact).**

$$\forall X \in \operatorname{Type}*,\; \forall Y \in \operatorname{Type}*,\; \forall k \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(X\right)],\ [\operatorname{CompactSpace}\left(X\right)],\ [\operatorname{TopologicalSpace}\left(Y\right)],\ [\operatorname{CompactSpace}\left(Y\right)],\ [\operatorname{MeasurableSpace}\left(Y\right)],\ [\operatorname{OpensMeasurableSpace}\left(Y\right)],\ [\operatorname{RCLike}\left(k\right)],\ \forall m \in \operatorname{Measure}\left(Y\right),\; [\operatorname{IsFiniteMeasure}\left(m\right)],\ \forall p \in [0, \infty],\; [\operatorname{Fact}\left(1 \le p\right)],\ \forall K \in \operatorname{C}\left(X \times Y, k\right),\; \exists T \in \operatorname{ContinuousLinearMap}\left(k, \operatorname{Lp}\left(k, p, m\right), \operatorname{C}\left(X, k\right)\right),\; \operatorname{IsCompactOperator}\left(T\right) \land \left(\forall f \in \operatorname{Lp}\left(k, p, m\right),\; \forall x \in X,\; T\left(f\right)\left(x\right) = \int K\left(x, y\right) \cdot f\left(y\right) \,\mathrm{d}m\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CompactGroups/ContinuousKernelCompact.exists_isCompactOperator_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be compact topological spaces, let Y carry a measurable structure containing its open sets, and let m be a finite measure on Y. The scalar field k is a real or complex field in the sense of the class RCLike (the real numbers, the complex numbers, or a field carrying the same structure), the exponent p lies in [1, infinity], and K is a continuous function on the product X x Y with values in k. The statement provides a continuous k-linear map T from the Lebesgue space Lp(k, p, m) into the space C(X, k) of continuous functions on X with the supremum norm, such that T is a compact operator and, for every f in Lp(k, p, m) and every x in X, the value of T(f) at x is the integral of K(x, y) f(y) over y with respect to m. The integral does not depend on the representative of f, and T(f) is continuous on X.

Since m is finite and p is at least one, every f in Lp(k, p, m) is integrable, and the integral of the absolute value of f is at most C times the norm of f, where C is the real number m(Y) raised to the power 1 - 1/p. Pairing f with a continuous function g on Y is therefore bounded by the supremum norm of g times C times the norm of f. This gives the pointwise bound: the absolute value of T(f)(x) is at most the supremum of the absolute value of K times C times the norm of f, so T is bounded with operator norm at most that product. It also gives, for points x and x' of X, a bound for the absolute value of T(f)(x) - T(f)(x') by the supremum over y of the absolute value of K(x, y) - K(x', y), times C times the norm of f. The map sending x to the section K(x, -) is continuous from X into C(Y, k) with the supremum norm, because K is continuous on the compact space X x Y.

Hence the image of the unit ball of Lp(k, p, m) under T is uniformly bounded and equicontinuous on the compact space X, with values in a compact disc of k. The Arzela-Ascoli theorem gives a compact subset of C(X, k) containing this image, and T is a compact operator. This is the classical compactness of integral operators with a continuous kernel, obtained by the standard argument.

Continuity of the kernel is used twice, for the continuity of T(f) and for the equicontinuity of the image of the unit ball; finiteness of the measure is used for the integrability of Lp functions and the bound C. Compactness of X and Y makes K bounded and its sections uniformly continuous in x. On the one-point space Y with the unit point mass, the operator sends the constant function 1 to the function whose value at x is K(x, y0), where y0 is the point, so the values of T recover the kernel itself.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CompactGroups/ContinuousKernelCompact.exists_isCompactOperator_kernel`
