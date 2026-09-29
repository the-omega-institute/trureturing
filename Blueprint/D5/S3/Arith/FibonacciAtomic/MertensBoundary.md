# The Seven-Ten Boundary and Mertens Power Bounds

## Abstract

Power bounds for the seven-ten boundary and coprime Mertens sums.

**Definition 1.1 (Coprime Mertens sums).**

$$\operatorname{C}\left(R, X\right) = \sum_{0<n\le\left\lfloor X\right\rfloor,\operatorname{gcd}\left(n, R\right)=1}\operatorname{mu}\left(n\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/MertensBoundary.coprimeMertens` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural modulus R and real cutoff X, C(R,X) sums the integer Moebius function over positive natural numbers at most the natural floor of X and coprime to R. The natural floor is zero for negative inputs. Thus C(70,X) is the coprime Mertens sum, and C(1,X) is the ordinary Mertens sum M(X).

**Definition 1.2 (The signed boundary interval).**

$$\operatorname{B}\left(X\right) = \sum_{\left\lfloor\frac{X}{10}\right\rfloor<n\le\left\lfloor\frac{X}{7}\right\rfloor,\operatorname{gcd}\left(n, 70\right)=1}\operatorname{mu}\left(n\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/MertensBoundary.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(X) sums the same Moebius coefficients coprime to seventy over the real interval X/10 < n <= X/7. Its natural-index form uses the open-closed interval between the two natural floors. In particular, endpoints are retained with their stated strict and weak inequalities.

**Theorem 1.3 (Equivalent positive power bounds).**

$$\forall a\in\mathbb{R},0<a\Rightarrow(\operatorname{P}\left(B, a\right)\Leftrightarrow\operatorname{P}\left(\operatorname{C}\left(70\right), a\right))\land(\operatorname{P}\left(\operatorname{C}\left(70\right), a\right)\Leftrightarrow\operatorname{P}\left(\operatorname{C}\left(1\right), a\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/MertensBoundary.power_bounds_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real exponent a, both equivalences hold as X tends to positive infinity through all real cutoffs. P(f,a) denotes Asymptotics.IsBigO atTop f (fun X => Real.rpow X a). The boundary is C(70,X/7)-C(70,X/10). Iterating the contraction q=7/10 until q^j X<1 gives a finite telescoping sum, bounded by a geometric series with ratio q^a<1. For a prime p coprime to R, splitting the Moebius sum according to divisibility by p gives C(R,X)=C(pR,X)-C(pR,X/p). The same contraction estimate, applied successively at p=2,5,7, relates the restricted and ordinary sums. These equivalences impose no Riemann hypothesis assumption and assert no Riemann hypothesis criterion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MertensBoundary.boundary`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MertensBoundary.coprimeMertens`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MertensBoundary.power_bounds_iff`
