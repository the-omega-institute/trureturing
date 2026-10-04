# Dyadic Cost Support Lines

## Abstract

Affine supporting inequalities for the classical dyadic cost on the three- and five-outcome real simplexes.

**Definition 1.1 (Dyadic residual).**

$$\forall I: Type, [\operatorname{Fintype}\left(I\right)], \forall p: I \to \mathbb{R}, \forall d: \mathbb{N}, \operatorname{R}\left(p, d\right) = 2^{d} - \sum_{i \in I}\left\lfloor2^{d} \operatorname{p}\left(i\right)\right\rfloor$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.residual` (`✓ std3`).

*Citation.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

R(p,d) counts unassigned dyadic cylinders algebraically. The floor is the integer floor. For a nonnegative real probability vector with m coordinates summing to one, R(p,d) is an integer between zero and m-1. Zero coordinates and terminating dyadic expansions are included.

**Definition 1.2 (Classical dyadic tail cost).**

$$\forall I: Type, [\operatorname{Fintype}\left(I\right)], \forall p: I \to \mathbb{R}, \operatorname{L}\left(p\right) = \sum_{d \in \mathbb{N}}\frac{\operatorname{R}\left(p, d\right)}{2^{d}}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.cost` (`✓ std3`).

*Citation.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

L(p) is the real infinite sum of these normalized residuals. The geometric bound (m-1) divided by 2 to the power d gives summability on each finite simplex. The series expression is the classical Knuth-Yao DDG cost recalled by Lumbroso, Section 2.1. The support theorem below concerns this numerical series. Both definitions accept arbitrary finite real vectors. Lean takes an unsummable real tsum to be zero; values outside the probability simplex do not represent sampling costs.

**Theorem 1.3 (Five-outcome support lines).**

$$\forall p: \operatorname{Fin}\left(5\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left(5\right), 0 \le \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left(5\right)}\operatorname{p}\left(i\right) = 1) \Rightarrow (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(p, d\right)}{2^{d}}\right) \land \forall t: \mathbb{R}, (t = \operatorname{min}\left(p\right) \Rightarrow (0 \le t \land (t \le \frac{1}{5} \land (16 t \le \operatorname{L}\left(p\right) \land 48 t - 6 \le \operatorname{L}\left(p\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real probability vector on Fin(5), let t be its smallest coordinate. The series is summable, 0 <= t <= 1/5, and both 16t <= L(p) and 48t-6 <= L(p) hold. No rationality or strict positivity hypothesis is imposed. For positive t, in the five consecutive intervals ending at 1/16, 1/8, 5/32, 1/6 and 3/16, finite dyadic bucket budgets give partial-cost bounds 1, 2, 5/2, 11/4 and 3. Above 3/16 the vector q(i)=16p(i)-3 is again a probability vector and L(p)=27/8+L(q)/16. Iterating an error bound of size 4/16^n and taking its zero limit proves the second supporting line, including the uniform law. The two bounds supply necessary inequalities and assert no attainment claim for each prescribed smallest coordinate.

**Theorem 1.4 (Three-outcome support lines).**

$$\forall p: \operatorname{Fin}\left(3\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left(3\right), 0 \le \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left(3\right)}\operatorname{p}\left(i\right) = 1) \Rightarrow (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(p, d\right)}{2^{d}}\right) \land \forall t: \mathbb{R}, (t = \operatorname{min}\left(p\right) \Rightarrow (0 \le t \land (t \le \frac{1}{3} \land (6 t \le \operatorname{L}\left(p\right) \land 14 t - 2 \le \operatorname{L}\left(p\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.three_outcome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real probability vector on Fin(3), its smallest coordinate t lies between zero and 1/3, the dyadic series is summable, and 6t <= L(p) and 14t-2 <= L(p). At t=0 nonnegativity suffices. When 0<t<=1/4, the first two terms total at least 3/2. Above 1/4 all coordinates are below 1/2, those terms total two, and q(i)=4p(i)-1 is a probability vector with L(p)=2+L(q)/4. An error bound of size 3/4^n tends to zero and supplies the second line on the entire real simplex, including the uniform vector. For the uniform three-outcome law the same exact tail identity gives L(p)=8/3. These are support inequalities for the numerical series; no optimization or phase-transition statement is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.cost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.residual`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.three_outcome`
