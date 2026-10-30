# Native command lifetimes

## Abstract

Uniform lifetime estimates for finite native commands driven by unreweighted fair signs.

A model fixes r>0, 0<l<u<r/2 and an interior source. Its raw density is smooth and positive, and its horizontal covariance is smooth, symmetric and positive definite on an open neighbourhood of the closed height cylinder. Both phase lifts are periodic under integer multiples of 2π. The drift is the density-divergence drift of these raw coefficients, and sigma is the positive square root of the covariance.

The source map sends a control triple (a,b,j) to height k_o+a and the actual phase classes of alpha_o+b/2 and beta_o+(1/2-k_o/r)b-j/r. The two phase circles have period 2π. On each cell of duration delta=1/n², the increment is d(q)delta+sqrt(2delta)sigma(q)xi. Each of the four sign pairs has probability 1/4 independently of every preceding pair.

A chord with increment v has controls a+theta v1 and b+theta v2, and chronological area j+theta a v2+theta²v1v2/2. Its first contact with either height wall cuts the chord and starts a hold. The complete word has n³ cells. If all cells survive, a final cell of the same original duration moves the height linearly to the upper wall while the second control stays constant. The control lifts and the area are translated at joins, without a reset.

**Definition 1.1 (Ordinary chronological area).**

$$\forall B: \operatorname{Model}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left((n)^{3}\right) \to \operatorname{SignPair}, \forall T: \mathbb{R}, \operatorname{commandArea}\left(B, n, w, T\right) = \operatorname{intervalIntegral}\left(0, T, (s: \mathbb{R} \mapsto \operatorname{command}\left(B, n, w, s\right)\left(0\right) \cdot \operatorname{deriv}\left((x: \mathbb{R} \mapsto \operatorname{command}\left(B, n, w, x\right)\left(1\right)), s\right))\right)$$

*Formalization.* `D5/S3/Analytic/Probability/NativeCommandLifetime.commandArea` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral is the ordinary integral of the first control against the derivative of the absolutely continuous second control. It includes a partial final chord and all elapsed original durations.

**Definition 1.2 (Uniform finite-word tail probability).**

$$\forall B: \operatorname{Model}, \forall n: \mathbb{N}, \forall t: \mathbb{R}, \operatorname{tailProbability}\left(B, n, t\right) = (\frac{1}{4})^{(n)^{3}} \cdot \sum_{w: \operatorname{Fin}\left((n)^{3}\right) \to \operatorname{SignPair}} (\operatorname{ite}\left(t < \operatorname{zeta}\left(B, n, w\right), 1, 0\right))$$

*Formalization.* `D5/S3/Analytic/Probability/NativeCommandLifetime.tailProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum ranges over every sign-pair word, including words with unused suffixes after killing. No word is rejected or reweighted. The first wall time zeta is computed from the actual held state, whose third coordinate is the physical beta phase class. The ordinary chronological integral is the third coordinate of the command/control triple (commandArea), and the theorem identifies it with the corresponding input of physicalState.

**Definition 1.3 (Expected excess lifetime).**

$$\forall B: \operatorname{Model}, \forall n: \mathbb{N}, \forall R: \mathbb{R}, \operatorname{excessExpectation}\left(B, n, R\right) = (\frac{1}{4})^{(n)^{3}} \cdot \sum_{w: \operatorname{Fin}\left((n)^{3}\right) \to \operatorname{SignPair}} (\operatorname{max}\left(\operatorname{zeta}\left(B, n, w\right) - R, 0\right))$$

*Formalization.* `D5/S3/Analytic/Probability/NativeCommandLifetime.excessExpectation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same uniform finite-word law defines the expectation of the positive part of the excess lifetime.

**Theorem 1.4 (Uniform full-lifetime estimates).**

$$\forall B: \operatorname{Model}, \exists h: \mathbb{R}, \exists M: \mathbb{R}, \exists n0: \mathbb{N}, (0 < h) \land ((0 < M) \land ((1 \le n0) \land (\forall n: \mathbb{N}, (n0 \le n) \Rightarrow ((\forall t: \mathbb{R}, (0 \le t) \Rightarrow (\operatorname{tailProbability}\left(B, n, t\right) \le (\frac{1}{2})^{\operatorname{Nat.floor}\left(\frac{\operatorname{max}\left(t - 1, 0\right)}{h}\right)})) \land ((\forall R: \mathbb{R}, (1 \le R) \Rightarrow (\operatorname{excessExpectation}\left(B, n, R\right) \le 2 \cdot h \cdot (\frac{1}{2})^{\operatorname{Nat.floor}\left(\frac{R - 1}{h}\right)})) \land (\forall w: \operatorname{Fin}\left((n)^{3}\right) \to \operatorname{SignPair}, (0 < \operatorname{zeta}\left(B, n, w\right)) \land ((\operatorname{zeta}\left(B, n, w\right) \le \left((n)^{3} + 1\right) \cdot \operatorname{mesh}\left(n\right)) \land (\forall T: \mathbb{R}, (0 \le T) \Rightarrow ((\operatorname{OriginalControl}\left(\operatorname{nativeBase}\left(B\right), T, (t: \mathbb{R} \mapsto \operatorname{Prod.fst}\left(\operatorname{heldState}\left(B, n, w, t\right)\right)), (t: \mathbb{R} \mapsto \operatorname{command}\left(B, n, w, t\right)\left(1\right))\right)) \land ((\operatorname{commandArea}\left(B, n, w, T\right) = \operatorname{command}\left(B, n, w, T\right)\left(2\right)) \land (\operatorname{heldState}\left(B, n, w, T\right) = \operatorname{physicalState}\left(B, \operatorname{command}\left(B, n, w, T\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/NativeCommandLifetime.actual_lifetime_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constants depend only on the fixed raw model and interval. Every sufficiently fine mesh satisfies both estimates for every nonnegative real time and every real cutoff at least one. The theorem also identifies the ordinary integral with the recursively computed chronological area at every nonnegative prefix, identifies the held state on the actual torus, and certifies the original control and the finite positive first-wall lifetime.

Compactness of one phase fundamental domain bounds the derivative-defined height drift and gives a positive lower bound for the first diagonal covariance entry. A positive exponential test of height has a uniformly positive expected increment for sufficiently small mesh. The exact fair-sign exponential average is the exponential drift factor times two hyperbolic cosines. The public even-factorial-sum inequality supplies the required quadratic lower bounds.

Summing the stopped increments over an arbitrary finite horizon bounds delta times the sum of endpoint survival probabilities. The last comparison endpoint retains its exit overshoot; bounded raw increments bound the exponential test there. Thus the occupation estimate is derived from the raw model rather than imposed as a drift, tail or contraction hypothesis.

The occupation bound gives a common mean bound from every alive triple. Markov's inequality then bounds survival across a block by one half. Fresh fair signs give geometric decay over successive blocks. Finite-prefix arguments bound both the tail and excess lifetime, with the terminal upper-wall cell accounted for by the time shift of at most one.

For each cut chord, absolute continuity and the fundamental theorem of calculus identify its polynomial area with its ordinary integral. Public original-control concatenation gives integral additivity with the translated real control lift. Induction establishes the identification at every prefix. The chord height is affine, so the recursive killing fraction is exactly the first hit of either wall. These identities transfer both estimates to the actual executed law.

## References

- Truth anchor: `D5/S3/Analytic/Probability/NativeCommandLifetime.actual_lifetime_estimates`
- Truth anchor: `D5/S3/Analytic/Probability/NativeCommandLifetime.commandArea`
- Truth anchor: `D5/S3/Analytic/Probability/NativeCommandLifetime.excessExpectation`
- Truth anchor: `D5/S3/Analytic/Probability/NativeCommandLifetime.tailProbability`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift](../../Arith/Lattices/Klartag/Walk/ChainDrift.md)
- Dependency: [D5/S3/Observer/Hankel/PositiveGramianBalancing](../../Observer/Hankel/PositiveGramianBalancing.md)
- Dependency: [D5/S3/Quantum/Fibers/OriginalControlComposition](../../Quantum/Fibers/OriginalControlComposition.md)
- Dependency: [D5/S3/Zeros/Jensen/FactorialJensenKernelBound](../../Zeros/Jensen/FactorialJensenKernelBound.md)
