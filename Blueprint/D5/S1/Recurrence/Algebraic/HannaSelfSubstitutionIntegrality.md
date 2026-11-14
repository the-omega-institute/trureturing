# Hanna's Self-Substitution Integrality

## Abstract

Integral exponential inputs give integral Hanna self-substitution fixed points.

All series are ordinary formal power series over the rationals. IntegralSeries means that each coefficient is the image of an integer. The index zero of L is unused. In logSum, N-n is subtraction in the natural numbers; division is in the rationals after casting n. The finite coefficient sum defines the infinite formal sum without an analytic convergence condition.

**Definition 1.1 (The coefficientwise logarithmic sum).**

$$\forall f: \mathbb{N} \to \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{logSum}\left(f\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((fun N: \mathbb{N} \mapsto \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{Icc}\left(1, N\right), (fun n: \mathbb{N} \mapsto \frac{\operatorname{PowerSeries}.\operatorname{coeff}\left(N - n, f\left(n\right)\right)}{(n: \mathbb{Q})})\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.logSum` (`✓ std3`).

*Citation.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

OEIS A163921, comment (unpaginated): "Conjecture: if F(x) = exp( Sum_{n>=1} L(n)*x^n/n ) is an integer series, then the g.f. that satisfies: G(x) = exp( Sum_{n>=1} G( L(n)*x )^n*x^n/n ) is also an integer series." For a series-valued family f, the degree-N coefficient of Sum_{n>=1} f(n)*x^n/n is the sum of coeff(N-n,f(n))/n over 1<=n<=N.

**Definition 1.2 (The self-substitution equation).**

$$\forall L: \mathbb{N} \to \mathbb{Q}, \forall G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{SolvesHanna}\left(L, G\right) = (G = \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{logSum}\left((fun n: \mathbb{N} \mapsto \operatorname{PowerSeries}.\operatorname{rescale}\left(L\left(n\right), G\right)^{n})\right), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.SolvesHanna` (`✓ std3`).

*Citation.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

OEIS A163921, comment (unpaginated): "Conjecture: if F(x) = exp( Sum_{n>=1} L(n)*x^n/n ) is an integer series, then the g.f. that satisfies: G(x) = exp( Sum_{n>=1} G( L(n)*x )^n*x^n/n ) is also an integer series." PowerSeries.rescale (L n) G is G(L(n)*x); the nth power is multiplied by x^n through logSum. PowerSeries.subst substitutes the zero-constant logarithmic sum into PowerSeries.exp.

**Definition 1.3 (Hanna's integrality conjecture).**

$$claim = (\forall L: \mathbb{N} \to \mathbb{Q}, \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(\operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{logSum}\left((fun n: \mathbb{N} \mapsto \operatorname{PowerSeries}.\operatorname{C}\left(L\left(n\right)\right))\right), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right)\right) \Rightarrow \left((\exists G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{SolvesHanna}\left(L, G\right)) \land (\forall G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{SolvesHanna}\left(L, G\right) \Rightarrow \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(G\right))\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.claim` (`✓ std3`).

*Citation.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

OEIS A163921, comment (unpaginated): "Conjecture: if F(x) = exp( Sum_{n>=1} L(n)*x^n/n ) is an integer series, then the g.f. that satisfies: G(x) = exp( Sum_{n>=1} G( L(n)*x )^n*x^n/n ) is also an integer series." L ranges over rational sequences. The conclusion asserts that a solution exists and that every solution has integer coefficients. Integral input forces all positive-index values of L to be integers.

**Theorem 1.4 (Integral self-substitution fixed points).**

$$\forall L: \mathbb{N} \to \mathbb{Q}, \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(\operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{logSum}\left((fun n: \mathbb{N} \mapsto \operatorname{PowerSeries}.\operatorname{C}\left(L\left(n\right)\right))\right), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right)\right) \Rightarrow \left((\exists G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{SolvesHanna}\left(L, G\right)) \land (\forall G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{SolvesHanna}\left(L, G\right) \Rightarrow \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(G\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hannasubst` (proved) by `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hannasubst","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

For every rational sequence L with integral exponential input, the positive-index values L(n) have integer representatives c(n). The integer Euler ledger of the input gives p dividing c(p*m)-c(m) for every prime p and positive m. Frobenius and power lifting show that the exponential self-substitution operator preserves integer coefficients by the sufficient Dieudonne-Dwork criterion. Its logarithmic sum has constant coefficient zero, so every output has constant coefficient one. The operator raises coefficient agreement by one degree. PowerSeriesNormalizedContraction.exists_unique_fixed supplies a unique rational solution. Starting from 1, each iterate has integer coefficients. For every natural degree N, every solution agrees through degree N with the Nth iterate, so its degree-N coefficient is an integer. Thus a solution exists and every solution is integral in every degree. These are formal power-series statements without an analytic convergence hypothesis or a finite degree bound.

**Lemma 1.5 (Divisibility lifting for powers).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)] \forall p: \mathbb{N}, \forall U: R, \forall V: R, (p: R) \mid U - V \Rightarrow \forall m: \mathbb{N}, (p: R)^{\operatorname{padicValNat}\left(p, m\right) + 1} \mid U^{m} - V^{m}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.power_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

In any commutative ring R, if p divides U-V, then p^(padicValNat(p,m)+1) divides U^m-V^m for every natural m. Here p is any natural number. Ideal congruence power lifting and the divisibility of m by p^padicValNat(p,m) give the conclusion. No unit or coprimality hypothesis is required. This supplies the exponent-changing step for HannaA181076Integrality.

**Theorem 1.6 (Geometric exponential inputs).**

$$\forall a: \mathbb{Z}, \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(\operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{logSum}\left((fun n: \mathbb{N} \mapsto \operatorname{PowerSeries}.\operatorname{C}\left((a: \mathbb{Q})^{n}\right))\right), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.geometric_input` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

For every integer a the exponential of Sum_{n>=1} a^n*x^n/n equals (1-a*X) inverse and has integer coefficients. The specialization a=2 supplies the input for the A157675 equation through HannaSelfSubstitutionIntegralityA157675.result. The identity and integrality hold at every natural degree.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.SolvesHanna`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.geometric_input`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.logSum`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.power_lift`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](../Invariants/CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../Residue/CompositionalSquareDyadicDenominators.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](../Residue/ParametricExponentialSquareCongruence.md)
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](../Witt/HannaDiagonalGhostPowerIntegrality.md)
