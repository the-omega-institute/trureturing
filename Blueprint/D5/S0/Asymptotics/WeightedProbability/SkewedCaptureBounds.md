# Skewed Capture and Escape Bounds

## Abstract

Independent finite listings with column marginals q_b obey the exact skewed capture formulas, two-sided Bonferroni escape bounds, the uniform kernel, and the one-address edge.

**Theorem 1.1 (Skewed exact capture laws and escape bounds).**

$$(\forall b, y,\ 0\leq q_{b}(y) \land \forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow (\forall a,\ \operatorname{P}\left(E_{a}\right) = \varphi_{a} \prod_{b\neq a} c_{b} \land \forall a, a',\ a\neq a' \Rightarrow \operatorname{Ppair}\left(a, a'\right) = \operatorname{fixedSquareMass}\left(q, f, a\right) \operatorname{fixedSquareMass}\left(q, f, a'\right) \prod_{b\neq a, b\neq a'} \operatorname{collisionSquareMass}\left(q, f, b\right) \land 1-\sum_{a} \operatorname{P}\left(E_{a}\right) \leq \operatorname{Pescape}\left(q, f\right) \leq 1-\sum_{a} \operatorname{P}\left(E_{a}\right)+\sum_{a<a'} \operatorname{Ppair}\left(a, a'\right) \land (\forall a,\ \operatorname{P}\left(q^{\mathrm{unif}}, E_{a}\right) = k\,n^{-A} \land \forall a, a',\ a\neq a' \Rightarrow \operatorname{Ppair}\left(q^{\mathrm{unif}}, a, a'\right) = \operatorname{P}\left(q^{\mathrm{unif}}, E_{a}\right)\,\operatorname{P}\left(q^{\mathrm{unif}}, E_{a'}\right)) \land \forall q^{1}: \operatorname{Fin}(1) \to Y \to \mathbb{R},\ (\forall b, y,\ 0\leq q^{1}_{b}(y) \land \forall b,\ \sum_{y} q^{1}_{b}(y) = 1) \Rightarrow \operatorname{Pescape}\left(q^{1}, f\right) = 1-\operatorname{fixedMass}\left(q^{1}, f, 0\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/SkewedCaptureBounds.skewed_capture_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The address type is finite and linearly ordered only to write each unordered pair once as a<a'. Every matrix cell in column b is an independent draw with nonnegative normalized mass q_b.

Here phi_a is fixedMass q f a, c_b is collisionMass q f b, and their superscript-two forms are fixedSquareMass and collisionSquareMass. The finite-product dependency proves the two exact event formulas.

Pointwise first- and second-order Bonferroni inequalities are multiplied by the nonnegative listing weights and summed. For uniform marginals, q^unif is the constant marginal (b,y) |-> 1/n, k is card(Fix f), n is card(Y), and A is card(Address). The final clause quantifies separately over every nonnegative normalized Fin(1) marginal q^1; its fixedMass at address zero is the source's phi_0.

Thus the effective equivalent-mutant quantity is the weighted fixed-point mass q(Fix f), not the alphabet cardinality. No bijectivity assumption is placed on f.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/SkewedCaptureBounds.skewed_capture_bounds`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni](FiniteBonferroni.md)
