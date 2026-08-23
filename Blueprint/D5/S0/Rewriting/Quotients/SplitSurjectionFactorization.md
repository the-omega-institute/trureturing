# Split Surjection Factorization

## Abstract

A fiber-constant map factors uniquely through a split surjection.

**Theorem 1.1 (Fiber constancy and a section give unique factorization).**

$$\forall X, B', B,\ \forall q': X \to B', q: X \to B, s: B' \to X,\ (\forall x, y,\ q'(x) = q'(y) \Rightarrow q(x) = q(y)) \Rightarrow \operatorname{RightInverse}\left(s, q'\right) \Rightarrow \exists! p: B' \to B,\ q = p \circ q'.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Quotients/SplitSurjectionFactorization.split_surjection_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let qPrime map X to BPrime, let q map X to B, and let s be a section of qPrime. Fiber constancy says that q takes equal values whenever qPrime does.

The unique factor sends bPrime to q(s(bPrime)). The section equation and fiber constancy prove that composing this factor with qPrime recovers q.

Repository search found only self-map and continuous variants. Pinned Mathlib supplies RightInverse.surjective and Surjective.injective_comp_right; the proof applies both directly.

The module compiles the identity section on Bool with Boolean negation as a simultaneous witness for the hypotheses and conclusion.

## References

- Truth anchor: `D5/S0/Rewriting/Quotients/SplitSurjectionFactorization.split_surjection_factorization`
