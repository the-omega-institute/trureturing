# Arbitrary-alphabet circuit lower bounds

## Abstract

Low automatic complexity and its complement defeat bounded-depth circuits.

**Definition 1.1 (Question 5.1).**

$$\operatorname{claim} = \left(\forall Alphabet \in Type,\; [\operatorname{Fintype}\left(Alphabet\right)], (2 \le \operatorname{Fintype}.\operatorname{card}\left(Alphabet\right)) \Rightarrow ((\operatorname{complexityTotal}\left(Alphabet\right)) \land (\forall q \in \mathbb{Q},\; (0 < q) \Rightarrow ((q < \frac{(1:\mathbb{Q})}{2}) \Rightarrow ((\forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow (\forall e \in Alphabet \to \operatorname{ZMod}\left(p\right),\; (\operatorname{Function}.\operatorname{Injective}\left(e\right)) \Rightarrow ((\neg (\operatorname{arithmeticRecognizable}\left(p, e, \operatorname{Lq}\left(Alphabet := Alphabet, q\right)\right))) \land (\neg (\operatorname{arithmeticRecognizable}\left(p, e, (\operatorname{Lq}\left(Alphabet := Alphabet, q\right))^{c}\right)))))) \land (\forall t \in \mathbb{N},\; \forall e \in Alphabet \to \left(\operatorname{Fin}\left(t\right) \to Bool\right),\; (\operatorname{Function}.\operatorname{Injective}\left(e\right)) \Rightarrow ((\neg (\operatorname{booleanRecognizable}\left(t, e, \operatorname{Lq}\left(Alphabet := Alphabet, q\right)\right))) \land (\neg (\operatorname{booleanRecognizable}\left(t, e, (\operatorname{Lq}\left(Alphabet := Alphabet, q\right))^{c}\right)))))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Question 5.1, p. 19: “Do the results from Theorem 4.9 apply to arbitrary alphabets using the definition of ⊕SAC⁰ given in Definition 4.4?” Theorem 4.9 asserts both the Lq and complement lower bounds. Alphabet is an arbitrary finite type with at least two elements; q is rational with 0 < q < 1/2. The first conclusion proves that exact complexity is finite and attained. The remaining conclusions quantify over every prime-field alphabet embedding and every fixed injective Boolean block encoding. Original-symbol length is used in Lq. Constants are allowed, circuit size and addition fan-in are unrestricted, and correctness is required only on valid encoded words.

**Theorem 1.2 (The affirmative arbitrary-alphabet result).**

$$\forall Alphabet \in Type,\; [\operatorname{Fintype}\left(Alphabet\right)], (2 \le \operatorname{Fintype}.\operatorname{card}\left(Alphabet\right)) \Rightarrow ((\operatorname{complexityTotal}\left(Alphabet\right)) \land (\forall q \in \mathbb{Q},\; (0 < q) \Rightarrow ((q < \frac{(1:\mathbb{Q})}{2}) \Rightarrow ((\forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow (\forall e \in Alphabet \to \operatorname{ZMod}\left(p\right),\; (\operatorname{Function}.\operatorname{Injective}\left(e\right)) \Rightarrow ((\neg (\operatorname{arithmeticRecognizable}\left(p, e, \operatorname{Lq}\left(Alphabet := Alphabet, q\right)\right))) \land (\neg (\operatorname{arithmeticRecognizable}\left(p, e, (\operatorname{Lq}\left(Alphabet := Alphabet, q\right))^{c}\right)))))) \land (\forall t \in \mathbb{N},\; \forall e \in Alphabet \to \left(\operatorname{Fin}\left(t\right) \to Bool\right),\; (\operatorname{Function}.\operatorname{Injective}\left(e\right)) \Rightarrow ((\neg (\operatorname{booleanRecognizable}\left(t, e, \operatorname{Lq}\left(Alphabet := Alphabet, q\right)\right))) \land (\neg (\operatorname{booleanRecognizable}\left(t, e, (\operatorname{Lq}\left(Alphabet := Alphabet, q\right))^{c}\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

A repeated-factor estimate supplies sparse nonempty sections without a density assumption. If a word of length n has an exact k-state realization and no repeated m-factor, then n + 1 ≤ 2k + m². Low complexity therefore forces a repeated factor when m² ≤ (1 − 2q)n. The number of such length-n words over an r-letter alphabet is at most (n + 1)² r^(n−m). Choosing n proportional to m² makes this exponentially smaller than the whole section. The finite-grid polynomial obstruction then excludes each arithmetic circuit family. For Boolean encodings, restrict each block to two distinct alphabet letters and substitute their affine bit coordinates. This proves both language and complement conclusions at every rational threshold strictly between zero and one half. It asserts no endpoint q = 1/2 result, no growing-depth or growing-fan-in bound, and no separate density-limit theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound.claim`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound.result`
- Dependency: [D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure](ExactNFACircuitInfrastructure.md)
