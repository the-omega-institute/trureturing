# Result

## Abstract

Continuants, path entries and Katz cut-offs.

Natural division is truncated division on the natural numbers. val denotes the coercion of a finite index to its natural value. All vertex indices start at zero.

**Definition 1.1 (claim).**

$$claim = ((\forall n: \mathbb{N}, (6 \le n) \implies (\exists a: \mathbb{R}, (\frac{1}{\operatorname{Real.sqrt}\left(5\right)} < a) \land ((a < \frac{1}{2}) \land (\operatorname{p1}\left(n, a\right) = 0)))) \land (\forall a: \mathbb{N} \to \mathbb{R}, (\forall n: \mathbb{N}, (6 \le n) \implies ((0 < \operatorname{a}\left(n\right)) \land ((\operatorname{a}\left(n\right) < \frac{1}{2}) \land (\operatorname{p1}\left(n, \operatorname{a}\left(n\right)\right) = 0)))) \implies ((\forall n: \mathbb{N}, (6 \le n) \implies (\frac{1}{\operatorname{Real.sqrt}\left(5\right)} < \operatorname{a}\left(n\right))) \land (\operatorname{Tendsto}\left(a, atTop, \operatorname{nhds}\left(\frac{1}{\operatorname{Real.sqrt}\left(5\right)}\right)\right)))))$$

*Formalization.* `D5/S1/Recurrence/KatzCutoff/Result.claim` (`✓ std3`).

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Conjecture 4, page 17: “The cut-off values α_n converge to 1/√5 from above.” Page 16: “We call the roots α_n of the polynomials ₙp₁ the cut-off values for the path graph P_n.” Theorem 19, page 16: “For n − j ≥ 5, ₙp_j(α) has a root between 1/√5 and 1/2.” The first conjunct supplies existence for n ≥ 6. The second quantifies every sequence of roots in (0, 1/2); its first six values are unrestricted.

**Theorem 1.2 (result).**

$$(\forall n: \mathbb{N}, (6 \le n) \implies (\exists a: \mathbb{R}, (\frac{1}{\operatorname{Real.sqrt}\left(5\right)} < a) \land ((a < \frac{1}{2}) \land (\operatorname{p1}\left(n, a\right) = 0)))) \land (\forall a: \mathbb{N} \to \mathbb{R}, (\forall n: \mathbb{N}, (6 \le n) \implies ((0 < \operatorname{a}\left(n\right)) \land ((\operatorname{a}\left(n\right) < \frac{1}{2}) \land (\operatorname{p1}\left(n, \operatorname{a}\left(n\right)\right) = 0)))) \implies ((\forall n: \mathbb{N}, (6 \le n) \implies (\frac{1}{\operatorname{Real.sqrt}\left(5\right)} < \operatorname{a}\left(n\right))) \land (\operatorname{Tendsto}\left(a, atTop, \operatorname{nhds}\left(\frac{1}{\operatorname{Real.sqrt}\left(5\right)}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/evans-francis-jones-2025-katz-cutoff-limit` (proved) by `D5/S1/Recurrence/KatzCutoff/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"evans-francis-jones-2025-katz-cutoff-limit","declaration_gid":"D5/S1/Recurrence/KatzCutoff/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Every path size n ≥ 6 has a cut-off in (1/√5, 1/2), and every sequence choosing roots in (0, 1/2) converges to 1/√5 from above. Positive continuants identify the extremal entries; a positive continued fraction makes the crossing strictly increasing, and a geometric-power limit traps every root.

## References

- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Result.claim`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Result.result`
- Dependency: [D5/S1/Recurrence/KatzCutoff/Monotone](Monotone.md)
- Dependency: [D5/S1/Recurrence/KatzCutoff/ProductExtrema](ProductExtrema.md)
- Dependency: [D5/S1/Recurrence/KatzCutoff/Reduction](Reduction.md)
