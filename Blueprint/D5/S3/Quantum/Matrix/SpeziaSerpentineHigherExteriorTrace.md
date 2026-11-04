# Spezia’s higher exterior traces

## Abstract

All exterior traces above order two of the serpentine matrix vanish.

**Definition 1.1 (Spezia’s second conjecture).**

$$claim \Leftrightarrow (\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), (2 < k) \Rightarrow (\operatorname{D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.traceExt}\left(k, \operatorname{D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.M}\left(n\right)\right) = 0))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace.claim` (`✓ std3`).

*Citation.* Stefano Spezia (2018). *OEIS A322844 and the serpentine matrix A317614*. URL: <https://oeis.org/A322844>.

*Commentary.*

A322844 COMMENTS, revision 68, unpaginated: “For k > 2, the trace of the k-th exterior power of the matrix M(n) is equal to zero.” Both n and k range over the naturals. The matrix and the signed characteristic-coefficient exterior trace are those of the second-trace module, including zero for k > n.

**Theorem 1.2 (Every higher exterior trace is zero).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), (2 < k) \Rightarrow (\operatorname{D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.traceExt}\left(k, \operatorname{D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.M}\left(n\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace.result` (`✓ std3`). ∎

*Resolves.* `Problems/sp322844-serpentine-higher` (proved) by `D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sp322844-serpentine-higher","declaration_gid":"D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stefano Spezia (2018). *OEIS A322844 and the serpentine matrix A317614*. URL: <https://oeis.org/A322844>.

*Commentary.*

When k ≤ n, the factor X^(n−2) forces the relevant coefficient to vanish because k > 2. When k > n, the exterior trace is zero by its zero-space case. Thus small matrix orders are included.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace.result`
- Dependency: [D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace](SpeziaSerpentineSecondExteriorTrace.md)
