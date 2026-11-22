# Finite modular-frequency evaluation on the Petz upper boundary

## Abstract

Finite upper-strip frequency counts control evaluation at zero and the squared trace norm of the endpoint Gram difference.

Throughout, w(s) = pi/(cosh(2 pi s) + 1) and every integral runs over the whole real line with Lebesgue measure.

**Theorem 1.1 (Evaluation in a finite orthogonal sum).**

Lean statement: `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.weighted_evaluation_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.weighted_evaluation_blocks` (`✓ std3`). ∎

*Citation.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For a finite set of blocks, let each block have a complex inner product space, a finite index type, real frequencies omega(b,i), and vector coefficients a(b,i). Let F(s) be the orthogonal Hilbert sum of the vectors sum_i exp(i omega(b,i) s) a(b,i). If the image of each block's frequency list has cardinality at most m, then w(s) times the squared norm of F(s) is integrable and the squared norm of F(0) is at most 2m times its integral. Empty lists and coincident frequencies are allowed.

The scalar estimate at zero is Yang's Lemma IV.2, equation (IV.2). The proof uses the frozen ExponentialGramWeightedEvaluation.weighted_evaluation on the two reflected half-lines with rate 2 pi. Equal frequencies are merged by summing their coefficients. Parseval on the finite span of each block's coefficients lifts the estimate to vector amplitudes. Summing the integrable squared block norms gives the same common coefficient.

**Theorem 1.2 (Mixed modular-frequency coordinates).**

Lean statement: `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.weighted_evaluation_petz_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.weighted_evaluation_petz_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix finite row, column, block, and retained index types, with a block assignment for each row and column pair. Given real arrays outer, q and p and complex coefficient matrices A and C, set R(b,k) = outer(b)/(q(k.left)/p(k.right)) for k in the product of the retained index types. In block b, the error E(s) has constant term A and subtracts the terms sqrt(R(b,k)) C(k) exp(i log(R(b,k)) s) entrywise. Let m bound the number of distinct values in each list consisting of zero and the log(R(b,k)). Then w(s) times the squared Frobenius norm of E(s) is integrable, and the squared Frobenius norm of E(0) is at most 2m times its integral.

The coordinate fibers of the block assignment are orthogonal in the Frobenius norm. Their frequency lists include the constant mode. Repeated ratios and collisions with zero are counted once. Counting the entries of the Option index gives m = 1 + card(Q) card(P), and equal retained dimensions d give m = 1 + d squared. The real arrays and coefficient matrices are abstract inputs. The formulas use Lean’s totalized real operations, with division by zero, the square root of a nonpositive real, and log of zero all equal to zero, and log of a negative real equal to log of its absolute value.

**Theorem 1.3 (Endpoint Gram trace error).**

Lean statement: `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.traceNorm_gram_sub_sq_le_petz_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.traceNorm_gram_sub_sq_le_petz_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the same finite data and count m, put B = A - E(0) and assume A and B both have unit Frobenius norm. The squared trace norm of B B* - A A* is at most 8m times the integral of w(s) times the squared Frobenius norm of E(s). The bound is 8(1 + d squared) times this energy for equal retained dimensions d. The proof splits the Gram difference into two products and uses the frozen rectangular Schatten–Hölder inequality before applying the modular-frequency estimate.

A channel application requires identifying the coefficients and coordinate blocks with the supported Stinespring boundary amplitude and verifying that the endpoint Grams are the input and the ordinary Petz output. It also requires proving unit normalization and bounding the upper-boundary energy by the relative-entropy loss through the strip identity, including any Schwarz correction for the chosen realization.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.traceNorm_gram_sub_sq_le_petz_boundary`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.weighted_evaluation_blocks`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation.weighted_evaluation_petz_boundary`
- Dependency: [D5/S3/Analytic/ExponentialGramWeightedEvaluation](../../Analytic/ExponentialGramWeightedEvaluation.md)
- Dependency: [D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM](../Entanglement/TavakoliMorelliIncompleteEAM.md)
