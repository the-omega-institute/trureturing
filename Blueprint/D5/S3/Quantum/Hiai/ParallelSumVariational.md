# ParallelSumVariational

## Abstract

The matrix parallel sum as an attained quadratic split minimum.

**Theorem 1.1 (A common split domain in Loewner order).**

$$\forall w: \operatorname{Level}(),\ d: \operatorname{Type}(w), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ P, Q, K: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(P)\land\operatorname{PosDef}(Q)\implies\ \exists Z: \operatorname{Prod}(\operatorname{Matrix}(d, d, \mathbb{C}), \operatorname{Matrix}(d, d, \mathbb{C})),\ \operatorname{fst}(Z)=\operatorname{inverse}(P)\operatorname{parallelSum}(P, Q)K\land\operatorname{snd}(Z)=\operatorname{inverse}(Q)\operatorname{parallelSum}(P, Q)K\land\operatorname{fst}(Z)+\operatorname{snd}(Z)=K\land\operatorname{adjoint}(\operatorname{fst}(Z))P\operatorname{fst}(Z)+\operatorname{adjoint}(\operatorname{snd}(Z))Q\operatorname{snd}(Z)=\operatorname{adjoint}(K)\operatorname{parallelSum}(P, Q)K\land(\forall W: \operatorname{Prod}(\operatorname{Matrix}(d, d, \mathbb{C}), \operatorname{Matrix}(d, d, \mathbb{C})),\ \operatorname{fst}(W)+\operatorname{snd}(W)=K\implies\operatorname{adjoint}(K)\operatorname{parallelSum}(P, Q)K\le\operatorname{adjoint}(\operatorname{fst}(W))P\operatorname{fst}(W)+\operatorname{adjoint}(\operatorname{snd}(W))Q\operatorname{snd}(W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/ParallelSumVariational.parallel_sum_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P and Q be positive definite complex square matrices, H = (P inverse + Q inverse) inverse, and K any complex square matrix. For every split U + V = K, the energy U* P U + V* Q V dominates K* H K in the actual Loewner order. The split U = P inverse H K and V = Q inverse H K attains equality.

Subtracting the minimum energy gives the sum of the two positive quadratic energies of U minus its optimizer and V minus its optimizer. The two cross terms cancel because the split shares the same K. No commutation, selfadjointness or invertibility is required of K, U or V.

This is the matrix minimum needed by the real variational candidate route to the Hiai outer-power concavity supplier. Setting P to t inverse times B to exponent p and Q to A to exponent p gives the weighted inverse sum. The next obligations are the weighted trace minimum, its joint concavity using the existing Lieb theorem, the geometric-mean integral, and the trace Legendre maximum. This theorem does not assert those analytic steps or resolve Hiai Problem 5.18.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/ParallelSumVariational.parallel_sum_minimum`
- Dependency: [D5/S3/Quantum/Hiai/InverseMeanVariational](InverseMeanVariational.md)
