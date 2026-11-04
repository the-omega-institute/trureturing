# Weighted defects of finite operator words

## Abstract

The complete weighted pair defect controls every finite Hermitian operator word.

Let Phi be any unital completely positive linear map from complex d by d matrices to complex k by k matrices. No trace preservation, idempotence, or dynamical assumption is imposed on Phi. Every matrix norm in this result is the operator norm on the Euclidean coordinate Hilbert space. The finite list is ordered and may contain repetitions or zero matrices; its length is unrestricted, including zero and one.

**Theorem 1.1 (The weighted pair bound).**

$$\forall d \in Type,\; \forall k \in Type,\; [\operatorname{Fintype}\left(d\right)] [\operatorname{DecidableEq}\left(d\right)] [\operatorname{Fintype}\left(k\right)] [\operatorname{DecidableEq}\left(k\right)] \forall l \in \mathbb{N},\; \forall f \in \operatorname{UCP}\left(\operatorname{Matrix}\left(d, d, \mathbb{C}\right), \operatorname{Matrix}\left(k, k, \mathbb{C}\right)\right),\; \forall A \in \operatorname{Fin}\left(l\right) \to \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; (\forall i\in \operatorname{Fin}\left(l\right), A_{i}^{*}=A_{i}) \implies \Vert f(\prod_{0\le r<l}A_{r})-\prod_{0\le r<l}f(A_{r}) \Vert_{op} \le \sum_{0\le i<j<l}\sqrt{\Vert f(A_{i}^{*}A_{i})-f(A_{i})^{*}f(A_{i}) \Vert_{op}}\sqrt{\Vert f(A_{j}^{*}A_{j})-f(A_{j})^{*}f(A_{j}) \Vert_{op}} \prod_{0\le r<l,r\neq i,r\neq j}\Vert A_{r} \Vert_{op}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/WeightedWordDefect.ucp_word_pair_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the jth letter set M_j equal to its Euclidean operator norm and epsilon_j equal to the square root of the operator norm of Phi(A_j adjoint times A_j) minus Phi(A_j) adjoint times Phi(A_j). The norm of Phi applied to the ordered product minus the ordered product of the images is at most the sum over all positional pairs i less than j of epsilon_i times epsilon_j times the product of M_r over all remaining positions. The function pairSum is exactly this finite sum: the two omitted factors are replaced by one. No norm is divided out.

FiniteKrausChannel.krausRepresentation supplies the original rectangular matrices L_r with Phi(X) equal to the sum of L_r X L_r adjoint. The source convention K_r is L_r adjoint. Stack these adjoints into V and amplify X by the identity on the finite Kraus index. Unitality proves V adjoint times V equals the identity, and compressing this amplification gives the original Phi on every matrix. The original IsometricCompression support, compress, and normal definitions implement this same frame. With Q equal to I minus V V adjoint, the discarded map D(X) is Q pi(X) V. Its Gram product is exactly the original multiplicative defect. The C-star norm identity proves that the norm of D(X) equals the square root used in the bound.

The intertwining residual for the entire ordered word is bounded by the sum of the single-deletion weights. Projecting the residual bounds the leakage of the word. The first Hermitian letter then contributes its leakage norm times the remaining single-deletion sum; induction supplies the remaining pairs with the first letter's norm as a factor. This analytic induction works at every finite length. Recursive weights are equated to the explicit sums on finite positions.

If all letters are chosen from two Hermitian contractions and both squared defects have norm at most delta, every pair contributes at most delta. There are length choose two pairs, so the word error is at most that number times delta. This consequence concerns finite words; it asserts neither uniform control over all word lengths nor convergence of an infinite iteration.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/WeightedWordDefect.ucp_word_pair_bound`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Reduction/IsometricCompression](IsometricCompression.md)
