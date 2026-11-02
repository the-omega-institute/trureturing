# Ordered GNS Projections

## Abstract

Faithful matrix states detect positivity through internal compressions of a star-subalgebra.

**Theorem 1.1 (Internal compressions detect positivity).**

$$\forall y\in A, y^{*}=y\implies(\forall q\in A, \Re\varphi_{\rho}(q^{*}yq)\geq0)\implies y\geq0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OrderedGNSProjection.positive_of_internal_compressions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an arbitrary positive definite complex matrix rho and a unital star-subalgebra A. A Hermitian matrix y in A is positive semidefinite if every compression q-star y q, with q in A, has nonnegative real rho-weighted trace.

Continuous functional calculus keeps the square root of the negative part of y in A. Its compression is the negative of the square of that negative part. Faithfulness of the weighted matrix inner product forces the negative part to vanish.

**Theorem 1.2 (Ordered comparisons and complete positivity).**

$$(\forall x, \forall a\in A, \varphi_{\rho}(E(x)a)=\varphi_{\rho}(xa))\iff(\forall x, E(x^{*})=E(x)^{*})\iff\operatorname{Expectation}\left(\rho, A, E\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OrderedGNSProjection.ordered_gns_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be any positive definite complex matrix of trace one, and let A be any unital star-subalgebra on the same finite carrier. The map E is the unique orthogonal projection onto A for the inner product tr(rho x-star y). Its left ordered comparisons determine E without any positivity assumption.

Retraction, preservation of the unit and state, and the left module law follow from that orthogonal projection. The additional complex identity tr(rho E(x) a) = tr(rho x a), for every a in A, holds exactly when E preserves adjoints. Conjugating the left module law then gives the right module law.

For a positive input, bimodularity and state preservation make all internal compressions of its image nonnegative under the faithful state. The preceding positivity test therefore makes the image positive. At every finite matrix amplification the block algebra M_k(A), the entrywise map id tensor E, and the faithful density I_k tensor rho satisfy the same identities. This density evaluates a matrix as the sum of its diagonal-block states; for nonzero k, division by k gives the normalized amplified state and preserves the sign test. The empty amplification is included. Thus every actual PSD input has a PSD image.

The resulting expectation is unital, completely positive, idempotent, state preserving and an A-bimodule map, with image exactly A. Conversely, its bimodule and state identities recover the original right ordered comparison. The equivalence concerns these three conditions; no modular-flow or block classification is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OrderedGNSProjection.ordered_gns_characterization`
- Truth anchor: `D5/S3/Quantum/Algebra/OrderedGNSProjection.positive_of_internal_compressions`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
