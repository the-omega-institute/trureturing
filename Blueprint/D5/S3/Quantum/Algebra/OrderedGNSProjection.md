# Ordered GNS Projections

## Abstract

Faithful matrix states detect positivity through internal compressions of a star-subalgebra.

**Theorem 1.1 (Internal compressions detect positivity).**

$$\forall (n: Type*), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], \operatorname{let} M: Type* := \operatorname{Matrix}\left(n, n, \mathbb{C}\right); (\forall (rho: M), (\forall (hrho: \operatorname{PosDef}\left(rho\right)), (\forall (A: \operatorname{StarSubalgebra}\left(\mathbb{C}, M\right)), (\forall (y: M), ((\operatorname{IsHermitian}\left(y\right)) \Rightarrow ((y \in A) \Rightarrow ((\forall (q: M), ((q \in A) \Rightarrow (0\leq\Re\operatorname{state}\left(rho, q^{*}yq\right)))) \Rightarrow (\operatorname{PosSemidef}\left(y\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OrderedGNSProjection.positive_of_internal_compressions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an arbitrary positive definite complex matrix rho and a unital star-subalgebra A. A Hermitian matrix y in A is positive semidefinite if every compression q-star y q, with q in A, has nonnegative real rho-weighted trace.

Continuous functional calculus keeps the square root of the negative part of y in A. Its compression is the negative of the square of that negative part. Faithfulness of the weighted matrix inner product forces the negative part to vanish.

**Theorem 1.2 (Ordered comparisons and complete positivity).**

$$\forall (n: Type*), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], \operatorname{let} M: Type* := \operatorname{Matrix}\left(n, n, \mathbb{C}\right); (\forall (rho: M), (\forall (hrho: \operatorname{PosDef}\left(rho\right)), (\forall (htrace: \operatorname{trace}\left(rho\right) = 1), (\forall (A: \operatorname{StarSubalgebra}\left(\mathbb{C}, M\right)), (\operatorname{let} E: \operatorname{LinearMap}\left(\mathbb{C}, M, M\right) := \operatorname{projection}\left(rho, hrho, A\right); ((\operatorname{state}\left(rho, 1\right) = 1) \land ((\forall (x: M), (E\left(x\right) \in A)) \land ((\forall (x: M), (\forall (a: M), ((a \in A) \Rightarrow (\operatorname{state}\left(rho, a^{*}E\left(x\right)\right) = \operatorname{state}\left(rho, a^{*}x\right))))) \land ((\forall (x: M), (\forall (y: M), ((y \in A) \Rightarrow ((\forall (a: M), ((a \in A) \Rightarrow (\operatorname{state}\left(rho, a^{*}y\right) = \operatorname{state}\left(rho, a^{*}x\right)))) \Rightarrow (y = E\left(x\right)))))) \land (((\forall (x: M), (\forall (a: M), ((a \in A) \Rightarrow (\operatorname{state}\left(rho, E\left(x\right)a\right) = \operatorname{state}\left(rho, xa\right))))) \Leftrightarrow (\forall (x: M), (E\left(x^{*}\right) = E\left(x\right)^{*}))) \land ((\forall (x: M), (\forall (a: M), ((a \in A) \Rightarrow (\operatorname{state}\left(rho, E\left(x\right)a\right) = \operatorname{state}\left(rho, xa\right))))) \Leftrightarrow ((E\left(1\right) = 1) \land ((\operatorname{IsCompletelyPositive}\left(E\right)) \land (((\operatorname{IsPositive}\left(E\right)) \land (\forall (k: \mathbb{N}), (\operatorname{let} Ek: \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right) \times n), (\operatorname{Fin}\left(k\right) \times n), \mathbb{C}\right), \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right) \times n), (\operatorname{Fin}\left(k\right) \times n), \mathbb{C}\right)\right) := \operatorname{kron}\left((id: \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right)\right)), E\right); ((\operatorname{IsPositive}\left(Ek\right)) \land ((Ek\left(1\right) = 1) \land (\forall (X: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right) \times n), (\operatorname{Fin}\left(k\right) \times n), \mathbb{C}\right)), (\operatorname{state}\left(\operatorname{amplifiedDensity}\left(\operatorname{Fin}\left(k\right), rho\right), Ek\left(X\right)\right) = \operatorname{state}\left(\operatorname{amplifiedDensity}\left(\operatorname{Fin}\left(k\right), rho\right), X\right)))))))) \land ((\forall (x: M), (E\left(E\left(x\right)\right) = E\left(x\right))) \land ((\operatorname{range}\left(E\right) = \operatorname{carrier}\left(A\right)) \land ((\forall (x: M), (\operatorname{state}\left(rho, E\left(x\right)\right) = \operatorname{state}\left(rho, x\right))) \land (\forall (a: M), ((a \in A) \Rightarrow (\forall (b: M), ((b \in A) \Rightarrow (\forall (x: M), (E\left(axb\right) = aE\left(x\right)b))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OrderedGNSProjection.ordered_gns_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be any positive definite complex matrix of trace one, and let A be any unital star-subalgebra on the same finite carrier. The map E is the unique orthogonal projection onto A for the inner product tr(rho x-star y). Its left ordered comparisons determine E without any positivity assumption.

Retraction, preservation of the unit and state, and the left module law follow from that orthogonal projection. The additional complex identity tr(rho E(x) a) = tr(rho x a), for every a in A, holds exactly when E preserves adjoints. Conjugating the left module law then gives the right module law.

For a positive input, bimodularity and state preservation make all internal compressions of its image nonnegative under the faithful state. The preceding positivity test therefore makes the image positive. At every finite matrix amplification the block algebra M_k(A), the entrywise map id tensor E, and the faithful density I_k tensor rho satisfy the same identities. This density evaluates a matrix as the sum of its diagonal-block states; for nonzero k, division by k gives the normalized amplified state and preserves the sign test. The empty amplification is included. Thus every actual PSD input has a PSD image.

The resulting expectation is unital, completely positive, idempotent, state preserving and an A-bimodule map, with image exactly A. Conversely, its bimodule and state identities recover the original right ordered comparison. The equivalence concerns these three conditions; no modular-flow or block classification is asserted.

In the display, M is the full complex matrix algebra on n, state(rho,x) is tr(rho*x), and E is defined to be projection(rho,hrho,A), the actual weighted orthogonal projection. The final parenthesized condition expands exactly Expectation(rho,A,E). IsPositive, IsCompletelyPositive and kron are the PhyslibLeaf.MatrixMap predicates and tensor map. The identity in Ek is the complex-linear identity on matrices indexed by Fin k. The density amplifiedDensity(Fin k,rho) is k-inverse times (I_k tensor rho), using the real scalar inverse, including k=0. Every matrix variable and both ordered comparisons retain their full complex values.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OrderedGNSProjection.ordered_gns_characterization`
- Truth anchor: `D5/S3/Quantum/Algebra/OrderedGNSProjection.positive_of_internal_compressions`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
