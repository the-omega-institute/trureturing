# Finite Reference Channel Distance

## Abstract

Finite reference amplification and unhalved stabilized distance for canonical quantum channels.

All coordinate types are finite and have decidable equality. The reference coordinate is the first factor of each product. QuantumChannel and DensityState are the canonical completely positive, trace-preserving channel and positive trace-one state types. raw converts a state value or a CStarMatrix to its ordinary matrix coordinates. block(X,i,j) is the input matrix with entries X((i,u),(j,w)); channelMatrixAction applies the channel to that matrix. entry evaluates a matrix at two coordinates.

**Definition 1.1 (Reference-amplified linear map).**

$$\forall r \in FiniteType, a \in FiniteType, b \in FiniteType, c \in \operatorname{QuantumChannel}\left(a, b\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Product}\left(r, a\right), \operatorname{Product}\left(r, a\right), \mathbb{C}\right), i \in r, j \in r, u \in b, w \in b,\; \operatorname{entry}\left(\operatorname{referenceLinear}\left(c, X\right), \operatorname{pair}\left(i, u\right), \operatorname{pair}\left(j, w\right)\right) = \operatorname{entry}\left(\operatorname{channelMatrixAction}\left(c, \operatorname{block}\left(X, i, j\right)\right), u, w\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each reference block is transformed by the same channel linear map.

**Definition 1.2 (Reference-amplified action).**

$$\forall r \in FiniteType, a \in FiniteType, b \in FiniteType, c \in \operatorname{QuantumChannel}\left(a, b\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Product}\left(r, a\right), \operatorname{Product}\left(r, a\right), \mathbb{C}\right),\; \operatorname{referenceAction}\left(c, X\right) = \operatorname{referenceLinear}\left(c, X\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This evaluates the reference-amplified linear map on a joint matrix.

**Definition 1.3 (Amplified density state).**

$$\forall r \in FiniteType, a \in FiniteType, b \in FiniteType, c \in \operatorname{QuantumChannel}\left(a, b\right),\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Product}\left(r, a\right)\right),\; \operatorname{raw}\left(\operatorname{referenceState}\left(c, rho\right)\right) = \operatorname{raw}\left(\operatorname{referenceAction}\left(c, \operatorname{value}\left(rho\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complete positivity preserves the joint matrix order, and trace preservation preserves the sum of the diagonal reference-block traces.

**Definition 1.4 (Unhalved error at a joint input).**

$$\forall r \in FiniteType, a \in FiniteType, b \in FiniteType, c \in \operatorname{QuantumChannel}\left(a, b\right),\; \forall d \in \operatorname{QuantumChannel}\left(a, b\right), rho \in \operatorname{DensityState}\left(\operatorname{Product}\left(r, a\right)\right),\; \operatorname{referenceError}\left(c, d, rho\right) = \operatorname{traceNorm}\left(\operatorname{raw}\left(\operatorname{referenceState}\left(c, rho\right)\right) - \operatorname{raw}\left(\operatorname{referenceState}\left(d, rho\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state difference is measured by its trace norm without the conventional division by two.

**Definition 1.5 (Pure density state).**

$$\forall q \in FiniteType, rho \in \operatorname{DensityState}\left(q\right),\; \operatorname{IsPure}\left(rho\right) \Leftrightarrow \left(\exists v \in \operatorname{Function}\left(q, \mathbb{C}\right),\; \operatorname{raw}\left(rho\right) = \operatorname{vecMulVec}\left(v, \operatorname{star}\left(v\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDiamondDistance.IsPure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pure state is represented by one vector outer product.

**Definition 1.6 (State of a unit vector).**

$$\forall q \in FiniteType, v \in \operatorname{Function}\left(q, \mathbb{C}\right),\; \operatorname{dotProduct}\left(\operatorname{star}\left(v\right), v\right) = 1 \Rightarrow \operatorname{raw}\left(\operatorname{pureState}\left(v\right)\right) = \operatorname{vecMulVec}\left(v, \operatorname{star}\left(v\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDiamondDistance.pureState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector outer product is positive, and its trace is the squared vector norm.

finiteReferenceErrors(c,d) consists of zero and every referenceError(c,d,rho) with a natural number n and rho a DensityState on Fin(n) times a. The unhalved stabilized distance is the real supremum of this set. The zero element includes empty input types, which have no density state.

**Definition 1.7 (Unhalved stabilized distance).**

$$\forall a \in FiniteType, b \in FiniteType, c \in \operatorname{QuantumChannel}\left(a, b\right), d \in \operatorname{QuantumChannel}\left(a, b\right),\; \operatorname{diamondDistance}\left(c, d\right) = \operatorname{sSup}\left(\operatorname{finiteReferenceErrors}\left(c, d\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDiamondDistance.diamondDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every natural-number reference dimension participates in the supremum.

pureFixedReferenceErrors(c,d) consists of zero and every referenceError(c,d,tau) for a pure DensityState tau on Fin(card(a)) times a. Reference and input types may inhabit independent universes. Each joint density state is dominated in error by a pure state on the same reference, and by a pure state with reference dimension card(a). No nonempty-type assumption is needed.

**Theorem 1.8 (Pure inputs and a fixed reference dimension).**

$$\forall a \in FiniteType, b \in FiniteType, c \in \operatorname{QuantumChannel}\left(a, b\right), d \in \operatorname{QuantumChannel}\left(a, b\right),\; \left(\forall r \in FiniteType, rho \in \operatorname{DensityState}\left(\operatorname{Product}\left(r, a\right)\right),\; \exists tau \in \operatorname{DensityState}\left(\operatorname{Product}\left(r, a\right)\right),\; \operatorname{IsPure}\left(tau\right) \land \operatorname{referenceError}\left(c, d, rho\right) \le \operatorname{referenceError}\left(c, d, tau\right)\right) \land \left(\left(\forall r \in FiniteType, rho \in \operatorname{DensityState}\left(\operatorname{Product}\left(r, a\right)\right),\; \exists tau \in \operatorname{DensityState}\left(\operatorname{Product}\left(\operatorname{Fin}\left(\operatorname{card}\left(a\right)\right), a\right)\right),\; \operatorname{IsPure}\left(tau\right) \land \operatorname{referenceError}\left(c, d, rho\right) \le \operatorname{referenceError}\left(c, d, tau\right)\right) \land \operatorname{diamondDistance}\left(c, d\right) = \operatorname{sSup}\left(\operatorname{pureFixedReferenceErrors}\left(c, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteDiamondDistance.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A spectral decomposition reduces mixed inputs to pure inputs. Factorization of the pure-state coefficient matrix compresses the reference to at most the input dimension. Reference isometries preserve the channel error, so the stabilized supremum equals the pure-state supremum at that fixed dimension.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.IsPure`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.diamondDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.pureState`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceAction`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceError`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceLinear`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.referenceState`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDiamondDistance.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](FiniteTraceDistance.md)
