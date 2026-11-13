# FixedPointProjection

## Abstract

Faithful fixed projections and their transport.

**Theorem 1.1 (traceLocalLeft).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( rho : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , ( kroneckerMap ( \cdot * \cdot ) X ( 1 : Matrix b b \mathbb{C} ) * rho ) . trace = ( X * partialTraceRight rho ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.traceLocalLeft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint trace of a left local observable equals its pairing with the right partial trace.

**Theorem 1.2 (traceLocalRight).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( rho : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , \forall ( Y : Matrix b b \mathbb{C} ) , ( kroneckerMap ( \cdot * \cdot ) ( 1 : Matrix a a \mathbb{C} ) Y * rho ) . trace = ( Y * partialTraceLeft rho ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.traceLocalRight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint trace of a right local observable equals its pairing with the left partial trace.

**Theorem 1.3 (localTrace).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( rho : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , ( ( Matrix . conjTranspose ( ( kroneckerMap ( \cdot * \cdot ) X ( 1 : Matrix b b \mathbb{C} ) ) ) ) * rho * kroneckerMap ( \cdot * \cdot ) X ( 1 : Matrix b b \mathbb{C} ) ) . trace = ( ( Matrix . conjTranspose ( X ) ) * partialTraceRight rho * X ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.localTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An observable acting on the left subsystem has the same quadratic moment in the joint state and in its marginal.

**Theorem 1.4 (fromBipartiteTrace).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( J : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , ( ( \lambda ( Z : Matrix a a \mathbb{C} ) \mapsto \lambda k l \mapsto \sum_{i : a} \sum_{j : a} Z i j * J ( i , k ) ( j , l ) ) X ) . trace = ( ( Matrix . transpose ( ( partialTraceRight J ) ) ) * X ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.fromBipartiteTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate Choi map pairs an input with the transposed left marginal.

**Theorem 1.5 (fromBipartitePairing).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( J : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , \forall ( Y : Matrix b b \mathbb{C} ) , ( ( \lambda ( Z : Matrix a a \mathbb{C} ) \mapsto \lambda k l \mapsto \sum_{i : a} \sum_{j : a} Z i j * J ( i , k ) ( j , l ) ) X * Y ) . trace = ( kroneckerMap ( \cdot * \cdot ) ( Matrix . transpose ( X ) ) Y * J ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.fromBipartitePairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Choi-map pairing equals the joint trace with a transposed left observable.

**Theorem 1.6 (fromBipartiteOne).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( J : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , ( \lambda ( Z : Matrix a a \mathbb{C} ) \mapsto \lambda k l \mapsto \sum_{i : a} \sum_{j : a} Z i j * J ( i , k ) ( j , l ) ) 1 = partialTraceLeft J$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.fromBipartiteOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Choi map sends the identity to the right marginal.

**Theorem 1.7 (normalizedBipartiteChannel).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( J : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , ( J . PosSemidef ) \to \forall ( S : Matrix a a \mathbb{C} ) , ( S . IsHermitian ) \to ( S * ( Matrix . transpose ( ( partialTraceRight J ) ) ) * S = 1 ) \to \exists E : QuantumChannel a b , ( \forall X : Matrix a a \mathbb{C} , CStarMatrix . ofMatrix . symm ( E . toCompletelyPositiveMap ( CStarMatrix . ofMatrix X ) ) = ( \lambda ( Z : Matrix a a \mathbb{C} ) \mapsto \lambda k l \mapsto \sum_{i : a} \sum_{j : a} Z i j * J ( i , k ) ( j , l ) ) ( S * X * S ) ) \land CStarMatrix . ofMatrix . symm ( E . toCompletelyPositiveMap ( CStarMatrix . ofMatrix ( Matrix . transpose ( ( partialTraceRight J ) ) ) ) ) = partialTraceLeft J$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.normalizedBipartiteChannel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hermitian normalization of a positive Choi matrix defines a trace-preserving quantum channel with the displayed marginal image.

**Theorem 1.8 (faithfulTraceZero).**

$$\forall ( n : Type ) , [ Fintype n ] [ DecidableEq n ] \forall ( sigma : Matrix n n \mathbb{C} ) , \forall ( D : Matrix n n \mathbb{C} ) , ( sigma . PosDef ) \to ( D . PosSemidef ) \to ( ( sigma * D ) . trace = 0 ) \to D = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.faithfulTraceZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive matrix with zero pairing against a positive definite matrix vanishes.

**Theorem 1.9 (rawStar).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( r : Type ) , [ Fintype a ] [ Fintype b ] [ Fintype r ] \forall ( K : r \to Matrix b a \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , ( Matrix . conjTranspose ( ( \sum_{i} K i * X * ( Matrix . conjTranspose ( ( K i ) ) ) ) ) ) = \sum_{i} K i * ( Matrix . conjTranspose ( X ) ) * ( Matrix . conjTranspose ( ( K i ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.rawStar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite Kraus sum commutes with conjugate transpose.

**Theorem 1.10 (rawPair).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( r : Type ) , [ Fintype a ] [ Fintype b ] [ Fintype r ] \forall ( K : r \to Matrix b a \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , \forall ( Y : Matrix b b \mathbb{C} ) , ( ( \sum_{i} K i * X * ( Matrix . conjTranspose ( ( K i ) ) ) ) * Y ) . trace = ( X * \sum_{i} ( Matrix . conjTranspose ( ( K i ) ) ) * Y * K i ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.rawPair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking conjugate transposes of the Kraus matrices gives the adjoint map for the trace pairing.

**Theorem 1.11 (channelCommutingFixedProjection).**

$$\forall ( n : Type ) , [ Fintype n ] [ DecidableEq n ] \forall ( T : QuantumChannel n n ) , \forall ( sigma : Matrix n n \mathbb{C} ) , ( sigma . PosDef ) \to ( ( \lambda ( Phi : CompletelyPositiveMap ( CStarMatrix n n \mathbb{C} ) ( CStarMatrix n n \mathbb{C} ) ) \mapsto CStarMatrix . ofMatrix_{l} . symm . conj Phi . toLinearMap ) T . toCompletelyPositiveMap sigma = sigma ) \to ( 1 < Module . finrank \mathbb{C} ( ( \lambda ( Phi : CompletelyPositiveMap ( CStarMatrix n n \mathbb{C} ) ( CStarMatrix n n \mathbb{C} ) ) \mapsto CStarMatrix . ofMatrix_{l} . symm . conj Phi . toLinearMap ) T . toCompletelyPositiveMap ) . fixedSubmodule ) \to \exists P : Matrix n n \mathbb{C} , P . IsHermitian \land P * P = P \land P \neq 0 \land P \neq 1 \land Commute sigma P \land \forall X : Matrix n n \mathbb{C} , ( P * ( \lambda ( Phi : CompletelyPositiveMap ( CStarMatrix n n \mathbb{C} ) ( CStarMatrix n n \mathbb{C} ) ) \mapsto CStarMatrix . ofMatrix_{l} . symm . conj Phi . toLinearMap ) T . toCompletelyPositiveMap X ) . trace = ( P * X ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.channelCommutingFixedProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A channel preserving a faithful matrix and having fixed-space dimension greater than one admits a nontrivial projection commuting with that matrix and preserving the displayed trace pairings.

**Theorem 1.12 (projectionOfImageProjection).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( Psi : Matrix b b \mathbb{C} \to_{l}[ \mathbb{C} ] Matrix a a \mathbb{C} ) , \forall ( sigma : Matrix a a \mathbb{C} ) , \forall ( tau : Matrix b b \mathbb{C} ) , ( tau . PosDef ) \to ( \forall D : Matrix b b \mathbb{C} , 0 \le D \to 0 \le Psi D ) \to ( \forall D : Matrix b b \mathbb{C} , ( sigma * Psi D ) . trace = ( tau * D ) . trace ) \to ( \forall D : Matrix b b \mathbb{C} , ( Matrix . conjTranspose ( ( Psi D ) ) ) * Psi D \le Psi ( ( Matrix . conjTranspose ( D ) ) * D ) ) \to \forall ( P : Matrix a a \mathbb{C} ) , ( P . IsHermitian ) \to ( P * P = P ) \to \forall ( Q : Matrix b b \mathbb{C} ) , ( 0 \le Q ) \to ( Q \le 1 ) \to ( Psi Q = P ) \to Q . IsHermitian \land Q * Q = Q$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedPointProjection.projectionOfImageProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under positivity, the Schwarz inequality and faithful trace duality, an effect whose image is a projection is itself a projection.

## References

- Truth anchor: `D5/S3/Quantum/FixedPointProjection.channelCommutingFixedProjection`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.faithfulTraceZero`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.fromBipartiteOne`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.fromBipartitePairing`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.fromBipartiteTrace`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.localTrace`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.normalizedBipartiteChannel`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.projectionOfImageProjection`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.rawPair`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.rawStar`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.traceLocalLeft`
- Truth anchor: `D5/S3/Quantum/FixedPointProjection.traceLocalRight`
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](Entanglement/LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/HedgingMajorityThreshold](Information/HedgingMajorityThreshold.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/ActualChannelAlgebra](Recovery/ActualChannelAlgebra.md)
