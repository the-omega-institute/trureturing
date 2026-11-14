# The arithmetic and geometric endpoints

## Abstract

Geometric maximal correlation one forces arithmetic maximal correlation one.

**Theorem 1.1 (gramContractionOfPositiveSimilarity).**

$$\forall ( E : Type ) , \forall ( F : Type ) , \forall ( A : Type ) , [ NormedAddCommGroup E ] [ InnerProductSpace \mathbb{C} E ] [ FiniteDimensional \mathbb{C} E ] [ NormedAddCommGroup F ] [ InnerProductSpace \mathbb{C} F ] [ CompleteSpace F ] [ CStarAlgebra A ] [ PartialOrder A ] [ StarOrderedRing A ] [ NonnegSpectrumClass \mathbb{R} A ] [ Nontrivial A ] [ NormOneClass A ] \forall ( C : E \to_{L}[ \mathbb{C} ] F ) , \forall ( U : A \to_{l}[ \mathbb{C} ] A ) , ( \forall X , 0 \le X \to 0 \le U X ) \to \forall ( sigma : A ) , ( IsStrictlyPositive sigma ) \to ( U sigma = sigma ) \to \forall ( e : E \equiv_{l}[ \mathbb{C} ] A ) , ( \forall x : E , U ( e x ) = e ( C . adjoint ( C x ) ) ) \to \Vert C \Vert \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.gramContractionOfPositiveSimilarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive map with a strictly positive fixed element controls the norm of a Hilbert-space map whose Gram operator is similar to it.

**Definition 1.2 (centeredUnit).**

$$\forall ( E : Type ) , [ NormedAddCommGroup E ] [ InnerProductSpace \mathbb{C} E ] \forall ( e : E ) , centeredUnit e = \{ x | \Vert x \Vert = 1 \land inner \mathbb{C} e x = 0 \}$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.centeredUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered unit sphere consists of unit vectors orthogonal to the specified vector.

**Definition 1.3 (centeredCorrelationValues).**

$$\forall ( E : Type ) , \forall ( F : Type ) , [ NormedAddCommGroup E ] [ InnerProductSpace \mathbb{C} E ] [ NormedAddCommGroup F ] [ InnerProductSpace \mathbb{C} F ] \forall ( C : E \to_{L}[ \mathbb{C} ] F ) , \forall ( e : E ) , \forall ( f : F ) , centeredCorrelationValues C e f = Set . image ( \lambda p : E \times F \mapsto \Vert inner \mathbb{C} ( C p . 1 ) p . 2 \Vert ) ( Set . prod ( centeredUnit e ) ( centeredUnit f ) )$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.centeredCorrelationValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered correlation values are absolute inner products of images and vectors from the two centered unit spheres.

**Theorem 1.4 (fixedDimensionOfCenteredCorrelation).**

$$\forall ( E : Type ) , \forall ( F : Type ) , \forall ( V : Type ) , [ NormedAddCommGroup E ] [ InnerProductSpace \mathbb{C} E ] [ NormedAddCommGroup F ] [ InnerProductSpace \mathbb{C} F ] [ FiniteDimensional \mathbb{C} E ] [ FiniteDimensional \mathbb{C} F ] [ AddCommGroup V ] [ Module \mathbb{C} V ] [ FiniteDimensional \mathbb{C} V ] [ CompleteSpace E ] [ CompleteSpace F ] \forall ( C : E \to_{L}[ \mathbb{C} ] F ) , ( \Vert C \Vert \le 1 ) \to \forall ( v : E ) , \forall ( f : F ) , ( v \neq 0 ) \to \forall ( U : V \to_{l}[ \mathbb{C} ] V ) , \forall ( e : E \equiv_{l}[ \mathbb{C} ] V ) , ( \forall x : E , U ( e x ) = e ( C . adjoint ( C x ) ) ) \to ( U ( e v ) = e v ) \to \forall ( S : Set \mathbb{R} ) , ( S \subseteq centeredCorrelationValues C v f ) \to ( sSup S = 1 ) \to 1 < Module . finrank \mathbb{C} U . fixedSubmodule$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.fixedDimensionOfCenteredCorrelation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Centered correlation supremum one supplies a fixed vector independent of the specified nonzero fixed vector, so the fixed submodule has dimension greater than one.

**Theorem 1.5 (pullPush).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( X : Matrix c c \mathbb{C} ) , ( ( Matrix . conjTranspose ( ( U ) ) ) * ( ( ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) ) * ( U ) ) = X$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullPush` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compression reverses an isometric matrix embedding.

**Theorem 1.6 (pushMul).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( X : Matrix c c \mathbb{C} ) , \forall ( Y : Matrix c c \mathbb{C} ) , ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) * ( ( U ) * ( Y ) * ( Matrix . conjTranspose ( ( U ) ) ) ) = ( ( U ) * ( ( X * Y ) ) * ( Matrix . conjTranspose ( ( U ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushMul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by an isometry preserves multiplication.

**Theorem 1.7 (pushHermitian).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( X : Matrix c c \mathbb{C} ) , ( X . IsHermitian ) \to ( ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) . IsHermitian$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Isometric embedding preserves Hermitian matrices.

**Theorem 1.8 (pullHermitian).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , ( X . IsHermitian ) \to ( ( ( Matrix . conjTranspose ( ( U ) ) ) * ( X ) * ( U ) ) ) . IsHermitian$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compression preserves Hermitian matrices.

**Theorem 1.9 (pushTrace).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( X : Matrix c c \mathbb{C} ) , ( ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) . trace = X . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Isometric embedding preserves the trace.

**Theorem 1.10 (tracePair).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( S : Matrix c c \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , ( ( ( U ) * ( S ) * ( Matrix . conjTranspose ( ( U ) ) ) ) * X ) . trace = ( S * ( ( Matrix . conjTranspose ( ( U ) ) ) * ( X ) * ( U ) ) ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tracePair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedding and compression maps are adjoint for the trace pairing.

**Theorem 1.11 (gmPairCompress).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( S : Matrix c c \mathbb{C} ) , ( S . PosSemidef ) \to \forall ( X : Matrix a a \mathbb{C} ) , ( X . IsHermitian ) \to ( ( Matrix . conjTranspose ( X ) ) * ( CFC . sqrt ( ( ( ( U ) * ( S ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) ) * ( X ) * CFC . sqrt ( ( ( ( U ) * ( S ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) ) ) ) . trace = ( ( Matrix . conjTranspose ( ( ( ( Matrix . conjTranspose ( ( U ) ) ) * ( X ) * ( U ) ) ) ) ) * ( CFC . sqrt ( S ) * ( ( ( ( Matrix . conjTranspose ( ( U ) ) ) * ( X ) * ( U ) ) ) ) * CFC . sqrt ( S ) ) ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.gmPairCompress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric quadratic moment in an embedded positive matrix equals the quadratic moment of the compressed observable.

**Definition 1.12 (FaithfulFrame).**

$$\forall ( a : Type ) , [ Fintype a ] structure FaithfulFrame ( S : Matrix a a \mathbb{C} ) where \langle iota : Type ; [ Fintype iota ] ; [ DecidableEq iota ] ; U : Matrix a iota \mathbb{C} ; small : Matrix iota iota \mathbb{C} ; iso : ( Matrix . conjTranspose ( U ) ) * U = 1 ; positive : small . PosDef ; reconstruct : U * small * ( Matrix . conjTranspose ( U ) ) = S \rangle$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.FaithfulFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A faithful support frame records a finite support space, an isometry and a positive definite matrix reconstructing the original matrix.

**Theorem 1.13 (existsFaithfulFrame).**

$$\forall ( a : Type ) , [ Fintype a ] [ DecidableEq a ] \forall ( S : Matrix a a \mathbb{C} ) , ( S . PosSemidef ) \to Nonempty ( FaithfulFrame S )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.existsFaithfulFrame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting the spectral decomposition to positive eigenvalues constructs a faithful support frame for every positive semidefinite matrix.

**Theorem 1.14 (tensorIso).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to ( ( Matrix . conjTranspose ( V ) ) * V = 1 ) \to ( Matrix . conjTranspose ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) * ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tensorIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Kronecker product of two isometries is an isometry.

**Theorem 1.15 (pullTensor).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , \forall ( Y : Matrix b b \mathbb{C} ) , ( ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) * ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( X ) ( Y ) ) ) ) * ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) = ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( ( ( Matrix . conjTranspose ( ( U ) ) ) * ( X ) * ( U ) ) ) ( ( ( Matrix . conjTranspose ( ( V ) ) ) * ( Y ) * ( V ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullTensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compression by a product isometry acts separately on tensor factors.

**Theorem 1.16 (marginalAPush).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , ( ( Matrix . conjTranspose ( V ) ) * V = 1 ) \to \forall ( rho : Matrix ( c \times d ) ( c \times d ) \mathbb{C} ) , partialTraceRight ( ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) * ( rho ) * ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) ) ) = ( ( U ) * ( ( partialTraceRight rho ) ) * ( Matrix . conjTranspose ( ( U ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalAPush` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding the joint matrix by two local isometries embeds its left marginal by the left isometry.

**Theorem 1.17 (marginalBPush).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( rho : Matrix ( c \times d ) ( c \times d ) \mathbb{C} ) , partialTraceLeft ( ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) * ( rho ) * ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) ) ) = ( ( V ) * ( ( partialTraceLeft rho ) ) * ( Matrix . conjTranspose ( ( V ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalBPush` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding the joint matrix by two local isometries embeds its right marginal by the right isometry.

**Theorem 1.18 (jointSupportFrame).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( rho : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , ( rho . PosSemidef ) \to \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to ( ( Matrix . conjTranspose ( V ) ) * V = 1 ) \to \forall ( S : Matrix c c \mathbb{C} ) , \forall ( T : Matrix d d \mathbb{C} ) , ( partialTraceRight rho = ( ( U ) * ( S ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) \to ( partialTraceLeft rho = ( ( V ) * ( T ) * ( Matrix . conjTranspose ( ( V ) ) ) ) ) \to ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) * ( ( ( ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) * ( rho ) * ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) ) * ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) ) = rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.jointSupportFrame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive joint matrix is supported on the product of the two marginal support spaces.

**Theorem 1.19 (amCorrelationLeOne).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( rho : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , ( rho . PosSemidef ) \to \forall ( X : Matrix a a \mathbb{C} ) , \forall ( Y : Matrix b b \mathbb{C} ) , ( X . IsHermitian ) \to ( Y . IsHermitian ) \to ( ( ( Matrix . conjTranspose ( X ) ) * ( ( 1 / 2 : \mathbb{C} ) \cdot ( ( ( partialTraceRight rho ) ) * ( X ) + ( X ) * ( ( partialTraceRight rho ) ) ) ) ) . trace = 1 ) \to ( ( ( Matrix . conjTranspose ( Y ) ) * ( ( 1 / 2 : \mathbb{C} ) \cdot ( ( ( partialTraceLeft rho ) ) * ( Y ) + ( Y ) * ( ( partialTraceLeft rho ) ) ) ) ) . trace = 1 ) \to \Vert ( kroneckerMap ( \cdot * \cdot ) X ( Matrix . conjTranspose ( Y ) ) * rho ) . trace \Vert \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.amCorrelationLeOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state Cauchy–Schwarz inequality bounds the correlation of Hermitian observables with unit arithmetic quadratic moments by one.

**Theorem 1.20 (projectionProbability).**

$$\forall ( n : Type ) , [ Fintype n ] [ DecidableEq n ] \forall ( sigma : Matrix n n \mathbb{C} ) , \forall ( P : Matrix n n \mathbb{C} ) , ( sigma . PosDef ) \to ( sigma . trace = 1 ) \to ( P . IsHermitian ) \to ( P * P = P ) \to ( P \neq 0 ) \to ( P \neq 1 ) \to \exists p : \mathbb{R} , 0 < p \land p < 1 \land ( sigma * P ) . trace = ( p : \mathbb{C} )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.projectionProbability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nontrivial Hermitian projection has probability strictly between zero and one in a faithful trace-one matrix.

**Definition 1.21 (binaryObservable).**

$$\forall ( n : Type ) , [ DecidableEq n ] \forall ( P : Matrix n n \mathbb{C} ) , \forall ( p : \mathbb{R} ) , binaryObservable P p = ( ( Inv . inv ( ( Real . sqrt ( p * ( 1 - p ) ) : \mathbb{C} ) ) ) ) \cdot ( P - ( p : \mathbb{C} ) \cdot 1 )$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary observable centers a projection at probability p and divides by the standard deviation sqrt(p(1-p)).

**Theorem 1.22 (binaryObservableHermitian).**

$$\forall ( n : Type ) , [ Fintype n ] [ DecidableEq n ] \forall ( P : Matrix n n \mathbb{C} ) , ( P . IsHermitian ) \to \forall ( p : \mathbb{R} ) , ( binaryObservable P p ) . IsHermitian$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservableHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Centering and rescaling a Hermitian projection gives a Hermitian observable.

**Theorem 1.23 (binaryObservableCentered).**

$$\forall ( n : Type ) , [ Fintype n ] [ DecidableEq n ] \forall ( sigma : Matrix n n \mathbb{C} ) , \forall ( P : Matrix n n \mathbb{C} ) , \forall ( p : \mathbb{R} ) , ( sigma . trace = 1 ) \to ( ( sigma * P ) . trace = ( p : \mathbb{C} ) ) \to ( sigma * binaryObservable P p ) . trace = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservableCentered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binary observable has zero expectation when p is the projection probability.

**Theorem 1.24 (binaryObservableAmUnit).**

$$\forall ( n : Type ) , [ Fintype n ] [ DecidableEq n ] \forall ( sigma : Matrix n n \mathbb{C} ) , \forall ( P : Matrix n n \mathbb{C} ) , ( P . IsHermitian ) \to \forall ( p : \mathbb{R} ) , ( 0 < p ) \to ( p < 1 ) \to ( sigma . trace = 1 ) \to ( ( sigma * P ) . trace = ( p : \mathbb{C} ) ) \to ( P * P = P ) \to ( ( Matrix . conjTranspose ( ( binaryObservable P p ) ) ) * ( ( 1 / 2 : \mathbb{C} ) \cdot ( ( sigma ) * ( ( binaryObservable P p ) ) + ( ( binaryObservable P p ) ) * ( sigma ) ) ) ) . trace = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservableAmUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p strictly between zero and one, the binary observable has unit arithmetic quadratic moment.

**Definition 1.25 (traceCorrelation).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( rho : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , traceCorrelation rho = ( Matrix . kroneckerBilinear ( R : = \mathbb{C} ) ) . compr_{2} ( ( Matrix . traceLinearMap ( a \times b ) \mathbb{C} \mathbb{C} ) . comp ( LinearMap . mulRight \mathbb{C} rho ) )$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.traceCorrelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint trace defines a bilinear pairing of local matrices.

**Theorem 1.26 (sharedBinaryCorrelation).**

$$\forall ( a : Type ) , \forall ( b : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] \forall ( rho : Matrix ( a \times b ) ( a \times b ) \mathbb{C} ) , \forall ( P : Matrix a a \mathbb{C} ) , \forall ( Q : Matrix b b \mathbb{C} ) , \forall ( p : \mathbb{R} ) , ( 0 < p ) \to ( p < 1 ) \to ( traceCorrelation rho P Q = ( p : \mathbb{C} ) ) \to ( traceCorrelation rho P 1 = ( p : \mathbb{C} ) ) \to ( traceCorrelation rho 1 Q = ( p : \mathbb{C} ) ) \to ( traceCorrelation rho 1 1 = 1 ) \to traceCorrelation rho ( binaryObservable P p ) ( binaryObservable Q p ) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.sharedBinaryCorrelation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal marginal and joint projection probabilities produce binary observables with correlation exactly one.

**Definition 1.27 (Feasible Hermitian correlation values).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (J:\forall (c:\operatorname {Type}), ([\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)](\operatorname {Matrix}\left(c, c, \mathbb{C}\right))\to((\operatorname {Matrix}\left(c, c, \mathbb{C}\right))\to(\operatorname {Matrix}\left(c, c, \mathbb{C}\right))))), (\forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {correlationValues}\left(J, rho\right) = \{r:\mathbb{R}\mid\exists (X:\operatorname {Matrix}\left(a, a, \mathbb{C}\right)), (\exists (Y:\operatorname {Matrix}\left(b, b, \mathbb{C}\right)), ((\operatorname {Matrix.IsHermitian}\left(X\right)) \land ((\operatorname {Matrix.IsHermitian}\left(Y\right)) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.of}\left(\lambda i j \mapsto \sum k:b, \operatorname {rho}\left((i,k), (j,k)\right)\right)) \cdot (X)\right) = 0) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.of}\left(\lambda k l \mapsto \sum i:a, \operatorname {rho}\left((i,k), (i,l)\right)\right)) \cdot (Y)\right) = 0) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.conjTranspose}\left(X\right)) \cdot (\operatorname {J}\left(\lambda i j \mapsto \sum k:b, \operatorname {rho}\left((i,k), (j,k)\right), X\right))\right) = 1) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.conjTranspose}\left(Y\right)) \cdot (\operatorname {J}\left(\lambda k l \mapsto \sum i:a, \operatorname {rho}\left((i,k), (i,l)\right), Y\right))\right) = 1) \land (r = \Vert\operatorname {Matrix.trace}\left((\operatorname {Matrix.kroneckerMap}\left(\lambda x y \mapsto (x) \cdot (y), X, \operatorname {Matrix.conjTranspose}\left(Y\right)\right)) \cdot (rho)\right)\Vert))))))))\}))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.correlationValues` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Definition 24, equation (54), page 19: “where the maximization is over X ∈ Herm(A), Y ∈ Herm(B).” The displayed set consists of the feasible absolute traces with zero marginal expectation and unit quadratic norm. The index types are arbitrary finite types; the marginal matrices are the two finite partial sums.

**Definition 1.28 (Arithmetic maximal correlation).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {muAM}\left(rho\right) = \operatorname {sSup}\left(\operatorname {correlationValues}\left(\lambda (c:\operatorname {Type}) [\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)] (sigma Y:\operatorname {Matrix}\left(c, c, \mathbb{C}\right)) \mapsto (\frac{1}{2}:\mathbb{C})\cdot((sigma) \cdot (Y) + (Y) \cdot (sigma)), rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muAM` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

The arithmetic mean gives the linear mean operator X ↦ (sigma X + X sigma)/2. The coefficient is the supremum of the feasible absolute correlations.

**Definition 1.29 (Geometric maximal correlation).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {muGM}\left(rho\right) = \operatorname {sSup}\left(\operatorname {correlationValues}\left(\lambda (c:\operatorname {Type}) [\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)] (sigma Y:\operatorname {Matrix}\left(c, c, \mathbb{C}\right)) \mapsto ((\operatorname {CFC.sqrt}\left(sigma\right)) \cdot (Y)) \cdot (\operatorname {CFC.sqrt}\left(sigma\right)), rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muGM` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

The geometric mean gives X ↦ sqrt(sigma) X sqrt(sigma). The real supremum of an empty feasible set is zero.

**Definition 1.30 (The endpoint proposition).**

$$\operatorname {claim} = \forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), ((\operatorname {Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname {Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\operatorname {muGM}\left(rho\right) = 1) \Rightarrow (\operatorname {muAM}\left(rho\right) = 1))))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.claim` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Section VII, page 66: “Does there exist a quantum state ρ_AB such that µ_AM(A : B)_ρ < 1 and µ_GM(A : B)_ρ = 1?” Here rho is a positive semidefinite trace-one complex matrix on a product of finite index types. The displayed implication answers the question negatively, including states with singular marginals.

**Theorem 1.31 (Coincidence at maximal correlation one).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), ((\operatorname {Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname {Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\operatorname {muGM}\left(rho\right) = 1) \Rightarrow (\operatorname {muAM}\left(rho\right) = 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result` (`✓ std3`). ∎

*Resolves.* `Problems/george-tomamichel-2025-am-gm-maximal-correlation` (proved) by `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"george-tomamichel-2025-am-gm-maximal-correlation","declaration_gid":"D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Compressing to the marginal supports preserves the geometric feasible values. At geometric correlation one, a centered fixed vector gives a nontrivial projection commuting with the marginal state. A partner projection has the same marginal and joint probability p, with 0 < p < 1. Centering both projections and dividing by sqrt(p(1-p)) gives arithmetic correlation one. The arithmetic Cauchy–Schwarz bound supplies the matching upper bound.

## References

- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.FaithfulFrame`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.amCorrelationLeOne`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservable`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservableAmUnit`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservableCentered`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.binaryObservableHermitian`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.centeredCorrelationValues`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.centeredUnit`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.claim`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.correlationValues`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.existsFaithfulFrame`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.fixedDimensionOfCenteredCorrelation`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.gmPairCompress`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.gramContractionOfPositiveSimilarity`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.jointSupportFrame`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalAPush`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalBPush`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muAM`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muGM`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.projectionProbability`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullHermitian`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullPush`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullTensor`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushHermitian`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushMul`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushTrace`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.sharedBinaryCorrelation`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tensorIso`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.traceCorrelation`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tracePair`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](Divergence/SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/FixedPointProjection](FixedPointProjection.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](QuantumChannels/TwoPositiveTransitionTrace.md)
