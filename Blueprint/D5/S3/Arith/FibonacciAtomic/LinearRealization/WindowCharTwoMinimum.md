# Characteristic-Two Joint Hankel Rank of Fibonacci Windows

## Abstract

The integer-induced five-window task has joint Hankel rank and minimum linear dimension four over every characteristic-two field.

Let K be any field of characteristic two. The input alphabet consists of null, [2], [3], [25] and [5], with low-to-high printed bits 000, 100, 010, 101 and 001. Words arrive high to low. The preceding higher window's low bit cannot meet a one in the incoming window's high bit. The unit bit is zero. The task includes the empty word and high-end null padding; an illegal seam is absorbing. It is the task of Theorem 8.4 in FIB Relational Continuation Geometry.

Use the existing integerFieldTask K: first run the immediate integer quantity reader, then apply the canonical integer-to-K map to both outputs. A legal composition (a,b) produces (1,2a+3b), reduced in K; error produces (0,0). Legal zero therefore produces (1,0). All word products use the existing chronological wordMap and WordRepresentation conventions.

**Definition 1.1 (Two seam blocks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.BlockState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.BlockState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state space is K^4 with coordinates (b_0,c_0,b_1,c_1). The homogeneous coordinate c records legality in its seam block.

**Definition 1.2 (Reduced affine transitions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Null and [2] preserve b; [3], [25] and [5] add c to b. Each legal source block is sent to the original seam destination, and forbidden source blocks contribute zero. Contributions are added when the destination is shared. These formulas act on all of K^4.

**Definition 1.3 (Linear letter maps).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each blockUpdate defines a K-linear endomorphism.

**Definition 1.4 (Legality and quantity).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockOutput`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear output is (c_0+c_1,b_0+b_1), retaining both channels.

**Definition 1.5 (The four-dimensional representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.fourDimensional`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.fourDimensional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial vector is (0,1,0,0), letter maps are blockTransition, and the output is blockOutput.

**Definition 1.6 (Integer-state reduction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.embed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.embed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual integer state with seam s and composition (a,b) is placed in block s as (b,1), using the canonical map to K. The other block is zero. Error is the zero vector.

**Definition 1.7 (Output selection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.channel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.channel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Channel zero selects legality and channel one selects quantity through K-linear projections.

**Definition 1.8 (Joint residual responses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.jointResidual`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.jointResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a two-output task f and a prefix u, its joint residual is the single function (v,j) mapping to channel j of f(u++v). Both channels share the same prefix and continuation.

**Definition 1.9 (The joint Hankel row space).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.jointHankelSpace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.jointHankelSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the K-linear span of jointResidual f u over all finite prefixes u inside the function space on all continuation-channel pairs. Its dimension is the joint two-output Hankel rank.

**Definition 1.10 (Future observation of an arbitrary state).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.futureObservation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.futureObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any linear word representation R, map a state x to all scalar observations obtained by continuing x with v and reading channel j. This is a K-linear map into the same continuation-channel function space.

**Definition 1.11 (Four actual histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.prefixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.prefixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The histories are the empty word, [3], [2] and [3][2]. They reach both Boolean quantities in both seams.

**Definition 1.12 (Four joint observations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.tests`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.tests` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read legality and quantity after [5], and then legality and quantity after null[5].

**Definition 1.13 (A joint response minor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.responseMinor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.responseMinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows are the four tests and columns are the four histories. The entry (i,j) is the selected output after history j followed by the continuation in test i. Its rows are (1,1,0,0), (1,0,0,0), (1,1,1,1) and (1,0,1,0), and its determinant is one.

**Theorem 1.14 (Joint rank and attained minimum).**

$$\forall K, (\operatorname{CharTwoField}\left(K\right)) \implies ((\operatorname{Realizes}\left(FK, fK\right)) \land \\(\operatorname{FiniteDimensional}\left(K, JK\right)) \land \\(\operatorname{dim}\left(K, JK\right) = 4) \land \\(\operatorname{dim}\left(K, K4\right) = 4) \land \\(\forall V, \forall R, ((\operatorname{FiniteKSpace}\left(V\right)) \land \\(\operatorname{LinearWordRep}\left(R, V, K\right))) \implies ((\operatorname{Realizes}\left(R, fK\right)) \implies (4 \leq \operatorname{dim}\left(K, V\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, CharTwoField(K) means that K is a field of characteristic two, fK is integerFieldTask K, FK is fourDimensional K, JK is jointHankelSpace K fK, and K4 is BlockState K. Realizes(R,fK) means equality of both outputs on every finite word. The dimension symbols denote dimension over K. FiniteKSpace(V) asserts that V is a finite-dimensional K-vector space. LinearWordRep(R,V,K) includes its initial vector, linear letter operators and linear output to K^2. No finiteness condition on K and no reachability or observability condition on R is imposed.

The integer clock sends (a,b) to (a+2b,2a+3b). In characteristic two its second coordinate is b, and the quantity is b. The embedding therefore commutes with each legal affine update and with every error transition. Induction on chronological words gives the all-word realization, including the empty word and illegal words.

Every joint residual is the future observation of its reached four-dimensional state. Hence the entire residual span lies in the range of one linear map from K^4. This proves finite dimensionality and dimension at most four. Sampling four joint residuals at the four tests gives the determinant-one response matrix, so those residuals are linearly independent and the dimension is exactly four.

For any competing realization, the same four reached vectors map under its future observations and the same sampling map to the four independent response columns. The reached vectors are therefore linearly independent in the competitor's full state space. Its dimension is at least four, and the explicit K^4 realization attains this bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.BlockState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockOutput`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.blockUpdate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.channel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.embed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.fourDimensional`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.futureObservation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.jointHankelSpace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.jointResidual`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.prefixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.responseMinor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.tests`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum](../ParityLiftRationalMinimum.md)
