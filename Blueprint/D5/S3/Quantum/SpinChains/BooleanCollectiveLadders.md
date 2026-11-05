# Complete complex Boolean spin decomposition

## Abstract

Complete complex Boolean decomposition into every native spin block, with derived primitive multiplicities and normalized strings.

The carrier is V(N) = EuclideanSpace(ℂ, Fin(N) → Fin(2)), with its complex Hermitian inner product. Every configuration is retained. A zero bit denotes membership. These are the single-block algebra and spanning prerequisites in TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION, Theorem 6.2, equations (6.6)–(6.8). The classical Boolean representation is cited there to Srinivasan, arXiv:1001.0280v2, and Feinsilver, arXiv:1102.0368v2; no claim of mathematical novelty is made.

**Definition 1.1 (Occupancy).**

$$\forall N \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{occupancy}\left(x\right) = \sum_{i \in \operatorname{Fin}\left(N\right)} \operatorname{ite}\left(x\left(i\right) = 0, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.occupancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every zero bit contributes one occupied coordinate.

**Definition 1.2 (The native collective raising map).**

$$\forall N \in \mathbb{N},\; \operatorname{U}\left(N\right) = \operatorname{toEuclideanLin}\left(\operatorname{totalPlus}\left(N\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the existing unweighted totalPlus matrix acting on Euclidean coordinates.

**Definition 1.3 (The native collective lowering map).**

$$\forall N \in \mathbb{N},\; \operatorname{L}\left(N\right) = \operatorname{toEuclideanLin}\left(\operatorname{totalMinus}\left(N\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the existing unweighted totalMinus matrix, the Hermitian adjoint of U.

**Definition 1.4 (The number operator).**

$$\forall N \in \mathbb{N},\; \forall v \in \operatorname{V}\left(N\right),\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{number}\left(N\right)\left(v\right)\left(x\right) = \operatorname{occupancy}\left(x\right) \cdot v\left(x\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.number` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The number operator multiplies each configuration coefficient by its occupancy.

**Definition 1.5 (Centered occupancy).**

$$\forall N \in \mathbb{N},\; \operatorname{Z}\left(N\right) = \operatorname{number}\left(N\right) - (\frac{N}{2}) \cdot \operatorname{id}\left(\operatorname{V}\left(N\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.Z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity shift centers occupancy at half of N, using complex scalar division.

**Definition 1.6 (Homogeneous rank space).**

$$\forall N \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall v \in \operatorname{V}\left(N\right),\; v \in \operatorname{rankSpace}\left(N, t\right) \Leftrightarrow \left(\forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right),\; (\operatorname{occupancy}\left(x\right) \neq t \Rightarrow v\left(x\right) = 0)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.rankSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Homogeneous vectors have support only at the stated occupancy.

**Definition 1.7 (Every primitive vector).**

$$\forall N \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall v \in \operatorname{V}\left(N\right),\; v \in \operatorname{primitive}\left(N, t\right) \Leftrightarrow ((v \in \operatorname{rankSpace}\left(N, t\right)) \land (\operatorname{L}\left(N\right)\left(v\right) = 0))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.primitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A primitive vector is homogeneous and is annihilated by the actual lowering map.

**Definition 1.8 (The finite strings).**

$$\forall S \in \mathbb{N},\; \forall w \in \operatorname{V}\left(2 \cdot S\right),\; w \in \operatorname{finitePrimitiveStrings}\left(S\right) \Leftrightarrow \left(\exists t \in \mathbb{N},\; ((t \leq S) \land (\exists v \in \operatorname{V}\left(2 \cdot S\right),\; ((v \in \operatorname{primitive}\left(2 \cdot S, t\right)) \land (\exists q \in \mathbb{N},\; ((q \leq 2 \cdot S - 2 \cdot t) \land (w = \left(\operatorname{U}\left(2 \cdot S\right)^{q}\right)\left(v\right)))))))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.finitePrimitiveStrings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All primitive vacua are included, including the spin-zero sector t=S; q=0 is retained.

**Theorem 1.9 (Span and exact primitive-string identities).**

$$\forall S \in \mathbb{N},\; (1 \leq S \Rightarrow ((\operatorname{span}\left(\mathbb{C}, \operatorname{finitePrimitiveStrings}\left(S\right)\right) = \operatorname{top}\left(\operatorname{V}\left(2 \cdot S\right)\right)) \land (((\forall t \in \mathbb{N},\; \forall v \in \operatorname{V}\left(2 \cdot S\right),\; (v \in \operatorname{primitive}\left(2 \cdot S, t\right) \Rightarrow (v \neq 0 \Rightarrow t \leq S))) \land (((\forall t \in \mathbb{N},\; (t \leq S \Rightarrow \forall v \in \operatorname{V}\left(2 \cdot S\right),\; (v \in \operatorname{primitive}\left(2 \cdot S, t\right) \Rightarrow ((\left(\operatorname{U}\left(2 \cdot S\right)^{2 \cdot S - 2 \cdot t + 1}\right)\left(v\right) = 0) \land (\forall q \in \mathbb{N},\; ((\operatorname{L}\left(2 \cdot S\right)\left(\left(\operatorname{U}\left(2 \cdot S\right)^{q + 1}\right)\left(v\right)\right) = (\left(q + 1\right) \cdot \left(2 \cdot S - 2 \cdot t - q\right)) \cdot \left(\operatorname{U}\left(2 \cdot S\right)^{q}\right)\left(v\right)) \land (((\operatorname{Z}\left(2 \cdot S\right)\left(\left(\operatorname{U}\left(2 \cdot S\right)^{q}\right)\left(v\right)\right) = (q - \left(S - t\right)) \cdot \left(\operatorname{U}\left(2 \cdot S\right)^{q}\right)\left(v\right)) \land ((q \leq 2 \cdot S - 2 \cdot t \Rightarrow \operatorname{innerC}\left(\left(\operatorname{U}\left(2 \cdot S\right)^{q}\right)\left(v\right), \left(\operatorname{U}\left(2 \cdot S\right)^{q}\right)\left(v\right)\right) = \operatorname{factorial}\left(q\right) \cdot \operatorname{descFactorial}\left(2 \cdot S - 2 \cdot t, q\right) \cdot \operatorname{innerC}\left(v, v\right))))))))))) \land (\forall t \in \mathbb{N},\; \forall tprime \in \mathbb{N},\; \forall v \in \operatorname{V}\left(2 \cdot S\right),\; \forall w \in \operatorname{V}\left(2 \cdot S\right),\; (v \in \operatorname{primitive}\left(2 \cdot S, t\right) \Rightarrow (w \in \operatorname{primitive}\left(2 \cdot S, tprime\right) \Rightarrow (((t \neq tprime \Rightarrow \operatorname{innerC}\left(v, w\right) = 0)) \land ((\operatorname{innerC}\left(v, w\right) = 0 \Rightarrow \forall q \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{innerC}\left(\left(\operatorname{U}\left(2 \cdot S\right)^{q}\right)\left(v\right), \left(\operatorname{U}\left(2 \cdot S\right)^{r}\right)\left(w\right)\right) = 0))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite span, cutoff, endpoint, lowering coefficient, weight, norm and orthogonality clauses all hold jointly on the same full complex carrier.

**Definition 1.10 (Previous binomial coefficient).**

$$\forall N \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{previousChoose}\left(N, t\right) = \operatorname{ite}\left(t = 0, 0, \operatorname{choose}\left(N, t - 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.previousChoose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rank zero has previousChoose(N,0)=0; successor ranks use the preceding binomial coefficient.

**Theorem 1.11 (Every primitive multiplicity).**

$$\forall S \in \mathbb{N},\; \forall t \in \mathbb{N},\; (t \leq S \Rightarrow \operatorname{dimC}\left(\operatorname{primitive}\left(2 \cdot S, t\right)\right) = \operatorname{choose}\left(2 \cdot S, t\right) - \operatorname{previousChoose}\left(2 \cdot S, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.primitive_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension formula is proved for every natural S and t≤S, using actual subspaces and operators.

**Definition 1.12 (Primitive orthonormal bases).**

$$\forall N \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{primitiveBasis}\left(N, t\right) = \operatorname{stdOrthonormalBasis}\left(\mathbb{C}, \operatorname{primitive}\left(N, t\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.primitiveBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pinned standard orthonormal basis is chosen inside each actual primitive subspace.

**Definition 1.13 (Normalized full strings).**

$$\forall S \in \mathbb{N},\; \forall a \in \operatorname{StringIndex}\left(S\right),\; \operatorname{normalizedString}\left(S, a\right) = (\frac{1}{\operatorname{norm}\left(\left(\operatorname{U}\left(2 \cdot S\right)^{\operatorname{position}\left(a\right)}\right)\left(\operatorname{primitiveBasis}\left(2 \cdot S, \operatorname{rank}\left(a\right)\right)\left(\operatorname{copy}\left(a\right)\right)\right)\right)}) \cdot \left(\operatorname{U}\left(2 \cdot S\right)^{\operatorname{position}\left(a\right)}\right)\left(\operatorname{primitiveBasis}\left(2 \cdot S, \operatorname{rank}\left(a\right)\right)\left(\operatorname{copy}\left(a\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.normalizedString` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every selected raising vector is divided by its actual positive norm.

**Definition 1.14 (Complete string basis).**

$$\forall S \in \mathbb{N},\; (1 \leq S \Rightarrow \forall a \in \operatorname{StringIndex}\left(S\right),\; \operatorname{stringBasis}\left(S\right)\left(a\right) = \operatorname{normalizedString}\left(S, a\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.stringBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected normalized family is orthonormal and spans the full carrier.

**Definition 1.15 (String coordinate unitary).**

$$\forall S \in \mathbb{N},\; (1 \leq S \Rightarrow \operatorname{stringUnitary}\left(S\right) = \operatorname{repr}\left(\operatorname{stringBasis}\left(S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.stringUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates in the proved complete string basis form a complex linear isometric equivalence.

**Definition 1.16 (Reversed native spin basis).**

$$\forall S \in \mathbb{N},\; (1 \leq S \Rightarrow \forall a \in \operatorname{NativeIndex}\left(S\right),\; \operatorname{nativeBasis}\left(S\right)\left(a\right) = \operatorname{normalizedString}\left(S, \operatorname{stringLabel}\left(\operatorname{rank}\left(a\right), \operatorname{copy}\left(a\right), \operatorname{finRev}\left(\operatorname{position}\left(a\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native coordinate r reverses the ascending string coordinate k by Fin.rev.

**Definition 1.17 (Full native spin unitary).**

$$\forall S \in \mathbb{N},\; (1 \leq S \Rightarrow \operatorname{nativeUnitary}\left(S\right) = \operatorname{repr}\left(\operatorname{nativeBasis}\left(S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The isometric equivalence includes every primitive copy and the native spin-zero space.

**Definition 1.18 (All native matrix blocks).**

$$\forall S \in \mathbb{N},\; \forall A \in \operatorname{SpinMatrixFamily}\left(\right),\; \operatorname{nativeMatrix}\left(S, A\right) = \operatorname{blockDiagonalNativeCopies}\left(S, A\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each primitive copy receives the corresponding repository-native spin matrix.

**Definition 1.19 (Native raising on all blocks).**

$$\forall S \in \mathbb{N},\; \operatorname{nativeU}\left(S\right) = \operatorname{toEuclideanLin}\left(\operatorname{nativeMatrix}\left(S, \operatorname{Jplus}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block operator uses the original Jplus matrices.

**Definition 1.20 (Native lowering on all blocks).**

$$\forall S \in \mathbb{N},\; \operatorname{nativeL}\left(S\right) = \operatorname{toEuclideanLin}\left(\operatorname{nativeMatrix}\left(S, \operatorname{conjugateTransposeJplus}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block operator uses the conjugate transposes of the original Jplus matrices.

**Definition 1.21 (Native weights on all blocks).**

$$\forall S \in \mathbb{N},\; \operatorname{nativeZ}\left(S\right) = \operatorname{toEuclideanLin}\left(\operatorname{nativeMatrix}\left(S, \operatorname{Jz}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block operator uses the original Jz matrices.

**Theorem 1.22 (Multiplicity, complete basis and native intertwiners).**

$$\forall S \in \mathbb{N},\; (1 \leq S \Rightarrow ((\forall t \in \operatorname{Fin}\left(S + 1\right),\; \operatorname{dimC}\left(\operatorname{primitive}\left(2 \cdot S, t\right)\right) = \operatorname{choose}\left(2 \cdot S, t\right) - \operatorname{previousChoose}\left(2 \cdot S, t\right)) \land (((\forall a \in \operatorname{NativeIndex}\left(S\right),\; \operatorname{nativeBasis}\left(S\right)\left(a\right) = \operatorname{normalizedString}\left(S, \operatorname{stringLabel}\left(\operatorname{rank}\left(a\right), \operatorname{copy}\left(a\right), \operatorname{finRev}\left(\operatorname{position}\left(a\right)\right)\right)\right)) \land (\forall v \in \operatorname{V}\left(2 \cdot S\right),\; ((\operatorname{nativeUnitary}\left(S\right)\left(\operatorname{U}\left(2 \cdot S\right)\left(v\right)\right) = \operatorname{nativeU}\left(S\right)\left(\operatorname{nativeUnitary}\left(S\right)\left(v\right)\right)) \land (((\operatorname{nativeUnitary}\left(S\right)\left(\operatorname{L}\left(2 \cdot S\right)\left(v\right)\right) = \operatorname{nativeL}\left(S\right)\left(\operatorname{nativeUnitary}\left(S\right)\left(v\right)\right)) \land (\operatorname{nativeUnitary}\left(S\right)\left(\operatorname{Z}\left(2 \cdot S\right)\left(v\right)\right) = \operatorname{nativeZ}\left(S\right)\left(\operatorname{nativeUnitary}\left(S\right)\left(v\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.native_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension identity, reversed normalized basis and three actual intertwiners hold jointly.

The raising and lowering maps are Matrix.toEuclideanLin of the existing PronkoFredkinAntiAdjointExpansion.totalPlus and totalMinus, using the existing sigmaPlus, sigmaMinus and site operators. Their tensor multiplication is reused from StabilizerPairLocalUnitaryInequivalence.tensor_mul. The proof derives the concrete commutator and complex adjoint relation. At each rank, orthogonal decomposition into the image of the preceding rank and its complement constructs primitive generators; induction proves full span. Thus neither a complete basis nor a homogeneous complement is an assumption. The pinned mathlib sl₂ primitive-vector theorems supply the recurrence and terminal zero on the whole nonzero carrier, including primitive strings of spin zero.

In the formulas, powers act by composition, ⟪v,w⟫ is complex Hermitian inner product, and scalars act on the left. Subtraction in the natural quantities d = 2S−2t and S−t is truncated; the lowering coefficient and weight are interpreted in ℂ after casting their natural operands. The notation scalar·vector denotes complex scalar multiplication. descFactorial(d,q) is the natural descending product ∏_{a=0}^{q−1}(d−a), equal to d!/(d−q)! when q≤d. The zero-power and zero-deficit cases are included. The result permits any primitive vector, without a reality restriction or a restriction to the permutation-invariant sector.

For each rank t≤S, the dimension is derived as choose(2S,t)−previousChoose(2S,t), where previousChoose(N,0)=0 and previousChoose(N,t+1)=choose(N,t). Fixed-occupancy configurations are identified with t-element subsets, and the actual rank space is identified with the complex function space on these subsets. The commutator and adjoint identity prove injectivity of U below the middle rank. Orthogonal splitting of rank t+1 into U(rank t) and its primitive subspace then gives the dimension formula; no rank multiplicity is assumed.

Write d=2S−2t=2(S−t), and let b(t,a) be the selected orthonormal primitive basis. StringIndex(S) consists of (t,(a,k)) with t in Fin(S+1), a in Fin(dim P(2S,t)), and k in Fin(d+1). The normalized vector is U^k b(t,a) divided by its positive real norm, as a complex scalar. Its squared unnormalized norm is k!·descFactorial(d,k), so every position in every selected string is nonzero. Orthogonality and the primitive spanning theorem prove that these normalized vectors form a complete orthonormal basis, rather than assuming a complete family or a unitary.

CopyIndex(S) is the dependent pair (t,a), and NativeIndex(S) is ((t,a),r), with r in Fin(d+1). EuclideanSpace(ℂ,NativeIndex(S)) is the finite Hilbert direct sum, over all primitive copies, of native spin-(S−t) spaces. The native basis vector at ((t,a),r) is the normalized string at (t,(a,Fin.rev(r))). Thus r=d−k=2j−k, including d=0. The coordinate unitary is constructed from this complete basis. nativeMatrix is the dependent block diagonal of the supplied native matrices; nativeU uses PrecessionSpinOneSeparableBound.Jplus, nativeL its conjugate transpose, and nativeZ its Jz. The raising matrix entry is sqrt(r·(d+1−r)) at row r−1, column r; the lowering entry is sqrt((r+1)·(d−r)) at row r+1, column r. Entries outside the range vanish, and Jz has weight d/2−r. Equivalently on ascending normalized strings, U has coefficient sqrt((k+1)·(d−k)), L has coefficient sqrt(k·(d−k+1)), and Z has weight −(S−t)+k. Both endpoints, all multiplicities and spin zero are included.

The native U/L/Z intertwiners are proved through the constructed basis and its full-span proof. They hold for every vector on the entire complex Boolean carrier and use no supplied basis, unitary, completeness, homogeneous complement, or multiplicity hypothesis. These are the single-site decomposition clauses of Theorem 6.2 only. Graph tensors, half-filling restrictions, projectors, token adjacency, energy gaps, and downstream section 32.2 remain separate. The public escape registration is unfinished under issue https://github.com/the-omega-institute/trureturing/issues/26983; this document claims neither registration validation nor atom closure.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.L`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.U`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.Z`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.finitePrimitiveStrings`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeBasis`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeL`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeMatrix`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeU`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeUnitary`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.nativeZ`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.native_decomposition`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.normalizedString`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.number`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.occupancy`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.previousChoose`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.primitive`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.primitiveBasis`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.primitive_multiplicity`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.rankSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.stringBasis`
- Truth anchor: `D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.stringUnitary`
- Dependency: [D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment](../Contextuality/TemporalHardySpinAttainment.md)
- Dependency: [D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion](../Dynamics/PronkoFredkinAntiAdjointExpansion.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
