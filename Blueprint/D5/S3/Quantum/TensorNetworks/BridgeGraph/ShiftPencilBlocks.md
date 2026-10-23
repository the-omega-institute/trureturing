# ShiftPencilBlocks

## Abstract

ShiftPencilBlocks supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Definition 1.1 (ParameterizedBaseWitness).**

$$\operatorname{ShiftPencilBlocks.ParameterizedBaseWitness} \iff (\forall (p q alpha beta gamma delta : \mathbb{N}) , 0 < p \to 0 < q \to 0 < beta \to 0 < delta \to \operatorname{QuantumMaxFlowBound.RationalWitness} (p \cdot alpha + (p + 1) \cdot beta) ((p + 1) \cdot alpha + (p + 2) \cdot beta) (q \cdot gamma + (q + 1) \cdot delta) ((q + 1) \cdot gamma + (q + 2) \cdot delta))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.ParameterizedBaseWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ParameterizedBaseWitness asserts rational full-rank flows for pairs whose dimensions are sums of short and long shift-block dimensions, with positive depths and positive long-block multiplicities; base_of_parameterized uses the decomposition of strict base pairs to recover BaseWitness.

**Theorem 1.2 (base_of_parameterized).**

$$\operatorname{ShiftPencilBlocks.ParameterizedBaseWitness} \to \operatorname{QuantumMaxFlowBound.BaseWitness}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.base_of_parameterized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strict base dimension pair can be decomposed into short and long shift blocks, so full rank for the parameterized family implies BaseWitness; LongReservoir.base_witness applies this implication to its constructions.

**Definition 1.3 (rectExtend).**

$$\forall (x y : \mathbb{N}) (z : Fin x \times Fin y \to \mathbb{Q}) (i k : \mathbb{N}) , \operatorname{ShiftPencilBlocks.rectExtend} z i k = (if hi : i < x then if hk : k < y then z (\langle i , hi \rangle , \langle k , hk \rangle) else 0 else 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.rectExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rectExtend extends a finite rectangular array by zero to natural-number coordinates; pencil_mulVec uses it to express the pencil recurrence uniformly at the boundary.

**Definition 1.4 (shift1).**

$$\forall (x : \mathbb{N}) , \operatorname{ShiftPencilBlocks.shift1} x = (\operatorname{Matrix.submatrix} 1 (fun (i : Fin x) \mapsto (\operatorname{val}\left(i\right)) + 1) \operatorname{Fin.val})$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.shift1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

shift1 has entry one when the column index is one greater than the row index and zero elsewhere; pencil combines it with the rectangular identity to couple adjacent coordinates.

**Definition 1.5 (pencil).**

$$\forall (x y : \mathbb{N}) , \operatorname{ShiftPencilBlocks.pencil} x y = ((\operatorname{QuantumMaxFlowBound.rectId} x (x + 1)) . kronecker (\operatorname{QuantumMaxFlowBound.rectId} y (y + 1)) . transpose + (\operatorname{ShiftPencilBlocks.shift1} x) . kronecker (\operatorname{ShiftPencilBlocks.shift1} y) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.pencil` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pencil is the sum of the unshifted and shifted Kronecker terms, mapping (x+1)*y input coordinates to x*(y+1) output coordinates; pencil_rank_of_le proves full row rank when x ≤ y.

**Theorem 1.6 (pencil_rank_of_le).**

$$\forall (x y : \mathbb{N}) , x \leq y \to (\operatorname{ShiftPencilBlocks.pencil} x y) . rank = x \cdot (y + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.pencil_rank_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When x ≤ y, pencil has full row rank x*(y+1), because its transpose recurrence propagates to a zero boundary. widthTwo_rank_of_lt applies this blockwise to dimension pairs with increasing depths.

**Theorem 1.7 (block_mulVec).**

$$\forall \{\iota : Type\} [Fintype \iota] [DecidableEq \iota] \{m : \iota \to Type\} \{n : \iota \to Type\} [(i : \iota) \to Fintype (m i)] [(i : \iota) \to Fintype (n i)] (A : (i : \iota) \to Matrix (m i) (n i) \mathbb{Q}) (z : (\Sigma_{i : \iota} n i) \to \mathbb{Q}) (i : \iota) (j : m i) , (\operatorname{Matrix.blockDiagonal} ' A) . mulVec z \langle i , j \rangle = (A i) . mulVec (fun (k : n i) \mapsto z \langle i , k \rangle) j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.block_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by a block-diagonal matrix acts on each block using only the corresponding input coordinates; blockKernelEquiv uses this identity to identify its kernel with the product of the individual kernels.

**Definition 1.8 (tensorBlockEquiv).**

$$\forall (\iota : Type) (\kappa : Type) (m : \iota \to Type) (n : \kappa \to Type) , \operatorname{ShiftPencilBlocks.tensorBlockEquiv} m n = ((\operatorname{Equiv.sigmaProdDistrib} m (\Sigma_{j : \kappa} n j)) . trans ((\operatorname{Equiv.sigmaCongrRight} fun (i : \iota) \mapsto (\operatorname{Equiv.prodComm} (m i) (\Sigma_{j : \kappa} n j)) . trans ((\operatorname{Equiv.sigmaProdDistrib} n (m i)) . trans (\operatorname{Equiv.sigmaCongrRight} fun (j : \kappa) \mapsto \operatorname{Equiv.prodComm} (n j) (m i)))) . trans \operatorname{Equiv.sigmaAssocProd.symm}))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.tensorBlockEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tensorBlockEquiv groups a pair of dependent block indices into a single index for the pair of blocks; widthTwo_block_decomposition uses this reindexing to express the tensor matrix as a block-diagonal family of pencils.

**Theorem 1.9 (pencil_mulVec).**

$$\forall (x y : \mathbb{N}) (u : Fin (x + 1) \times Fin y \to \mathbb{Q}) (r : Fin x \times Fin (y + 1)) , (\operatorname{ShiftPencilBlocks.pencil} x y) . mulVec u r = \operatorname{ShiftPencilBlocks.rectExtend} u (\operatorname{val}\left(r . 1\right)) (\operatorname{val}\left(r . 2\right)) + if 0 < (\operatorname{val}\left(r . 2\right)) then \operatorname{ShiftPencilBlocks.rectExtend} u ((\operatorname{val}\left(r . 1\right)) + 1) ((\operatorname{val}\left(r . 2\right)) - 1) else 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.pencil_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each output position, pencil multiplication adds the current input coordinate and the adjacent shifted coordinate, with zero extension at the boundary; antiDiagonal_kernel uses this recurrence to cancel successive alternating signs.

**Definition 1.10 (antiDiagonal).**

$$\forall (p : \mathbb{N}) (k : Fin (p + 1) \times Fin (p + 1)) , \operatorname{ShiftPencilBlocks.antiDiagonal} p k = (if (\operatorname{val}\left(k . 1\right)) + (\operatorname{val}\left(k . 2\right)) = p then (- 1)^{\operatorname{val}\left(k . 1\right)} else 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.antiDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

antiDiagonal is supported where the two coordinate indices sum to p and has alternating signs there; antiDiagonal_kernel shows that it lies in the kernel of the short-long pencil.

**Theorem 1.11 (antiDiagonal_kernel).**

$$\forall (p : \mathbb{N}) , (\operatorname{ShiftPencilBlocks.pencil} p (p + 1)) . mulVec (\operatorname{ShiftPencilBlocks.antiDiagonal} p) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.antiDiagonal_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alternating anti-diagonal vector is annihilated by pencil p (p+1); ReservoirSchur.widthTwo_kernelEmbedding applies this in every short-long block to construct kernel vectors.

**Definition 1.12 (blockLength).**

$$\forall (p alpha beta : \mathbb{N}) , \operatorname{ShiftPencilBlocks.blockLength} p alpha beta = \operatorname{Sum.elim} (fun _ \mapsto p) (fun _ \mapsto p + 1)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.blockLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

blockLength assigns length p to each of the alpha short blocks and p+1 to each of the beta long blocks; arrow0 and arrow1 use these lengths to form their block-diagonal matrices.

**Definition 1.13 (leftDim).**

$$\forall (p alpha beta : \mathbb{N}) , \operatorname{ShiftPencilBlocks.leftDim} p alpha beta = (p \cdot alpha + (p + 1) \cdot beta)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.leftDim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

leftDim is the total row dimension p*alpha+(p+1)*beta of the shift blocks; rows_card identifies it with the cardinality of the dependent row-index type.

**Definition 1.14 (rightDim).**

$$\forall (p alpha beta : \mathbb{N}) , \operatorname{ShiftPencilBlocks.rightDim} p alpha beta = ((p + 1) \cdot alpha + (p + 2) \cdot beta)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.rightDim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rightDim is the total column dimension (p+1)*alpha+(p+2)*beta of the shift blocks; cols_card identifies it with the cardinality of the dependent column-index type.

**Theorem 1.15 (rows_card).**

$$\forall (p alpha beta : \mathbb{N}) , \operatorname{Fintype.card} ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t))) = \operatorname{ShiftPencilBlocks.leftDim} p alpha beta$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.rows_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dependent row-index type has cardinality leftDim; same_depth_kernel_dimension uses this count with the rank calculation to compute the kernel dimension.

**Theorem 1.16 (cols_card).**

$$\forall (p alpha beta : \mathbb{N}) , \operatorname{Fintype.card} ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) = \operatorname{ShiftPencilBlocks.rightDim} p alpha beta$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.cols_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dependent column-index type has cardinality rightDim; same_depth_kernel_dimension uses this count as the domain dimension in rank-nullity.

**Definition 1.17 (arrow0).**

$$\forall (p alpha beta : \mathbb{N}) , \operatorname{ShiftPencilBlocks.arrow0} p alpha beta = (\operatorname{Matrix.blockDiagonal} ' fun (t : Sum (Fin alpha) (Fin beta)) \mapsto \operatorname{QuantumMaxFlowBound.rectId} (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t) (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.arrow0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

arrow0 is the block-diagonal sum of the rectangular identity maps for the short and long blocks; widthTwoMatrix pairs it with the transpose of the second dimension pair’s unshifted map.

**Definition 1.18 (arrow1).**

$$\forall (p alpha beta : \mathbb{N}) , \operatorname{ShiftPencilBlocks.arrow1} p alpha beta = (\operatorname{Matrix.blockDiagonal} ' fun (t : Sum (Fin alpha) (Fin beta)) \mapsto \operatorname{ShiftPencilBlocks.shift1} (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.arrow1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

arrow1 is the block-diagonal sum of the one-step shift maps for the short and long blocks; widthTwoMatrix pairs it with the transpose of the second dimension pair’s shifted map.

**Definition 1.19 (widthTwoMatrix).**

$$\forall (p q alpha beta gamma delta : \mathbb{N}) , \operatorname{ShiftPencilBlocks.widthTwoMatrix} p q alpha beta gamma delta = ((\operatorname{ShiftPencilBlocks.arrow0} p alpha beta) . kronecker (\operatorname{ShiftPencilBlocks.arrow0} q gamma delta) . transpose + (\operatorname{ShiftPencilBlocks.arrow1} p alpha beta) . kronecker (\operatorname{ShiftPencilBlocks.arrow1} q gamma delta) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.widthTwoMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

widthTwoMatrix is the sum of the two Kronecker products formed from arrow0 and arrow1; widthTwo_block_decomposition splits it into rectangular pencils indexed by pairs of blocks.

**Theorem 1.20 (widthTwo_block_decomposition).**

$$\forall (p q alpha beta gamma delta : \mathbb{N}) , \operatorname{ShiftPencilBlocks.widthTwoMatrix} p q alpha beta gamma delta = (\operatorname{Matrix.blockDiagonal} ' fun (t : (Sum (Fin alpha) (Fin beta)) \times (Sum (Fin gamma) (Fin delta))) \mapsto \operatorname{ShiftPencilBlocks.pencil} (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t . 1) (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta t . 2)) . submatrix (\operatorname{CoeFun.coe}\left(\operatorname{ShiftPencilBlocks.tensorBlockEquiv} (fun (t : Sum (Fin alpha) (Fin beta)) \mapsto Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t)) fun (t : Sum (Fin gamma) (Fin delta)) \mapsto Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta t + 1)\right)) (\operatorname{CoeFun.coe}\left(\operatorname{ShiftPencilBlocks.tensorBlockEquiv} (fun (t : Sum (Fin alpha) (Fin beta)) \mapsto Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1)) fun (t : Sum (Fin gamma) (Fin delta)) \mapsto Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta t)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.widthTwo_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the rows and columns identifies widthTwoMatrix with a block-diagonal family of rectangular pencils; widthTwo_rank_sum uses this decomposition to add their ranks.

**Theorem 1.21 (witness_of_typed_slices).**

$$\forall \{I : Type\} \{J : Type\} \{K : Type\} \{L : Type\} [Fintype I] [Fintype J] [Fintype K] [Fintype L] \{a b c d : \mathbb{N}\} , \operatorname{Fintype.card} I = a \to \operatorname{Fintype.card} J = b \to \operatorname{Fintype.card} K = c \to \operatorname{Fintype.card} L = d \to \forall (M : Fin 3 \to Matrix I J \mathbb{Q}) (N : Fin 3 \to Matrix L K \mathbb{Q}) , (\sum_{r : Fin 3} ((M r) . kronecker (N r))) . rank = min (a \cdot d) (b \cdot c) \to \operatorname{QuantumMaxFlowBound.RationalWitness} a b c d$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.witness_of_typed_slices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational three-slice contraction attaining the smaller outer cut on arbitrary finite index types can be reindexed to Fin a, Fin b, Fin c and Fin d without changing rank; witness_of_widthTwo_rank applies this to the block-indexed construction.

**Theorem 1.22 (different_depth_witness).**

$$\forall (p q alpha beta gamma delta : \mathbb{N}) , p \neq q \to \operatorname{QuantumMaxFlowBound.RationalWitness} (\operatorname{ShiftPencilBlocks.leftDim} p alpha beta) (\operatorname{ShiftPencilBlocks.rightDim} p alpha beta) (\operatorname{ShiftPencilBlocks.leftDim} q gamma delta) (\operatorname{ShiftPencilBlocks.rightDim} q gamma delta)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.different_depth_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the two depths differ, the width-two pencil already gives rational matrices attaining min(a*d,b*c) for the parameterized dimensions; LongReservoir.parameterized_base_witness uses this for the unequal-depth case.

**Theorem 1.23 (same_depth_kernel_dimension).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , \operatorname{Module.finrank} \mathbb{Q} (\operatorname{CoeSort.coe}\left((\operatorname{ShiftPencilBlocks.widthTwoMatrix} p p alpha beta gamma delta) . mulVecLin . ker\right)) = alpha \cdot delta$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.same_depth_kernel_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At equal depths, the kernel of widthTwoMatrix has dimension alpha*delta; ReservoirSchur.kernelEmbedding_range combines this count with its injective kernel parametrization to show that every kernel vector has those coordinates.

**Theorem 1.24 (zero_defect_witness).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , (alpha \cdot delta = 0 \lor beta \cdot gamma = 0) \to \operatorname{QuantumMaxFlowBound.RationalWitness} (\operatorname{ShiftPencilBlocks.leftDim} p alpha beta) (\operatorname{ShiftPencilBlocks.rightDim} p alpha beta) (\operatorname{ShiftPencilBlocks.leftDim} p gamma delta) (\operatorname{ShiftPencilBlocks.rightDim} p gamma delta)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.zero_defect_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At equal depths, if alpha*delta or beta*gamma vanishes, the width-two matrix attains the smaller outer cut; LongReservoir.parameterized_base_witness uses this for the zero-defect cases.

**Theorem 1.25 (double_fin_pick).**

$$\forall (n m r s : \mathbb{N}) (a b : \mathbb{Q}) (u : Fin n \times Fin m \to \mathbb{Q}) , \sum_{i : Fin n} (\sum_{j : Fin m} (((if (\operatorname{val}\left(i\right)) = r then a else 0) \cdot if (\operatorname{val}\left(j\right)) = s then b else 0) \cdot u (i , j))) = a \cdot b \cdot \operatorname{ShiftPencilBlocks.rectExtend} u r s$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.double_fin_pick` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A double finite sum supported at a single pair of indices equals the product of the two coefficients times the zero-extended array value; ReservoirSchur.reservoirCross_SL_short_row uses this to compute the added slice at a short-row position.

**Theorem 1.26 (neg_one_pow_square).**

$$\forall (n : \mathbb{N}) , (- 1)^{n} \cdot (- 1)^{n} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.neg_one_pow_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square of every integer power of -1 is one; ReservoirSchur.cokernel_reservoir_kernel uses this identity to cancel the two anti-diagonal signs in the projected reservoir equation.

**Theorem 1.27 (short_short_cyclic_schur_rank).**

$$\forall (A B G D p : \mathbb{N}) , 0 < B \to B \leq A \to 0 < D \to D \leq G \to 0 < p \to (((\operatorname{Coe.coe}\left(p\right)) + 1) \cdot (\operatorname{FloorSelectorCycles.rowSelector} A B) . kronecker (\operatorname{FloorSelectorCycles.rowSelector} G D) . transpose - (\operatorname{FloorSelectorCycles.rowSelector} A B) . kronecker (\operatorname{FloorSelectorCycles.forwardHalf} G) \cdot (\operatorname{FloorSelectorCycles.reservoir} A G)^{-1} \cdot (- \operatorname{FloorSelectorCycles.backward} A) . kronecker (\operatorname{FloorSelectorCycles.rowSelector} G D) . transpose) . rank = min (A \cdot D) (B \cdot G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.short_short_cyclic_schur_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < B ≤ A, 0 < D ≤ G and p > 0, the short reservoir Schur complement has rank min(A*D,B*G); ReservoirSchur.short_short_injective_witness combines this with the relevant dimension ordering to obtain an injective Schur map.

**Theorem 1.28 (long_long_cyclic_schur_rank).**

$$\forall (A B G D p : \mathbb{N}) , 0 < A \to A \leq B \to 0 < G \to G \leq D \to 0 < p \to (((\operatorname{Coe.coe}\left(p\right)) + 1) \cdot (\operatorname{FloorSelectorCycles.rowSelector} B A) . \operatorname{transpose.kronecker} (\operatorname{FloorSelectorCycles.rowSelector} D G) - (- \operatorname{FloorSelectorCycles.backward} B) . \operatorname{transpose.kronecker} (\operatorname{FloorSelectorCycles.rowSelector} D G) \cdot (1 + (- \operatorname{FloorSelectorCycles.backward} B) . \operatorname{transpose.kronecker} (\operatorname{FloorSelectorCycles.forwardHalf} D) . transpose)^{-1} \cdot (\operatorname{FloorSelectorCycles.rowSelector} B A) . \operatorname{transpose.kronecker} (\operatorname{FloorSelectorCycles.forwardHalf} D) . transpose) . rank = min (A \cdot D) (B \cdot G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.long_long_cyclic_schur_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < A ≤ B, 0 < G ≤ D and p > 0, the long reservoir Schur complement has rank min(A*D,B*G); LongReservoir.long_long_injective_witness uses this rank to eliminate the remaining kernel coordinates.

**Theorem 1.29 (matrix_injective_of_rank).**

$$\forall \{m : Type\} \{n : Type\} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n \mathbb{Q}) , \operatorname{A.rank} = \operatorname{Fintype.card} n \to \operatorname{Function.Injective} (\operatorname{CoeFun.coe}\left(A . mulVecLin\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.matrix_injective_of_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational matrix whose rank equals its number of columns defines an injective linear map; LongReservoir.long_long_injective_witness applies this to its full-column-rank Schur complement.

**Theorem 1.30 (schur_two_equations).**

$$\forall \{m : Type\} \{n : Type\} \{k : Type\} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k] (R : Matrix m m \mathbb{Q}) (T : Matrix m n \mathbb{Q}) (L : Matrix k m \mathbb{Q}) (H : Matrix k n \mathbb{Q}) , IsUnit R \to \operatorname{Function.Injective} (H - L \cdot R^{-1} \cdot T) . mulVec \to \forall (v : m \to \mathbb{Q}) (w : n \to \mathbb{Q}) , \operatorname{R.mulVec} v + \operatorname{T.mulVec} w = 0 \to \operatorname{L.mulVec} v + \operatorname{H.mulVec} w = 0 \to v = 0 \land w = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.schur_two_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If R is invertible and H-L*R⁻¹*T is injective, the two displayed coupled homogeneous equations imply v=w=0; ReservoirSchur.short_reservoir_injective and LongReservoir.long_reservoir_injective use this to prove injectivity of the augmented flow matrices.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.ParameterizedBaseWitness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.antiDiagonal`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.antiDiagonal_kernel`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.arrow0`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.arrow1`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.base_of_parameterized`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.blockLength`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.block_mulVec`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.cols_card`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.different_depth_witness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.double_fin_pick`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.leftDim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.long_long_cyclic_schur_rank`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.matrix_injective_of_rank`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.neg_one_pow_square`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.pencil`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.pencil_mulVec`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.pencil_rank_of_le`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.rectExtend`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.rightDim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.rows_card`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.same_depth_kernel_dimension`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.schur_two_equations`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.shift1`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.short_short_cyclic_schur_rank`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.tensorBlockEquiv`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.widthTwoMatrix`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.widthTwo_block_decomposition`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.witness_of_typed_slices`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks.zero_defect_witness`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent](CyclicResolvent.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound](QuantumMaxFlowBound.md)
