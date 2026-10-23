# ReservoirSchur

## Abstract

ReservoirSchur supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Definition 1.1 (kernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t))) , \operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta w u = (match u . 1 , u . 2 with | \langle \operatorname{Sum.inl} i , s \rangle , \langle \operatorname{Sum.inr} h , j \rangle \mapsto w (i , h) \cdot \operatorname{ShiftPencilBlocks.antiDiagonal} p (s , j) | - , - \mapsto 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

kernelEmbedding places one alternating anti-diagonal vector in each short-long block and is zero on the other blocks; kernel_coordinates shows that these vectors parametrize the entire same-depth width-two kernel.

**Theorem 1.2 (kernelEmbedding_injective).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , \operatorname{Function.Injective} (\operatorname{CoeFun.coe}\left(\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The anti-diagonal kernel coordinates determine their embedded vector uniquely; kernelEmbedding_range combines this injectivity with the kernel dimension to identify the entire kernel.

**Theorem 1.3 (kernel_coordinates).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t)) \to \mathbb{Q}) , (\operatorname{ShiftPencilBlocks.widthTwoMatrix} p p alpha beta gamma delta) . mulVec u = 0 \to \exists (w : Fin alpha \times Fin delta \to \mathbb{Q}) , (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w = u$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernel_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vector annihilated by the same-depth widthTwoMatrix is an image of kernelEmbedding; LongReservoir.single_update_injective uses this parametrization to reduce the added-slice equation to the kernel coordinates.

**Definition 1.4 (cokernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin beta \times Fin gamma \to \mathbb{Q}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t + 1))) , \operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta w u = (match u . 1 , u . 2 with | \langle \operatorname{Sum.inr} k , s \rangle , \langle \operatorname{Sum.inl} j , t \rangle \mapsto w (k , j) \cdot \operatorname{ShiftPencilBlocks.antiDiagonal} p ((s , t) . 2 , (s , t) . 1) | - , - \mapsto 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cokernelEmbedding places transposed alternating anti-diagonal vectors in the long-short output blocks; cokernelMatrix_mul_widthTwo shows that the associated coordinate projection annihilates the width-two matrix.

**Theorem 1.5 (kernelMatrix_mulVec).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta)) . mulVec w = (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelMatrix_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying by the matrix of kernelEmbedding gives the embedded kernel vector; LongReservoir.single_update_injective uses this to apply the kernel sampling identity to its parametrized input.

**Theorem 1.6 (cokernelMatrix_mul_widthTwo).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta)) . transpose \cdot \operatorname{ShiftPencilBlocks.widthTwoMatrix} p p alpha beta gamma delta = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelMatrix_mul_widthTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transpose of the matrix of cokernelEmbedding annihilates widthTwoMatrix; short_reservoir_injective uses this projection to remove the original width-two term from the augmented flow equation.

**Definition 1.7 (kernelSample).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (t : Fin alpha \times Fin delta) , \operatorname{ReservoirSchur.kernelSample} p alpha beta gamma delta t = ((\langle \operatorname{Sum.inl} t . 1 , \langle 0 \rangle \rangle , \langle \operatorname{Sum.inr} t . 2 , \langle p \rangle \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

kernelSample chooses coordinates zero and p in each short-long input block; kernel_sample_identity shows that sampling at these positions recovers the kernel coefficients.

**Definition 1.8 (cokernelSample).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (t : Fin beta \times Fin gamma) , \operatorname{ReservoirSchur.cokernelSample} p alpha beta gamma delta t = ((\langle \operatorname{Sum.inr} t . 1 , \langle p \rangle \rangle , \langle \operatorname{Sum.inl} t . 2 , \langle 0 \rangle \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cokernelSample chooses coordinates p and zero in each long-short output block; cokernel_sample_identity shows that insertion at these positions is a right inverse of the cokernel projection.

**Theorem 1.9 (kernel_sample_identity).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.kernelSample} p alpha beta gamma delta)) . transpose \cdot \operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernel_sample_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sampling an embedded anti-diagonal kernel vector returns its coefficient vector; LongReservoir.single_update_injective uses this identity to reduce the added slice to a map on the kernel coefficients.

**Theorem 1.10 (cokernel_sample_identity).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta)) . transpose \cdot \operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.cokernelSample} p alpha beta gamma delta) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernel_sample_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inserting a vector at the cokernel sample positions and then applying the cokernel projection returns that vector; LongReservoir.single_update_injective uses this to read the added slice in cokernel coordinates.

**Definition 1.11 (singleCross).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (BM : Matrix (Fin beta) (Fin alpha) \mathbb{Q}) (DM : Matrix (Fin gamma) (Fin delta) \mathbb{Q}) , \operatorname{ReservoirSchur.singleCross} p alpha beta gamma delta BM DM = (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.cokernelSample} p alpha beta gamma delta) \cdot \operatorname{BM.kronecker} DM \cdot (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.kernelSample} p alpha beta gamma delta)) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singleCross inserts the Kronecker map BM⊗DM between the kernel sample positions and the cokernel sample positions; LongReservoir.single_update_injective uses this map to remove the width-two kernel.

**Theorem 1.12 (inclusion_prod).**

$$\forall \{m : Type\} \{n : Type\} \{r : Type\} \{s : Type\} [DecidableEq m] [DecidableEq r] (e : n \to m) (f : s \to r) , (\operatorname{CyclicResolvent.inclusion} fun (k : n \times s) \mapsto (e k . 1 , f k . 2)) = (\operatorname{CyclicResolvent.inclusion} e) . kronecker (\operatorname{CyclicResolvent.inclusion} f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.inclusion_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate insertion along a product of two maps is the Kronecker product of their insertion matrices; singleCross_kronecker uses this factorization to express the added matrix as one tensor slice.

**Definition 1.13 (shortZeroCol).**

$$\forall (p alpha beta : \mathbb{N}) (i : Fin alpha) , \operatorname{ReservoirSchur.shortZeroCol} p alpha beta i = (\langle \operatorname{Sum.inl} i , \langle 0 \rangle \rangle)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.shortZeroCol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

shortZeroCol selects column zero in each short block; singleThirdLeft uses these columns to read the kernel sample coordinates.

**Definition 1.14 (longLastRow).**

$$\forall (p alpha beta : \mathbb{N}) (k : Fin beta) , \operatorname{ReservoirSchur.longLastRow} p alpha beta k = (\langle \operatorname{Sum.inr} k , \langle p \rangle \rangle)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.longLastRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

longLastRow selects row p in each long block; singleThirdLeft uses these rows to insert the transformed coefficients into the cokernel sample positions.

**Definition 1.15 (singleThirdLeft).**

$$\forall (p alpha beta : \mathbb{N}) (BM : Matrix (Fin beta) (Fin alpha) \mathbb{Q}) , \operatorname{ReservoirSchur.singleThirdLeft} p alpha beta BM = (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.longLastRow} p alpha beta) \cdot BM \cdot (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.shortZeroCol} p alpha beta)) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleThirdLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singleThirdLeft applies BM from the zero columns of the short blocks to the final rows of the long blocks; singleCross_kronecker uses it as the left factor of the third tensor slice.

**Definition 1.16 (singleThirdRight).**

$$\forall (p gamma delta : \mathbb{N}) (DM : Matrix (Fin gamma) (Fin delta) \mathbb{Q}) , \operatorname{ReservoirSchur.singleThirdRight} p gamma delta DM = (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.shortZeroCol} p gamma delta) \cdot DM \cdot (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.longLastRow} p gamma delta)) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleThirdRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singleThirdRight applies DM from the final rows of the long blocks to the zero columns of the short blocks in the second factor; singleCross_kronecker uses it as the right factor of the third tensor slice.

**Theorem 1.17 (singleCross_kronecker).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (BM : Matrix (Fin beta) (Fin alpha) \mathbb{Q}) (DM : Matrix (Fin gamma) (Fin delta) \mathbb{Q}) , \operatorname{ReservoirSchur.singleCross} p alpha beta gamma delta BM DM = (\operatorname{ReservoirSchur.singleThirdLeft} p alpha beta BM) . kronecker (\operatorname{ReservoirSchur.singleThirdRight} p gamma delta DM)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleCross_kronecker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The update singleCross is the Kronecker product of singleThirdLeft and singleThirdRight; LongReservoir.single_reversal_injective_witness uses this equality to realize the kernel-removing update as a third bond slice.

**Definition 1.18 (localSource).**

$$\forall (p q alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta t)) \to \mathbb{Q}) (i : Sum (Fin alpha) (Fin beta)) (j : Sum (Fin gamma) (Fin delta)) (k : Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta i + 1) \times Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta j)) , \operatorname{ReservoirSchur.localSource} p q alpha beta gamma delta u i j k = (u (\langle i , k . 1 \rangle , \langle j , k . 2 \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.localSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

localSource restricts the input vector to one pair of shift blocks; widthTwo_mulVec_block uses this restriction to express each block equation as a rectangular pencil equation.

**Theorem 1.19 (widthTwo_mulVec_block).**

$$\forall (p q alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta t)) \to \mathbb{Q}) (i : Sum (Fin alpha) (Fin beta)) (j : Sum (Fin gamma) (Fin delta)) (s : Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta i)) (t : Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta j + 1)) , (\operatorname{ShiftPencilBlocks.widthTwoMatrix} p q alpha beta gamma delta) . mulVec u (\langle i , s \rangle , \langle j , t \rangle) = (\operatorname{ShiftPencilBlocks.pencil} (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta i) (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta j)) . mulVec (\operatorname{ReservoirSchur.localSource} p q alpha beta gamma delta u i j) (s , t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.widthTwo_mulVec_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any pair of blocks, multiplication by widthTwoMatrix equals pencil multiplication on localSource; sourceSL_kernel_of_updated_zero uses this to isolate the short-long kernel equations.

**Definition 1.20 (sourceSL).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t)) \to \mathbb{Q}) (k : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t))) , \operatorname{ReservoirSchur.sourceSL} p alpha beta gamma delta u k = (match k . 1 . fst , k . 2 . fst with | \operatorname{Sum.inl} - , \operatorname{Sum.inr} - \mapsto u k | - , - \mapsto 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.sourceSL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceSL keeps the short-long input blocks and sets all other blocks to zero; sourceSL_kernelEmbedding shows that this projection fixes every vector in the parametrized kernel.

**Definition 1.21 (slLine).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t)) \to \mathbb{Q}) (r t : Fin (p + 1)) (k : Fin alpha \times Fin delta) , \operatorname{ReservoirSchur.slLine} p alpha beta gamma delta u r t k = (u (\langle \operatorname{Sum.inl} k . 1 , \langle p - (\operatorname{val}\left(r\right)) \rangle \rangle , \langle \operatorname{Sum.inr} k . 2 , \langle p - (\operatorname{val}\left(t\right)) \rangle \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.slLine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

slLine reads the short-long input blocks at the coordinate pair (p-r,p-t); slLine_kernelEmbedding computes this array for an embedded anti-diagonal vector.

**Theorem 1.22 (cokernel_mulVec_formula).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (z : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t + 1)) \to \mathbb{Q}) (k : Fin beta) (j : Fin gamma) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta)) . \operatorname{transpose.mulVec} z (k , j) = \sum_{t : Fin (p + 1)} ((- 1)^{\operatorname{val}\left(t\right)} \cdot z (\langle \operatorname{Sum.inr} k , \langle p - (\operatorname{val}\left(t\right)) \rangle \rangle , \langle \operatorname{Sum.inl} j , t \rangle))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernel_mulVec_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cokernel projection is the displayed alternating sum along each long-short anti-diagonal; cokernel_reservoir_kernel uses this formula to compute the reservoir contribution in cokernel coordinates.

**Theorem 1.23 (slLine_kernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) (r t : Fin (p + 1)) , \operatorname{ReservoirSchur.slLine} p alpha beta gamma delta ((\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w) r t = if (\operatorname{val}\left(r\right)) + (\operatorname{val}\left(t\right)) = p then (- 1)^{p - (\operatorname{val}\left(r\right))} \cdot w else 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.slLine_kernelEmbedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an embedded kernel vector, slLine vanishes unless r+t=p and otherwise equals the coefficient vector multiplied by the displayed sign; cokernel_reservoir_kernel uses this to compute the projected added slice.

**Theorem 1.24 (sourceSL_kernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) , \operatorname{ReservoirSchur.sourceSL} p alpha beta gamma delta ((\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w) = (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.sourceSL_kernelEmbedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The short-long block projection fixes every image of kernelEmbedding; short_reservoir_injective uses this identity to recover the full kernel vector from the vanishing short-long component.

**Theorem 1.25 (short_short_witness).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , 0 < p \to 0 < beta \to beta \leq alpha \to 0 < delta \to delta \leq gamma \to \operatorname{QuantumMaxFlowBound.RationalWitness} (\operatorname{ShiftPencilBlocks.leftDim} p alpha beta) (\operatorname{ShiftPencilBlocks.rightDim} p alpha beta) (\operatorname{ShiftPencilBlocks.leftDim} p gamma delta) (\operatorname{ShiftPencilBlocks.rightDim} p gamma delta)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.short_short_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p > 0, 0 < beta ≤ alpha and 0 < delta ≤ gamma, the short reservoir construction yields rational three-slice matrices attaining the outer cut by eliminating the kernel through its Schur complement. LongReservoir.parameterized_base_witness applies this in the equal-depth case with these multiplicity orderings.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelEmbedding`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelMatrix_mul_widthTwo`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelSample`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernel_mulVec_formula`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernel_sample_identity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.inclusion_prod`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelEmbedding`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelEmbedding_injective`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelMatrix_mulVec`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelSample`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernel_coordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernel_sample_identity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.localSource`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.longLastRow`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.shortZeroCol`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.short_short_witness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleCross`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleCross_kronecker`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleThirdLeft`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleThirdRight`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.slLine`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.slLine_kernelEmbedding`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.sourceSL`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.sourceSL_kernelEmbedding`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.widthTwo_mulVec_block`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks](ShiftPencilBlocks.md)
