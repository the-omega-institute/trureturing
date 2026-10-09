# ReservoirSchur

## Abstract

ReservoirSchur supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Definition 1.1 (kernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t))) , \operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta w u = (match u . 1 , u . 2 with | \langle \operatorname{Sum.inl} i , s \rangle , \langle \operatorname{Sum.inr} h , j \rangle \mapsto w (i , h) \cdot \operatorname{ShiftPencilBlocks.antiDiagonal} p (s , j) | - , - \mapsto 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes kernelEmbedding for the consumed ReservoirSchur construction.

**Theorem 1.2 (kernelEmbedding_injective).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , \operatorname{Function.Injective} (\operatorname{CoeFun.coe}\left(\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

kernelEmbedding_injective is used on the live proof path of the width-three bridge construction.

**Theorem 1.3 (kernel_coordinates).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t)) \to \mathbb{Q}) , (\operatorname{ShiftPencilBlocks.widthTwoMatrix} p p alpha beta gamma delta) . mulVec u = 0 \to \exists (w : Fin alpha \times Fin delta \to \mathbb{Q}) , (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w = u$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernel_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

kernel_coordinates is used on the live proof path of the width-three bridge construction.

**Definition 1.4 (cokernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin beta \times Fin gamma \to \mathbb{Q}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t + 1))) , \operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta w u = (match u . 1 , u . 2 with | \langle \operatorname{Sum.inr} k , s \rangle , \langle \operatorname{Sum.inl} j , t \rangle \mapsto w (k , j) \cdot \operatorname{ShiftPencilBlocks.antiDiagonal} p ((s , t) . 2 , (s , t) . 1) | - , - \mapsto 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes cokernelEmbedding for the consumed ReservoirSchur construction.

**Theorem 1.5 (kernelMatrix_mulVec).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta)) . mulVec w = (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelMatrix_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

kernelMatrix_mulVec is used on the live proof path of the width-three bridge construction.

**Theorem 1.6 (cokernelMatrix_mul_widthTwo).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta)) . transpose \cdot \operatorname{ShiftPencilBlocks.widthTwoMatrix} p p alpha beta gamma delta = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelMatrix_mul_widthTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

cokernelMatrix_mul_widthTwo is used on the live proof path of the width-three bridge construction.

**Definition 1.7 (kernelSample).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (t : Fin alpha \times Fin delta) , \operatorname{ReservoirSchur.kernelSample} p alpha beta gamma delta t = ((\langle \operatorname{Sum.inl} t . 1 , \langle 0 \rangle \rangle , \langle \operatorname{Sum.inr} t . 2 , \langle p \rangle \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernelSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes kernelSample for the consumed ReservoirSchur construction.

**Definition 1.8 (cokernelSample).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (t : Fin beta \times Fin gamma) , \operatorname{ReservoirSchur.cokernelSample} p alpha beta gamma delta t = ((\langle \operatorname{Sum.inr} t . 1 , \langle p \rangle \rangle , \langle \operatorname{Sum.inl} t . 2 , \langle 0 \rangle \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernelSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes cokernelSample for the consumed ReservoirSchur construction.

**Theorem 1.9 (kernel_sample_identity).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.kernelSample} p alpha beta gamma delta)) . transpose \cdot \operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.kernel_sample_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

kernel_sample_identity is used on the live proof path of the width-three bridge construction.

**Theorem 1.10 (cokernel_sample_identity).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta)) . transpose \cdot \operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.cokernelSample} p alpha beta gamma delta) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernel_sample_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

cokernel_sample_identity is used on the live proof path of the width-three bridge construction.

**Definition 1.11 (singleCross).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (BM : Matrix (Fin beta) (Fin alpha) \mathbb{Q}) (DM : Matrix (Fin gamma) (Fin delta) \mathbb{Q}) , \operatorname{ReservoirSchur.singleCross} p alpha beta gamma delta BM DM = (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.cokernelSample} p alpha beta gamma delta) \cdot \operatorname{BM.kronecker} DM \cdot (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.kernelSample} p alpha beta gamma delta)) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes singleCross for the consumed ReservoirSchur construction.

**Theorem 1.12 (inclusion_prod).**

$$\forall \{m : Type\} \{n : Type\} \{r : Type\} \{s : Type\} [DecidableEq m] [DecidableEq r] (e : n \to m) (f : s \to r) , (\operatorname{CyclicResolvent.inclusion} fun (k : n \times s) \mapsto (e k . 1 , f k . 2)) = (\operatorname{CyclicResolvent.inclusion} e) . kronecker (\operatorname{CyclicResolvent.inclusion} f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.inclusion_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

inclusion_prod is used on the live proof path of the width-three bridge construction.

**Definition 1.13 (shortZeroCol).**

$$\forall (p alpha beta : \mathbb{N}) (i : Fin alpha) , \operatorname{ReservoirSchur.shortZeroCol} p alpha beta i = (\langle \operatorname{Sum.inl} i , \langle 0 \rangle \rangle)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.shortZeroCol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes shortZeroCol for the consumed ReservoirSchur construction.

**Definition 1.14 (longLastRow).**

$$\forall (p alpha beta : \mathbb{N}) (k : Fin beta) , \operatorname{ReservoirSchur.longLastRow} p alpha beta k = (\langle \operatorname{Sum.inr} k , \langle p \rangle \rangle)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.longLastRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes longLastRow for the consumed ReservoirSchur construction.

**Definition 1.15 (singleThirdLeft).**

$$\forall (p alpha beta : \mathbb{N}) (BM : Matrix (Fin beta) (Fin alpha) \mathbb{Q}) , \operatorname{ReservoirSchur.singleThirdLeft} p alpha beta BM = (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.longLastRow} p alpha beta) \cdot BM \cdot (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.shortZeroCol} p alpha beta)) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleThirdLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes singleThirdLeft for the consumed ReservoirSchur construction.

**Definition 1.16 (singleThirdRight).**

$$\forall (p gamma delta : \mathbb{N}) (DM : Matrix (Fin gamma) (Fin delta) \mathbb{Q}) , \operatorname{ReservoirSchur.singleThirdRight} p gamma delta DM = (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.shortZeroCol} p gamma delta) \cdot DM \cdot (\operatorname{CyclicResolvent.inclusion} (\operatorname{ReservoirSchur.longLastRow} p gamma delta)) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleThirdRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes singleThirdRight for the consumed ReservoirSchur construction.

**Theorem 1.17 (singleCross_kronecker).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (BM : Matrix (Fin beta) (Fin alpha) \mathbb{Q}) (DM : Matrix (Fin gamma) (Fin delta) \mathbb{Q}) , \operatorname{ReservoirSchur.singleCross} p alpha beta gamma delta BM DM = (\operatorname{ReservoirSchur.singleThirdLeft} p alpha beta BM) . kronecker (\operatorname{ReservoirSchur.singleThirdRight} p gamma delta DM)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.singleCross_kronecker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

singleCross_kronecker is used on the live proof path of the width-three bridge construction.

**Definition 1.18 (localSource).**

$$\forall (p q alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta t)) \to \mathbb{Q}) (i : Sum (Fin alpha) (Fin beta)) (j : Sum (Fin gamma) (Fin delta)) (k : Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta i + 1) \times Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta j)) , \operatorname{ReservoirSchur.localSource} p q alpha beta gamma delta u i j k = (u (\langle i , k . 1 \rangle , \langle j , k . 2 \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.localSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes localSource for the consumed ReservoirSchur construction.

**Theorem 1.19 (widthTwo_mulVec_block).**

$$\forall (p q alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta t)) \to \mathbb{Q}) (i : Sum (Fin alpha) (Fin beta)) (j : Sum (Fin gamma) (Fin delta)) (s : Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta i)) (t : Fin (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta j + 1)) , (\operatorname{ShiftPencilBlocks.widthTwoMatrix} p q alpha beta gamma delta) . mulVec u (\langle i , s \rangle , \langle j , t \rangle) = (\operatorname{ShiftPencilBlocks.pencil} (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta i) (\operatorname{ShiftPencilBlocks.blockLength} q gamma delta j)) . mulVec (\operatorname{ReservoirSchur.localSource} p q alpha beta gamma delta u i j) (s , t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.widthTwo_mulVec_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

widthTwo_mulVec_block is used on the live proof path of the width-three bridge construction.

**Definition 1.20 (sourceSL).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t)) \to \mathbb{Q}) (k : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t))) , \operatorname{ReservoirSchur.sourceSL} p alpha beta gamma delta u k = (match k . 1 . fst , k . 2 . fst with | \operatorname{Sum.inl} - , \operatorname{Sum.inr} - \mapsto u k | - , - \mapsto 0)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.sourceSL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes sourceSL for the consumed ReservoirSchur construction.

**Definition 1.21 (slLine).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (u : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t + 1))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t)) \to \mathbb{Q}) (r t : Fin (p + 1)) (k : Fin alpha \times Fin delta) , \operatorname{ReservoirSchur.slLine} p alpha beta gamma delta u r t k = (u (\langle \operatorname{Sum.inl} k . 1 , \langle p - (\operatorname{val}\left(r\right)) \rangle \rangle , \langle \operatorname{Sum.inr} k . 2 , \langle p - (\operatorname{val}\left(t\right)) \rangle \rangle))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.slLine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes slLine for the consumed ReservoirSchur construction.

**Theorem 1.22 (cokernel_mulVec_formula).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (z : ((\Sigma_{t : Sum (Fin alpha) (Fin beta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p alpha beta t))) \times (\Sigma_{t : Sum (Fin gamma) (Fin delta)} Fin (\operatorname{ShiftPencilBlocks.blockLength} p gamma delta t + 1)) \to \mathbb{Q}) (k : Fin beta) (j : Fin gamma) , (\operatorname{LinearMap.toMatrix} ' (\operatorname{ReservoirSchur.cokernelEmbedding} p alpha beta gamma delta)) . \operatorname{transpose.mulVec} z (k , j) = \sum_{t : Fin (p + 1)} ((- 1)^{\operatorname{val}\left(t\right)} \cdot z (\langle \operatorname{Sum.inr} k , \langle p - (\operatorname{val}\left(t\right)) \rangle \rangle , \langle \operatorname{Sum.inl} j , t \rangle))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.cokernel_mulVec_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

cokernel_mulVec_formula is used on the live proof path of the width-three bridge construction.

**Theorem 1.23 (slLine_kernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) (r t : Fin (p + 1)) , \operatorname{ReservoirSchur.slLine} p alpha beta gamma delta ((\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w) r t = if (\operatorname{val}\left(r\right)) + (\operatorname{val}\left(t\right)) = p then (- 1)^{p - (\operatorname{val}\left(r\right))} \cdot w else 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.slLine_kernelEmbedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

slLine_kernelEmbedding is used on the live proof path of the width-three bridge construction.

**Theorem 1.24 (sourceSL_kernelEmbedding).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) (w : Fin alpha \times Fin delta \to \mathbb{Q}) , \operatorname{ReservoirSchur.sourceSL} p alpha beta gamma delta ((\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w) = (\operatorname{ReservoirSchur.kernelEmbedding} p alpha beta gamma delta) w$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.sourceSL_kernelEmbedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

sourceSL_kernelEmbedding is used on the live proof path of the width-three bridge construction.

**Theorem 1.25 (short_short_witness).**

$$\forall (p alpha beta gamma delta : \mathbb{N}) , 0 < p \to 0 < beta \to beta \leq alpha \to 0 < delta \to delta \leq gamma \to \operatorname{QuantumMaxFlowBound.RationalWitness} (\operatorname{ShiftPencilBlocks.leftDim} p alpha beta) (\operatorname{ShiftPencilBlocks.rightDim} p alpha beta) (\operatorname{ShiftPencilBlocks.leftDim} p gamma delta) (\operatorname{ShiftPencilBlocks.rightDim} p gamma delta)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur.short_short_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The short reservoir construction resolves the strict same-depth case with alpha*delta ≤ beta*gamma, using its higher-order Schur complement.

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
