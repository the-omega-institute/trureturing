# QuantumMaxFlowBound

## Abstract

QuantumMaxFlowBound supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Definition 1.1 (flow).**

$$\forall (K : Type) [CommSemiring K] (a b c d : \mathbb{N}) (M : Fin 3 \to Matrix (Fin a) (Fin b) K) (N : Fin 3 \to Matrix (Fin d) (Fin c) K) , \operatorname{QuantumMaxFlowBound.flow} M N = (\sum_{r : Fin 3} ((M r) . kronecker (N r)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.flow` (`✓ std3`).

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

Page 3: “Let F_{T,T′} ∈ A ⊗ B ⊗ A′ ⊗ B′ be the tensor obtained by contracting the factor W of T with the factor W* of T′; this is the tensor network state defined by T and T′ on the bridge graph.” For width three the flow matrix is the sum of three Kronecker products. Its dimensions are a*d by b*c. With (a,b,c,d)=(a,b,a′,b′), it is the transpose of the source flattening (A ⊗ B′)* → B ⊗ A′; transpose preserves rank.

**Definition 1.2 (attainable).**

$$\forall (a b c d : \mathbb{N}) , \operatorname{QuantumMaxFlowBound.attainable} a b c d = (\{r : \mathbb{N} | \exists (M : Fin 3 \to Matrix (Fin a) (Fin b) \mathbb{C}) (N : Fin 3 \to Matrix (Fin d) (Fin c) \mathbb{C}) , (\operatorname{QuantumMaxFlowBound.flow} M N) . rank = r\})$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.attainable` (`✓ std3`).

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

Attainable is the set of natural ranks of the literal width-three complex flow matrices.

**Definition 1.3 (QMaxFlow).**

$$\forall (a b c d : \mathbb{N}) , \operatorname{QuantumMaxFlowBound.QMaxFlow} a b c d = (sSup (\operatorname{QuantumMaxFlowBound.attainable} a b c d))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMaxFlow` (`✓ std3`).

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

Page 3: “The quantum max-flow is the maximum possible value of rank(F_{T,T′}) as T and T′ vary in the respective spaces; we write”. The source then displays the maximum over T ∈ A ⊗ B ⊗ W and T′ ∈ A′ ⊗ B′ ⊗ W*. Here the attained supremum of the finite nonempty natural rank set gives that maximum.

**Definition 1.4 (QMinCut).**

$$\forall (a b c d : \mathbb{N}) , \operatorname{QuantumMaxFlowBound.QMinCut} a b c d = (min (3 \cdot a \cdot c) (min (a \cdot d) (b \cdot c)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMinCut` (`✓ std3`).

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

Proposition 2.4, page 9: “Let a, b, w, a′, b′ be integers with a ≤ b, a′ ≤ b′. The quantum min-cut in the bridge graph is” followed by QMinCut = min{aa′w, ab′, a′b}. This is the ordered-case cut formula: its identification with the graph min-cut is used under a ≤ b and c ≤ d, as in claim. The Lean letters (a,b,c,d) denote (a,b,a′,b′) and the bridge width is three.

**Theorem 1.5 (QMaxFlow_attained).**

$$\forall (a b c d : \mathbb{N}) , \exists (M : Fin 3 \to Matrix (Fin a) (Fin b) \mathbb{C}) (N : Fin 3 \to Matrix (Fin d) (Fin c) \mathbb{C}) , (\operatorname{QuantumMaxFlowBound.flow} M N) . rank = \operatorname{QuantumMaxFlowBound.QMaxFlow} a b c d$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMaxFlow_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

QMaxFlow_attained is used on the live proof path of the width-three bridge construction.

**Theorem 1.6 (rank_le_QMaxFlow).**

$$\forall \{a b c d : \mathbb{N}\} (M : Fin 3 \to Matrix (Fin a) (Fin b) \mathbb{C}) (N : Fin 3 \to Matrix (Fin d) (Fin c) \mathbb{C}) , (\operatorname{QuantumMaxFlowBound.flow} M N) . rank \leq \operatorname{QuantumMaxFlowBound.QMaxFlow} a b c d$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.rank_le_QMaxFlow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

rank_le_QMaxFlow is used on the live proof path of the width-three bridge construction.

**Theorem 1.7 (QMaxFlow_le_QMinCut).**

$$\forall (a b c d : \mathbb{N}) , \operatorname{QuantumMaxFlowBound.QMaxFlow} a b c d \leq \operatorname{QuantumMaxFlowBound.QMinCut} a b c d$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMaxFlow_le_QMinCut` (`✓ std3`). ∎

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

QMaxFlow_le_QMinCut is used on the live proof path of the width-three bridge construction.

**Theorem 1.8 (cone_bounds).**

$$\forall \{a b : \mathbb{N}\} , 0 < a \to a \cdot a + b \cdot b \leq 3 \cdot a \cdot b \to b < 3 \cdot a$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.cone_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

cone_bounds is used on the live proof path of the width-three bridge construction.

**Theorem 1.9 (cone_QMinCut).**

$$\forall \{a b c d : \mathbb{N}\} , 0 < a \to 0 < c \to a \cdot a + b \cdot b \leq 3 \cdot a \cdot b \to c \cdot c + d \cdot d \leq 3 \cdot c \cdot d \to \operatorname{QuantumMaxFlowBound.QMinCut} a b c d = min (a \cdot d) (b \cdot c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.cone_QMinCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

cone_QMinCut is used on the live proof path of the width-three bridge construction.

**Definition 1.10 (RationalWitness).**

$$\forall (a b c d : \mathbb{N}) , \operatorname{QuantumMaxFlowBound.RationalWitness} a b c d = (\exists (M : Fin 3 \to Matrix (Fin a) (Fin b) \mathbb{Q}) (N : Fin 3 \to Matrix (Fin d) (Fin c) \mathbb{Q}) , (\operatorname{QuantumMaxFlowBound.flow} M N) . rank = min (a \cdot d) (b \cdot c))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.RationalWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes RationalWitness for the consumed QuantumMaxFlowBound construction.

**Theorem 1.11 (rationalWitness_full_rank).**

$$\forall \{a b c d : \mathbb{N}\} , \operatorname{QuantumMaxFlowBound.RationalWitness} a b c d \to \operatorname{QuantumMaxFlowBound.QMaxFlow} a b c d = min (a \cdot d) (b \cdot c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.rationalWitness_full_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

rationalWitness_full_rank is used on the live proof path of the width-three bridge construction.

**Definition 1.12 (BaseWitness).**

$$\operatorname{QuantumMaxFlowBound.BaseWitness} \iff (\forall (a b c d : \mathbb{N}) , 0 < a \to a < b \to b < 2 \cdot a \to 0 < c \to c < d \to d < 2 \cdot c \to \operatorname{QuantumMaxFlowBound.RationalWitness} a b c d)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.BaseWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes BaseWitness for the consumed QuantumMaxFlowBound construction.

**Definition 1.13 (Castling).**

$$\operatorname{QuantumMaxFlowBound.Castling} \iff (\forall (a b c d : \mathbb{N}) , a \leq 3 \cdot b \to c \leq 3 \cdot d \to ((a \cdot d : \mathbb{N}) : \mathbb{Z}) - (\operatorname{QuantumMaxFlowBound.QMaxFlow} a b c d : \mathbb{Z}) = ((b \cdot (3 \cdot d - c) : \mathbb{N}) : \mathbb{Z}) - (\operatorname{QuantumMaxFlowBound.QMaxFlow} b (3 \cdot b - a) d (3 \cdot d - c) : \mathbb{Z}))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.Castling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes Castling for the consumed QuantumMaxFlowBound construction.

**Definition 1.14 (WidthTwo).**

$$\operatorname{QuantumMaxFlowBound.WidthTwo} \iff (\forall (a b c d : \mathbb{N}) , 0 < a \to a \leq b \to 0 < c \to c \leq d \to (a = b \lor c = d \lor (2 \cdot a \leq b \land d \leq 2 \cdot c) \lor (b \leq 2 \cdot a \land 2 \cdot c \leq d)) \to \operatorname{QuantumMaxFlowBound.RationalWitness} a b c d)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.WidthTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes WidthTwo for the consumed QuantumMaxFlowBound construction.

**Definition 1.15 (threeSlices).**

$$\forall (m : Type) (n : Type) (A B C : Matrix m n \mathbb{Q}) (r : Fin 3) , \operatorname{QuantumMaxFlowBound.threeSlices} A B C r = (if r = 0 then A else if r = 1 then B else C)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.threeSlices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes threeSlices for the consumed QuantumMaxFlowBound construction.

**Theorem 1.16 (typed_three_slice_flow).**

$$\forall \{I : Type\} \{J : Type\} \{K : Type\} \{L : Type\} (A B C : Matrix I J \mathbb{Q}) (D E F : Matrix L K \mathbb{Q}) , \sum_{r : Fin 3} ((\operatorname{QuantumMaxFlowBound.threeSlices} A B C r) . kronecker (\operatorname{QuantumMaxFlowBound.threeSlices} D E F r)) = \operatorname{A.kronecker} D + \operatorname{B.kronecker} E + \operatorname{C.kronecker} F$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.typed_three_slice_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

typed_three_slice_flow is used on the live proof path of the width-three bridge construction.

**Definition 1.17 (rectId).**

$$\forall (m n : \mathbb{N}) , \operatorname{QuantumMaxFlowBound.rectId} m n = (\operatorname{Matrix.submatrix} 1 \operatorname{Fin.val} \operatorname{Fin.val})$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.rectId` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression fixes rectId for the consumed QuantumMaxFlowBound construction.

**Theorem 1.18 (witness_swap).**

$$\forall \{a b c d : \mathbb{N}\} , \operatorname{QuantumMaxFlowBound.RationalWitness} a b c d \to \operatorname{QuantumMaxFlowBound.RationalWitness} c d a b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.witness_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

witness_swap is used on the live proof path of the width-three bridge construction.

**Theorem 1.19 (widthTwo_proved).**

$$\operatorname{QuantumMaxFlowBound.WidthTwo}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.widthTwo_proved` (`✓ std3`). ∎

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

widthTwo_proved is used on the live proof path of the width-three bridge construction.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.BaseWitness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.Castling`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMaxFlow`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMaxFlow_attained`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMaxFlow_le_QMinCut`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.QMinCut`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.RationalWitness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.WidthTwo`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.attainable`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.cone_QMinCut`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.cone_bounds`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.flow`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.rank_le_QMaxFlow`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.rationalWitness_full_rank`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.rectId`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.threeSlices`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.typed_three_slice_flow`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.widthTwo_proved`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.witness_swap`
