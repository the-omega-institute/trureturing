# Finite Hilbert Memory

## Abstract

A fixed emission isometry on any finite complex memory has one fixed unitary circuit realization for every word.

H is a complex inner product space. Space(I) is the complex Euclidean space on a finite type I, with its standard orthonormal alphabet basis. Tensor denotes the complex Hilbert tensor product; tmul is a pure tensor and smul is complex scalar multiplication. coefficients(I) is a linear equivalence from Space(I) tensor H to I-indexed H-valued coefficients. It uses no basis of H. Its inverse reconstructs the tensor exactly, including every complex phase.

**Definition 1.1 (coefficients).**

$$\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall I \in Type,\; Fintype\left(I\right) \Rightarrow coefficients\left(I\right) = composeEquivalences\left(equivFinsuppOfBasisLeft\left(toBasis\left(alphabetBasis\left(I\right)\right)\right), linearEquivFunOnFinite\left(\mathbb{C}, H, I\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/FiniteMemory.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the tensor coefficient equivalence for the alphabet basis with the equivalence between finite-support functions and functions on a finite type.

**Theorem 1.2 (coefficients_tmul).**

$$\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall I \in Type,\; Fintype\left(I\right) \Rightarrow \left(\forall z \in Space\left(I\right),\; \forall x \in H,\; \forall i \in I,\; coefficients\left(I, tmul\left(z, x\right), i\right) = smul\left(z\left(i\right), x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.coefficients_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The memory coefficient of a pure tensor z tensor x at i is z(i) times x.

A is a finite alphabet and V is one fixed linear isometry from H to Space(A) tensor H. wordMemory(V,w) is a linear map on H: the empty word acts as the identity, and a first symbol reads that coefficient of V before the rest of the word is processed. Words(n) means functions from Fin(n) to A; ofFn lists their symbols in order. output(V,n,x) belongs to Space(Words(n)) tensor H. The zero and successor identities specify repeated emission in this word-indexed presentation, using the same V at every step.

**Definition 1.3 (wordMemory).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \left(\forall x \in H,\; wordMemory\left(V, nil\left(\right), x\right) = x\right) \land \left(\forall i \in A,\; \forall w \in List\left(A\right),\; \forall x \in H,\; wordMemory\left(V, cons\left(i, w\right), x\right) = wordMemory\left(V, w, coefficients\left(A, V\left(x\right), i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/FiniteMemory.wordMemory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equations define the ordered iteration as a linear map.

**Definition 1.4 (output).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall n \in \mathbb{N},\; \forall x \in H,\; output\left(V, n, x\right) = inverse\left(coefficients\left(Fin\left(n\right) \to A\right), w:Fin\left(n\right) \to A \mapsto wordMemory\left(V, ofFn\left(w\right), x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reconstruct the full tensor from the memory reached at every word.

**Theorem 1.5 (output_coefficients).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall n \in \mathbb{N},\; \forall x \in H,\; \forall w \in Fin\left(n\right) \to A,\; coefficients\left(Fin\left(n\right) \to A, output\left(V, n, x\right), w\right) = wordMemory\left(V, ofFn\left(w\right), x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extraction is inverse to reconstruction, so each output coefficient is its word memory.

**Theorem 1.6 (output_zero).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall x \in H,\; \forall w \in Fin\left(0\right) \to A,\; coefficients\left(Fin\left(0\right) \to A, output\left(V, 0, x\right), w\right) = x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before any emission, the sole empty-word coefficient is the initial memory.

**Theorem 1.7 (output_succ).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall n \in \mathbb{N},\; \forall x \in H,\; \forall w \in Fin\left(n + 1\right) \to A,\; coefficients\left(Fin\left(n + 1\right) \to A, output\left(V, n + 1, x\right), w\right) = coefficients\left(Fin\left(n\right) \to A, output\left(V, n, coefficients\left(A, V\left(x\right), w\left(0\right)\right)\right), tail\left(w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a word of length n plus one, first apply V and read its first symbol, then emit the tail of length n. tail removes the first coordinate.

**Theorem 1.8 (output_eq_tmul_iff).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall n \in \mathbb{N},\; \forall x \in H,\; \forall f \in H,\; \forall psi \in Space\left(Fin\left(n\right) \to A\right),\; output\left(V, n, x\right) = tmul\left(psi, f\right) \Leftrightarrow \left(\forall w \in Fin\left(n\right) \to A,\; wordMemory\left(V, ofFn\left(w\right), x\right) = smul\left(psi\left(w\right), f\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_eq_tmul_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tensor output factors through one common f exactly when every word memory equals the corresponding scalar coefficient times that same f. There are no word-dependent phases or choices of final memory.

**Theorem 1.9 (output_tensor_step).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall n \in \mathbb{N},\; \forall x \in H,\; tensorMap\left(linearIdentity\left(Space\left(Fin\left(n\right) \to A\right)\right), V, output\left(V, n, x\right)\right) = inverse\left(coefficients\left(Fin\left(n\right) \to A\right), w:Fin\left(n\right) \to A \mapsto inverse\left(coefficients\left(A\right), i:A \mapsto coefficients\left(Fin\left(n + 1\right) \to A, output\left(V, n + 1, x\right), snoc\left(w, i\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_tensor_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the identity tensor V to the n-symbol output gives the next output, regrouped as an n-symbol word followed by one symbol. snoc(w,i) appends i to w. The outer coefficient inverse has values in Space(A) tensor H; the inner inverse has values in H. Both are exact equivalences, and every word has the unique split into its initial segment and last symbol. This identifies the word presentation with the tensor operation at every stage.

Now H is finite-dimensional over the complex numbers, and K is Fin(finrank(C,H)). coordinates(H) is an isometric linear equivalence from H to Space(K). tensorCoordinates(H,I) is an isometric linear equivalence from Space(I) tensor H to Space(I times K), formed from the tensor product orthonormal basis. Thus K has exactly the dimension of H, including zero.

**Definition 1.10 (coordinates).**

$$\forall H \in Type,\; \left(\left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \land FiniteDimensional\left(\mathbb{C}, H\right)\right) \Rightarrow coordinates\left(H\right) = repr\left(stdOrthonormalBasis\left(\mathbb{C}, H\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/FiniteMemory.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the representation of the finite-dimensional orthonormal basis.

**Definition 1.11 (tensorCoordinates).**

$$\forall H \in Type,\; \left(\left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \land FiniteDimensional\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall I \in Type,\; Fintype\left(I\right) \Rightarrow tensorCoordinates\left(H, I\right) = repr\left(tensorProductBasis\left(alphabetBasis\left(I\right), stdOrthonormalBasis\left(\mathbb{C}, H\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/FiniteMemory.tensorCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the representation of the alphabet basis tensor the memory basis.

**Theorem 1.12 (tensorCoordinates_apply).**

$$\forall H \in Type,\; \left(\left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \land FiniteDimensional\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall I \in Type,\; Fintype\left(I\right) \Rightarrow \left(\forall z \in Tensor\left(\mathbb{C}, Space\left(I\right), H\right),\; \forall i \in I,\; \forall k \in Fin\left(finrank\left(\mathbb{C}, H\right)\right),\; tensorCoordinates\left(H, I, z\right)\left(pair\left(i, k\right)\right) = coordinates\left(H, coefficients\left(I, z, i\right)\right)\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.tensorCoordinates_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking a joint coordinate is the same as extracting the original H-valued coefficient and then taking its memory coordinate. Pure tensors give the identity, and linearity extends it to every tensor.

**Theorem 1.13 (exists_fixed_unitary).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(\left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \land FiniteDimensional\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall blank \in A,\; \forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \exists U \in Unitary\left(Product\left(A, Fin\left(finrank\left(\mathbb{C}, H\right)\right)\right)\right),\; \left(\forall x \in H,\; emission\left(blank, U, coordinates\left(H, x\right)\right) = tensorCoordinates\left(H, A, V\left(x\right)\right)\right) \land \left(\left(\forall w \in List\left(A\right),\; \forall x \in H,\; prefixMemory\left(blank, U, w, coordinates\left(H, x\right)\right) = coordinates\left(H, wordMemory\left(V, w, x\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall x \in H,\; circuit\left(s:\mathbb{N} \mapsto U, n, t, initialized\left(blank, n, coordinates\left(H, x\right)\right)\right) = tensorCoordinates\left(H, Fin\left(n\right) \to A, output\left(V, n, x\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.exists_fixed_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any blank symbol. The blank embedding and the coordinate form of V are two isometric embeddings into the same finite-dimensional joint space. A unitary agrees with them. Their letter maps intertwine, so induction on the word gives the middle equality. The actual circuit coefficient theorem then gives the last vector equality for every length, starting time and x. The schedule in circuit is the constant function with value U.

**Theorem 1.14 (output_norm).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(\left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \land FiniteDimensional\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\forall blank \in A,\; \forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall n \in \mathbb{N},\; \forall x \in H,\; norm\left(output\left(V, n, x\right)\right) = norm\left(x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full circuit, initialization and coordinate equivalences preserve norms. Their output equality proves that the repeated emission preserves the norm of x.

For the lower bound A is finite, nonempty and has decidable equality. sector(n,a) is the Euclidean vector with coefficients sectorVector(n,a): the reciprocal square root of the occupation multiplicity on words with occupation a, and zero elsewhere. Both initial x and final f have norm one. The final f is common to every word and need not be a prescribed reset. The subtraction in the dimension bound is natural-number subtraction; sup is the maximum over the finite nonempty alphabet.

**Theorem 1.15 (stationary_memory_dimension_lower_bound).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(\left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \land FiniteDimensional\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall x \in H,\; \forall f \in H,\; \left(norm\left(x\right) = 1 \land \left(norm\left(f\right) = 1 \land output\left(V, card\left(a\right), x\right) = tmul\left(sector\left(card\left(a\right), a\right), f\right)\right)\right) \Rightarrow \prod_{i:A}{count\left(a, i\right) + 1} - sup\left(univ\left(A\right), i:A \mapsto count\left(a, i\right)\right) \le finrank\left(\mathbb{C}, H\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.stationary_memory_dimension_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the exact tensor output to the fixed-blank, constant-unitary circuit. coordinates preserves both endpoint norms and the common f. Applying the physical stationary bound gives the displayed dimension bound. Zero occupation is included; a unit initial vector excludes zero-dimensional H.

**Definition 1.16 (capacityOccupation).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall a \in A \to \mathbb{N},\; capacityOccupation\left(a\right) = toMultiset\left(inverse\left(equivFunOnFinite\left(\right), a\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/FiniteMemory.capacityOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural-valued capacity function gives a finite-support function and hence a multiset. Zero capacities are retained without any positivity assumption.

**Theorem 1.17 (count_capacityOccupation).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(DecidableEq\left(A\right) \Rightarrow \left(\forall a \in A \to \mathbb{N},\; \forall i \in A,\; count\left(capacityOccupation\left(a\right), i\right) = a\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.count_capacityOccupation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiset count at each alphabet symbol is exactly the supplied capacity.

**Theorem 1.18 (card_capacityOccupation).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall a \in A \to \mathbb{N},\; card\left(capacityOccupation\left(a\right)\right) = \sum_{i:A}{a\left(i\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.card_capacityOccupation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of emissions is exactly the sum of the capacities.

**Theorem 1.19 (stationary_capacity_dimension_lower_bound).**

$$\forall A \in Type,\; Fintype\left(A\right) \Rightarrow \left(\forall H \in Type,\; \left(\left(NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right)\right) \land FiniteDimensional\left(\mathbb{C}, H\right)\right) \Rightarrow \left(\left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right) \Rightarrow \left(\forall a \in A \to \mathbb{N},\; \forall V \in LinearIsometry\left(\mathbb{C}, H, Tensor\left(\mathbb{C}, Space\left(A\right), H\right)\right),\; \forall x \in H,\; \forall f \in H,\; \left(norm\left(x\right) = 1 \land \left(norm\left(f\right) = 1 \land output\left(V, card\left(capacityOccupation\left(a\right)\right), x\right) = tmul\left(sector\left(card\left(capacityOccupation\left(a\right)\right), capacityOccupation\left(a\right)\right), f\right)\right)\right) \Rightarrow \prod_{i:A}{a\left(i\right) + 1} - sup\left(univ\left(A\right), a\right) \le finrank\left(\mathbb{C}, H\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/FiniteMemory.stationary_capacity_dimension_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the multiset theorem to capacityOccupation(a) and substitute its counts. The output still uses the same fixed V, unit endpoints and exact common-memory tensor equation.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.capacityOccupation`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.card_capacityOccupation`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.coefficients`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.coefficients_tmul`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.coordinates`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.count_capacityOccupation`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.exists_fixed_unitary`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_coefficients`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_eq_tmul_iff`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_norm`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_succ`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_tensor_step`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.output_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.stationary_capacity_dimension_lower_bound`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.stationary_memory_dimension_lower_bound`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.tensorCoordinates`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.tensorCoordinates_apply`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/FiniteMemory.wordMemory`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PhysicalGram](PhysicalGram.md)
