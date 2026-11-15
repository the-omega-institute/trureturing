# FrobeniusCholeskyLinear

## Abstract

Arithmetic recipes, coordinate frames and characteristic-two matrix recursion.

**Definition 1.1 (minorCoordinates).**

$$\forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{I} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{n}) , \forall (\operatorname{v} : \operatorname{Fin} \operatorname{m} \to \operatorname{F}) , \operatorname{minorCoordinates} (\operatorname{m} := \operatorname{m}) (\operatorname{n} := \operatorname{n}) (\operatorname{r} := \operatorname{r}) (\operatorname{F} := \operatorname{F}) (\operatorname{A} := \operatorname{A}) (\operatorname{I} := \operatorname{I}) (\operatorname{J} := \operatorname{J}) (\operatorname{v} := \operatorname{v}) = ((\operatorname{A} . \operatorname{submatrix} \operatorname{I} \operatorname{J}) ^{-1} *_{v} (\operatorname{v} \circ \operatorname{I}))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.2 (minorKernel).**

$$\forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{I} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{n}) , \forall (\operatorname{j} : \operatorname{Fin} \operatorname{n}) , \operatorname{minorKernel} (\operatorname{m} := \operatorname{m}) (\operatorname{n} := \operatorname{n}) (\operatorname{r} := \operatorname{r}) (\operatorname{F} := \operatorname{F}) (\operatorname{A} := \operatorname{A}) (\operatorname{I} := \operatorname{I}) (\operatorname{J} := \operatorname{J}) (\operatorname{j} := \operatorname{j}) = (\operatorname{Pi} . \operatorname{single} \operatorname{j} 1 - ((1 : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) . \operatorname{submatrix} \operatorname{id} \operatorname{J}) *_{v} \operatorname{minorCoordinates} \operatorname{A} \operatorname{I} \operatorname{J} (\operatorname{fun} \operatorname{i} \mapsto \operatorname{A} \operatorname{i} \operatorname{j}))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.3 (minorKernel mem).**

$$\forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{I} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{n}) , ((\operatorname{A} . \operatorname{submatrix} \operatorname{I} \operatorname{J}) . \operatorname{det} \neq 0) \to ((\forall \operatorname{j} , \exists \operatorname{a} : \operatorname{Fin} \operatorname{r} \to \operatorname{F} , \forall \operatorname{i} , \operatorname{A} \operatorname{i} \operatorname{j} = \sum \operatorname{k} , \operatorname{A} \operatorname{i} (\operatorname{J} \operatorname{k}) * \operatorname{a} \operatorname{k}) \to (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{n}) , \operatorname{A} *_{v} \operatorname{minorKernel} \operatorname{A} \operatorname{I} \operatorname{J} \operatorname{j} = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorKernel_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.4 (minorKernel span).**

$$\forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{I} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{n}) , (\operatorname{Function} . \operatorname{Injective} \operatorname{J}) \to (((\operatorname{A} . \operatorname{submatrix} \operatorname{I} \operatorname{J}) . \operatorname{det} \neq 0) \to ((\forall \operatorname{j} , \exists \operatorname{a} : \operatorname{Fin} \operatorname{r} \to \operatorname{F} , \forall \operatorname{i} , \operatorname{A} \operatorname{i} \operatorname{j} = \sum \operatorname{k} , \operatorname{A} \operatorname{i} (\operatorname{J} \operatorname{k}) * \operatorname{a} \operatorname{k}) \to (\operatorname{Submodule} . \operatorname{span} \operatorname{F} (\operatorname{Set} . \operatorname{range} (\operatorname{fun} \operatorname{j} : \{ \operatorname{j} / / \operatorname{j} \neg \in \operatorname{Set} . \operatorname{range} \operatorname{J} \} \mapsto \operatorname{minorKernel} \operatorname{A} \operatorname{I} \operatorname{J} \operatorname{j} . \operatorname{val})) = \operatorname{LinearMap} . \operatorname{ker} \operatorname{A} . \operatorname{mulVecLin})))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorKernel_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.5 (frameTransport).**

$$\forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{P} \operatorname{Q} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) \operatorname{F}) , \forall (\operatorname{I} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{v} : \operatorname{Fin} \operatorname{m} \to \operatorname{F}) , \operatorname{frameTransport} (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{F} := \operatorname{F}) (\operatorname{P} := \operatorname{P}) (\operatorname{Q} := \operatorname{Q}) (\operatorname{I} := \operatorname{I}) (\operatorname{v} := \operatorname{v}) = (\operatorname{Q} *_{v} \operatorname{minorCoordinates} \operatorname{P} \operatorname{I} \operatorname{id} \operatorname{v})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.frameTransport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.6 (adaptedFrame transport).**

$$\forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{k} : \mathbb{N}) , \forall (\operatorname{A} \operatorname{U} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m}) \operatorname{F}) , \forall (\operatorname{P} \operatorname{Q} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) \operatorname{F}) , \forall (\operatorname{I} \operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{S} : \operatorname{Fin} \operatorname{k} \to \operatorname{Fin} \operatorname{r}) , ((\operatorname{P} . \operatorname{submatrix} \operatorname{I} \operatorname{id}) . \operatorname{det} \neq 0) \to (((\operatorname{Q} . \operatorname{submatrix} \operatorname{J} \operatorname{id}) . \operatorname{det} \neq 0) \to ((\operatorname{LinearMap} . \operatorname{range} \operatorname{P} . \operatorname{mulVecLin} = \operatorname{LinearMap} . \operatorname{ker} \operatorname{A} . \operatorname{mulVecLin}) \to ((\operatorname{LinearMap} . \operatorname{range} \operatorname{Q} . \operatorname{mulVecLin} = \operatorname{LinearMap} . \operatorname{ker} \operatorname{U} . \operatorname{transpose} . \operatorname{mulVecLin}) \to ((\operatorname{LinearMap} . \operatorname{range} (\operatorname{P} . \operatorname{submatrix} \operatorname{id} \operatorname{S}) . \operatorname{mulVecLin} = \operatorname{LinearMap} . \operatorname{range} \operatorname{A} . \operatorname{mulVecLin}) \to ((\operatorname{LinearMap} . \operatorname{range} (\operatorname{Q} . \operatorname{submatrix} \operatorname{id} \operatorname{S}) . \operatorname{mulVecLin} = \operatorname{LinearMap} . \operatorname{range} \operatorname{U} . \operatorname{mulVecLin}) \to (\operatorname{Set} . \operatorname{BijOn} (\operatorname{frameTransport} \operatorname{P} \operatorname{Q} \operatorname{I}) \{ \operatorname{v} | \operatorname{A} *_{v} \operatorname{v} = 0 \} \{ \operatorname{w} | \operatorname{U} . \operatorname{transpose} *_{v} \operatorname{w} = 0 \} \land \forall \operatorname{v} , \operatorname{A} *_{v} \operatorname{v} = 0 \to (\operatorname{frameTransport} \operatorname{P} \operatorname{Q} \operatorname{I} \operatorname{v} \in \operatorname{LinearMap} . \operatorname{range} \operatorname{U} . \operatorname{mulVecLin} \iff \operatorname{v} \in \operatorname{LinearMap} . \operatorname{range} \operatorname{A} . \operatorname{mulVecLin})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.adaptedFrame_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.7 (selectedColumns independent).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \operatorname{LinearIndependent} \operatorname{F} (\operatorname{A} . \operatorname{submatrix} \operatorname{id} ((((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) \operatorname{A} . \operatorname{col} \emptyset (\operatorname{List} . \operatorname{ofFn} \operatorname{id}))) . \operatorname{orderEmbOfFin} \operatorname{rfl}))) . \operatorname{col}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selectedColumns_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.8 (selectedColumns span).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \operatorname{span} \operatorname{F} (\operatorname{Set} . \operatorname{range} (\operatorname{A} . \operatorname{submatrix} \operatorname{id} ((((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) \operatorname{A} . \operatorname{col} \emptyset (\operatorname{List} . \operatorname{ofFn} \operatorname{id}))) . \operatorname{orderEmbOfFin} \operatorname{rfl}))) . \operatorname{col}) = \operatorname{span} \operatorname{F} (\operatorname{Set} . \operatorname{range} \operatorname{A} . \operatorname{col})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selectedColumns_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.9 (selectedIndices card).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , ((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) \operatorname{A} . \operatorname{col} \emptyset (\operatorname{List} . \operatorname{ofFn} \operatorname{id}))) . \operatorname{card} = \operatorname{A} . \operatorname{rank}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selectedIndices_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.10 (selected columns reconstruct).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall \operatorname{j} , \exists \operatorname{a} : \operatorname{Fin} ((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) \operatorname{A} . \operatorname{col} \emptyset (\operatorname{List} . \operatorname{ofFn} \operatorname{id}))) . \operatorname{card} \to \operatorname{F} , \forall \operatorname{i} , \operatorname{A} \operatorname{i} \operatorname{j} = \sum \operatorname{k} , \operatorname{A} \operatorname{i} ((((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) \operatorname{A} . \operatorname{col} \emptyset (\operatorname{List} . \operatorname{ofFn} \operatorname{id}))) . \operatorname{orderEmbOfFin} \operatorname{rfl}) \operatorname{k}) * \operatorname{a} \operatorname{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selected_columns_reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.11 (minorRowCodes).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) \operatorname{F}) , \operatorname{minorRowCodes} (\operatorname{F} := \operatorname{F}) (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{A} := \operatorname{A}) = (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{A} . \operatorname{submatrix} ((\operatorname{Fintype} . \operatorname{equivFin} (\operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m})) . \operatorname{symm} \operatorname{i}) \operatorname{id}) . \operatorname{det} \neq 0))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorRowCodes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.12 (minorRowCodesNonempty).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) \operatorname{F}) , (\operatorname{LinearIndependent} \operatorname{F} \operatorname{A} . \operatorname{col}) \to ((\operatorname{minorRowCodes} \operatorname{A}) . \operatorname{Nonempty})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorRowCodesNonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.13 (firstMinorRows).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) \operatorname{F}) , \forall (\operatorname{hA} : \operatorname{LinearIndependent} \operatorname{F} \operatorname{A} . \operatorname{col}) , \operatorname{firstMinorRows} (\operatorname{F} := \operatorname{F}) (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{A} := \operatorname{A}) (\operatorname{hA} := \operatorname{hA}) = ((\operatorname{Fintype} . \operatorname{equivFin} (\operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m})) . \operatorname{symm} ((\operatorname{minorRowCodes} \operatorname{A}) . \operatorname{min} ' (\operatorname{minorRowCodesNonempty} \operatorname{A} \operatorname{hA})))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.firstMinorRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.14 (firstMinorRows det).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) \operatorname{F}) , \forall (\operatorname{hA} : \operatorname{LinearIndependent} \operatorname{F} \operatorname{A} . \operatorname{col}) , (\operatorname{A} . \operatorname{submatrix} (\operatorname{firstMinorRows} \operatorname{A} \operatorname{hA}) \operatorname{id}) . \operatorname{det} \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.firstMinorRows_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.15 (adaptedIndices spec).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{V} : \operatorname{Type}) , [ \operatorname{AddCommGroup} \operatorname{V} ] , [ \operatorname{Module} \operatorname{F} \operatorname{V} ] , \forall (\operatorname{a} \operatorname{b} : \mathbb{N}) , \forall (\operatorname{v} : \operatorname{Fin} \operatorname{a} \to \operatorname{V}) , \forall (\operatorname{w} : \operatorname{Fin} \operatorname{b} \to \operatorname{V}) , (\operatorname{LinearIndependent} \operatorname{F} \operatorname{v}) \to (\forall (\operatorname{p} : \operatorname{Submodule} \operatorname{F} \operatorname{V}) , (\forall \operatorname{i} , \operatorname{v} \operatorname{i} \in \operatorname{p}) \to ((\operatorname{span} \operatorname{F} (\operatorname{Set} . \operatorname{range} \operatorname{w}) = \operatorname{p}) \to (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} \operatorname{Sum} . \operatorname{inl} \subseteq (\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) (\operatorname{Sum} . \operatorname{elim} \operatorname{v} \operatorname{w}) (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} \operatorname{Sum} . \operatorname{inl}) (\operatorname{List} . \operatorname{ofFn} (\operatorname{fun} \operatorname{j} \mapsto \operatorname{Sum} . \operatorname{inr} \operatorname{j}))) \land \operatorname{LinearIndepOn} \operatorname{F} (\operatorname{Sum} . \operatorname{elim} \operatorname{v} \operatorname{w}) ((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) (\operatorname{Sum} . \operatorname{elim} \operatorname{v} \operatorname{w}) (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} \operatorname{Sum} . \operatorname{inl}) (\operatorname{List} . \operatorname{ofFn} (\operatorname{fun} \operatorname{j} \mapsto \operatorname{Sum} . \operatorname{inr} \operatorname{j}))) : \operatorname{Set} (\operatorname{Sum} (\operatorname{Fin} \operatorname{a}) (\operatorname{Fin} \operatorname{b}))) \land \operatorname{span} \operatorname{F} ((\operatorname{Sum} . \operatorname{elim} \operatorname{v} \operatorname{w}) '' ((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) (\operatorname{Sum} . \operatorname{elim} \operatorname{v} \operatorname{w}) (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} \operatorname{Sum} . \operatorname{inl}) (\operatorname{List} . \operatorname{ofFn} (\operatorname{fun} \operatorname{j} \mapsto \operatorname{Sum} . \operatorname{inr} \operatorname{j}))) : \operatorname{Set} (\operatorname{Sum} (\operatorname{Fin} \operatorname{a}) (\operatorname{Fin} \operatorname{b})))) = \operatorname{p} \land ((\operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) (\operatorname{Sum} . \operatorname{elim} \operatorname{v} \operatorname{w}) (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} \operatorname{Sum} . \operatorname{inl}) (\operatorname{List} . \operatorname{ofFn} (\operatorname{fun} \operatorname{j} \mapsto \operatorname{Sum} . \operatorname{inr} \operatorname{j})))) . \operatorname{card} = \operatorname{Module} . \operatorname{finrank} \operatorname{F} \operatorname{p})))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.adaptedIndices_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

## References

- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.adaptedFrame_transport`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.adaptedIndices_spec`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.firstMinorRows`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.firstMinorRows_det`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.frameTransport`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorCoordinates`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorKernel`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorKernel_mem`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorKernel_span`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorRowCodes`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.minorRowCodesNonempty`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selectedColumns_independent`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selectedColumns_span`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selectedIndices_card`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyLinear.selected_columns_reconstruct`
- Dependency: [D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis](../Estimation/ExperimentCost/MinimumCostRoleBasis.md)
- Dependency: [D5/S3/QuadraticForms/FrobeniusCholeskyRecipes](FrobeniusCholeskyRecipes.md)
