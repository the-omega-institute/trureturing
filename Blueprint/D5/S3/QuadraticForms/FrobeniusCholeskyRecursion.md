# FrobeniusCholeskyRecursion

## Abstract

Arithmetic recipes, coordinate frames and characteristic-two matrix recursion.

**Definition 1.1 (border).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{w} : \operatorname{Fin} \operatorname{n} \to \operatorname{F}) , \forall (\operatorname{c} : \operatorname{F}) , \operatorname{border} (\operatorname{n} := \operatorname{n}) (\operatorname{F} := \operatorname{F}) (\operatorname{A} := \operatorname{A}) (\operatorname{w} := \operatorname{w}) (\operatorname{c} := \operatorname{c}) = ((\operatorname{Matrix} . \operatorname{fromBlocks} \operatorname{A} (\operatorname{Matrix} . \operatorname{replicateCol} (\operatorname{Fin} 1) \operatorname{w}) (0 : \operatorname{Matrix} (\operatorname{Fin} 1) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) (\operatorname{Matrix} . \operatorname{replicateCol} (\operatorname{Fin} 1) (\operatorname{Function} . \operatorname{const} (\operatorname{Fin} 1) \operatorname{c}))) . \operatorname{submatrix} \operatorname{finSumFinEquiv} . \operatorname{symm} \operatorname{finSumFinEquiv} . \operatorname{symm})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.border` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.2 (recursiveStep).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{f} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F} \to \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\psi : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F} \to (\operatorname{Fin} \operatorname{n} \to \operatorname{F}) \to (\operatorname{Fin} \operatorname{n} \to \operatorname{F})) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{Fin} (\operatorname{n} + 1)) \operatorname{F}) , \operatorname{recursiveStep} (\operatorname{n} := \operatorname{n}) (\operatorname{F} := \operatorname{F}) (\operatorname{f} := \operatorname{f}) (\psi := \psi) (\operatorname{X} := \operatorname{X}) = (\operatorname{let} \operatorname{w} := \psi ((\operatorname{fun} \operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{Fin} (\operatorname{n} + 1)) \operatorname{F} \mapsto \operatorname{X} . \operatorname{submatrix} \operatorname{Fin} . \operatorname{castSucc} \operatorname{Fin} . \operatorname{castSucc}) \operatorname{X}) ((\operatorname{fun} \operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{Fin} (\operatorname{n} + 1)) \operatorname{F} \mapsto \operatorname{fun} \operatorname{i} : \operatorname{Fin} \operatorname{n} \mapsto \operatorname{X} \operatorname{i} . \operatorname{castSucc} (\operatorname{Fin} . \operatorname{last} \operatorname{n})) \operatorname{X}) ; \operatorname{border} (\operatorname{f} ((\operatorname{fun} \operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{Fin} (\operatorname{n} + 1)) \operatorname{F} \mapsto \operatorname{X} . \operatorname{submatrix} \operatorname{Fin} . \operatorname{castSucc} \operatorname{Fin} . \operatorname{castSucc}) \operatorname{X})) \operatorname{w} (\sum \operatorname{i} , \operatorname{w} \operatorname{i}))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.3 (recursiveStep bijOn).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{CharP} \operatorname{F} 2 ] , \forall (\operatorname{f} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F} \to \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\psi : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F} \to (\operatorname{Fin} \operatorname{n} \to \operatorname{F}) \to (\operatorname{Fin} \operatorname{n} \to \operatorname{F})) , (\operatorname{Set} . \operatorname{BijOn} \operatorname{f} (\operatorname{B} \operatorname{F} \operatorname{n}) (\operatorname{C} \operatorname{F} \operatorname{n})) \to ((\forall \operatorname{A} \in \operatorname{B} \operatorname{F} \operatorname{n} , \operatorname{Set} . \operatorname{BijOn} (\psi \operatorname{A}) \{ \operatorname{v} | \operatorname{A} *_{v} \operatorname{v} = 0 \} \{ \operatorname{w} | (\operatorname{f} \operatorname{A}) . \operatorname{transpose} *_{v} \operatorname{w} = 0 \}) \to (\operatorname{Set} . \operatorname{BijOn} (\operatorname{recursiveStep} \operatorname{f} \psi) (\operatorname{B} \operatorname{F} (\operatorname{n} + 1)) (\operatorname{C} \operatorname{F} (\operatorname{n} + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveStep_bijOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.4 (recursiveStep rank).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{CharP} \operatorname{F} 2 ] , \forall (\operatorname{f} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F} \to \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\psi : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F} \to (\operatorname{Fin} \operatorname{n} \to \operatorname{F}) \to (\operatorname{Fin} \operatorname{n} \to \operatorname{F})) , (\operatorname{Set} . \operatorname{MapsTo} \operatorname{f} (\operatorname{B} \operatorname{F} \operatorname{n}) (\operatorname{C} \operatorname{F} \operatorname{n})) \to ((\forall \operatorname{A} \in \operatorname{B} \operatorname{F} \operatorname{n} , (\operatorname{f} \operatorname{A}) . \operatorname{rank} = \operatorname{A} . \operatorname{rank}) \to ((\forall \operatorname{A} \in \operatorname{B} \operatorname{F} \operatorname{n} , \forall \operatorname{v} , \operatorname{A} *_{v} \operatorname{v} = 0 \to (\psi \operatorname{A} \operatorname{v} \in \operatorname{LinearMap} . \operatorname{range} (\operatorname{f} \operatorname{A}) . \operatorname{mulVecLin} \iff \operatorname{v} \in \operatorname{LinearMap} . \operatorname{range} \operatorname{A} . \operatorname{mulVecLin})) \to (\forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{Fin} (\operatorname{n} + 1)) \operatorname{F}) , (\operatorname{X} \in \operatorname{B} \operatorname{F} (\operatorname{n} + 1)) \to ((\operatorname{recursiveStep} \operatorname{f} \psi \operatorname{X}) . \operatorname{rank} = \operatorname{X} . \operatorname{rank}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveStep_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.5 (Recipe.rename).**

$$\forall (\operatorname{k} \operatorname{n} : \mathbb{N}) , \forall (\operatorname{I} \operatorname{J} : \operatorname{Fin} \operatorname{k} \to \operatorname{Fin} \operatorname{n}) , \operatorname{Recipe} . \operatorname{rename} (\operatorname{k} := \operatorname{k}) (\operatorname{n} := \operatorname{n}) (\operatorname{I} := \operatorname{I}) (\operatorname{J} := \operatorname{J}) = (\operatorname{fun} | \operatorname{Recipe} . \operatorname{zero} \mapsto \operatorname{Recipe} . \operatorname{zero} | \operatorname{Recipe} . \operatorname{one} \mapsto \operatorname{Recipe} . \operatorname{one} | \operatorname{Recipe} . \operatorname{entry} \operatorname{i} \operatorname{j} \mapsto \operatorname{Recipe} . \operatorname{entry} (\operatorname{I} \operatorname{i}) (\operatorname{J} \operatorname{j}) | \operatorname{Recipe} . \operatorname{add} \operatorname{a} \operatorname{b} \mapsto \operatorname{Recipe} . \operatorname{add} (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{a}) (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{b}) | \operatorname{Recipe} . \operatorname{mul} \operatorname{a} \operatorname{b} \mapsto \operatorname{Recipe} . \operatorname{mul} (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{a}) (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{b}) | \operatorname{Recipe} . \operatorname{inv} \operatorname{a} \mapsto \operatorname{Recipe} . \operatorname{inv} (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{a}) | \operatorname{Recipe} . \operatorname{iteZero} \operatorname{a} \operatorname{b} \operatorname{c} \mapsto \operatorname{Recipe} . \operatorname{iteZero} (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{a}) (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{b}) (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{c}))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.rename` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.6 (recipe rename eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\operatorname{k} : \mathbb{N}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{I} \operatorname{J} : \operatorname{Fin} \operatorname{k} \to \operatorname{Fin} \operatorname{n}) , \forall (\operatorname{p} : \operatorname{Recipe} \operatorname{k}) , (\operatorname{Recipe} . \operatorname{rename} \operatorname{I} \operatorname{J} \operatorname{p}) . \operatorname{eval} \operatorname{X} = \operatorname{p} . \operatorname{eval} (\operatorname{X} . \operatorname{submatrix} \operatorname{I} \operatorname{J})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recipe_rename_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.7 (recursiveRecipe).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{p} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{q} : \operatorname{Fin} \operatorname{n} \to \operatorname{Recipe} (\operatorname{n} + 1)) , \operatorname{recursiveRecipe} (\operatorname{n} := \operatorname{n}) (\operatorname{p} := \operatorname{p}) (\operatorname{q} := \operatorname{q}) = (\operatorname{fun} \operatorname{i} \operatorname{j} \mapsto \operatorname{Fin} . \operatorname{lastCases} (\operatorname{Fin} . \operatorname{lastCases} (\operatorname{Recipe} . \operatorname{sum} (\operatorname{List} . \operatorname{ofFn} \operatorname{q})) \operatorname{q} \operatorname{i}) (\operatorname{fun} \operatorname{j} \mapsto \operatorname{Fin} . \operatorname{lastCases} \operatorname{Recipe} . \operatorname{zero} (\operatorname{fun} \operatorname{i} \mapsto \operatorname{Recipe} . \operatorname{rename} \operatorname{Fin} . \operatorname{castSucc} \operatorname{Fin} . \operatorname{castSucc} (\operatorname{p} \operatorname{i} \operatorname{j})) \operatorname{i}) \operatorname{j})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveRecipe` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.8 (recursiveRecipe eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\operatorname{p} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{q} : \operatorname{Fin} \operatorname{n} \to \operatorname{Recipe} (\operatorname{n} + 1)) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{Fin} (\operatorname{n} + 1)) \operatorname{F}) , (((\operatorname{recursiveRecipe} \operatorname{p} \operatorname{q})) . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X})) = \operatorname{border} (((\operatorname{p}) . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} ((\operatorname{fun} \operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{Fin} (\operatorname{n} + 1)) \operatorname{F} \mapsto \operatorname{X} . \operatorname{submatrix} \operatorname{Fin} . \operatorname{castSucc} \operatorname{Fin} . \operatorname{castSucc}) \operatorname{X})))) (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{q} \operatorname{i}) . \operatorname{eval} \operatorname{X}) (\sum \operatorname{i} , (\operatorname{q} \operatorname{i}) . \operatorname{eval} \operatorname{X})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveRecipe_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

## References

- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.border`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recipe_rename_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveRecipe`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveRecipe_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveStep`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveStep_bijOn`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.recursiveStep_rank`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecursion.rename`
- Dependency: [D5/S3/QuadraticForms/FrobeniusCholeskyRecipes](FrobeniusCholeskyRecipes.md)
