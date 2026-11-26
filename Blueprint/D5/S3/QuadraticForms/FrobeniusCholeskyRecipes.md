# FrobeniusCholeskyRecipes

## Abstract

Arithmetic recipes, coordinate frames and characteristic-two matrix recursion.

**Definition 1.1 (B).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{B} (\operatorname{F} := \operatorname{F}) (\operatorname{n} := \operatorname{n}) = (\{ \operatorname{X} | \operatorname{X} . \operatorname{IsUpperTriangular} \land \operatorname{X} * \operatorname{X} = 0 \})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.B` (`✓ std3`).

*Citation.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

Wu and Zhou, Section 6, p. 31: “Let q = 2^e. Recall the definitions”. B is the displayed upper triangular square-zero fiber, with F as the scalar field and Fin n as the row and column index type.

**Definition 1.2 (C).**

$$\forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{C} (\operatorname{F} := \operatorname{F}) (\operatorname{n} := \operatorname{n}) = (\{ \operatorname{U} | \operatorname{U} . \operatorname{IsUpperTriangular} \land \operatorname{U} . \operatorname{transpose} * \operatorname{U} = 0 \})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.C` (`✓ std3`).

*Citation.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

Wu and Zhou, Section 6, p. 31: “Let q = 2^e. Recall the definitions”. C is the displayed upper triangular zero Gram fiber, with F as the scalar field and Fin n as the row and column index type.

**Definition 1.3 (Recipe).**

$$\forall (\operatorname{n} : \mathbb{N}) , \operatorname{Recipe} \operatorname{n} : \operatorname{Type} ; \operatorname{Recipe} . \operatorname{zero} : \operatorname{Recipe} \operatorname{n} ; \operatorname{Recipe} . \operatorname{one} : \operatorname{Recipe} \operatorname{n} ; \operatorname{Recipe} . \operatorname{entry} : \operatorname{Fin} \operatorname{n} \to \operatorname{Fin} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} ; \operatorname{Recipe} . \operatorname{add} : \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} ; \operatorname{Recipe} . \operatorname{mul} : \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} ; \operatorname{Recipe} . \operatorname{inv} : \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} ; \operatorname{Recipe} . \operatorname{iteZero} : \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n} \to \operatorname{Recipe} \operatorname{n}$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.Recipe` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.4 (Recipe.eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \operatorname{Recipe} . \operatorname{eval} (\operatorname{n} := \operatorname{n}) (\operatorname{F} := \operatorname{F}) (\operatorname{X} := \operatorname{X}) = (\operatorname{fun} | \operatorname{Recipe} . \operatorname{zero} \mapsto 0 | \operatorname{Recipe} . \operatorname{one} \mapsto 1 | \operatorname{Recipe} . \operatorname{entry} \operatorname{i} \operatorname{j} \mapsto \operatorname{X} \operatorname{i} \operatorname{j} | \operatorname{Recipe} . \operatorname{add} \operatorname{a} \operatorname{b} \mapsto \operatorname{a} . \operatorname{eval} \operatorname{X} + \operatorname{b} . \operatorname{eval} \operatorname{X} | \operatorname{Recipe} . \operatorname{mul} \operatorname{a} \operatorname{b} \mapsto \operatorname{a} . \operatorname{eval} \operatorname{X} * \operatorname{b} . \operatorname{eval} \operatorname{X} | \operatorname{Recipe} . \operatorname{inv} \operatorname{a} \mapsto (\operatorname{a} . \operatorname{eval} \operatorname{X}) ^{-1} | \operatorname{Recipe} . \operatorname{iteZero} \operatorname{a} \operatorname{b} \operatorname{c} \mapsto \operatorname{if} \operatorname{a} . \operatorname{eval} \operatorname{X} = 0 \operatorname{then} \operatorname{b} . \operatorname{eval} \operatorname{X} \operatorname{else} \operatorname{c} . \operatorname{eval} \operatorname{X})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.eval` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.5 (recipe map frobenius).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , [ \operatorname{CharP} \operatorname{F} 2 ] , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{p} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) (\operatorname{Recipe} \operatorname{n})) , ((\operatorname{p}) . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} (\operatorname{X} . \operatorname{map} (\operatorname{frobenius} \operatorname{F} 2)))) = (((\operatorname{p}) . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X}))) . \operatorname{map} (\operatorname{frobenius} \operatorname{F} 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipe_map_frobenius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.6 (Recipe.sum).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{l} : \operatorname{List} (\operatorname{Recipe} \operatorname{n})) , \operatorname{Recipe} . \operatorname{sum} (\operatorname{n} := \operatorname{n}) (\operatorname{l} := \operatorname{l}) = (\operatorname{l} . \operatorname{foldr} \operatorname{Recipe} . \operatorname{add} \operatorname{Recipe} . \operatorname{zero})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.sum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.7 (recipe sum eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{l} : \operatorname{List} (\operatorname{Recipe} \operatorname{n})) , (\operatorname{Recipe} . \operatorname{sum} \operatorname{l}) . \operatorname{eval} \operatorname{X} = (\operatorname{l} . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X})) . \operatorname{sum}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipe_sum_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.8 (recipeDet).**

$$\forall (\operatorname{n} : \mathbb{N}) , (\forall (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} 0) (\operatorname{Fin} 0) (\operatorname{Recipe} \operatorname{n})) , \operatorname{recipeDet} (\operatorname{n} := \operatorname{n}) 0 \operatorname{M} = \operatorname{Recipe} . \operatorname{one}) \land (\forall (\operatorname{r} : \mathbb{N}) (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{r} + 1)) (\operatorname{Fin} (\operatorname{r} + 1)) (\operatorname{Recipe} \operatorname{n})) , \operatorname{recipeDet} (\operatorname{r} + 1) \operatorname{M} = \operatorname{Recipe} . \operatorname{sum} (\operatorname{List} . \operatorname{ofFn} (\operatorname{fun} (\operatorname{j} : \operatorname{Fin} (\operatorname{r} + 1)) \mapsto \operatorname{Recipe} . \operatorname{mul} (\operatorname{M} 0 \operatorname{j}) (\operatorname{recipeDet} \operatorname{r} (\operatorname{M} . \operatorname{submatrix} \operatorname{Fin} . \operatorname{succ} \operatorname{j} . \operatorname{succAbove})))))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.9 (recipeAdjugate).**

$$\forall (\operatorname{n} : \mathbb{N}) , (\forall (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} 0) (\operatorname{Fin} 0) (\operatorname{Recipe} \operatorname{n})) , \operatorname{recipeAdjugate} (\operatorname{n} := \operatorname{n}) 0 \operatorname{M} = \operatorname{Fin} . \operatorname{elim0}) \land (\forall (\operatorname{r} : \mathbb{N}) (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} (\operatorname{r} + 1)) (\operatorname{Fin} (\operatorname{r} + 1)) (\operatorname{Recipe} \operatorname{n})) , \operatorname{recipeAdjugate} (\operatorname{r} + 1) \operatorname{M} = (\operatorname{fun} (\operatorname{i} \operatorname{j} : \operatorname{Fin} (\operatorname{r} + 1)) \mapsto \operatorname{recipeDet} \operatorname{r} (\operatorname{M} . \operatorname{submatrix} \operatorname{j} . \operatorname{succAbove} \operatorname{i} . \operatorname{succAbove})))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeAdjugate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.10 (recipeInverse).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{r}) (\operatorname{Fin} \operatorname{r}) (\operatorname{Recipe} \operatorname{n})) , \operatorname{recipeInverse} (\operatorname{n} := \operatorname{n}) (\operatorname{r} := \operatorname{r}) (\operatorname{M} := \operatorname{M}) = (\operatorname{fun} \operatorname{i} \operatorname{j} \mapsto \operatorname{Recipe} . \operatorname{mul} (\operatorname{Recipe} . \operatorname{inv} (\operatorname{recipeDet} \operatorname{r} \operatorname{M})) (\operatorname{recipeAdjugate} \operatorname{r} \operatorname{M} \operatorname{i} \operatorname{j}))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeInverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.11 (recipeInverse eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , [ \operatorname{CharP} \operatorname{F} 2 ] , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{r}) (\operatorname{Fin} \operatorname{r}) (\operatorname{Recipe} \operatorname{n})) , (\operatorname{recipeInverse} \operatorname{r} \operatorname{M}) . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X}) = (\operatorname{M} . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X})) ^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeInverse_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Theorem 1.12 (independent columns iff minor).**

$$\forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{r} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) \operatorname{F}) , \operatorname{LinearIndependent} \operatorname{F} \operatorname{A} . \operatorname{col} \iff \exists \operatorname{I} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m} , (\operatorname{A} . \operatorname{submatrix} \operatorname{I} \operatorname{id}) . \operatorname{det} \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.independent_columns_iff_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.13 (rowChoices).**

$$\forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \operatorname{rowChoices} (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) = (\operatorname{List} . \operatorname{ofFn} (\operatorname{Fintype} . \operatorname{equivFin} (\operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m})) . \operatorname{symm})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.rowChoices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.14 (Recipe.firstNonzero).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{tests} : \operatorname{List} (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{yes} \operatorname{no} : \operatorname{Recipe} \operatorname{n}) , \operatorname{Recipe} . \operatorname{firstNonzero} (\operatorname{n} := \operatorname{n}) (\operatorname{tests} := \operatorname{tests}) (\operatorname{yes} := \operatorname{yes}) (\operatorname{no} := \operatorname{no}) = (\operatorname{match} \operatorname{tests} \operatorname{with} | [ ] \mapsto \operatorname{no} | \operatorname{a} :: \operatorname{l} \mapsto \operatorname{Recipe} . \operatorname{iteZero} \operatorname{a} (\operatorname{Recipe} . \operatorname{firstNonzero} \operatorname{l} \operatorname{yes} \operatorname{no}) \operatorname{yes})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.firstNonzero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.15 (minorConditional).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{yes} \operatorname{no} : \operatorname{Recipe} \operatorname{n}) , \operatorname{minorConditional} (\operatorname{n} := \operatorname{n}) (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{M} := \operatorname{M}) (\operatorname{yes} := \operatorname{yes}) (\operatorname{no} := \operatorname{no}) = (\operatorname{Recipe} . \operatorname{firstNonzero} ((\operatorname{rowChoices} \operatorname{m} \operatorname{r}) . \operatorname{map} (\operatorname{fun} \operatorname{I} \mapsto \operatorname{recipeDet} \operatorname{r} (\operatorname{M} . \operatorname{submatrix} \operatorname{I} \operatorname{id}))) \operatorname{yes} \operatorname{no})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.minorConditional` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.16 (RecipeChoice).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\alpha : \operatorname{Type}) , \operatorname{RecipeChoice} \operatorname{n} \alpha : \operatorname{Type} ; \operatorname{RecipeChoice} . \operatorname{pure} : \alpha \to \operatorname{RecipeChoice} \operatorname{n} \alpha ; \operatorname{RecipeChoice} . \operatorname{branch} : \operatorname{Recipe} \operatorname{n} \to \operatorname{RecipeChoice} \operatorname{n} \alpha \to \operatorname{RecipeChoice} \operatorname{n} \alpha \to \operatorname{RecipeChoice} \operatorname{n} \alpha$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.RecipeChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.17 (RecipeChoice.evaluate).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\alpha : \operatorname{Type}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \operatorname{RecipeChoice} . \operatorname{evaluate} (\operatorname{n} := \operatorname{n}) (\operatorname{F} := \operatorname{F}) (\alpha := \alpha) (\operatorname{X} := \operatorname{X}) = (\operatorname{fun} | \operatorname{RecipeChoice} . \operatorname{pure} \operatorname{a} \mapsto \operatorname{a} | \operatorname{RecipeChoice} . \operatorname{branch} \operatorname{a} \operatorname{b} \operatorname{c} \mapsto \operatorname{if} \operatorname{a} . \operatorname{eval} \operatorname{X} = 0 \operatorname{then} \operatorname{b} . \operatorname{evaluate} \operatorname{X} \operatorname{else} \operatorname{c} . \operatorname{evaluate} \operatorname{X})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.18 (RecipeChoice.reify).**

$$\forall (\operatorname{n} : \mathbb{N}) , \operatorname{RecipeChoice} . \operatorname{reify} (\operatorname{n} := \operatorname{n}) = (\operatorname{fun} | \operatorname{RecipeChoice} . \operatorname{pure} \operatorname{a} \mapsto \operatorname{a} | \operatorname{RecipeChoice} . \operatorname{branch} \operatorname{a} \operatorname{b} \operatorname{c} \mapsto \operatorname{Recipe} . \operatorname{iteZero} \operatorname{a} \operatorname{b} . \operatorname{reify} \operatorname{c} . \operatorname{reify})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.reify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.19 (choice reify eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{q} : \operatorname{RecipeChoice} \operatorname{n} (\operatorname{Recipe} \operatorname{n})) , \operatorname{q} . \operatorname{reify} . \operatorname{eval} \operatorname{X} = (\operatorname{q} . \operatorname{evaluate} \operatorname{X}) . \operatorname{eval} \operatorname{X}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.choice_reify_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.20 (RecipeChoice.bind).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\alpha \beta : \operatorname{Type}) , \operatorname{RecipeChoice} . \operatorname{bind} (\operatorname{n} := \operatorname{n}) (\alpha := \alpha) (\beta := \beta) = (\operatorname{fun} | \operatorname{RecipeChoice} . \operatorname{pure} \operatorname{a} , \operatorname{k} \mapsto \operatorname{k} \operatorname{a} | \operatorname{RecipeChoice} . \operatorname{branch} \operatorname{a} \operatorname{b} \operatorname{c} , \operatorname{k} \mapsto \operatorname{RecipeChoice} . \operatorname{branch} \operatorname{a} (\operatorname{b} . \operatorname{bind} \operatorname{k}) (\operatorname{c} . \operatorname{bind} \operatorname{k}))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.bind` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.21 (choice bind eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\alpha \beta : \operatorname{Type}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{q} : \operatorname{RecipeChoice} \operatorname{n} \alpha) , \forall (\operatorname{k} : \alpha \to \operatorname{RecipeChoice} \operatorname{n} \beta) , (\operatorname{q} . \operatorname{bind} \operatorname{k}) . \operatorname{evaluate} \operatorname{X} = (\operatorname{k} (\operatorname{q} . \operatorname{evaluate} \operatorname{X})) . \operatorname{evaluate} \operatorname{X}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.choice_bind_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.22 (minorChoiceFrom).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) (\operatorname{Recipe} \operatorname{n})) , \operatorname{minorChoiceFrom} (\operatorname{n} := \operatorname{n}) (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{M} := \operatorname{M}) = (\operatorname{fun} | [ ] \mapsto \operatorname{RecipeChoice} . \operatorname{pure} \operatorname{none} | \operatorname{I} :: \operatorname{l} \mapsto \operatorname{RecipeChoice} . \operatorname{branch} (\operatorname{recipeDet} \operatorname{r} (\operatorname{M} . \operatorname{submatrix} \operatorname{I} \operatorname{id})) (\operatorname{minorChoiceFrom} \operatorname{m} \operatorname{r} \operatorname{M} \operatorname{l}) (\operatorname{RecipeChoice} . \operatorname{pure} (\operatorname{some} \operatorname{I})))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.minorChoiceFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.23 (minorChoice exists).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , [ \operatorname{CharP} \operatorname{F} 2 ] , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{M} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) (\operatorname{Recipe} \operatorname{n})) , (\operatorname{LinearIndependent} \operatorname{F} (\operatorname{M} . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X})) . \operatorname{col}) \to (\exists \operatorname{I} , (\operatorname{minorChoiceFrom} \operatorname{m} \operatorname{r} \operatorname{M} (\operatorname{rowChoices} \operatorname{m} \operatorname{r})) . \operatorname{evaluate} \operatorname{X} = \operatorname{some} \operatorname{I} \land ((\operatorname{M} . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X})) . \operatorname{submatrix} \operatorname{I} \operatorname{id}) . \operatorname{det} \neq 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.minorChoice_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.24 (recipeMulVec).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{v} : \operatorname{Fin} \operatorname{r} \to \operatorname{Recipe} \operatorname{n}) , \operatorname{recipeMulVec} (\operatorname{n} := \operatorname{n}) (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{A} := \operatorname{A}) (\operatorname{v} := \operatorname{v}) = (\operatorname{fun} \operatorname{i} \mapsto \operatorname{Recipe} . \operatorname{sum} (\operatorname{List} . \operatorname{ofFn} (\operatorname{fun} \operatorname{j} \mapsto \operatorname{Recipe} . \operatorname{mul} (\operatorname{A} \operatorname{i} \operatorname{j}) (\operatorname{v} \operatorname{j}))))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeMulVec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.25 (recipeMulVec eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{r}) (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{v} : \operatorname{Fin} \operatorname{r} \to \operatorname{Recipe} \operatorname{n}) , (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{recipeMulVec} \operatorname{A} \operatorname{v} \operatorname{i}) . \operatorname{eval} \operatorname{X}) = \operatorname{A} . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X}) *_{v} (\operatorname{fun} \operatorname{j} \mapsto (\operatorname{v} \operatorname{j}) . \operatorname{eval} \operatorname{X})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeMulVec_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.26 (candidateRecipes).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\iota : \operatorname{Type}) , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{v} : \iota \to \operatorname{Fin} \operatorname{m} \to \operatorname{Recipe} \operatorname{n}) , \forall (\operatorname{s} : \operatorname{Finset} \iota) , \forall (\operatorname{i} : \iota) , \operatorname{candidateRecipes} (\operatorname{n} := \operatorname{n}) (\iota := \iota) (\operatorname{m} := \operatorname{m}) (\operatorname{v} := \operatorname{v}) (\operatorname{s} := \operatorname{s}) (\operatorname{i} := \operatorname{i}) = (\operatorname{fun} \operatorname{row} \operatorname{col} \mapsto \operatorname{Fin} . \operatorname{cases} (\operatorname{v} \operatorname{i} \operatorname{row}) (\operatorname{fun} \operatorname{a} \mapsto \operatorname{v} ((\operatorname{s} . \operatorname{equivFin} . \operatorname{symm} \operatorname{a}) . \operatorname{val}) \operatorname{row}) \operatorname{col})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.candidateRecipes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Definition 1.27 (greedyChoice).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\iota : \operatorname{Type}) , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{v} : \iota \to \operatorname{Fin} \operatorname{m} \to \operatorname{Recipe} \operatorname{n}) , \operatorname{greedyChoice} (\operatorname{n} := \operatorname{n}) (\iota := \iota) (\operatorname{m} := \operatorname{m}) (\operatorname{v} := \operatorname{v}) = (\operatorname{fun} | [ ] , \operatorname{s} \mapsto \operatorname{RecipeChoice} . \operatorname{pure} \operatorname{s} | \operatorname{i} :: \operatorname{l} , \operatorname{s} \mapsto \operatorname{RecipeChoice} . \operatorname{branch} (\operatorname{minorConditional} \operatorname{m} (\operatorname{s} . \operatorname{card} + 1) (\operatorname{candidateRecipes} \operatorname{v} \operatorname{s} \operatorname{i}) \operatorname{Recipe} . \operatorname{one} \operatorname{Recipe} . \operatorname{zero}) (\operatorname{greedyChoice} \operatorname{v} \operatorname{l} \operatorname{s}) (\operatorname{greedyChoice} \operatorname{v} \operatorname{l} (\operatorname{insert} \operatorname{i} \operatorname{s})))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.greedyChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.28 (greedyChoice eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\iota : \operatorname{Type}) , [ \operatorname{CharP} \operatorname{F} 2 ] , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{v} : \iota \to \operatorname{Fin} \operatorname{m} \to \operatorname{Recipe} \operatorname{n}) , \forall (\operatorname{l} : \operatorname{List} \iota) , \forall (\operatorname{s} : \operatorname{Finset} \iota) , (\operatorname{LinearIndepOn} \operatorname{F} (\operatorname{fun} \operatorname{j} \operatorname{row} \mapsto (\operatorname{v} \operatorname{j} \operatorname{row}) . \operatorname{eval} \operatorname{X}) (\operatorname{s} : \operatorname{Set} \iota)) \to ((\operatorname{greedyChoice} \operatorname{v} \operatorname{l} \operatorname{s}) . \operatorname{evaluate} \operatorname{X} = \operatorname{greedyRoleScanFrom} (\operatorname{K} := \operatorname{F}) (\operatorname{fun} \operatorname{j} \operatorname{row} \mapsto (\operatorname{v} \operatorname{j} \operatorname{row}) . \operatorname{eval} \operatorname{X}) \operatorname{s} \operatorname{l})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.greedyChoice_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.29 (recipeCoordinateColumns).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \operatorname{recipeCoordinateColumns} (\operatorname{n} := \operatorname{n}) (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{J} := \operatorname{J}) = (\operatorname{fun} \operatorname{i} \operatorname{a} \mapsto \operatorname{if} \operatorname{i} = \operatorname{J} \operatorname{a} \operatorname{then} \operatorname{Recipe} . \operatorname{one} \operatorname{else} \operatorname{Recipe} . \operatorname{zero})$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeCoordinateColumns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.30 (recipeCoordinateColumns eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , (\operatorname{recipeCoordinateColumns} (\operatorname{n} := \operatorname{n}) \operatorname{J}) . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X}) = ((1 : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m}) \operatorname{F}) . \operatorname{submatrix} \operatorname{id} \operatorname{J})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeCoordinateColumns_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

**Definition 1.31 (recipeKernel).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m}) (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{I} \operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}) , \operatorname{recipeKernel} (\operatorname{n} := \operatorname{n}) (\operatorname{m} := \operatorname{m}) (\operatorname{r} := \operatorname{r}) (\operatorname{A} := \operatorname{A}) (\operatorname{I} := \operatorname{I}) (\operatorname{J} := \operatorname{J}) (\operatorname{j} := \operatorname{j}) = (\operatorname{fun} \operatorname{i} \mapsto \operatorname{Recipe} . \operatorname{add} (\operatorname{if} \operatorname{i} = \operatorname{j} \operatorname{then} \operatorname{Recipe} . \operatorname{one} \operatorname{else} \operatorname{Recipe} . \operatorname{zero}) (\operatorname{recipeMulVec} (\operatorname{recipeCoordinateColumns} \operatorname{J}) (\operatorname{recipeMulVec} (\operatorname{recipeInverse} \operatorname{r} (\operatorname{A} . \operatorname{submatrix} \operatorname{I} \operatorname{J})) (\operatorname{fun} \operatorname{a} \mapsto \operatorname{A} (\operatorname{I} \operatorname{a}) \operatorname{j})) \operatorname{i}))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This construction uses standard coordinate indices and exact field arithmetic.

**Theorem 1.32 (recipeKernel eval).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{F} : \operatorname{Type}) , [ \operatorname{Field} \operatorname{F} ] , [ \operatorname{DecidableEq} \operatorname{F} ] , [ \operatorname{CharP} \operatorname{F} 2 ] , \forall (\operatorname{m} \operatorname{r} : \mathbb{N}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \operatorname{F}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m}) (\operatorname{Recipe} \operatorname{n})) , \forall (\operatorname{I} \operatorname{J} : \operatorname{Fin} \operatorname{r} \to \operatorname{Fin} \operatorname{m}) , \forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}) , (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{recipeKernel} \operatorname{A} \operatorname{I} \operatorname{J} \operatorname{j} \operatorname{i}) . \operatorname{eval} \operatorname{X}) = \operatorname{Pi} . \operatorname{single} \operatorname{j} 1 - ((1 : \operatorname{Matrix} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m}) \operatorname{F}) . \operatorname{submatrix} \operatorname{id} \operatorname{J}) *_{v} (((\operatorname{A} . \operatorname{map} (\operatorname{Recipe} . \operatorname{eval} \operatorname{X})) . \operatorname{submatrix} \operatorname{I} \operatorname{J}) ^{-1} *_{v} (\operatorname{fun} \operatorname{a} \mapsto (\operatorname{A} (\operatorname{I} \operatorname{a}) \operatorname{j}) . \operatorname{eval} \operatorname{X}))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeKernel_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

This identity or implication uses standard coordinate indices and exact field arithmetic.

## References

- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.B`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.C`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.Recipe`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.RecipeChoice`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.bind`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.candidateRecipes`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.choice_bind_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.choice_reify_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.evaluate`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.firstNonzero`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.greedyChoice`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.greedyChoice_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.independent_columns_iff_minor`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.minorChoiceFrom`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.minorChoice_exists`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.minorConditional`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeAdjugate`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeCoordinateColumns`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeCoordinateColumns_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeDet`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeInverse`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeInverse_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeKernel`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeKernel_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeMulVec`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipeMulVec_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipe_map_frobenius`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.recipe_sum_eval`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.reify`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.rowChoices`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyRecipes.sum`
- Dependency: [D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis](../Estimation/ExperimentCost/MinimumCostRoleBasis.md)
