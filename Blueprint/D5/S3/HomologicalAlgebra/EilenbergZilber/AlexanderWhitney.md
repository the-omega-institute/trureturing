# The bisimplicial Alexander–Whitney map

## Abstract

The bisimplicial Alexander–Whitney map

Let C : Type u have Category.{v} C, with object and morphism universes independent. A bisimplicial object is a simplicial object in simplicial objects of C. Its diagonal in degree n is X[n,n], with both simplex operators acting together. The diagonal functor itself needs only the category structure. The chain-complex constructions in this module assume Abelian C.

FOne(X) is the natural-number total complex of the double alternating-face complex of X. Its degree n object is the finite coproduct over p+q=n, and its differential on bidegree (p,q) is the first differential plus (-1)^p times the second. FTwo(X) is the alternating-face chain complex of the diagonal. Finite antidiagonals require only coproducts already available in an abelian category.

The front coface selects the first p+1 vertices of [p+q], and the back coface selects the last q+1. Applying these in the two simplicial variables gives awComponent : X[p+q,p+q] → X[p,q]. Summing its inclusions into the total complex gives alexanderWhitney : FTwo(X) → FOne(X). The coface identities separate the two total boundary directions with the required sign.

**Definition 1.1 (BisimplicialObject).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.BisimplicialObject`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.BisimplicialObject` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A bisimplicial object in `C`: a simplicial object in simplicial objects in `C`.

In this notation, abbrev BisimplicialObject.

**Definition 1.2 (diag).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.diag`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.diag` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The diagonal simplicial object `[n] ↦ X_{n,n}` of a bisimplicial object.

In this notation, @[simps!] def diag : BisimplicialObject C ⥤ SimplicialObject C.

**Definition 1.3 (FOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.FOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.FOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The total complex of the double complex obtained by taking alternating face map complexes in both simplicial directions.

In this notation, noncomputable abbrev FOne : BisimplicialObject C ⥤ ChainComplex C ℕ.

**Definition 1.4 (FTwo).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.FTwo`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.FTwo` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The alternating face map complex of the diagonal simplicial object.

In this notation, abbrev FTwo : BisimplicialObject C ⥤ ChainComplex C ℕ.

**Definition 1.5 (doubleComplex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.doubleComplex`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.doubleComplex` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The double complex obtained by applying `alternatingFaceMapComplex` in both simplicial directions. Its `(p, q)` entry is `X_{p,q}`.

In this notation, noncomputable abbrev doubleComplex (X : BisimplicialObject C) : HomologicalComplex (ChainComplex C ℕ) (ComplexShape.down ℕ).

**Definition 1.6 (ιFront).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Front face inclusion `[p] ⟶ [p+q]`: the unique monotone map sending `i ↦ i`.

In this notation, def ιFront (p q : ℕ) : (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌.

**Definition 1.7 (ιBack).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Back face inclusion `[q] ⟶ [p+q]`: the unique monotone map sending `j ↦ p + j`.

In this notation, def ιBack (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌.

**Theorem 1.8 (ιFront_comp_δ_of_le).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront_comp_δ_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront_comp_δ_of_le` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`ιFront(p, q) ≫ δ k = δ k ≫ ιFront(p+1, q)` when `k ≤ p`, i.e., the face map acts within the front range. Here `δ k` on the left is `[p+q] → [p+q+1]` and `δ k` on the right is `[p] → [p+1]`.

In this notation, lemma ιFront_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2)) (hk : (k : ℕ) ≤ p) : ιFront p q ≫ SimplexCategory.δ k = SimplexCategory.δ ⟨k, by omega⟩ ≫ ιFront (p + 1) q ≫ eqToHom (by ring_nf).

**Theorem 1.9 (ιFront_comp_δ_of_gt).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront_comp_δ_of_gt`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront_comp_δ_of_gt` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`ιFront(p, q) ≫ δ k = ιFront(p, q+1)` when `k > p`, i.e., the face map acts beyond the front range — all front vertices stay below the skipped index.

In this notation, lemma ιFront_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2)) (hk : p < (k : ℕ)) : ιFront p q ≫ SimplexCategory.δ k = ιFront p (q + 1) ≫ eqToHom (by ring_nf).

**Theorem 1.10 (ιBack_comp_δ_of_le).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack_comp_δ_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack_comp_δ_of_le` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`ιBack(p, q) ≫ δ k = ιBack(p+1, q)` when `k ≤ p`, i.e., the face map acts before the back range — all back vertices shift by one.

In this notation, lemma ιBack_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2)) (hk : (k : ℕ) ≤ p) : ιBack p q ≫ SimplexCategory.δ k = ιBack (p + 1) q ≫ eqToHom (by ring_nf).

**Theorem 1.11 (ιBack_comp_δ_of_gt).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack_comp_δ_of_gt`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack_comp_δ_of_gt` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`ιBack(p, q) ≫ δ k = δ (k - p) ≫ ιBack(p, q+1)` when `k > p`, i.e., the face map acts within the back range. Here `δ (k-p)` is the face map on `[q]`.

In this notation, lemma ιBack_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2)) (hk : p < (k : ℕ)) : ιBack p q ≫ SimplexCategory.δ k = SimplexCategory.δ ⟨k - p, by omega⟩ ≫ ιBack p (q + 1) ≫ eqToHom (by ring_nf).

**Definition 1.12 (awComponent).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.awComponent`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.awComponent` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The `(p, q)` component of the Alexander-Whitney map.

In this notation, noncomputable def awComponent (X : BisimplicialObject C) (p q : ℕ) : (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) ⟶ (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌).

**Definition 1.13 (alexanderWhitney).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.alexanderWhitney`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.alexanderWhitney` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The Alexander-Whitney chain map `FTwo(X) ⟶ FOne(X)`.

In this notation, noncomputable def alexanderWhitney (X : BisimplicialObject C) : FTwo.obj X ⟶ FOne.obj X.

**Theorem 1.14 (val_eqToHom_apply).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.val_eqToHom_apply`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.val_eqToHom_apply` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

For every x,y : SimplexCategory, h : x = y and i : Fin(x.len+1), the natural-number value of (eqToHom h).toOrderHom i equals i. Equality transport changes the bound, preserving the vertex value.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.BisimplicialObject`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.FOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.FTwo`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.alexanderWhitney`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.awComponent`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.diag`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.doubleComplex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.val_eqToHom_apply`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack_comp_δ_of_gt`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιBack_comp_δ_of_le`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront_comp_δ_of_gt`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney.ιFront_comp_δ_of_le`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic](ShuffleBasic.md)
