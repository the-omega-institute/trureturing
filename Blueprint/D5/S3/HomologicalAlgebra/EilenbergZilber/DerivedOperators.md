# Integral operators on bisimplicial diagonals

## Abstract

Integral operators on bisimplicial diagonals

For arbitrary natural degrees s,q, an OpLetter(s,q) is a pair of simplex maps [q] → [s]. A DerivedOp(s,q) is a finitely supported integer coefficient function on these letters. Its realization on X sends X[s,s] to X[q,q]. Realization is the integer-linear extension of the two contravariant simplex actions.

For every use of a realization let C : Type u, Category.{v} C and Abelian C, with u,v independent, and let X be a bisimplicial object of C. Pure letter and coefficient operations do not depend on C. If MOne : DerivedOp(s,q) and MTwo : DerivedOp(q,r), then MTwo.comp MOne realizes as MOne.realize X followed by MTwo.realize X.

Priming prepends a new zero vertex to each simplex map and shifts every old vertex by one; its integer-linear extension raises both degrees. Boundary operators are alternating sums of paired faces. D0op, the last face, and the truncated boundary interact with priming to express the recursion of the Eilenberg–Mac Lane homotopy. A diagonal noninjective simplex map is killed by Moore retraction.

**Definition 1.1 (OpLetter).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.OpLetter`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.OpLetter` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A **letter**: a pair of `SimplexCategory` maps `⟦q⟧ ⟶ ⟦s⟧`. The `fst` map acts on the horizontal (first / `K`) simplicial variable and `snd` on the vertical (second / `L`) one. Realized on a bisimplicial object it gives a single summand `X_{s,s} ⟶ X_{q,q}` of an EM natural operator (their (2.10)).

In this notation, structure OpLetter (s q : ℕ).

**Definition 1.2 (DerivedOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.DerivedOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.DerivedOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

An EM natural operator `(K×L)_s → (K×L)_q` (their (2.10)): a finite `ℤ`-linear combination of letters, with uniqueness of representation supplied by carrying the representation as data.

In this notation, abbrev DerivedOp (s q : ℕ).

**Definition 1.3 (OpLetter.realizeLetter).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realizeLetter`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realizeLetter` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realize a single letter as a degreewise hom on the diagonal complex `FTwo.obj X`.

In this notation, noncomputable def OpLetter.realizeLetter {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) : (FTwo.obj X).X s ⟶ (FTwo.obj X).X q.

**Definition 1.4 (DerivedOp.realize).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realize a formal operator as a degreewise hom on `FTwo.obj X` (`ℤ`-linear extension of `OpLetter.realizeLetter`).

In this notation, noncomputable def DerivedOp.realize {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) : (FTwo.obj X).X s ⟶ (FTwo.obj X).X q.

**Definition 1.5 (primeHom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The 0-th-coface shift of a monotone map: `0 ↦ 0`, `j+1 ↦ θ(j)+1`. This is EM's `δ⁰` prepending used to define the derived operator.

In this notation, def primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) : (⦋q + 1⦌ : SimplexCategory) ⟶ ⦋s + 1⦌.

**Definition 1.6 (OpLetter.primeLetter).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeLetter`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeLetter` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The derived operator on a single letter: prime both `SimplexCategory` maps.

In this notation, def OpLetter.primeLetter {s q : ℕ} (l : OpLetter s q) : OpLetter (s + 1) (q + 1).

**Definition 1.7 (DerivedOp.prime).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

EM's **derived operator** `M ↦ M'` (their (2.10)): prime every letter, `ℤ`-linearly.

In this notation, noncomputable def DerivedOp.prime {s q : ℕ} (M : DerivedOp s q) : DerivedOp (s + 1) (q + 1).

**Definition 1.8 (OpLetter.compLetter).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.compLetter`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.compLetter` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Composition of letters: `comp l₂ l₁` realizes to `realize l₁ ≫ realize l₂` (apply `l₁` then `l₂`). Horizontal and vertical maps compose independently.

In this notation, def OpLetter.compLetter {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) : OpLetter s r.

**Definition 1.9 (DerivedOp.comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`ℤ`-bilinear composition of operators (apply `MOne` then `MTwo`).

In this notation, noncomputable def DerivedOp.comp {s q r : ℕ} (MTwo : DerivedOp q r) (MOne : DerivedOp s q) : DerivedOp s r.

**Theorem 1.10 (realize_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_zero` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realizing the zero integer operator gives the zero morphism in every pair of degrees.

In this notation, @[simp] lemma realize_zero {s q : ℕ} (X : BisimplicialObject C) : (0 : DerivedOp s q).realize X = 0.

**Theorem 1.11 (realize_single).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_single`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_single` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realizing one letter with integer coefficient c gives c times that letter’s realized morphism.

In this notation, @[simp] lemma realize_single {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) (c : ℤ) : DerivedOp.realize X (Finsupp.single l c) = c • l.realizeLetter X.

**Theorem 1.12 (realize_add).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_add`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_add` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realization preserves addition of formal operators.

In this notation, lemma realize_add {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) : (M + N).realize X = M.realize X + N.realize X.

**Theorem 1.13 (realize_neg).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_neg`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_neg` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realization preserves negation of formal operators.

In this notation, lemma realize_neg {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) : (-M).realize X = -(M.realize X).

**Theorem 1.14 (realize_sub).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_sub`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_sub` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realization preserves subtraction of formal operators.

In this notation, lemma realize_sub {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) : (M - N).realize X = M.realize X - N.realize X.

**Definition 1.15 (realizeAddMonoidHom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realizeAddMonoidHom`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realizeAddMonoidHom` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Integer-linear realization packaged as an additive monoid homomorphism from formal operators to degreewise morphisms.

In this notation, noncomputable def realizeAddMonoidHom {s q : ℕ} (X : BisimplicialObject C) : DerivedOp s q →+ ((FTwo.obj X).X s ⟶ (FTwo.obj X).X q).

**Theorem 1.16 (realize_zsmul).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_zsmul`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_zsmul` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

An integer coefficient factors out of realization.

In this notation, lemma realize_zsmul {s q : ℕ} (X : BisimplicialObject C) (c : ℤ) (M : DerivedOp s q) : (c • M).realize X = c • M.realize X.

**Theorem 1.17 (DerivedOp.comp_add_right).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp_add_right`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp_add_right` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`comp` is additive in its right argument.

In this notation, lemma DerivedOp.comp_add_right {s q r : ℕ} (MTwo : DerivedOp q r) (M N : DerivedOp s q) : MTwo.comp (M + N) = MTwo.comp M + MTwo.comp N.

**Theorem 1.18 (DerivedOp.add_comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.add_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.add_comp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`comp` is additive in its left argument.

In this notation, lemma DerivedOp.add_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) : (M + N).comp K = M.comp K + N.comp K.

**Theorem 1.19 (DerivedOp.single_comp_single).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.single_comp_single`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.single_comp_single` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`comp` of two `single`s.

In this notation, lemma DerivedOp.single_comp_single {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) (c₂ c₁ : ℤ) : DerivedOp.comp (Finsupp.single l₂ c₂) (Finsupp.single l₁ c₁) = Finsupp.single (l₂.compLetter l₁) (c₁ * c₂).

**Theorem 1.20 (realize_comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_comp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`realize` turns operator composition into hom composition (contravariantly: apply `MOne` then `MTwo`). The functoriality fact that drives the operator-level induction. Proved by reducing to the single-single case (`OpLetter.realizeLetter_compLetter`) via bilinearity of `comp` and additivity of `realize`.

In this notation, lemma realize_comp {s q r : ℕ} (X : BisimplicialObject C) (MTwo : DerivedOp q r) (MOne : DerivedOp s q) : (MTwo.comp MOne).realize X = MOne.realize X ≫ MTwo.realize X.

**Theorem 1.21 (realize_single_id).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_single_id`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_single_id` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The identity letter realizes to the identity hom.

In this notation, lemma realize_single_id {q : ℕ} (X : BisimplicialObject C) : DerivedOp.realize X (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp q q) = 𝟙 ((FTwo.obj X).X q).

**Definition 1.22 (D0op).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.D0op`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.D0op` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The 0-th degeneracy operator `D₀ = s₀ × s₀ : (K×L)_q → (K×L)_{q+1}` of EM (2.13).

In this notation, noncomputable def D0op (q : ℕ) : DerivedOp q (q + 1).

**Definition 1.23 (faceOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.faceOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.faceOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The `i`-th face operator `F_i = δ_i × δ_i : (K×L)_{q+1} → (K×L)_q`.

In this notation, noncomputable def faceOp (q : ℕ) (i : Fin (q + 2)) : DerivedOp (q + 1) q.

**Definition 1.24 (lastFaceOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.lastFaceOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.lastFaceOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The **last face** `F₀` in EM's `∂ = F₀ − ∂'` decomposition — here the 0-th face `F_0`.

In this notation, noncomputable def lastFaceOp (q : ℕ) : DerivedOp (q + 1) q.

**Definition 1.25 (truncBoundaryOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.truncBoundaryOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.truncBoundaryOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The **truncated boundary** `∂' = Σ_{i≥1} (-1)^{i-1} F_i` (the part of the boundary omitting the 0-th face), so that the full boundary is `∂ = F₀ − ∂'`.

In this notation, noncomputable def truncBoundaryOp (q : ℕ) : DerivedOp (q + 1) q.

**Definition 1.26 (boundaryOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundaryOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundaryOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The full simplicial boundary operator `∂ = Σ_i (-1)^i F_i : (K×L)_{q+1} → (K×L)_q`.

In this notation, noncomputable def boundaryOp (q : ℕ) : DerivedOp (q + 1) q.

**Theorem 1.27 (realize_faceOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_faceOp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_faceOp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The realized `i`-th face is the `i`-th face of the diagonal simplicial object: the horizontal/vertical legs of `⟨δ i, δ i⟩` reassemble into `(diag X).δ i` via naturality of `X.map (δ i).op`.

In this notation, lemma realize_faceOp (X : BisimplicialObject C) (q : ℕ) (i : Fin (q + 2)) : (faceOp q i).realize X = (diag.obj X).δ i.

**Theorem 1.28 (realize_boundaryOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_boundaryOp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_boundaryOp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The realized boundary operator is the differential of `FTwo.obj X`.

In this notation, lemma realize_boundaryOp (X : BisimplicialObject C) (q : ℕ) : (boundaryOp q).realize X = (FTwo.obj X).d (q + 1) q.

**Theorem 1.29 (boundaryOp_eq).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundaryOp_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundaryOp_eq` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`∂ = F₀ − ∂'` (EM, just above (2.13)): the full boundary splits as the 0-th face minus the truncated boundary.

In this notation, lemma boundaryOp_eq (q : ℕ) : boundaryOp q = lastFaceOp q - truncBoundaryOp q.

**Theorem 1.30 (prime_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_zero` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The zero operator remains zero after prepending the new vertex.

In this notation, @[simp] lemma prime_zero {s q : ℕ} : (0 : DerivedOp s q).prime = 0.

**Theorem 1.31 (prime_add).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_add`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_add` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Priming distributes over addition of formal operators.

In this notation, lemma prime_add {s q : ℕ} (M N : DerivedOp s q) : (M + N).prime = M.prime + N.prime.

**Theorem 1.32 (primeHom_comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_comp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The 0-th coface shift is **multiplicative**: `(g ≫ f)' = g' ≫ f'`. The combinatorial core of `prime`-multiplicativity (a `SimplexCategory` identity, no `Finsupp`).

In this notation, lemma primeHom_comp {s q r : ℕ} (g : (⦋r⦌ : SimplexCategory) ⟶ ⦋q⦌) (f : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) : primeHom (g ≫ f) = primeHom g ≫ primeHom f.

**Theorem 1.33 (OpLetter.primeLetter_compLetter).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeLetter_compLetter`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeLetter_compLetter` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Letter-level multiplicativity of `prime`: `(l₂ ∘ l₁)' = l₂' ∘ l₁'`.

In this notation, lemma OpLetter.primeLetter_compLetter {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) : (l₂.compLetter l₁).primeLetter = l₂.primeLetter.compLetter l₁.primeLetter.

**Theorem 1.34 (prime_comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_comp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**`prime` is multiplicative** (`(β∘γ)' = β'∘γ'`), so `(MTwo ∘ MOne)' = MTwo' ∘ MOne'`. The key fact behind EM's `∂'M' = M'∂'`. Reduced to the single–single case `OpLetter.primeLetter_compLetter` by bilinearity of `comp` and additivity of `prime`.

In this notation, lemma prime_comp {s q r : ℕ} (MTwo : DerivedOp q r) (MOne : DerivedOp s q) : (MTwo.comp MOne).prime = MTwo.prime.comp MOne.prime.

**Theorem 1.35 (primeHom_δ).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_δ`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_δ` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`primeHom` shifts the face map index: `prime(δ_i) = δ_{i+1}`. The combinatorial core of `prime_faceOp`.

In this notation, lemma primeHom_δ {q : ℕ} (i : Fin (q + 2)) : primeHom (SimplexCategory.δ i) = SimplexCategory.δ i.succ.

**Theorem 1.36 (prime_faceOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_faceOp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_faceOp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**`prime` shifts faces**: `prime(δ_i) = δ_{i+1}` (prepending the `0`-th vertex pushes the omitted vertex up by one).

In this notation, lemma prime_faceOp (q : ℕ) (i : Fin (q + 2)) : (faceOp q i).prime = faceOp (q + 1) i.succ.

**Theorem 1.37 (primeHom_σ).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_σ`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_σ` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`primeHom` shifts the degeneracy map index: `prime(σ_i) = σ_{i+1}` (prepending the `0`-th vertex pushes the doubled vertex up by one). The degeneracy analog of `primeHom_δ`.

In this notation, lemma primeHom_σ {q : ℕ} (i : Fin (q + 1)) : primeHom (SimplexCategory.σ i) = SimplexCategory.σ i.succ.

**Definition 1.38 (primeAddHom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeAddHom`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeAddHom` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`prime` bundled as an additive hom, so it distributes over `Finset.sum` (`map_sum`) and `zsmul` (`map_zsmul`).

In this notation, noncomputable def primeAddHom {s q : ℕ} : DerivedOp s q →+ DerivedOp (s + 1) (q + 1).

**Theorem 1.39 (prime_boundaryOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_boundaryOp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_boundaryOp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**`∂' = prime(∂)`** (EM): the truncated boundary is the derived operator of the full boundary. Note the degree shift — `prime` of the degree-`q` boundary is the truncated boundary at degree `q+1` (this is the index offset that the literal EM transcription hides).

In this notation, lemma prime_boundaryOp (q : ℕ) : (boundaryOp q).prime = truncBoundaryOp (q + 1).

**Theorem 1.40 (faceZero_comp_primeHom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.faceZero_comp_primeHom`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.faceZero_comp_primeHom` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The 0-th face "eats" the prepended vertex: `δ 0 ≫ primeHom θ = θ ≫ δ 0`. The combinatorial core of `lastFace_comp_prime`.

In this notation, lemma faceZero_comp_primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) : SimplexCategory.δ (0 : Fin (q + 2)) ≫ primeHom θ = θ ≫ SimplexCategory.δ (0 : Fin (s + 2)).

**Theorem 1.41 (lastFace_comp_prime).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.lastFace_comp_prime`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.lastFace_comp_prime` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**`F₀ M' = M F₀`** (EM, Lemma I.3.3): dropping the bottom face commutes with priming. The one derived-operator/boundary identity that is *not* a consequence of multiplicativity, since the outer `F₀` is unprimed.

In this notation, lemma lastFace_comp_prime {s q : ℕ} (M : DerivedOp s q) : (lastFaceOp q).comp (M.prime) = M.comp (lastFaceOp s).

**Theorem 1.42 (face_zero_comp_D0).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.face_zero_comp_D0`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.face_zero_comp_D0` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The two unit faces `F_0 D₀ = F_1 D₀ = 1` (`δ_0 ≫ σ_0 = δ_1 ≫ σ_0 = 𝟙`); used to cancel the first two terms of `∂ D₀`.

In this notation, lemma face_zero_comp_D0 (q : ℕ) : (faceOp (q + 1) (0 : Fin (q + 3))).comp (D0op (q + 1)) = (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp (q + 1) (q + 1)).

**Theorem 1.43 (boundary_comp_D0).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundary_comp_D0`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundary_comp_D0` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Simplicial identity `∂ D₀ = D₀ ∂'` at the operator level. Writing `∂ = F₀ - ∂'`, the terms `F₀ D₀` and `F₁ D₀` both equal the identity, so the remaining faces assemble to `D₀ ∂'`.

In this notation, lemma boundary_comp_D0 (q : ℕ) : (boundaryOp (q + 1)).comp (D0op (q + 1)) = (D0op q).comp (truncBoundaryOp q).

**Theorem 1.44 (realize_diagLetter).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_diagLetter`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_diagLetter` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The realization of a **diagonal letter** `⟨θ, θ⟩` is the diagonal map `(diag X).map θ.op` (`realize_faceOp` generalized off the face case): the horizontal/vertical legs reassemble by naturality of `X.map θ.op`.

In this notation, lemma realize_diagLetter (X : BisimplicialObject C) {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) : DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) = (diag.obj X).map θ.op.

**Theorem 1.45 (realize_diagLetter_comp_retractionNTwo_eq_zero_of_not_mono).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_diagLetter_comp_retractionNTwo_eq_zero_of_not_mono`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_diagLetter_comp_retractionNTwo_eq_zero_of_not_mono` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A diagonal degeneracy `⟨θ, θ⟩` with `θ` non-monic is killed by `retractionNTwo`. Its realization is the diagonal map `(diag X).map θ.op`, and a non-monic `θ` is a simplicial degeneracy, so `degeneracy_comp_PInfty` applies after factoring `PInfty` through the Moore inclusion.

In this notation, lemma realize_diagLetter_comp_retractionNTwo_eq_zero_of_not_mono {s q : ℕ} (X : BisimplicialObject C) (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) : DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) ≫ (retractionNTwo X).f q = 0.

**Theorem 1.46 (realize_comp_diagLetter_not_mono_comp_retractionNTwo).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_comp_diagLetter_not_mono_comp_retractionNTwo`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_comp_diagLetter_not_mono_comp_retractionNTwo` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A diagonal degeneracy on the output side kills any composite after `retractionNTwo`. If `M = ⟨θ, θ⟩ ∘ N` with `θ` non-monic, then `realize M ≫ retractionNTwo = 0`. This is the form used later, where the norm term is expressed as a diagonal degeneracy postcomposed with an arbitrary operator.

In this notation, lemma realize_comp_diagLetter_not_mono_comp_retractionNTwo {r s q : ℕ} (X : BisimplicialObject C) (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) : DerivedOp.realize X (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N) ≫ (retractionNTwo X).f q = 0.

**Theorem 1.47 (comp_single_right).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp_single_right`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp_single_right` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

For every s,q,r : Nat, MTwo : DerivedOp q r, lOne : OpLetter s q and c : Int, MTwo.comp (Finsupp.single lOne c) = MTwo.sum (fun lTwo cTwo => Finsupp.single (lTwo.compLetter lOne) (c*cTwo)). Composition with a single input letter is the integer-linear sum over the output operator.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.D0op`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.DerivedOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.OpLetter`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.add_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundaryOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundaryOp_eq`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.boundary_comp_D0`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.compLetter`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp_add_right`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.comp_single_right`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.faceOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.faceZero_comp_primeHom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.face_zero_comp_D0`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.lastFaceOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.lastFace_comp_prime`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeAddHom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_δ`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeHom_σ`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeLetter`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.primeLetter_compLetter`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_add`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_boundaryOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_faceOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.prime_zero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realizeAddMonoidHom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realizeLetter`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_add`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_boundaryOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_comp_diagLetter_not_mono_comp_retractionNTwo`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_diagLetter`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_diagLetter_comp_retractionNTwo_eq_zero_of_not_mono`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_faceOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_neg`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_single`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_single_id`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_sub`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_zero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.realize_zsmul`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.single_comp_single`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators.truncBoundaryOp`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial](Bisimplicial.md)
