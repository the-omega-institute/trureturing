# The recursive Eilenberg–Mac Lane operator

## Abstract

The recursive Eilenberg–Mac Lane operator

All degrees are natural numbers. Pure DerivedOp constructions are integer combinations of pairs of simplex maps; a realization uses any abelian C : Type u with Category.{v} C, independent universes, and any bisimplicial X. Composition MTwo.comp MOne means first apply MOne and then MTwo.

The endomorphism hOp(q) sums over every split p+(q-p)=q and every shuffle of that split. Its realization is alexanderWhitney followed by shuffleMap. The degree-raising family phiOp is defined recursively: phiOp(0)=0 and phiOp(q+1)=-(phiOp(q)).prime+(hOp(q+1)).prime.comp(D0op(q+1)). The negative sign belongs to this recursion.

The representable bisimplicial free abelian object detects every formal coefficient: evaluating an operator on its universal diagonal generator is injective. This detects the operator-level chain identities from their realized versions. The raw degree-raising family is zero except from i to i+1; the normalized homotopy is obtained later by Moore inclusion and retraction, after the structural norm error has been killed.

**Definition 1.1 (hLetter).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hLetter`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hLetter` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A single summand of `h = ∇f`: split `q = p + (q - p)`, apply the AW front/back faces, then apply one `(p, q-p)` shuffle. The two `eqToHom`s transport across `p + (q-p) = q`.

In this notation, noncomputable def hLetter (q : ℕ) (p : Fin (q + 1)) (μ : Shuffle (p : ℕ) (q - p)) : OpLetter q q.

**Definition 1.2 (hOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`h = ∇f` as a derived operator: sum over the Alexander-Whitney split and then over shuffles.

In this notation, noncomputable def hOp (q : ℕ) : DerivedOp q q.

**Theorem 1.3 (hLetter_realize).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hLetter_realize`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hLetter_realize` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Realization of one `hLetter` summand is the corresponding `awComponent ≫ ezComponent` shuffle summand. This identifies the AW front/back faces with the shuffle degeneracies.

In this notation, lemma hLetter_realize (X : BisimplicialObject C) (q : ℕ) (p : Fin (q + 1)) (μ : Shuffle (p : ℕ) (q - p)) : (hLetter q p μ).realizeLetter X = eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫ awComponent X p (q - p) ≫ ((X.obj (Opposite.op ⦋(p : ℕ)⦌)).map (shuffleSndHom μ).op ≫ (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋(p : ℕ) + (q - p)⦌)) ≫ eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]).

**Theorem 1.4 (realize_hOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.realize_hOp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.realize_hOp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`hOp` realizes to the composite `alexanderWhitney ≫ shuffleMap = ∇f` on `FTwo.obj X`.

In this notation, lemma realize_hOp (X : BisimplicialObject C) (q : ℕ) : (hOp q).realize X = (alexanderWhitney X ≫ shuffleMap X).f q.

**Definition 1.5 (phiOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.phiOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.phiOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**The Eilenberg–Mac Lane homotopy `Φ`** as a derived operator, defined by EM's recursion (2.13): `Φ₀ = 0` and `Φ_{q} = − Φ'_{q-1} + h'_{q} D₀` for `q > 0`. Here `Φ_q : (K×L)_q → (K×L)_{q+1}`.

In this notation, noncomputable def phiOp : (q : ℕ) → DerivedOp q (q + 1).

**Definition 1.6 (phiHomRaw).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.phiHomRaw`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.phiHomRaw` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`Φ` packaged as a degree-`+1` `Homotopy.hom` family on `FTwo.obj X` (the unnormalized diagonal): `phiOp i` realized (transported along `j = i+1`) on the single nonzero entry, `0` elsewhere.

In this notation, noncomputable def phiHomRaw (X : BisimplicialObject C) (i j : ℕ) : (FTwo.obj X).X i ⟶ (FTwo.obj X).X j.

**Theorem 1.7 (prevD_phiHomRaw).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.prevD_phiHomRaw`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.prevD_phiHomRaw` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`prevD` of `phiHomRaw` is the realized operator `∂Φ` (apply `Φ` then `∂`): `prevD n (phiHomRaw X) = (phiOp n).realize X ≫ (boundaryOp n).realize X`.

In this notation, lemma prevD_phiHomRaw (X : BisimplicialObject C) (n : ℕ) : prevD n (phiHomRaw X) = DerivedOp.realize X ((boundaryOp n).comp (phiOp n)).

**Theorem 1.8 (dNext_phiHomRaw).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.dNext_phiHomRaw`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.dNext_phiHomRaw` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`dNext` of `phiHomRaw` (at `n+1`) is the realized operator `Φ∂` (apply `∂` then `Φ`): `dNext (n+1) (phiHomRaw X) = (boundaryOp n).realize X ≫ (phiOp n).realize X`.

In this notation, lemma dNext_phiHomRaw (X : BisimplicialObject C) (n : ℕ) : dNext (n + 1) (phiHomRaw X) = DerivedOp.realize X ((phiOp n).comp (boundaryOp n)).

**Definition 1.9 (idOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.idOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.idOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The identity operator `i = 𝟙 × 𝟙 : (K×L)_q → (K×L)_q` (EM's `i`). Realizes to `𝟙` (`realize_single_id`).

In this notation, noncomputable def idOp (q : ℕ) : DerivedOp q q.

**Definition 1.10 (ysimp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.ysimp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.ysimp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The represented simplicial type `Δ[s] : b ↦ (⦋b⦌ ⟶ ⦋s⦌)` (the `SimplexCategory` Yoneda).

In this notation, abbrev ysimp (s : ℕ) : SimplexCategoryᵒᵖ ⥤ Type.

**Definition 1.11 (bitype).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.bitype`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.bitype` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The bi-represented **bisimplicial type** at `(s, s)`: `(a, b) ↦ (⦋a⦌ ⟶ ⦋s⦌) × (⦋b⦌ ⟶ ⦋s⦌)`, the horizontal map acting on the first factor and the vertical on the second.

In this notation, def bitype (s : ℕ) : BisimplicialObject (Type).

**Definition 1.12 (freeWhisker).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.freeWhisker`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.freeWhisker` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Postcompose a (bi)simplicial type with the free `ℤ`-module functor.

In this notation, noncomputable def freeWhisker : (SimplexCategoryᵒᵖ ⥤ Type) ⥤ (SimplexCategoryᵒᵖ ⥤ ModuleCat.{0} ℤ).

**Definition 1.13 (univOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.univOp`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.univOp` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A **universal bisimplicial object** detecting all derived operators out of degree `s`: the free `ℤ`-module on the bi-represented bisimplicial set at `(s, s)`. Realizing a derived operator against it recovers it as a `Finsupp`, so `realize (univOp s)` is injective (`realize_univOp_injective`).

In this notation, noncomputable def univOp (s : ℕ) : BisimplicialObject (ModuleCat.{0} ℤ).

**Theorem 1.14 (realize_univOp_injective).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.realize_univOp_injective`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.realize_univOp_injective` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`realize` against the universal object is **injective**: a derived operator is determined by its realization on `univOp`. This is the faithfulness principle that lets us deduce formal `DerivedOp` identities from their (realized) chain-level counterparts.

In this notation, lemma realize_univOp_injective {s q : ℕ} : Function.Injective (fun M : DerivedOp s q => M.realize (univOp s)).

**Theorem 1.15 (boundaryOp_comp_hOp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.boundaryOp_comp_hOp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.boundaryOp_comp_hOp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**`∂ h = h ∂` (EM line 155, `∂*h' = h'∂*`).** `h = ∇f` is a chain map, so `boundaryOp` commutes with `hOp`. Proof: `realize` against the universal object is injective, and on the realized side this is just the chain-map condition `comm` of `alexanderWhitney ≫ shuffleMap`.

In this notation, lemma boundaryOp_comp_hOp (q : ℕ) : (boundaryOp q).comp (hOp (q + 1)) = (hOp q).comp (boundaryOp q).

**Theorem 1.16 (lastFace_comp_hPrime).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.lastFace_comp_hPrime`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.lastFace_comp_hPrime` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**`F₀ h' = h F₀` (EM, Lemma I.3.3).** Just `lastFace_comp_prime` specialized to `hOp`.

In this notation, lemma lastFace_comp_hPrime (q : ℕ) : (lastFaceOp q).comp ((hOp q).prime) = (hOp q).comp (lastFaceOp q).

**Theorem 1.17 (hOp_zero_comp_retraction).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hOp_zero_comp_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hOp_zero_comp_retraction` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Base degree: `hOp 0` agrees with the identity after postcomposing with `retractionNTwo`.

In this notation, lemma hOp_zero_comp_retraction (X : BisimplicialObject C) : DerivedOp.realize X (hOp 0) ≫ (retractionNTwo X).f 0 = DerivedOp.realize X (idOp 0) ≫ (retractionNTwo X).f 0.

**Theorem 1.18 (DerivedOp.comp_neg).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_neg`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_neg` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Negation in the operator applied first negates the composite.

In this notation, lemma DerivedOp.comp_neg {s q r : ℕ} (MTwo : DerivedOp q r) (N : DerivedOp s q) : MTwo.comp (-N) = -(MTwo.comp N).

**Theorem 1.19 (DerivedOp.neg_comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.neg_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.neg_comp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Negation in the operator applied second negates the composite.

In this notation, lemma DerivedOp.neg_comp {s q r : ℕ} (M : DerivedOp q r) (K : DerivedOp s q) : (-M).comp K = -(M.comp K).

**Theorem 1.20 (DerivedOp.comp_sub).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_sub`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_sub` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Composition distributes over a difference in the operator applied first.

In this notation, lemma DerivedOp.comp_sub {s q r : ℕ} (MTwo : DerivedOp q r) (M N : DerivedOp s q) : MTwo.comp (M - N) = MTwo.comp M - MTwo.comp N.

**Theorem 1.21 (DerivedOp.sub_comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.sub_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.sub_comp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Composition distributes over a difference in the operator applied second.

In this notation, lemma DerivedOp.sub_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) : (M - N).comp K = M.comp K - N.comp K.

**Theorem 1.22 (prime_neg).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.prime_neg`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.prime_neg` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Priming commutes with negation.

In this notation, lemma prime_neg {s q : ℕ} (M : DerivedOp s q) : (-M).prime = -M.prime.

**Theorem 1.23 (DerivedOp.comp_assoc).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_assoc`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_assoc` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Associativity of `DerivedOp.comp` (reduces to `single_comp_single` + bilinearity).

In this notation, lemma DerivedOp.comp_assoc {s q r p : ℕ} (M₃ : DerivedOp r p) (MTwo : DerivedOp q r) (MOne : DerivedOp s q) : (M₃.comp MTwo).comp MOne = M₃.comp (MTwo.comp MOne).

**Theorem 1.24 (DerivedOp.zero_comp).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.zero_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.zero_comp` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Applying the zero operator second gives the zero composite.

In this notation, @[simp] lemma DerivedOp.zero_comp {s q r : ℕ} (N : DerivedOp s q) : DerivedOp.comp (0 : DerivedOp q r) N = 0.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.bitype`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.boundaryOp_comp_hOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_assoc`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_neg`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.comp_sub`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.dNext_phiHomRaw`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.freeWhisker`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hLetter`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hLetter_realize`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.hOp_zero_comp_retraction`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.idOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.lastFace_comp_hPrime`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.neg_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.phiHomRaw`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.phiOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.prevD_phiHomRaw`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.prime_neg`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.realize_hOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.realize_univOp_injective`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.sub_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.univOp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.ysimp`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/RecursiveOperators.zero_comp`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators](DerivedOperators.md)
