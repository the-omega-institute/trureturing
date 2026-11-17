# The all-degree normalized homotopy

## Abstract

The all-degree normalized homotopy

All degrees q are natural numbers. Define the endomorphism error E(q) as (phiOp q).comp(boundaryOp q)+(boundaryOp(q+1)).comp(phiOp(q+1))+idOp(q+1)-hOp(q+1), acting in degree q+1. Composition MTwo.comp MOne applies MOne first. The base error is a diagonal degeneracy, and E(q+1) is E(q).prime. Structural norms are closed under prime, so E(q) is a norm for every q.

Let C : Type u have Category.{v} C and Abelian C, with independent u,v, and let X be arbitrary bisimplicial data in C. Moore retraction kills the realized error. Sandwich the raw degree-raising family between diagonal Moore inclusion and retraction to obtain phiHomNorm. Its component i → i+1 is inclusionNTwo.f i followed by (phiOp i).realize X and retractionNTwo.f(i+1); other components are zero.

The resulting Homotopy has source normalizedAlexanderWhitney X followed by normalizedShuffleMap X and target the identity of NTwo(X). In Lean’s convention the source map equals dNext plus prevD plus the target map. Thus the homotopy sign is dΦ+Φd = AW-then-shuffle minus identity. No assertion of vanishing higher side composites is included.

**Theorem 1.1 (phi_op_isNorm_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_isNorm_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_isNorm_zero` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Base case for the exact induction: the degree-1 error term is a norm.

In this notation, lemma phi_op_isNorm_zero : IsNorm ((phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1).

**Theorem 1.2 (phi_op_succ_eq).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_succ_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_succ_eq` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The error term `Φ∂ + ∂Φ + i - h` in the next degree is the `prime` of the preceding error term. After rewriting `∂ = F₀ - ∂'` and `Φ = -Φ' + h' D₀`, the remaining identity is a formal operator calculation using `lastFace_comp_prime`, `boundaryOp_comp_hOp`, and `boundary_comp_D0`.

In this notation, lemma phi_op_succ_eq (q : ℕ) : (phiOp (q + 1)).comp (boundaryOp (q + 1)) + (boundaryOp (q + 1 + 1)).comp (phiOp (q + 1 + 1)) + idOp (q + 1 + 1) - hOp (q + 1 + 1) = ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) + idOp (q + 1) - hOp (q + 1)).prime.

**Theorem 1.3 (phi_op_isNorm).**

$$\forall q: Nat, \operatorname{IsNorm}\left(\operatorname{comp}\left(\operatorname{phiOp}\left(q\right), \operatorname{boundaryOp}\left(q\right)\right) + \operatorname{comp}\left(\operatorname{boundaryOp}\left(q+1\right), \operatorname{phiOp}\left(q+1\right)\right) + \operatorname{idOp}\left(q+1\right) - \operatorname{hOp}\left(q+1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_isNorm` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The error term `Φ∂ + ∂Φ + i - h` is a norm in every degree.

In this notation, lemma phi_op_isNorm (q : ℕ) : IsNorm ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) + idOp (q + 1) - hOp (q + 1)).

**Theorem 1.4 (phi_comm_op).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_comm_op`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_comm_op` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Operator-level form of the EM homotopy identity, modulo norms. This is the realized statement corresponding to `Φ∂ + ∂Φ + i ≡ h`, obtained by killing the structural norm term from `phi_op_isNorm` with `retractionNTwo`.

In this notation, lemma phi_comm_op (X : BisimplicialObject C) (q : ℕ) : (DerivedOp.realize X ((phiOp q).comp (boundaryOp q)) + DerivedOp.realize X ((boundaryOp (q + 1)).comp (phiOp (q + 1))) + DerivedOp.realize X (idOp (q + 1))) ≫ (retractionNTwo X).f (q + 1) = DerivedOp.realize X (hOp (q + 1)) ≫ (retractionNTwo X).f (q + 1).

**Theorem 1.5 (phi_comm_retraction).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_comm_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_comm_retraction` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

EM's homotopy identity `∂Φ + Φ∂ = ∇f - i`, after postcomposing with `retractionNTwo`.

In this notation, lemma phi_comm_retraction (X : BisimplicialObject C) (n : ℕ) : (dNext n (phiHomRaw X) + prevD n (phiHomRaw X) + (𝟙 (FTwo.obj X) : (FTwo.obj X) ⟶ (FTwo.obj X)).f n) ≫ (retractionNTwo X).f n = (alexanderWhitney X ≫ shuffleMap X).f n ≫ (retractionNTwo X).f n.

**Theorem 1.6 (inclusionNTwo_comp_retractionNTwo).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.inclusionNTwo_comp_retractionNTwo`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.inclusionNTwo_comp_retractionNTwo` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The normalized Moore complex `NTwo` is a retract of `FTwo`: `inclusionNTwo ≫ retractionNTwo = 𝟙`.

In this notation, @[reassoc] lemma inclusionNTwo_comp_retractionNTwo (X : BisimplicialObject C) : inclusionNTwo X ≫ retractionNTwo X = 𝟙 (NTwo.obj X).

**Definition 1.7 (phiHomNorm).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`Φ` conjugated onto the normalized diagonal `NTwo.obj X` (EM's homotopy on `K ×_N L`): `inclusionNTwo ≫ phiOp.realize ≫ retractionNTwo`.

In this notation, noncomputable def phiHomNorm (X : BisimplicialObject C) (i j : ℕ) : (NTwo.obj X).X i ⟶ (NTwo.obj X).X j.

**Theorem 1.8 (phiHomNorm_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm_zero` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The normalized homotopy family is zero away from degree increase by one.

In this notation, lemma phiHomNorm_zero (X : BisimplicialObject C) (i j : ℕ) (hij : ¬ (ComplexShape.down ℕ).Rel j i) : phiHomNorm X i j = 0.

**Theorem 1.9 (phiHomNorm_eq).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm_eq` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`phiHomNorm` is the conjugate of `phiHomRaw` by `inclusionNTwo … retractionNTwo`.

In this notation, lemma phiHomNorm_eq (X : BisimplicialObject C) (i j : ℕ) : phiHomNorm X i j = (inclusionNTwo X).f i ≫ phiHomRaw X i j ≫ (retractionNTwo X).f j.

**Theorem 1.10 (dNext_phiHomNorm).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.dNext_phiHomNorm`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.dNext_phiHomNorm` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`dNext` commutes with the `inclusionNTwo … retractionNTwo` conjugation (both are chain maps).

In this notation, lemma dNext_phiHomNorm (X : BisimplicialObject C) (i : ℕ) : dNext i (phiHomNorm X) = (inclusionNTwo X).f i ≫ dNext i (phiHomRaw X) ≫ (retractionNTwo X).f i.

**Theorem 1.11 (prevD_phiHomNorm).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.prevD_phiHomNorm`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.prevD_phiHomNorm` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`prevD` commutes with the `inclusionNTwo … retractionNTwo` conjugation (both are chain maps).

In this notation, lemma prevD_phiHomNorm (X : BisimplicialObject C) (j : ℕ) : prevD j (phiHomNorm X) = (inclusionNTwo X).f j ≫ prevD j (phiHomRaw X) ≫ (retractionNTwo X).f j.

**Theorem 1.12 (normalizedAW_shuffle_eq).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.normalizedAW_shuffle_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.normalizedAW_shuffle_eq` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**(6b)** The normalized `AW ≫ ∇` is the `NTwo`-conjugate of the unnormalized `AW ≫ ∇`. Unfolding the definitions, `normalizedAlexanderWhitney ≫ normalizedShuffleMap` `= ι₂ ≫ AW ≫ (retractionNOne ≫ inclusionNOne) ≫ ∇ ≫ ρ₂`; the inner Dold–Kan round-trip `retractionNOne ≫ inclusionNOne` (the `PInfty` idempotent on `FOne`) is absorbed, leaving `ι₂ ≫ (AW ≫ ∇) ≫ ρ₂`.

In this notation, lemma normalizedAW_shuffle_eq (X : BisimplicialObject C) : normalizedAlexanderWhitney X ≫ normalizedShuffleMap X = inclusionNTwo X ≫ (alexanderWhitney X ≫ shuffleMap X) ≫ retractionNTwo X.

**Definition 1.13 (homotopyAWShuffleNormalized).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.homotopyAWShuffleNormalized`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.homotopyAWShuffleNormalized` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**`AW ≫ ∇ ≃ 𝟙` on the normalized diagonal `NTwo`** via the Eilenberg–Mac Lane homotopy `Φ` (EM Thm 2.1a, `∂Φ + Φ∂ = ∇f − i`). This is the contraction homotopy used by `eilenbergZilberNormalized` (`BisimplicialNormalized.lean`).

In this notation, noncomputable def homotopyAWShuffleNormalized (X : BisimplicialObject C) : Homotopy (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X) (𝟙 (NTwo.obj X)).

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.dNext_phiHomNorm`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.homotopyAWShuffleNormalized`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.inclusionNTwo_comp_retractionNTwo`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.normalizedAW_shuffle_eq`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm_eq`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phiHomNorm_zero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_comm_op`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_comm_retraction`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_isNorm`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_isNorm_zero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.phi_op_succ_eq`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy.prevD_phiHomNorm`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedOperators](NormalizedOperators.md)
