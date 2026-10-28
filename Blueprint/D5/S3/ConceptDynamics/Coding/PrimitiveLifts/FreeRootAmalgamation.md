# Free-root amalgamation and the infinite sharpness countermodel

## Abstract

The actual free group on Bool is an infinite nonnilpotent sharpness countermodel with unique coprime roots.

**Theorem 1.1 (Exact FreeGroup Bool countermodel).**

$$((\operatorname{Infinite}\left(\operatorname{FreeGroup}\left(Bool\right)\right) \land \neg \operatorname{Group.IsNilpotent}\left(\operatorname{FreeGroup}\left(Bool\right)\right)) \land \forall x \in \operatorname{FreeGroup}\left(Bool\right), y \in \operatorname{FreeGroup}\left(Bool\right), m \in Nat, n \in Nat,\; (\operatorname{Coprime}\left(m, n\right) \implies (x^{m} = y^{n} \iff \exists z \in \operatorname{FreeGroup}\left(Bool\right),\; ((x = z^{n} \land y = z^{m}) \land \forall w \in \operatorname{FreeGroup}\left(Bool\right),\; ((x = z^{n} \land y = z^{m}) \implies w = z)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FreeRootAmalgamation.freeGroupBool_infinite_not_nilpotent_coprime_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual group FreeGroup Bool, infinitude, failure of nilpotence, and the full coprime-power root equivalence hold in one conjunction. For every x,y and every natural m,n with m.Coprime n, x^m=y^n if and only if there exists exactly one z with x=z^n and y=z^m. The statement retains both zero-exponent boundaries: coprimality turns m=0 into n=1 (and symmetrically in the displayed equivalence), so no positivity hypothesis has been added.

The root proof first uses Mathlib's HasUniqueRoots instance for FreeGroup. Conjugating x by y and applying conj_pow transports the equality of mth powers to the conjugate; when m is nonzero, power injectivity gives y*x*y⁻¹=x and hence Commute x y. When m=0, the coprimality boundary gives n=1 and the equality gives y=1 directly. The commuting pair is placed in H=Subgroup.closure {x,y}; Subgroup.isMulCommutative_closure supplies the pinned commutative instance, and the existing repository theorem NilpotentRootAmalgamation.pow_eq_pow_iff_exists_unique is applied to H. Its witness is transported back to FreeGroup, while ambient uniqueness uses the nonzero m power map; the m=0 branch is handled explicitly. The reverse implication is the general identity (z^n)^m=(z^m)^n.

The same explicit quotient q:FreeGroup Bool→DihedralGroup 0 sends false to r(1) and true to sr(0). Every rotation r(i) is q((of false)^(ZMod.cast i)) and every reflection sr(i) is q(of true*(of false)^(ZMod.cast i)), using r_one_zpow and sr_mul_r; therefore q is surjective. Infinite.of_surjective transfers infinitude from DihedralGroup 0. If FreeGroup Bool were nilpotent, Group.nilpotent_of_surjective would make DihedralGroup 0 nilpotent, while center_ne_bot contradicts DihedralGroup.center_eq_bot_of_zero. Thus this quotient proves both countermodel properties in one construction.

The finite Sylow converse has a separate boundary. In a finite nilpotent group, Sylow subgroups commute and the group is their internal direct product; that finite decomposition is the route from local root data to a global statement. The present theorem does not assert that converse for infinite groups, does not replace the finite hypotheses by an unproved extension, and does not claim a classification of all nonnilpotent groups. It supplies the actual infinite sharpness example required here.

The formal inputs are pinned Mathlib results on cyclic reduction and unique roots in free groups, conjugation of natural powers, subgroup centralizers, DihedralGroup 0, and nilpotent quotients, together with the repository's NilpotentRootAmalgamation theorem. The displayed theorem is a repository derivation from those mature library mechanisms; no priority claim is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FreeRootAmalgamation.freeGroupBool_infinite_not_nilpotent_coprime_root`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/NilpotentRootAmalgamation](NilpotentRootAmalgamation.md)
