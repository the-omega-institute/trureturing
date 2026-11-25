# Single-fibre inventory of stationary frequencies

## Abstract

The stationary count in a literal short frequency box is controlled by a Euclidean lattice minimum; only a bounded number of projective directions have a small minimum.

**Definition 1.1 (Count the actual lower stationary quadruples).**

$$\operatorname{N}\left(R, d\right)=\operatorname{card}\left(\operatorname{StationaryFibre}\left(R, d\right)\right)$$

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiSingleFibreInventory.stationaryCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A frequency quadruple is grouped as (w₁,n₁),(w₂,n₂). Its entries lie in four translated closed integer intervals [Lᵢ,Lᵢ+H]. The theorem uses a nonzero lower pivot d=(alpha,beta) modulo p. Write u(a,b)=alpha a+beta b mod p.

For the lower point z=(x,y), the actual gradient of xy(h−x−y) is G=(y(h−2x−y),x(h−x−2y)). The count is of exactly those quadruples in the box with u(w₁,n₁)G₂=u(w₂,n₂)G₁. This is the lower parallelism condition, including zero reading; no numerical approximation or extra rank filter is applied.

**Theorem 1.2 (The stationary bound, long-direction volume estimate, and short-direction count).**

$$\operatorname{N}\left(R, d\right)\le8\frac{H^4}{p}+24\frac{H^3}{\ell}+4H^2\quad\land\quad(\frac{p}{H}\le\ell\implies\operatorname{N}\left(R, d\right)\le40\frac{H^4}{p})\quad\land\quad\operatorname{card}\left(\operatorname{Short}\left(R\right)\right)\le9(\frac{p}{H})^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiSingleFibreInventory.single_fibre_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here p is prime, 1≤H<p, and G is nonzero. The length ell is the Euclidean minimum of the nonzero integer kernel of u. Short(R) is the set of projective directions whose own Euclidean minimum is less than p/H. Its representatives are (0,1) and (1,t) for t modulo p, so each direction is counted once.

A square grid yields a primitive minimum in the sup norm with length at most floor(sqrt(p)). Compare this with the attained Euclidean minimum. In a fixed residue, determinant rows are separated by multiples of p and each row is traversed in steps of the primitive vector. Since one gradient coordinate is nonzero, one free coordinate pair fixes the other pair's residue.

In the long-direction case, ell²≤2p and ell≥p/H imply p≤2H²; this absorbs the quadratic term without assuming H≥sqrt(p). For short directions, choosing one short nonzero kernel vector is injective up to the chosen projective direction: its nonzero reduction determines the unique projective annihilator.

The formal statement is the literal width-H normalization. If the four coordinate intervals have widths at most C H for a fixed C≥1, cover each interval by at most ceil(C) closed width-H intervals and sum over at most ceil(C)⁴ boxes. This preserves H and the threshold p/H; overlapping endpoints only increase the upper count. This explains the O(H)-width formulation and is not a separate Lean claim.

These are counts of stationary frequencies at one lower point. They are not a short-window RMS or a signed energy estimate.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSingleFibreInventory.single_fibre_inventory`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSingleFibreInventory.stationaryCount`
