# APN Maps Need Not Break Large Flats

## Abstract

An almost perfect nonlinear map on a field with sixteen elements sends a three-dimensional binary flat onto another three-dimensional binary flat.

**Definition 1.1 (Almost perfect nonlinearity).**

$$\forall F \in M \to M,\; \operatorname{APN}\left(F\right) \Leftrightarrow \left(\forall a \in M,\; \forall b \in M,\; \left(\neg a = 0\right) \Rightarrow \operatorname{card}\left(\{ x \in M | \operatorname{F}\left(x + a\right) + \operatorname{F}\left(x\right) = b \}\right) \le 2\right)$$

*Formalization.* `D5/S3/Arith/APNBreakingRefutation.APN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each nonzero additive direction a and each value b, the equation F(x+a)+F(x)=b has at most two solutions. The definition applies to finite additive commutative groups and agrees with the APN condition on fields of characteristic two.

**Definition 1.2 (Binary affine flats).**

$$\forall a \in M,\; \forall V \in \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), M\right),\; \operatorname{affineFlat}\left(a, V\right) = \{ x \in M | \operatorname{mem}\left(x - a, V\right) \}$$

*Formalization.* `D5/S3/Arith/APNBreakingRefutation.affineFlat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a binary subspace V, membership of x in the coset a+V means x-a belongs to V. The dimension of the coset is the dimension of V.

**Definition 1.3 (Being an affine flat).**

$$\forall A \in \operatorname{Set}\left(M\right),\; \operatorname{IsFlat}\left(A\right) \Leftrightarrow \left(\exists a \in M,\; \exists V \in \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), M\right),\; A = \operatorname{affineFlat}\left(a, V\right)\right)$$

*Formalization.* `D5/S3/Arith/APNBreakingRefutation.IsFlat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An image is a flat when it is some coset of some binary subspace. The subspace may have any dimension; no injectivity assumption is imposed on the map.

**Definition 1.4 (Conjecture 3.1).**

$$claim \Leftrightarrow \left(\forall K \in Type,\; \left(\operatorname{Field}\left(K\right) \land \left(\operatorname{Fintype}\left(K\right) \land \left(\operatorname{DecidableEq}\left(K\right) \land \operatorname{CharP}\left(K, 2\right)\right)\right)\right) \Rightarrow \left(\forall n \in Nat,\; \operatorname{card}\left(K\right) = 2^{n} \Rightarrow \left(\forall F \in K \to K,\; \operatorname{APN}\left(F\right) \Rightarrow \left(\forall k \in Nat,\; \left(\lfloor \frac{n}{2} \rfloor + 1 \le k \land k \le n - 1\right) \Rightarrow \left(\forall a \in K,\; \forall V \in \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), K\right),\; \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), V\right) = k \Rightarrow \left(\neg \operatorname{IsFlat}\left(\operatorname{image}\left(F, \operatorname{affineFlat}\left(a, V\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/APNBreakingRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rodriguez-Aldama, Sehovic, Pasalic and Kudin, arXiv:2609.22394v2, Conjecture 3.1, assert that every APN function over a field of order 2 to the n breaks every k-flat for floor(n/2)+1 <= k <= n-1. Here the field, the function, the integer k, the coset offset and the subspace all remain arbitrary. The binary module structure comes from the prime-field algebra of the characteristic-two field.

**Theorem 1.5 (APN invariance under additive coordinates).**

$$\forall e \in \operatorname{AddEquiv}\left(M, N\right),\; \forall F \in M \to M,\; \operatorname{APN}\left(e \circ F \circ \operatorname{inverse}\left(e\right)\right) \Leftrightarrow \operatorname{APN}\left(F\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/APNBreakingRefutation.apn_conjugate_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An additive isomorphism e takes each derivative fiber bijectively to the derivative fiber in direction e(a) with value e(b). Thus conjugating a function by e preserves the APN condition in both directions.

**Theorem 1.6 (Cosets and dimensions under linear coordinates).**

$$\forall e \in \operatorname{LinearEquiv}\left(\operatorname{ZMod}\left(2\right), M, N\right),\; \forall a \in M,\; \forall V \in \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), M\right),\; \operatorname{image}\left(e, \operatorname{affineFlat}\left(a, V\right)\right) = \operatorname{affineFlat}\left(\operatorname{e}\left(a\right), \operatorname{map}\left(V, e\right)\right) \land \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{map}\left(V, e\right)\right) = \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), V\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/APNBreakingRefutation.affineFlat_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A binary linear isomorphism takes a+V to e(a)+e(V), and the restriction to V preserves its dimension. This supplies the coordinate-independent interpretation of both flats.

**Definition 1.7 (Four binary coordinates).**

$$W = \left(\operatorname{Fin}\left(4\right) \to \operatorname{ZMod}\left(2\right)\right)$$

*Formalization.* `D5/S3/Arith/APNBreakingRefutation.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates are ordered from the least significant bit to the most significant bit. The vector (a,b,c,d) has label a+2b+4c+8d.

**Definition 1.8 (The sixteen-value function).**

$$\operatorname{labelValues}\left(G\right) = [0, 9, 4, 11, 0, 14, 1, 9, 15, 2, 6, 13, 1, 11, 13, 1]$$

*Formalization.* `D5/S3/Arith/APNBreakingRefutation.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The listed values, read in label order from zero through fifteen, define G. The table originates from x cubed plus a binary linear map L in the polynomial field model with modulus x to the fourth plus x plus one, where L has column labels 8,12,12,5. The argument uses the table itself and asserts no polynomial identity for G.

**Theorem 1.9 (Failure at n = 4 and k = 3).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/APNBreakingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/rodriguez-aldama-et-al-2026-apn-breaking-refutation` (refuted) by `D5/S3/Arith/APNBreakingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rodriguez-aldama-et-al-2026-apn-breaking-refutation","declaration_gid":"D5/S3/Arith/APNBreakingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The input subspace has labels {0,1,2,3,8,9,10,11}, equivalently its third bit is zero. Its eight elements make its binary dimension three. Their images have labels {0,2,4,6,9,11,13,15}, the subspace whose first and fourth bits agree, spanned by labels 2,4,9. Every nonzero derivative fiber of G has at most two elements. The four-dimensional binary vector space is linearly isomorphic to GaloisField(2,4). Conjugate G and transport the two subspaces along this isomorphism. The field has sixteen elements, and k=3 satisfies both bounds. Its APN map therefore has an affine-flat image on a permitted flat, contradicting the conjecture. Field multiplication is never needed for this counterexample.

## References

- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.APN`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.G`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.IsFlat`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.W`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.affineFlat`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.affineFlat_image`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.apn_conjugate_iff`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.claim`
- Truth anchor: `D5/S3/Arith/APNBreakingRefutation.result`
