# Gcd orbit coordinates and Mersenne zero-family symmetries

## Abstract

The full literal integer-zero-family symmetry group of a Mersenne-difference source has gcd residue blocks and natural-index semidirect coordinates.

Fix n>0 and a any natural number. Keep every physical label in Fin(n), with its integer value SourceWidth.actualSource(n,2^a-1). A permutation belongs to ZeroFamilyAut(n,a) exactly when, for every finite physical subset A, the source sum on its image is zero if and only if the source sum on A is zero. Set g=gcd(n,a), ell=n/g and rho=(finRotate n)^a. The existing MersenneDifferenceZeroSubsets.actual_zero_iff_rotation identifies this literal zero condition with rho-invariance. Its subset-count theorem is reused as context, not reproved here.

**Theorem 1.1 (Exact arithmetic orbit relation).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; 0 < n \Rightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{SameCycle}\left(\operatorname{finRotate}\left(n\right)^{a}, i, j\right) \Leftrightarrow \operatorname{mod}\left(\operatorname{val}\left(i\right), \operatorname{gcd}\left(n, a\right)\right) = \operatorname{mod}\left(\operatorname{val}\left(j\right), \operatorname{gcd}\left(n, a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.sameCycle_iff_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by ZMod.finEquiv sends rotation to translation by one, including modulus one. Integer powers translate by z*a. Divisibility by g proves necessity of residue equality. Conversely, g divides j-i; Int.gcd_a_modEq supplies a Bezout coefficient, and multiplication by the quotient constructs an integer z with i+z*a congruent to j modulo n. This constructs a SameCycle witness, rather than just comparing the numbers of orbits.

**Definition 1.2 (Residue and quotient coordinates).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \operatorname{Equiv}\left(\operatorname{Fin}\left(n\right), \operatorname{Product}\left(\operatorname{Fin}\left(\operatorname{gcd}\left(n, a\right)\right), \operatorname{Fin}\left(\operatorname{div}\left(n, \operatorname{gcd}\left(n, a\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.residueChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chart is finProdFinEquiv inverse, after transporting ell*g=n, and then swapping factors. It sends a physical index i to (i mod g,i div g). The first coordinate labels its orbit; the second labels all ell elements of that orbit. The arithmetic identity follows from g dividing n; no additional division bijection is implemented.

**Theorem 1.3 (Orbit relation in the chart).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; 0 < n \Rightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{SameCycle}\left(\operatorname{finRotate}\left(n\right)^{a}, i, j\right) \Leftrightarrow \operatorname{fst}\left(\operatorname{apply}\left(\operatorname{residueChart}\left(n, a\right), i\right)\right) = \operatorname{fst}\left(\operatorname{apply}\left(\operatorname{residueChart}\left(n, a\right), j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.sameCycle_iff_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-coordinate equality is the exact residue theorem through the implemented equivalence. It is consumed by conjugation of the relation-automorphism subgroup.

**Definition 1.4 (Literal zero-family subgroup).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \operatorname{Subgroup}\left(\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.ZeroFamilyAut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership requires the zero-sum equivalence in both directions for every A. Composition follows by successive image actions; inverse closure uses the equivalence on the inverse image. This definition keeps the actual integer source, not a modular surrogate or a centralizer.

**Theorem 1.5 (The zero family reconstructs the orbit partition).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; 0 < n \Rightarrow \operatorname{ZeroFamilyAut}\left(n, a\right) = \operatorname{relationAut}\left(\operatorname{SameCycle}\left(\operatorname{finRotate}\left(n\right)^{a}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.zeroFamilyAut_eq_orbitAut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite permutation, invariant subsets have membership constant on SameCycle, by natural-power induction and inverse images. The class of q(x) is invariant. The reverse family implication makes its inverse image under q invariant; it contains x and therefore every y in x's orbit. This proves forward orbit preservation by q. Repeating the argument with q inverse proves reflection. Conversely, preserving and reflecting SameCycle transports every saturated subset. This private consumed reconstruction bridge does not duplicate the general function-algebra antiequivalence.

**Definition 1.6 (Complete semidirect classification).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; 0 < n \Rightarrow \operatorname{MulEquiv}\left(\operatorname{ZeroFamilyAut}\left(n, a\right), \operatorname{Coordinates}\left(\operatorname{Fin}\left(\operatorname{gcd}\left(n, a\right)\right), \operatorname{Fin}\left(\operatorname{div}\left(n, \operatorname{gcd}\left(n, a\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.zeroFamilyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugating physical permutations by residueChart carries ZeroFamilyAut onto UniformPartitionAutomorphisms.Aut(Fin(g),Fin(ell)). The existing automorphismEquiv then supplies all coordinates and their uniqueness. The coordinates are (sigma,alpha), with alpha permuting the g blocks and sigma(w) permuting Fin(ell) at destination w. Multiplication is (sigma,alpha)(tau,beta)=(eta,alpha beta), where eta(w)=sigma(w)*tau(alpha inverse(w)). The action on a chart label (v,t) is (alpha(v),sigma(alpha(v))(t)). Only the natural set of g block indices is used; a regular wreath product on all elements of Sym(g) has the wrong index set.

**Theorem 1.7 (Exact factorial order).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; 0 < n \Rightarrow \operatorname{card}\left(\operatorname{ZeroFamilyAut}\left(n, a\right)\right) = \operatorname{factorial}\left(\operatorname{div}\left(n, \operatorname{gcd}\left(n, a\right)\right)\right)^{\operatorname{gcd}\left(n, a\right)} \cdot \operatorname{factorial}\left(\operatorname{gcd}\left(n, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.card_zeroFamilyAut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The group isomorphism followed by the inverse generic automorphismEquiv transports the actual group to the uniform-partition automorphism group. Its existing card_aut yields (ell!)^g*g!. Positivity of n implies g>0 and ell>0, so its nonempty-fiber hypothesis is proved internally.

All exponents remain in scope. When n divides a, including a=0, g=n and ell=1: the source is zero and the group is Sym(n). When gcd(n,a)=1 there is one orbit and again the whole Sym(n), since the zero family then consists of the empty and full subsets. For n=1 the group is trivial. No cyclic ordering inside a block is retained by the zero family; its group can exceed the rotation centralizer. These are mathematical consequences for this exact source family, not claims about arbitrary sources, the full Circle problem, or literature novelty.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.ZeroFamilyAut`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.card_zeroFamilyAut`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.residueChart`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.sameCycle_iff_chart`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.sameCycle_iff_residue`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.zeroFamilyAut_eq_orbitAut`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.zeroFamilyEquiv`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneDifferenceZeroSubsets](MersenneDifferenceZeroSubsets.md)
- Dependency: [D5/S3/FiniteGroups/UniformPartitionAutomorphisms](../../../FiniteGroups/UniformPartitionAutomorphisms.md)
