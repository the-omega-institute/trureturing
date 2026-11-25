# Attainment and the largest maximal-slope element

## Abstract

Maximal destabilizing elements of finite-length ranked lattices

Let Λ be a lattice in any universe, with integer rank r strictly increasing on comparable distinct elements. Assume r(x join y)+r(x meet y)=r(x)+r(y). Let d be real-valued and supermodular. On a nontrivial interval [a,b] put μ(a,x)=(d(x)-d(a))/(r(x)-r(a)) for a<x.

**Theorem 1.1 (Existence, maximality and uniqueness).**

Lean statement: `D5/S3/Combinatorics/Lattices/HarderNarasimhan.exists_unique_destabilizer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/HarderNarasimhan.exists_unique_destabilizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

A unique destabilizer exists if and only if a<b. It has a<e≤b, and every nonzero subinterval [a,x] of [a,b] has μ(a,x)≤μ(a,e), and every x attaining equality is contained in e. Thus e also has largest rank among the maximal-slope elements.

The existence argument does not assume an extremum. First maximize an arbitrary supermodular function on [a,b] by induction on the natural number (r(b)-r(a)).toNat. If neither endpoint maximizes it, choose an interior point above both endpoint values, maximize below it, then maximize above that maximizer. The meet and join inequality proves that this second maximizer is global.

Apply this construction to d(x)-d(a)-t(r(x)-r(a)), where t=μ(a,b). A positive maximum lies in a proper interval. Induction in that interval gives a slope maximum; uncrossing with the tilted maximizer rules out a larger slope outside it. Among the slope maxima select a largest rank in the finite integer interval [r(a),r(b)]. The join of two maxima remains a maximum, so strict rank growth forces it to contain every other maximum.

This is an abstract construction in the classical HN tradition described in the source note. The proof does not assume a finite set of lattice elements, discrete degrees, bounded degrees, a bottom element, or bottom degree zero. Integer ranks may be negative and need no global lower bound or normalization. Strict growth makes each interval rank difference nonnegative and bounds its chain length. No covolume comparison for Euclidean lattices is asserted.

Strict rank growth makes every nonzero factor have positive rank difference, excluding zero-rank pseudo-factors. Mere monotonicity fails: on the three-element chain 0<1<2, ranks (0,0,1) and degrees (0,1,0) satisfy the modular and supermodular identities, but both [2] and [1,2] are valid filtrations with total division. The zero-rank factor has slope zero, while the following factor has slope minus one.

A nonzero interval [a,e] is semistable when every a<x≤e has μ(a,x)≤μ(a,e). A filtration is a finite list of successive upper endpoints, ending at b, with nonzero semistable factors and strictly decreasing adjacent factor slopes. No maximality condition is part of this definition. Rank modularity supplies the additive denominator identity, and degree supermodularity supplies the uncrossing bound; no separate modular-lattice assumption is required.

**Theorem 1.2 (A unique filtration on every interval).**

Lean statement: `D5/S3/Combinatorics/Lattices/HarderNarasimhan.exists_unique_filtration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/HarderNarasimhan.exists_unique_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

Exactly one such endpoint list exists if and only if a≤b. When a=b this list is empty. In a nontrivial interval choose the largest maximal-slope element e and recurse on [e,b]. All nonzero quotients above e have slope strictly below μ(a,e): equality would give a larger slope maximizer.

Conversely, uncrossing with the first endpoint of any semistable descending filtration shows that it contains every maximal-slope subobject. The tail bound is strictly smaller, so a subobject attaining the first slope must lie inside that endpoint. Uniqueness of the first endpoint and induction on the tail give uniqueness of the whole list.

**Theorem 1.3 (The first and last slopes are attained extrema).**

Lean statement: `D5/S3/Combinatorics/Lattices/HarderNarasimhan.filtration_extremes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/HarderNarasimhan.filtration_extremes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

For a nonempty filtration with first endpoint e, let q be the lower endpoint of its last factor. Then a≤q<b. The first slope is the greatest of all μ(a,x), a<x≤b. The last slope μ(q,b) is the least of all μ(x,b), a≤x<b. Consequently these are exactly the real supremum defining μmax and the real infimum defining μmin. The first endpoint is the full destabilizer, containing every maximal-slope subobject. Always μ(q,b)≤μ(a,e); if the tail is nonempty this inequality is strict. The whole interval is semistable if and only if the tail is empty, equivalently μmin=μmax.

Nonemptiness supplies actual witnesses for both extrema. For a=b both slope sets are empty; Lean's real supremum and infimum conventions give μmax=μmin=0. Semistability requires a<b, so equality alone on an empty interval is not a semistability criterion.

The quotient bound is proved along the filtration. For a quotient with lower endpoint x, intersect x with the first endpoint and join x with that endpoint. Semistability bounds the lower factor, the inductive tail bounds the upper factor, and supermodularity plus the rank identity combines the two bounds for the same x. This proves attainment without a compactness or discreteness hypothesis.

These results derive HN structure in the abstract model. Applying them to Euclidean lattices still requires a lattice of saturated subobjects, strict rank, subspace covolumes and the covolume supermodularity inequality. An operator-norm slope inequality and arithmetic normalization are separate statements; neither is asserted here.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/HarderNarasimhan.exists_unique_destabilizer`
- Truth anchor: `D5/S3/Combinatorics/Lattices/HarderNarasimhan.exists_unique_filtration`
- Truth anchor: `D5/S3/Combinatorics/Lattices/HarderNarasimhan.filtration_extremes`
