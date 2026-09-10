# First and maximum Egyptian fraction denominators

## Abstract

Separation of the first and maximal third denominators forces residue one modulo five.

**Definition 1.1 (Ordered integer solutions).**

$$\operatorname{IsSolution}\left(k, x, y, z\right) \iff 0<x<y<z \land 5xyz=k(yz+xz+xy)$$

*Formalization.* `D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.IsSolution` (`✓ std3`).

*Citation.* David Batista (2026). *OEIS A398581, separation of the lexicographically first and maximum-z Egyptian fraction solutions*. URL: <https://oeis.org/A398581>.

*Commentary.*

All four parameters are natural numbers. The defining equation is integral, and the three denominators are positive and strictly increasing.

**Definition 1.2 (The first solution).**

$$\operatorname{IsLexFirst}\left(k, x, y, z\right) \iff \operatorname{IsSolution}\left(k, x, y, z\right) \land (\forall u,v,w, \operatorname{IsSolution}\left(k, u, v, w\right) \Rightarrow (x<u \lor (x=u \land (y<v \lor (y=v \land z\le w)))))$$

*Formalization.* `D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.IsLexFirst` (`✓ std3`).

*Citation.* David Batista (2026). *OEIS A398581, separation of the lexicographically first and maximum-z Egyptian fraction solutions*. URL: <https://oeis.org/A398581>.

*Commentary.*

The predicate includes being a solution and preceding every solution in the lexicographic order on all three coordinates. It does not assume that every parameter has a solution.

**Theorem 1.3 (Separation forces residue one).**

$$\operatorname{IsLexFirst}\left(k, x, y, z\right) \land (\exists u,v,w, \operatorname{IsSolution}\left(k, u, v, w\right) \land z<w) \Rightarrow \operatorname{mod}\left(k, 5\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.first_maximum_separation_mod_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Batista (2026). *OEIS A398581, separation of the lexicographically first and maximum-z Egyptian fraction solutions*. URL: <https://oeis.org/A398581>.

*Commentary.*

Any competing solution with a larger third coordinate forces k to be one modulo five. A maximum-z solution supplies such a competitor whenever its third coordinate exceeds that of the first. The converse is not asserted.

Write a=5x-k and b=kx. The positive integer gap ay-b bounds z. Before 5x=2k the bound decreases with x; after that point the strict order gives 25z <= 2k(2k+5). Explicit solutions at x=floor(k/5)+1 dominate all later x in residues zero, two, three and four. In the difficult residue-two branch, a=8 cannot have gap one, since this would force a square to be three modulo four. Small parameter branches use the same residual estimate.

## References

- Truth anchor: `D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.IsLexFirst`
- Truth anchor: `D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.IsSolution`
- Truth anchor: `D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.first_maximum_separation_mod_five`
