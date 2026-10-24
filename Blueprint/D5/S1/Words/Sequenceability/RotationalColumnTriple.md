# Rotational columns with an additive triple

## Abstract

Directed rotational columns with a consecutive additive triple.

**Theorem 1.1 (Every prime at least seven).**

Lean statement: `D5/S1/Words/Sequenceability/RotationalColumnTriple.exists_rotational_column_triple`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/RotationalColumnTriple.exists_rotational_column_triple` (`✓ std3`). ∎

*Citation.* M. A. Ollis and D. T. Willmott (2011). *On twizzler, zigzag and graceful terraces*. URL: <https://ajc.maths.uq.edu.au/pdf/51/ajc_v51_p243.pdf>.

*Commentary.*

For every prime p at least seven, there is a function d from the cyclic phase group ZMod (p-1) to ZMod p. The function bijects all phases onto exactly the nonzero residues. Its actual directed cyclic differences d(i+1)-d(i) biject the same nonzero set, including the closing edge. After rotation its consecutive entries satisfy d(1)=d(0)+d(2). Since p-1 is at least six, the three phases are distinct.

Put p=2m+1. A graceful permutation g of 1 through m has adjacent absolute differences 1 through m-1, each once. Signed doubling forms g followed by reverse(g)+m. Each internal edge has a reflected edge with opposite sign. The middle edge is m and the closing edge is -m, giving precisely both signs of each length 1 through m. The integer bounds prove that no label vanishes modulo p; finite cardinality turns this complete surjectivity into the two bijections.

When m=3k, the Walecki formula w(2j)=j+1 and w(2j+1)=m-j has the consecutive triple (k,2k+1,k+1), including k=1. For m congruent to two modulo three and at least eight, reverse every full Walecki block of four. Choose the tail length R as 0,5,2,3 for m modulo four equal to 0,1,2,3, and put a=(m-R)/2+1. The tails are empty, (a,a+1), (a+1,a+2,a), or (a+3,a+2,a,a+4,a+1). Their seam has length R when the tail is nonempty, and the internal lengths complete 1 through R-1. The proof establishes the vertex and edge injectivity of these explicit formulas, with no supplied graceful certificate.

For m=6h+2 the twizzler triple centered at phase 4h is (2h-1,4h+1,2h+2), with zero neighbor-sum residual. For m=6h+5 it is centered at 4h+3 and equals (4h+5,2h+1,4h+2), with residual m+1. The last entry at h=1 or h=2 belongs to the tail and is included in the proof. A zero residual gives the first-half additive triple. A residual m+1 gives it in the reversed shifted half, because the shifted residual is p. Translation in the cyclic phase group preserves both inventories and moves this triple to phases zero, one, two.

Primality excludes m congruent to one modulo three. The remaining small case p=11 uses the literal column (1,3,2,7,4,8,6,9,10,5); its directed differences are (2,10,5,8,4,9,3,1,6,7). The construction follows the published Walecki and twizzler methods of Ollis and Willmott, with a shifted reverse of their Table 1 tail. The directed signed conversion and triple locations are checked here. No novelty claim is made.

The additive relation is the column part of the future two-orbit cut identity: one column equals the sum of its two neighbors, allowing the missing first-coordinate labels to match the splice. For a finite field K of characteristic p and nonzero u in K, in that planned lift put B=d(0), A=d(1), C=d(2), choose the phase-two row offset 2u and all other offsets zero. The heads are (C,2u) and (A,u), with predecessors (A,0) and (B,-u). The column identities C-A=-B and A-B=C make the removed vectors (-B,2u) and (C,2u) equal the replacement vectors to (0,u) and from (0,0); the remaining cross-edge has vector (0,u). These are the intended next-stage row equations, not additional claims of the column theorem. This source proves only the column supplier. The full-vector row relation, conjugate lift, whole-set surgery, endpoints, path enumeration and coefficient-one prefix and interval conclusions remain to be proved, as does the separate characteristic-five construction. Arbitrary subsets in the same original ambient group remain outside this result.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/RotationalColumnTriple.exists_rotational_column_triple`
