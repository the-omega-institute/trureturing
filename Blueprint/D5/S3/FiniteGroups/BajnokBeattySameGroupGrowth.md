# Same group and diameter, different growth

## Abstract

One noncyclic finite group supports equal-diameter coordinate markings with sharply different ball growth.

**Theorem 1.1 (Explicit quotient equivalences and a unique growth-gap peak).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattySameGroupGrowth.same_group_different_growth`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattySameGroupGrowth.same_group_different_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let p and t be integers with p >= 3 odd and t >= 2. Put m = 6t - 1 and D = (m^2 - 9)/2 = 18t^2 - 6t - 4. The lattice quotients for (a,b) = (1,9) and (3,3) both identify with H = Z/pZ x Z/(pD)Z. These are the actual quotients of the two displayed lattice bases, with their coordinate-generator markings. Finiteness, noncyclicity, order and exact diameter are consequences, not hypotheses. The (1,9) basis is (p(m-1)/2,p(m+1)/2), (p(m-9)/2,-p(m+9)/2); the (3,3) basis is (p(m-3)/2,p(m+3)/2), (p(m-3)/2,-p(m+3)/2). Here c19(r) and c33(r) count the images of {(x,y) in Z^2 : |x|+|y| <= r} under the respective quotient maps.

The identifications descend integer coordinate maps. For (1,9), the two rows are (-1,1) and (-3t,3t-1); for (3,3), they are (t,1-t) and (-3t-1,3t-2). Each coordinate matrix has determinant 1. For a primitive first column (x,y), Bezout coefficients alpha,beta give alpha*x+beta*y=1. The inverse integral lift of residues (A,B) is (x*A-beta*B,y*A+alpha*B). The lattice maps to zero in the product of residue groups. Surjectivity and the already established equal finite cardinalities turn the descended map into an additive equivalence. This uses the standard quotient and finite-cardinality criteria.

Both marked quotients have exact signed diameter s = (pm-1)/2. Write c19(r) and c33(r) for the cardinalities of their actual images of the signed Lee diamond. For every natural radius, c33(r) <= c19(r), with strict inequality exactly when p(m-3)/2 <= r < s. For every r >= s, both cardinalities equal p^2*D.

For 0 <= r <= s, let delta = pm-(2r+1)=2(s-r) and gap(r)=c19(r)-c33(r), interpreted as an integer. Subtracting the two established actual quotient counts cancels the full diamond count. The gap is zero if delta >= 3p. If p <= delta < 3p, twice the gap is (3p-delta)^2+1. If delta < p, the gap is 2p*delta. Positive widths are odd, so the half-cap rounding is exact; zero widths contribute zero. Beyond s, actual coverage makes each ball the entire finite quotient.

The even delta lattice and odd p force delta >= p+1 in the middle regime. The factorization (delta-p-1)(5p-delta-1) establishes the upper bound there and equality only at delta=p+1. In the terminal regime the gap is at most 2p(p-1), one below 2p^2-2p+1. Consequently the global maximum is 2p^2-2p+1, attained at exactly the natural radius r=p(m-1)/2-1. At the penultimate radius, delta=2 and the gap is 4p.

For p=3,t=2, H=Z/3Z x Z/168Z has order 504, both diameters are 16, the unique peak radius is 14 with gap 13, and the penultimate gap is 12. For p=5,t=2, the unique peak radius is 24 with gap 41. These applications illustrate that the abstract finite group and diameter together do not determine the marked growth profile.

An additive isomorphism carrying the two ordered coordinate generators to their counterparts would carry every signed word to its counterpart, preserving every ball cardinality. The positive penultimate gap rules this out. The theorem distinguishes the chosen generators on one abstract group; it does not assert that the abstract groups are nonisomorphic. It assumes no primality of p and gives no classification of all generating pairs or claim of literature novelty.

Bajnok-Beatty arXiv:2406.04045v1 supplies the Cayley-diameter problem context. The explicit comparison here is a repository derivation from the asymmetric quotient growth theorem and standard quotient/cardinality APIs. It makes no literature priority or external open-problem claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattySameGroupGrowth.same_group_different_growth`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyAsymmetricGrowth](BajnokBeattyAsymmetricGrowth.md)
