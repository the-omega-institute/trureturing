# Positive Rank-One Secants

## Abstract

Exact secant directions of strictly positive real rank-one matrices.

Source is the set of real 2 by 2 matrices R with every entry strictly positive and R11 R22 = R12 R21. These are precisely the strictly positive rank-one relation matrices. The diagonal entries of a traceless difference are a and -a.

**Theorem 1.1 (The complete traceless secant criterion).**

$$\forall a,b,c: \mathbb{R}, \begin{pmatrix}a&b\\c&-a\end{pmatrix} \neq 0 \implies ((\exists R_{0},R_{1}: \operatorname{Source}, \begin{pmatrix}a&b\\c&-a\end{pmatrix} = R_{1}-R_{0}) \iff (a \neq 0 \lor bc < 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/PositiveRankOneSecants.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero hypothesis excludes coincident endpoints. No condition on the determinant of the difference is imposed. Since the difference is traceless, the two endpoints have equal trace; since the difference is nonzero, they are distinct.

For necessity when a = 0, the diagonal entries agree. The rank-one equations then equate the products of the two offdiagonal entries. Subtracting those products gives b times the second endpoint's lower-left entry plus c times the first endpoint's upper-right entry equal to zero. Positivity and the nonzero difference force b and c to have opposite signs.

For a nonzero diagonal choose L = 1 + abs(b) + abs(c), T = (a squared + bc + (b+c)L)/a, and H = sqrt(T squared + 4L squared). Put p = (H-T)/2 and s = (H+T)/2. Then p and s are positive, ps = L squared, and s-p = T. The endpoints have rows (p,L),(L,s) and (p+a,L+b),(L+c,s-a). The second rank-one equation and the sign of a ensure that both its diagonal entries are positive.

For a = 0 and b > 0 > c, put d = sqrt(-2bc). The endpoints have rows (d,b),(-2c,d) and (d,2b),(-c,d). Their entries are positive, both offdiagonal products equal d squared, and their difference is the required matrix. For b < 0 < c apply this construction to the negative difference and exchange the endpoints.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/PositiveRankOneSecants.result`
- Dependency: [D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings](SelfCalibratingRulings.md)
