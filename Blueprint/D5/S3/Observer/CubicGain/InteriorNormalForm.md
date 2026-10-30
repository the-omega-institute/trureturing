# Integer rigidity of positive lattice transitions

## Abstract

Primitive positive integer columns constrain both signs of every legal transition.

Matrices act on columns by left multiplication. A finite Boolean word has false=M=[[0,1],[1,1]] and true=J=[[0,1],[1,0]], and its head acts first. LegalMatrixMonoid identifies exactly its matrices with nonnegative integral matrices of determinant +1 or -1, including empty and nonempty words with identity matrix. An integer matrix A is compared with its entrywise real cast real(A).

Let v=(x,y) and r=(d,c) be strictly positive primitive integer columns, with t=xc-yd>0. A transition of integer size j>=1 sends v to vprime=(x+jd,y+jc). The determinant sign is epsilon=det(A). All inequalities below retain this same matrix and these same columns.

For every integer matrix A and integer x,y,d,c,j, TransitionHypotheses means precisely nonnegative entries, determinant +1 or -1, x,y,d,c>0, gcd(x,y)=gcd(d,c)=1, xc-yd>0, j>=1, and A*(x,y)=(x+jd,y+jc). TransitionCertificate(A,x,y,d,c,j,l) is exactly the conjunction of the eight conclusions below, including l>=1, the vector identity, both entry identities, both determinant-conditional rational bounds, the positive-sign y<c implication and y<2c.

**Theorem 1.1 (The integral transition coefficient and both rational bounds).**

$$\forall A,x,y,d,c,j, \operatorname{TransitionHypotheses}(A, x, y, d, c, j)\implies \exists l\in \mathbb{Z}, \operatorname{TransitionCertificate}(A, x, y, d, c, j, l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/InteriorNormalForm.transition_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative integral A of either unimodular sign satisfying Av=vprime, an integer lambda>=1 satisfies Ar=epsilon*r+lambda*vprime. The lower-left and upper-left identities are t*A10=c*(y+jc-epsilon*y)-lambda*y*(y+jc) and t*A00=c*(x+jd)-epsilon*d*y-lambda*y*(x+jd). If epsilon=1, lambda<=j*c^2/(y*(y+jc)) and y<c. If epsilon=-1, lambda<=c*(1/y+1/(y+jc)). For both signs y<2c. The hypotheses retain every positivity, primitivity and action condition.

The given forward word preserves primitivity, so Bezout coefficients of vprime recover an integer multiplier from the integer vector Ar-epsilon*r parallel to vprime. In the negative-determinant branch positivity gives lambda>0. In the positive-determinant branch the strict increase of the coordinate sum on v excludes both identity and J; the same word must strictly increase the sum on the positive column r. Nonnegativity of the lower-left entry then gives both rational bounds and their consequences.

TwoTransitionHypotheses(K,H,x,y,d,c,j,h) means exactly the positivity, primitivity, t>0, x>d, j,h>=1, nonnegative integer entries and either unimodular determinant sign for both matrices, and the two consecutive action equations stated below.

**Theorem 1.2 (Two consecutive increments force the last matrix).**

$$\forall K,H,x,y,d,c,j,h, \operatorname{TwoTransitionHypotheses}(K, H, x, y, d, c, j, h)\implies j=1\land y=d\land c=x+hd\land \operatorname{H}(0, 0)=0\land \operatorname{H}(0, 1)=1\land \operatorname{H}(1, 0)=1\land \operatorname{H}(1, 1)=h$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/InteriorNormalForm.last_transition_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two consecutive legal matrices K,H, suppose Kv=v+jr and H(v+jr)=v+(j+h)r, with j,h>=1 and x>d. Then j=1, y=d, c=x+hd and H=[[0,1],[1,h]]. Both initial determinant signs remain allowed.

Apply the transition coefficient result to H with the input column v+jr. Its second coordinate is greater than c, so H has negative determinant and that coordinate is less than 2c, forcing j=1. The lower-left inequality excludes lambda>=2. The upper-left identity and x>d put the integral entry H00 between zero and one, so H00=0. Determinant -1 makes both off-diagonal entries one. The two original action equations then force y=d, c=x+hd and H11=h.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/InteriorNormalForm.last_transition_rigidity`
- Truth anchor: `D5/S3/Observer/CubicGain/InteriorNormalForm.transition_certificate`
- Dependency: [D5/S3/Observer/CubicGain/PhaseRigidity](PhaseRigidity.md)
