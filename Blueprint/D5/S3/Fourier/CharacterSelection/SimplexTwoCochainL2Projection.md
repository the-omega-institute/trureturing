# Ordered Simplex Two-Cochain Energy and Optimal Coefficient

## Abstract

Exact squared-energy projection and optimal coefficient for alternating ordered triangle cochains.

**Definition 1.1 (Triangle contraction).**

Lean statement: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.contraction`

*Formalization.* `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.contraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite vertex type V and a real triangle cochain F, S(i,j) is the sum of F(r,i,j) over every r in V.

**Definition 1.2 (Averaged edge cochain).**

Lean statement: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.averageEdge`

*Formalization.* `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.averageEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n=|V|, the edge cochain a(i,j) is S(i,j)/n. The energy theorem assumes V is nonempty, so this denominator is nonzero.

**Definition 1.3 (Edge coboundary).**

Lean statement: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.edgeCoboundary`

*Formalization.* `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.edgeCoboundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The triangle coboundary of an edge cochain a is da(i,j,k)=a(j,k)-a(i,k)+a(i,j).

**Definition 1.4 (Tetrahedral defect).**

Lean statement: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.tetraDefect`

*Formalization.* `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.tetraDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a triangle cochain F, dF(r,i,j,k)=F(i,j,k)-F(r,j,k)+F(r,i,k)-F(r,i,j).

**Theorem 1.5 (Exact tetrahedral energy and optimal coefficient).**

$$(\forall F \in \mathcal{A}, T(F) = 4nE(F))\quad\land\quad(n \geq 4 \implies \forall C \in \mathbb{R}, (\forall F \in \mathcal{A}, T(F) \leq CE(F)) \implies 4n \leq C)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any nonempty finite vertex type, n=|V|, and F a real triangle cochain. Assume F(j,i,k)=-F(i,j,k) and F(i,k,j)=-F(i,j,k) for every i,j,k. Let A be the set of all such alternating cochains. With S, a, da, and dF as above, define T(F) as the sum of dF(r,i,j,k)^2 over all ordered quadruples and E(F) as the sum of (F(i,j,k)-da(i,j,k))^2 over all ordered triples. Both sums include repeated vertices, and a is the averaged edge cochain of the particular F. No cocycle or exactness hypothesis is imposed.

For every alternating F, T(F)=4n E(F). If n>=4 and a real constant C satisfies T(F)<=C E(F) for every alternating F, then 4n<=C. When n>=4, 4n is the least admissible real coefficient, and for each C<4n an alternating cochain violates the bound.

The residual R=F-da is alternating and its sum over any one vertex vanishes. The edge coboundary has zero tetrahedral defect, so dF=dR. Expanding the four face terms gives four diagonal sums, each n times the squared norm of R. Each of the six mixed sums vanishes by a zero contraction. Thus the defect energy is exactly 4n times the residual energy.

For optimality when n>=4, choose four distinct vertices p0,p1,p2,p3 in V. Define u(x), v(x), and w(x) to be 1 at p1,p2,p3, respectively, and 0 elsewhere. The determinant cochain is F(i,j,k)=u(i)v(j)w(k)+u(j)v(k)w(i)+u(k)v(i)w(j)-u(i)v(k)w(j)-u(j)v(i)w(k)-u(k)v(j)w(i). Swapping either adjacent pair changes its sign. It has F(p1,p2,p3)=1 and vanishes whenever an argument is p0. Hence dF(p0,p1,p2,p3)=1, so T(F)>0. The energy equality and 4n>0 imply E(F)>0. Applying the universal C-bound to this cochain and cancelling its positive residual energy gives 4n<=C.

The complete-simplex spectral setting is classical. The theorem states its ordered-sum normalization, averaged edge reconstruction, and optimal coefficient.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.averageEdge`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.contraction`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.edgeCoboundary`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.tetraDefect`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.tetra_defect_energy_eq_and_optimal`
