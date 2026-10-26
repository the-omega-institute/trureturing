# Tournament Hessian: result

## Abstract

Regular tournament Hessians: result.

## The Hessian closed form and rational square

§1, Conjecture 6: “For every regular tournament $T^{*}$ on at least three vertices, $\mathcal {H} \ne 0$ and $\frac{d}{\mathcal {H}}$ is the square of a rational.”

**Theorem 1.1 (The closed form for the analytic Hessian determinant).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow (\operatorname {calH}\left(h\right) = \frac{\operatorname {Nat.cast}\left(d\right) \cdot \operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)^{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)^{2}\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.calH_closedForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every regular tournament of order d at least three and every complex C2 local solution h, the actual real angular Hessian determinant is d times det(d²I+S²) divided by det(d²I−S²). The Hessian is defined by two real Frechet derivatives of the logarithmic phase.

**Theorem 1.2 (The rational-square conjecture).**

$$\forall d \in \mathbb {N},\; (3 \le d) \Rightarrow (\forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow ((\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right)) \land (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {calH}\left(h\right) \ne 0) \land (\exists q \in \mathbb {Q},\; \frac{d}{\operatorname {calH}\left(h\right)} = \operatorname {Rat.cast}\left(q\right)^{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/wormald-2026-tournament-hessian-square` (proved) by `D5/S3/Combinatorics/WormaldTournamentHessian/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wormald-2026-tournament-hessian-square","declaration_gid":"D5/S3/Combinatorics/WormaldTournamentHessian/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Write C=½I+A and let J have every entry equal to one. Tournament completeness gives 2C=J+S. For nonzero coordinates y and nonsingular Q(y)=diag(2/y)−S, the matrix determinant lemma factors K(y) as det Q(y), the product of the coordinates y_j/2, and one minus the sum of all entries of Q(y) inverse. Call that inverse-entry sum alpha. At the constant point z=2/d, the resolvent is dI−S. Strict diagonal dominance makes it nonsingular, and regularity gives row and column sums 1/d for its inverse.

The resolvent inverse and alpha are complex C2 near the constant point. Every first coordinate derivative of alpha there is 1/2. Its second derivative in coordinates j and k is z to the power minus two times V_jk+V_kj, minus z inverse when j=k, where V=(dI−S) inverse. The equation alpha(y,h(y))=1 holds on a neighbourhood for every local solution. Its first derivative gives each coordinate derivative of h equal to minus one; its second derivative gives the corresponding difference of four alpha second derivatives.

The exponential coordinate chart and the principal logarithm are C2 at the base point because h takes the positive value z there. Applying the second Frechet chain rule and then substituting imaginary angular coordinates identifies the actual angular Hessian with minus R transpose T R. Here the columns of R are e_j−e_d and T=I−d(V+V transpose). Both row and column sums of T are minus one. The matrix whose columns are R followed by the all-ones vector has determinant d; conjugating T by this matrix gives diagonal blocks R transpose T R and minus d. Consequently det(R transpose T R)=−d det T.

The resolvent identity gives T=−(d²I+S²)(d²I−S²) inverse. All required inverses follow from the nonzero shifted determinants. The order d is odd, so its determinant contributes one minus sign, while the angular Hessian has the even size d−1 and its overall minus sign does not change its determinant. This proves the displayed closed form for calH.

Transposition identifies det(dI−S) with det(dI+S). Factoring the quadratic matrices therefore makes det(d²I−S²) the square of an integer. In odd dimension, det(S+idI) is a purely imaginary Gaussian integer; dividing it by i gives a nonzero integer, and det(d²I+S²) is its square. The quotient of these two quadratic determinants is thus the square of a nonzero rational. The closed form identifies this quotient with d divided by calH, and also gives nonvanishing of calH.

Finally, every first coordinate derivative of K at the constant point equals −det(dI−S)/(2d^d), which is nonzero. The complex implicit function theorem supplies a C2 local solution with value z and the required equation germ. Together with the Hessian calculation for every such solution, this proves both clauses of the conjecture.

## References

- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.calH_closedForm`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.result`
- Dependency: [D5/S3/Combinatorics/WormaldTournamentHessian/Derivative](Derivative.md)
