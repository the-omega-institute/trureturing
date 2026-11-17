# Sharp rectangular Birkhoff contraction

## Abstract

A positive finite rectangular matrix with nonempty row and column types has exact Hilbert image diameter log Theta and least nonnegative contraction coefficient (sqrt Theta-1)/(sqrt Theta+1).

The row and column types are finite, may be empty, and live in independent universes. The notation entry(A,i,j) means the real matrix entry A(i,j), and mulVec is the finite matrix-vector sum. Positive means strict positivity in every coordinate and is defined for any coordinate type. The definitions below impose no positivity assumption on their vector or matrix arguments. The contraction theorem assumes nonempty row and column types, strictly positive matrix entries, and strictly positive input vectors.

$\forall (K : \operatorname{Type}\left(\right)), \forall (x : K \to \mathbb{R}), \operatorname{Positive}\left(x\right) \iff \forall (k : K), 0 < \operatorname{x}\left(k\right)$

The operators iSup and iInf denote the total real indexed supremum and infimum of the displayed families. Both are zero for an empty index type; for a finite nonempty index type they are the maximum and minimum. The index in theta is a single quadruple in the product of two row types and two column types. Real division and logarithm use the total conventions a/0=0, log(0)=0, and log(a)=log(abs(a)). For a finite nonempty coordinate type, distance is log of the maximum coordinate ratio divided by the minimum. For a strictly positive matrix with nonempty row and column types, diagonal cross ratios show Theta is at least one. Kappa is (sqrt Theta-1)/(sqrt Theta+1).

$\forall (K : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(K\right)] \forall (x : K \to \mathbb{R}), \forall (y : K \to \mathbb{R}), \operatorname{distance}\left(x, y\right) = \operatorname{log}\left(\frac{\operatorname{iSup}_{k : K} \frac{\operatorname{x}\left(k\right)}{\operatorname{y}\left(k\right)}}{\operatorname{iInf}_{k : K} \frac{\operatorname{x}\left(k\right)}{\operatorname{y}\left(k\right)}}\right)$

$\forall (I : \operatorname{Type}\left(\right)), \forall (J : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] \forall (A : \operatorname{Matrix}\left(I, J, \mathbb{R}\right)), \operatorname{theta}\left(A\right) = \operatorname{iSup}_{(i,k,j,l) : I \times I \times J \times J} \frac{\operatorname{entry}\left(A, i, j\right) \cdot \operatorname{entry}\left(A, k, l\right)}{\operatorname{entry}\left(A, i, l\right) \cdot \operatorname{entry}\left(A, k, j\right)}$

$\forall (I : \operatorname{Type}\left(\right)), \forall (J : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] \forall (A : \operatorname{Matrix}\left(I, J, \mathbb{R}\right)), \operatorname{kappa}\left(A\right) = \frac{\sqrt{\operatorname{theta}\left(A\right)}-1}{\sqrt{\operatorname{theta}\left(A\right)}+1}$

imageDistances(A) consists of distance(Ax,Ay) for all strictly positive x and y. coefficients(A) consists of all real c at least zero such that distance(Ax,Ay) is at most c times distance(x,y) for every such pair. IsLUB asserts both the upper bound and its leastness; IsLeast asserts membership and minimality.

$\forall (I : \operatorname{Type}\left(\right)), \forall (J : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] \forall (A : \operatorname{Matrix}\left(I, J, \mathbb{R}\right)), \forall (r : \mathbb{R}), r \in \operatorname{imageDistances}\left(A\right) \iff \exists (x : J \to \mathbb{R}), \exists (y : J \to \mathbb{R}), (\operatorname{Positive}\left(x\right)) \land ((\operatorname{Positive}\left(y\right)) \land (\operatorname{distance}\left(\operatorname{mulVec}\left(A, x\right), \operatorname{mulVec}\left(A, y\right)\right) = r))$

$\forall (I : \operatorname{Type}\left(\right)), \forall (J : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] \forall (A : \operatorname{Matrix}\left(I, J, \mathbb{R}\right)), \forall (c : \mathbb{R}), c \in \operatorname{coefficients}\left(A\right) \iff (0 \leq c) \land (\forall (x : J \to \mathbb{R}), \forall (y : J \to \mathbb{R}), (\operatorname{Positive}\left(x\right)) \Rightarrow ((\operatorname{Positive}\left(y\right)) \Rightarrow (\operatorname{distance}\left(\operatorname{mulVec}\left(A, x\right), \operatorname{mulVec}\left(A, y\right)\right) \leq c \cdot \operatorname{distance}\left(x, y\right))))$

**Theorem 1.1 (Exact image diameter and least contraction coefficient).**

$$\forall (I : \operatorname{Type}\left(\right)), \forall (J : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] [\operatorname{Nonempty}\left(I\right)] [\operatorname{Nonempty}\left(J\right)] \forall (A : \operatorname{Matrix}\left(I, J, \mathbb{R}\right)), (\forall (i : I), \forall (j : J), 0 < \operatorname{entry}\left(A, i, j\right)) \Rightarrow ((\forall (x : J \to \mathbb{R}), (\operatorname{Positive}\left(x\right)) \Rightarrow (\operatorname{Positive}\left(\operatorname{mulVec}\left(A, x\right)\right))) \land ((\operatorname{IsLUB}\left(\operatorname{imageDistances}\left(A\right), \operatorname{log}\left(\operatorname{theta}\left(A\right)\right)\right)) \land ((\operatorname{sSup}\left(\operatorname{imageDistances}\left(A\right)\right) = \operatorname{log}\left(\operatorname{theta}\left(A\right)\right)) \land ((\operatorname{IsLeast}\left(\operatorname{coefficients}\left(A\right), \operatorname{kappa}\left(A\right)\right)) \land ((0 \leq \operatorname{kappa}\left(A\right)) \land (\operatorname{kappa}\left(A\right) < 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/BirkhoffSharpContraction.sharp_contraction` (`✓ std3`). ∎

*Citation.* S. P. Eveson and R. D. Nussbaum (1995). *An elementary proof of the Birkhoff-Hopf theorem*. DOI: [10.1017/S0305004100072911](https://doi.org/10.1017/S0305004100072911). URL: <https://sites.math.rutgers.edu/~nussbaum/Pubs/nusseveson1995.pdf>.

*Commentary.*

The entrywise maximal cross ratio bounds the cross ratio of the images of two nonnegative residual vectors, by multiplying each minor inequality by the two coordinate weights and summing. For minimum and maximum input ratios m and M, the residuals x-m y and M y-x are nonnegative. If m equals M, the pair is proportional. Otherwise both residual images are positive and the scalar two-dimensional Birkhoff inequality gives the factor kappa. Taking the extremal output row pair gives the upper estimate.

For the diameter lower bound, take a minor attaining Theta. The vectors e(j)+eta times the all-ones vector and e(l)+eta times the all-ones vector are strictly positive for eta positive. Their selected output row contrast tends to log Theta as eta tends to zero from above. Thus every number strictly below log Theta is exceeded by an actual positive image distance.

For coefficient leastness, a smaller nonnegative c forces Theta greater than one and distinct maximizing columns j and l. Put L=sqrt Theta and q=A(i,l)L/A(i,j). Choose t positive with c t below log((1+L exp(t))/(L+exp(t))); the derivative at zero of this curve is kappa. The vector w(eta,t) has coordinate q exp(t) at j, one at l, and eta elsewhere. The pair w(eta,t), w(eta,0) has input distance exactly t for every positive eta. For this fixed t its selected output row contrast tends to that scalar curve as eta tends to zero. Choosing eta afterwards defeats c.

Singleton types, rank-one matrices, Theta equal to one, and proportional input pairs are included. The diameter and coefficient are supremal and leastness statements; they need not be attained by a distinct positive pair. No square shape, common universe, rank, invertibility, stochasticity or normalization assumption is used. Empty coordinate types and zero input coordinates are outside the theorem's asserted domain.

The result is classical. Eveson and Nussbaum give the scalar sharpness and rectangular diameter formulas. The consumed upper estimates adapt TauCetiProject/TauCeti revision afa08a3ed16fb167e35de371afb1eb03fbc5913a under Apache-2.0; the complete license is docs/reports/licenses/tauceti-birkhoff/LICENSE.txt. The adaptation uses finite max/min distance and the direct square-root coefficient.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/BirkhoffSharpContraction.sharp_contraction`
