# Nonconvexity of the theta representation set

## Abstract

The five-cycle has a nonconvex trace-two orthonormal representation set.

**Theorem 1.1 (Cauchy-Schwarz for finite real vectors).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], \forall v \in V \to \mathbb{R},\; \forall w \in V \to \mathbb{R},\; \operatorname{dotProduct}\left(v, w\right)^{2} \le \operatorname{dotProduct}\left(v, v\right) \cdot \operatorname{dotProduct}\left(w, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.dot_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcel K Carli Silva; Gabriel Coutinho; Thiago Oliveira; Levent Tunçel (2026). *On some k-fold generalizations of Lovász theta and their sandwich theorems*. URL: <https://arxiv.org/html/2609.06312v1>.

*Commentary.*

For real vectors indexed by any finite type, the square of their dot product is at most the product of their squared lengths.

**Definition 1.2 (The full orthonormal representation set).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \mathbb{R},\; \forall x \in V \to \mathbb{R},\; x \in \operatorname{representationSet}\left(G, k\right) \Leftrightarrow \left(\left(\forall i \in V,\; 0 \le x\left(i\right)\right) \land \left(\exists M \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{PosSemidef}\left(M\right) \land \left(\operatorname{PosSemidef}\left(1 - M\right) \land \left(\operatorname{trace}\left(M\right) = k \land \left(\exists u \in V \to \left(V \to \mathbb{R}\right),\; \left(\forall i \in V,\; \operatorname{dotProduct}\left(u\left(i\right), u\left(i\right)\right) = 1\right) \land \left(\left(\forall i \in V,\; \forall j \in V,\; \operatorname{Adj}\left(G, i, j\right) \Rightarrow \operatorname{dotProduct}\left(u\left(i\right), u\left(j\right)\right) = 0\right) \land \left(\forall i \in V,\; x\left(i\right) = \operatorname{dotProduct}\left(u\left(i\right), \operatorname{mulVec}\left(M, u\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.representationSet` (`✓ std3`).

*Citation.* Marcel K Carli Silva; Gabriel Coutinho; Thiago Oliveira; Levent Tunçel (2026). *On some k-fold generalizations of Lovász theta and their sandwich theorems*. URL: <https://arxiv.org/html/2609.06312v1>.

*Commentary.*

Section 5.3, proof of Theorem 16, defines M_k(G). The finite vertex type V indexes both vector coordinates and matrix rows and columns. All coordinates of x use the same real matrix M and the same family u. M and I-M are positive semidefinite, and tr(M)=k exactly. PosSemidef includes the real symmetry condition. Each u_i is a unit vector; orthogonality is required on every edge of G. This is the source's orthonormal representation of the complement of G. There is no orthogonality condition on nonedges, no rank constraint, and no requirement that M be a projector. The real dot product on V->R is the standard Euclidean inner product in dimension |V|.

**Definition 1.3 (The universal affirmative convexity assertion).**

$$\mathrm{claim} \Leftrightarrow \left(\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], 1 \le \operatorname{FintypeCard}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \mathbb{R},\; 0 < k \Rightarrow \left(k \le \operatorname{NatCastReal}\left(\operatorname{FintypeCard}\left(V\right)\right) \Rightarrow \operatorname{Convex}\left(\mathbb{R}, \operatorname{representationSet}\left(G, k\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.claim` (`✓ std3`).

*Citation.* Marcel K Carli Silva; Gabriel Coutinho; Thiago Oliveira; Levent Tunçel (2026). *On some k-fold generalizations of Lovász theta and their sandwich theorems*. URL: <https://arxiv.org/html/2609.06312v1>.

*Commentary.*

Section 7 item (iv) asks: Is the orthonormal representation set M_k(G) convex? The affirmative assertion quantifies over every finite nonempty vertex type, every ordinary simple graph, and every real k with 0<k<=|V|. Convexity means closure under all real convex combinations, with both points, both nonnegative coefficients, and their sum-one condition quantified. DecidableEq is supplied classically on every finite vertex type and adds no graph restriction. The upper bound on k is feasibility of the matrix constraints. The source's separate question about the closed convex lower hull is outside this assertion.

**Theorem 1.4 (The five-cycle refutes convexity).**

$$\neg \mathrm{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.result` (`✓ std3`). ∎

*Resolves.* `Problems/carli-silva-2026-theta-representation-convexity-clause` (refuted) by `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"carli-silva-2026-theta-representation-convexity-clause","declaration_gid":"D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marcel K Carli Silva; Gabriel Coutinho; Thiago Oliveira; Levent Tunçel (2026). *On some k-fold generalizations of Lovász theta and their sandwich theorems*. URL: <https://arxiv.org/html/2609.06312v1>.

*Commentary.*

Label the five-cycle by 0,1,2,3,4, with edges 01,12,23,34,40. The points a=(0,1,1,1,1), b=(1,0,1,1,1), c=(1,1,0,1,1) belong to M_2(C_5). Use M=diag(1,1,0,0,0) and coordinate vectors e_0,e_1,e_2 in R^5. The vector families for a,b,c respectively are (e_2,e_0,e_1,e_0,e_1), (e_1,e_2,e_0,e_1,e_0), and (e_0,e_1,e_2,e_0,e_1). Every edge has orthogonal vectors. Their equal average is t=(2/3,2/3,2/3,1,1).

Suppose any allowed M and u realize t. Write A=u_3 and B=u_4. These are orthogonal unit vectors. Since the quadratic forms of I-M vanish at A and B, positivity implies MA=A and MB=B. Set P=AA^T+BB^T. For any w, subtract its A and B components to obtain r(w). Expansion gives w^T(M-P)w=r(w)^T M r(w)>=0. Thus M-P is positive semidefinite. Its trace is 2-1-1=0, so the positive semidefinite trace-zero theorem gives M=P. This derives the projection from the full contraction domain.

Let alpha=A dot u_0, beta=B dot u_2, p=A dot u_1, and q=B dot u_1. Edges 40 and 23 give B dot u_0=0 and A dot u_2=0. Hence alpha^2=beta^2=2/3 and p^2+q^2=2/3. The three residuals r(u_0),r(u_1),r(u_2) each have squared length 1/3. Edges 01 and 12 give residual inner products -alpha p and -beta q. Cauchy-Schwarz therefore yields (2/3)p^2<=1/9 and (2/3)q^2<=1/9, or p^2,q^2<=1/6. Their sum is at most 1/3, contradicting 2/3. This excludes every possible realization.

If M_2(C_5) were convex, first averaging b and c with coefficients 1/2,1/2 and then combining a and that average with 1/3,2/3 would put t in the set. Its exclusion proves nonconvexity. The counterexample uses k=2>1 and |V|=5. No characterization of the closed convex lower hull follows from this theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.claim`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.dot_cauchy`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.representationSet`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.result`
