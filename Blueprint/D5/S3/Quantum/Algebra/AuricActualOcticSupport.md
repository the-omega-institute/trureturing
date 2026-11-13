# Actual octic support connectivity

## Abstract

Directed support of the actual octic window operator.

F has characteristic zero, D/F has degree eight, and W is an arbitrary four dimensional F subspace whose multiplication idealizer is exactly F. The element a lies outside Q(W), the set of quotients of elements of W with nonzero denominator. K/F is a finite normal extension containing the same D, and L/K is any field extension. Omega consists of the literal F algebra embeddings of D into K.

nonzeroSupport(N) has an arrow from sigma to tau exactly when N(sigma,tau) is nonzero. StronglyConnected means that every ordered pair is joined by a finite directed path, allowing a path of length zero. The matrix map applies the coefficient embedding K to L to each entry; it leaves all embedding labels fixed. The constrained n and N express the let bindings defining the original inverse-obstruction matrix.

**Theorem 1.1 (Strong connectivity over every coefficient extension).**

$$\forall F \in Type,\; \forall D \in Type,\; \forall K \in Type,\; \forall L \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Field}\left(D\right)] [\operatorname{Field}\left(K\right)] [\operatorname{Field}\left(L\right)] [\operatorname{Algebra}\left(F, D\right)] [\operatorname{Algebra}\left(F, K\right)] [\operatorname{Algebra}\left(D, K\right)] [\operatorname{Algebra}\left(K, L\right)] [\operatorname{IsScalarTower}\left(F, D, K\right)] [\operatorname{FiniteDimensional}\left(F, D\right)] [\operatorname{CharZero}\left(F\right)] [\operatorname{FiniteDimensional}\left(F, K\right)] [\operatorname{Normal}\left(F, K\right)] \forall W \in \operatorname{Submodule}\left(F, D\right),\; \forall a \in D,\; ((\operatorname{finrank}\left(F, D\right) = 8) \land ((\operatorname{finrank}\left(F, W\right) = 4) \land ((\operatorname{Idealizer}\left(F, D, W\right) = \operatorname{range}\left(\operatorname{algebraMap}\left(F, D\right)\right)) \land (\neg a \in \operatorname{quotientSet}\left(W\right))))) \Rightarrow (\exists e \in \operatorname{AlgEquiv}\left(K, \operatorname{Tensor}\left(F, K, D\right), \operatorname{Map}\left(\operatorname{AlgHom}\left(F, D, K\right), K\right)\right),\; (\forall c \in K,\; \forall z \in D,\; \forall sigma \in \operatorname{AlgHom}\left(F, D, K\right),\; \operatorname{apply}\left(e, \operatorname{tensor}\left(c, z\right), sigma\right) = c \cdot \operatorname{apply}\left(sigma, z\right)) \land (\forall n \in \operatorname{LinearMap}\left(K, \operatorname{Map}\left(\operatorname{AlgHom}\left(F, D, K\right), K\right), \operatorname{Map}\left(\operatorname{AlgHom}\left(F, D, K\right), K\right)\right),\; (n = \operatorname{compose}\left(\operatorname{linear}\left(e\right), \operatorname{baseChange}\left(K, \operatorname{actualOperator}\left(W, a\right)\right), \operatorname{linear}\left(\operatorname{inverse}\left(e\right)\right)\right)) \Rightarrow (\forall N \in \operatorname{Matrix}\left(\operatorname{AlgHom}\left(F, D, K\right), \operatorname{AlgHom}\left(F, D, K\right), K\right),\; (N = \operatorname{toMatrix}\left(n\right)) \Rightarrow ((\operatorname{StronglyConnected}\left(\operatorname{nonzeroSupport}\left(N\right)\right)) \land (\operatorname{StronglyConnected}\left(\operatorname{nonzeroSupport}\left(\operatorname{map}\left(\operatorname{algebraMap}\left(K, L\right), N\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricActualOcticSupport.general43_2_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical evaluation splitting sends c tensor d to the function sigma maps to c times sigma(d). The strict projection rank inequality gives 2 rho(S) at least card(S)+1 for every nonempty proper S. Rank-nullity for the same actual operator, whose kernel and image are the split window, bounds 2 rho(S) above by card(S) plus rank N[S,S complement]. Every such crossing block therefore has positive rank. If sigma cannot reach tau, let S consist of the vertices that can reach tau. It contains tau and excludes sigma. Every entry from S complement to S is zero, since a nonzero entry would extend a path to tau. This contradicts the positive crossing rank for S complement. Finally the coefficient embedding is injective, so every edge and every finite path remains present over L. This establishes the support condition for the same actual N. Irreducibility of its determinantal polynomial and the normalized original equation are separate claims.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/AuricActualOcticSupport.general43_2_support`
- Dependency: [D5/S3/Quantum/Algebra/AuricActualOcticWindow](AuricActualOcticWindow.md)
