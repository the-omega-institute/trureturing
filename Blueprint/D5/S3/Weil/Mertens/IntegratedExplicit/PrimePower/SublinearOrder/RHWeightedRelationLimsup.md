# A quantitative left-window gap from disjoint relations

## Abstract

Disjoint integer relations can lower the normalized RH left-window upper limit.

Assume the Riemann hypothesis. Let J(T) be the positive zeta zeros with ordinate γ at most T. The real part is fixed by RH, so each ordinate in the cutoff identifies one zero. With analytic multiplicity mγ the weight is wγ = mγ γ/(1/4 + γ²), which is strictly positive. Use these weights both in the total mass W(T) and in the finite sine polynomial with frequencies γ. Its deficit D(T) is one minus the real supremum of the polynomial divided by W(T). `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine` `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup`

At any cutoff of positive mass, let δₐ be the norm of the difference between 1 and i raised to the sum of the integer coefficients in row a. For arbitrary overlapping integer relations and nonnegative multipliers, the squared sum of the multiplied defects divided by twice the mass times the column energy bounds D(T) from below, provided the column energy is positive. For disjoint nonzero relation rows, the lower bound is the sum of the squared row defects divided by their row energies, all divided by twice W(T). These are the finite character inequalities with ordinates and weights taken from J(T). `D5/S3/Fourier/WeightedIntegerRelations`

**Theorem 1.1 (An eventual packing gives a strict coefficient gap).**

$$\mathit{RH} \Rightarrow \left(\forall A \in \mathit{Type},\; \forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall epsilon \in \mathbb{R},\; \left(2 \le m \land \left(m + 1 = 2 \cdot r \land \left(\operatorname{mu}\left(r\right) \ne 0 \land \left(0 < \mathit{epsilon} \land \operatorname{Eventually}\left((\lambda T \mapsto \exists R \in \operatorname{Finset}\left(A\right),\; \exists k \in A \to \left(\mathit{PositiveZetaZero} \to \mathbb{Z}\right),\; \left(\forall a \in A,\; a \in R \Rightarrow \sum_{j\in \operatorname{J}\left(T\right)} \operatorname{k}\left(a, j\right) \cdot \operatorname{gamma}\left(j\right) = 0\right) \land \left(\left(\forall a \in A,\; a \in R \Rightarrow \left(\exists j \in \mathit{PositiveZetaZero},\; j \in \operatorname{J}\left(T\right) \land \operatorname{k}\left(a, j\right) \ne 0\right)\right) \land \left(\left(\forall a \in A,\; a \in R \Rightarrow \left(\forall b \in A,\; b \in R \Rightarrow \left(a \ne b \Rightarrow \left(\forall j \in \mathit{PositiveZetaZero},\; j \in \operatorname{J}\left(T\right) \Rightarrow \left(\operatorname{k}\left(a, j\right) = 0 \lor \operatorname{k}\left(b, j\right) = 0\right)\right)\right)\right)\right) \land \mathit{epsilon} \le \operatorname{P}\left(T, R, k\right)\right)\right)), \mathit{atTop}\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{limsup}\left((\lambda L \mapsto \operatorname{Q}\left(m, r, L\right)), \operatorname{nhdsGT}\left(0\right)\right) \le \operatorname{kappa}\left(m, r\right) \cdot \left(1 - \mathit{epsilon}\right) \land \operatorname{limsup}\left((\lambda L \mapsto \operatorname{Q}\left(m, r, L\right)), \operatorname{nhdsGT}\left(0\right)\right) < \operatorname{kappa}\left(m, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedRelationLimsup.signed_window_limsup_le_of_eventually_disjoint_relations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix natural m and r satisfying m ≥ 2 and m + 1 = 2r. Set s = orderRate(m) and cₘ = μ(m+1)(m+1)/(ms). At each positive width L and left endpoint exp(u), divide signedWindowResidual at exp(u), exp(u+L) by powerGap at rate s at those endpoints. Add cₘ and μ(r) times rootSignal(r,u), and take the absolute value. Write Q(m,r,L) for the limsup of this absolute value as u tends to positive infinity, divided by L log²(1/L). The full coefficient κ(m,r) is |μ(r)|/(4πs).

For a finite set R of row indices and integer coefficients k(a,j) on positive zeta zeros, P(T,R,k) is the sum over rows of δₐ² divided by the energy Σⱼ k(a,j)²/w(j), divided by 2W(T). Each sum over j is restricted to J(T). The formula requires at each sufficiently large T a choice of rows and coefficients giving P(T,R,k) ≥ ε. Each row is an integer relation among the ordinates, is nonzero on J(T), and shares no nonzero column with a distinct row.

The mass is eventually positive. The disjoint bound therefore gives D(T) ≥ ε on a tail. Since 2r/L tends to positive infinity as L tends to zero from above, the moving-coefficient formula bounds Q(m,r,L) by κ(m,r)(1 − ε) plus an error tending to zero on the same one-sided filter. Q is eventually nonnegative, so the resulting upper bound passes to its real limsup. The Möbius assumption makes κ(m,r) positive and the upper limit strictly smaller than κ(m,r). Whether such relation families exist for the zeta ordinates remains open. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup`

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedRelationLimsup.signed_window_limsup_le_of_eventually_disjoint_relations`
- Dependency: [D5/S3/Fourier/WeightedIntegerRelations](../../../../../Fourier/WeightedIntegerRelations.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup](RHWeightedPhaseLimsup.md)
- Narrative reference: [D5/S3/Fourier/WeightedIntegerRelations](../../../../../Fourier/WeightedIntegerRelations.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](RHRootWeightedSine.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup](RHWeightedPhaseLimsup.md)
