# Finite tournament path defects and convergence

## Abstract

Finite tournament path defects and convergence

An orientation is a list of signs, with true denoting a forward arc and false a backward arc. Its flips count adjacent unequal signs. ArcPreserving quantifies over every map from Fin(length+1) to Fin(N); maps need not be injective. The density homDensity is homCount divided by N^(length+1). TAS quantifies over every positive N and every loopless tournament relation on Fin(N), with bound (1/2)^length. Enumeration of the vertices identifies these hosts with arbitrary finite nonempty loopless tournaments. The function f is the maximum of precisely those m in {0,...,k} for which every length-k orientation with fewer than m flips is TAS. The set contains zero. No property at length zero is used. The motivating question is Question 6.1 in Hao Chen and Yupeng Lin, Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko, https://arxiv.org/abs/2609.14655v1.

**Definition 1.1 (Convergence over all positive lengths).**

$$FullConvergence \Leftrightarrow \left(\exists L \in \mathbb{R},\; \forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists K \in \mathbb{N},\; 1 \le K \land \left(\forall k \in \mathbb{N},\; K \le k \Rightarrow \operatorname{abs}\left(\frac{\operatorname{f}\left(k\right)}{k} - L\right) < e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.FullConvergence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the epsilon/K assertion for the source's exact strict threshold. The positive-length quantifiers retain saturation at f(k)=k.

**Theorem 1.2 (The saturated threshold is bounded).**

$$\forall k \in \mathbb{N},\; \operatorname{f}\left(k\right) \le k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of thresholds(k) belongs to {0,...,k}.

**Theorem 1.3 (A nonsaturated threshold is attained by a defect).**

$$\forall k \in \mathbb{N},\; \operatorname{f}\left(k\right) < k \Rightarrow \left(\exists w \in \operatorname{List}\left(Bool\right),\; \operatorname{length}\left(w\right) = k \land \left(\operatorname{flips}\left(w\right) = \operatorname{f}\left(k\right) \land \neg \operatorname{TAS}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_bad_at_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The property holds below f(k). Its failure at f(k)+1 supplies an orientation with exactly f(k) flips, rather than merely an orientation below a different threshold.

**Theorem 1.4 (Reflection produces a Gram transfer).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{transfer}\left(A, \operatorname{append}\left(w, \operatorname{reflect}\left(w\right)\right)\right) = \operatorname{transfer}\left(A, w\right) \cdot \operatorname{transpose}\left(\operatorname{transfer}\left(A, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_pair_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection reverses the word and complements every sign. It therefore transposes the product, retaining its endpoints and their correlations.

**Theorem 1.5 (Reflection amplifies the average).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall B \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{mass}\left(B\right)^{2} \le \operatorname{mass}\left(B \cdot \operatorname{transpose}\left(B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_mass_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mass is the sum of all entries divided by the number of indices. The mass of B times its transpose is the mean of the squares of the column sums. Cauchy-Schwarz bounds it below by the square of the original mass. No independent gluing of endpoint densities is used.

**Theorem 1.6 (Every bounded remainder admits padding).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall R \in V \to \left(V \to Prop\right),\; \operatorname{IsTournament}\left(R\right) \Rightarrow \left(\forall w \in \operatorname{List}\left(Bool\right),\; \forall s \in \mathbb{N},\; \exists v \in \operatorname{List}\left(Bool\right),\; \operatorname{length}\left(v\right) = s \land \frac{\operatorname{card}\left(V\right) - 1}{\operatorname{card}\left(V\right)}^{s} \cdot \operatorname{mass}\left(\operatorname{transfer}\left(\operatorname{normalizedArcMatrix}\left(R\right), w\right)\right) \le \operatorname{mass}\left(\operatorname{transfer}\left(\operatorname{normalizedArcMatrix}\left(R\right), \operatorname{append}\left(w, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tournament_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put A(i,j)=2/N when i points to j and zero otherwise. Looplessness and the unique orientation of distinct pairs give sum_j(A(i,j)+A(j,i))=2(N-1)/N. Thus the masses of the two possible one-edge extensions sum to 2(N-1)/N times the previous mass. At least one sign retains a factor (N-1)/N. Induction selects an s-edge tail retaining its s-th power, inside the same original tournament. It does not assert that an arbitrary prescribed tail is safe.

**Theorem 1.7 (All repetition counts amplify).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall C \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{PosSemidef}\left(C\right) \Rightarrow \left(\forall x \in V \to \mathbb{R},\; 0 < \operatorname{dot}\left(x, x\right) \Rightarrow \left(0 < \operatorname{moment}\left(C, x, 1\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{moment}\left(C, x, 1\right)^{n} \le \operatorname{moment}\left(C, x, n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.moment_geometric_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Moment(C,x,n) is x dot C^n x divided by x dot x. Cauchy-Schwarz in the positive semidefinite form C^n gives a(n+1)^2 <= a(n)a(n+2). With a(0)=1 and a(1)>0, successive moment ratios are nondecreasing, so a(n)>=a(1)^n. This bound holds for every natural repetition count, not only a subsequence.

**Theorem 1.8 (Exponential reflected amplification).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall B \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; 1 < \operatorname{mass}\left(B\right) \Rightarrow \left(\forall m \in \mathbb{N},\; \operatorname{mass}\left(B\right)^{2 \cdot m} \le \operatorname{mass}\left(\left(B \cdot \operatorname{transpose}\left(B\right)\right)^{m}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_power_amplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-ones moment is the mass of the matrix power. The Gram matrix is positive semidefinite, its first mass is at least mass(B)^2, and the geometric moment bound gives mass((B B^T)^m)>=mass(B)^(2m) for every m.

For the convergence argument, call (k,r) a defect when a length-k orientation with r flips has normalized density q=2^k t(P,T)>1 in some finite host T. For a positive-length defect N>=2. The transfer B for P has mass q. The reflected word W=P reflect(P) has transfer C=B B^T, length 2k, and 2r+1 flips. With x the all-ones vector, moment(C,x,m)=mass(C^m). The reflection and moment bounds give mass(C^m)>=q^(2m).

For every n write n=2km+s with 0<=s<2k. The word W repeated m times has 2m(r+1)-1 flips when m>=1. Append the tail selected by the padding inequality. Its normalized density is at least c^s q^(2m), where c=(N-1)/N lies in (0,1). This is at least c^(2k-1) q^(2m), which exceeds one for all sufficiently large m. The resulting length-n path is therefore a defect for every sufficiently large n. Its flips are at most 2m(r+1)-1+s, hence at most ((r+1)/k)n+2k. This proves eventual upper propagation f(n)/n < (r+1)/k+delta for every positive delta.

Let L be the infimum of {1} together with all (r+1)/k from defects. This nonempty set is bounded below by zero. At a saturated length f(n)=n, one has f(n)/n>=L. At a nonsaturated length the least-defect fact gives a defect with r=f(n), so L<=(f(n)+1)/n. Thus f(n)/n>=L-1/n at every positive length. For the upper bound, choose an element of the defining set below L+epsilon/2. If it is 1, saturation bounds every f(n)/n by 1. Otherwise it is a defect ratio, and upper propagation with delta=epsilon/2 applies to every sufficiently large length. Combining this with 1/n<epsilon proves convergence to L over all positive lengths. The argument does not determine a numerical value of L.

## References

- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.FullConvergence`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.exists_bad_at_f`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.f_le`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.moment_geometric_lower`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_mass_sq_le`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_pair_transfer`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.reflected_power_amplification`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.tournament_padding`
- Dependency: [D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence](../../ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.md)
