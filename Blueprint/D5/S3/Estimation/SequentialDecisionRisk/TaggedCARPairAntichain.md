# Fixed Pair Profiles and Tagged CAR Antichains

## Abstract

Equal pair masses force equality of tagged CAR profiles under a common stochastic simulation.

Let Q and K be finite types, with decidable equality on K, and let A(q) be a finite subset of K for each readout q. The actual rows are the dependent pairs (q,i) with i in A(q). The output alphabet O consists of every tagged nonempty subset (q,B) with B contained in A(q), including outputs of weight zero. Fibers A(q) may be empty; they then contribute neither rows nor outputs.

Write I(q,i,B) for the incidence relation saying that the tag of B is q and its underlying subset contains i. A CAR profile w assigns a nonnegative real weight to every B in O and satisfies sum over B of 1[I(q,i,B)] w(B) = 1 for every actual i in A(q). Its row is W_w((q,i),B) = 1[I(q,i,B)] w(B). Define r_w(q,i,j) as the sum of w(B) over outputs incident to both (q,i) and (q,j). Only pairs of distinct actual states in the same fiber will be compared.

**Definition 1.1 (One global partition law gives a CAR profile).**

$$\begin{gathered}R finite, P:R\to \operatorname{Partitions}\left(K\right), p:R\to \mathbb{R}\\{}(\forall r,0\leq \operatorname{p}\left(r\right))\land \sum_{r\in R}\operatorname{p}\left(r\right)=1\\{}\Rightarrow w=\operatorname{partitionProfile}\left(A, P, p\right):\operatorname{CARProfile}\left(A\right)\\{}\operatorname{w}\left(q, B\right)=\sum_{r\in R}\operatorname{p}\left(r\right)\cdot \operatorname{indicator}\left(B\in \operatorname{restrict}\left(\operatorname{P}\left(r\right), \operatorname{A}\left(q\right)\right)\right)\end{gathered}$$

*Formalization.* `D5/S3/Estimation/SequentialDecisionRisk/TaggedCARPairAntichain.partitionProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite type R, choose a partition P(r) of all of K for each r, and a single law p on R with p(r) nonnegative and sum p(r) = 1. Restrict P(r) to A(q) by intersecting each global block with A(q) and discarding empty intersections. The formula gives the weight of each tagged local block. The same P(r) and the same law p are used for every q. Each actual i belongs to exactly one block of each restricted partition, so summing the weights of incident blocks gives sum p(r) = 1. All weights are nonnegative.

In particular, fix a target t on the actual rows. Take R to be all global partitions whose blocks never contain two states i,j in any common actual fiber A(q) with different targets t(q,i) and t(q,j). A probability law on this finite family gives the public partition profiles to which the antichain theorem applies. Distinct partition laws can have the same profile. The construction only maps global partition laws to CAR profiles; it does not assert that every CAR profile is obtainable from such a law.

**Theorem 1.2 (A common simulator with equal pair masses forces equal weights).**

$$\begin{gathered}\forall Q,K:Type, \operatorname{Fintype}\left(Q\right)\land \operatorname{Fintype}\left(K\right)\land \operatorname{DecidableEq}\left(K\right),\\{}\forall A:Q\to \operatorname{Finset}\left(K\right), w,v:\operatorname{CARProfile}\left(A\right),\\{}\forall H:\operatorname{FiniteMarkovKernel}\left(\operatorname{TaggedBlock}\left(A\right), \operatorname{TaggedBlock}\left(A\right)\right),\\{}(\forall s:\operatorname{ActualRow}\left(A\right),\forall C:\operatorname{TaggedBlock}\left(A\right),\operatorname{channelOutput}\left(H, \operatorname{row}\left(w, s\right), C\right)=\operatorname{row}\left(v, s, C\right))\land\\{}(\forall q,i,j,i\in \operatorname{A}\left(q\right)\land j\in \operatorname{A}\left(q\right)\land i\neq j\Rightarrow\operatorname{pairMass}\left(w, q, i, j\right)=\operatorname{pairMass}\left(v, q, i, j\right))\\{}\Rightarrow \operatorname{weight}\left(w\right)=\operatorname{weight}\left(v\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/TaggedCARPairAntichain.equal_weights_of_common_simulator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem quantifies over two CAR profiles w and v on the same A and one full stochastic matrix H from O to O: every entry is nonnegative and every input row sums to one. Simulation means W_w H = W_v on every actual row and every output. This single H is independent of the actual state. It can read the source output tag and has no assumed tag or subset support restriction, including on input letters of zero weight.

Set f(B,C) = w(B) H(B,C). These numbers are nonnegative and have row sums w(B). If B contains an actual i at its tag and C is not incident to that same row, the target row at C is zero. The simulation identity expresses zero as a sum of nonnegative terms containing f(B,C), so f(B,C) = 0. Thus any nonzero flow preserves the tag and satisfies B contained in C. This restriction concerns the weighted flow; it need not restrict H on zero weight input letters.

Fix q and actual i,j. Expand the target pair mass using the simulated i row, and expand the source pair mass using the flow row sums. The terms for which both i and j already belong to B cancel. What remains is the exact nonnegative pair difference below; here B and C denote underlying subsets at the common tag q.

$$
\operatorname{r}\left(v, q, i, j\right)-\operatorname{r}\left(w, q, i, j\right)=\sum_{C,i\in C,j\in C}\sum_{\emptyset\neq B\subseteq C,i\in B,\neg(j\in B)}\operatorname{f}\left(B, C\right)\geq 0
$$

If B is a proper subset of C and f(B,C) is positive, choose i in B and j in C outside B. They are distinct actual states of the same fiber. Their pair difference contains this positive term. Equal pair masses therefore force every off-diagonal flow to vanish. For each C, its flow row sum then equals f(C,C); an actual i in C and the simulated column identity give f(C,C) = v(C). Hence w(C) = v(C) for every tagged block.

Consequently, at a fixed array of within-fiber pair masses, two distinct weight profiles admit no simulation in either direction: either direction would force equality. This applies in particular to the profiles constructed from global sufficient partition laws. Singleton fibers require no pair equation, and empty fibers require no row equation. The conclusion distinguishes weight profiles, not their possibly different partition-law representations.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/TaggedCARPairAntichain.equal_weights_of_common_simulator`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/TaggedCARPairAntichain.partitionProfile`
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](../DecisionRisk/DescentDefectBounds.md)
