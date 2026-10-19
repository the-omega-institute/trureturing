# Fixed positive partition exchange distance

## Abstract

The fixed positive group-ring partition family has exact maximum-coordinate exchange distance.

**Theorem 1.1 (The entire fixed partition family).**

$$\forall H: Type, [\operatorname{Group}\left(H\right)], [\operatorname{Fintype}\left(H\right)], [\operatorname{Nontrivial}\left(H\right)], \forall n: Nat, \forall p: \operatorname{Partition}\left(n\right), \forall r: \operatorname{Partition}\left(n\right), 1 \le n \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), \operatorname{partitionMatrix}\left(H, p\right), \operatorname{partitionMatrix}\left(H, r\right), \operatorname{dInf}\left(p, r\right)\right)\right) \land (\forall L: Nat, \operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), \operatorname{partitionMatrix}\left(H, p\right), \operatorname{partitionMatrix}\left(H, r\right), L\right) \Rightarrow \operatorname{dInf}\left(p, r\right) \le L)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.theorem32_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite nontrivial group, q its order, u the sum of its group elements, and write z(H)=q1-u in the integer group ring. Here smul denotes natural-number scalar multiplication, and toNat converts each integer coefficient to a natural number. A partition p of n is padded to n decreasing coordinates. Its nilpotent shift is the direct sum of the upper Jordan shifts of these lengths, flattened by prefix sums. Thus the coordinates and endpoint depend only on p.

$\forall H: Type, [\operatorname{Group}\left(H\right)], [\operatorname{Fintype}\left(H\right)], \operatorname{z}\left(H\right) = \operatorname{smul}\left(\operatorname{card}\left(H\right), 1\right) - \operatorname{uniform}\left(H\right)$

$\forall H: Type, [\operatorname{Group}\left(H\right)], [\operatorname{Fintype}\left(H\right)], \forall n: Nat, \forall p: \operatorname{Partition}\left(n\right), \forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), \operatorname{partitionMatrix}\left(H, p, i, j\right) = \operatorname{toNat}\left(\operatorname{smul}\left(\operatorname{power}\left(\operatorname{card}\left(H\right), 3\right) \cdot n, \operatorname{uniform}\left(H\right)\right) + \operatorname{smul}\left(\operatorname{card}\left(H\right) \cdot \operatorname{partitionShift}\left(p, i, j\right), \operatorname{z}\left(H\right)\right)\right)$

The displayed integer group-ring entries are strictly positive and hence determine natural group-ring entries. The baseline q cubed times n is fixed throughout the family.

For neighboring partitions, rectangular zero-one block factors P and Q multiply to their respective shifts. Empty blocks are allowed. Flattening uses the two independent prefix-sum coordinates. The group-ring factors U=qJu+Pz and V=qJu+Qz have strictly positive natural coefficients and their actual products are the two endpoints. The fixed-mass partition geodesic therefore gives a chain of the exact displayed length, including length zero.

For the lower bound, RectangularNilpotenceBarrier.exchange_chain_lag supplies the shared cumulative intertwining maps R and S for every competing rectangular chain; their two products are the endpoint powers of its length L. This reuses the original cumulative proof from theorem32_2, with no separate new-content credit. Intermediate dimensions may change and may be zero. Act on the kernel of rational augmentation, whose rational dimension is q-1. The uniform element annihilates this ideal, and the endpoint acts as q squared times its partition shift on each ideal coordinate.

For the endpoint operators T and Q, set I=im(T to the j), M=S(I), and N=im(T to the j+L). The map R from M onto N intertwines the restrictions. It induces an actual surjection from M/QM onto N/TN. Rank-nullity and the embedding of the kernel on M into the kernel on im(Q to the j) compare the endpoint layer dimensions.

$\forall V: Type, \forall W: Type, [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(Rational, V\right)], [\operatorname{FiniteDimensional}\left(Rational, V\right)], [\operatorname{AddCommGroup}\left(W\right)], [\operatorname{Module}\left(Rational, W\right)], [\operatorname{FiniteDimensional}\left(Rational, W\right)], \forall T: \operatorname{End}\left(Rational, V\right), \forall Q: \operatorname{End}\left(Rational, W\right), \forall R: \operatorname{LinearMap}\left(Rational, W, V\right), \forall S: \operatorname{LinearMap}\left(Rational, V, W\right), \forall L: Nat, \left(\operatorname{comp}\left(T, R\right) = \operatorname{comp}\left(R, Q\right) \land \left(\operatorname{comp}\left(Q, S\right) = \operatorname{comp}\left(S, T\right) \land \operatorname{comp}\left(R, S\right) = \operatorname{power}\left(T, L\right)\right)\right) \Rightarrow (\forall j: Nat, \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(T, j + L\right)\right)\right) - \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(T, j + L + 1\right)\right)\right) \le \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(Q, j\right)\right)\right) - \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(Q, j + 1\right)\right)\right))$

Explicit endpoint shift coordinates evaluate each layer as q-1 times the number of partition parts exceeding its threshold. Cancel q-1, which is positive. Taking j equal to each part of the opposite partition proves the coordinate bound in both directions. Their maximum gives the lower bound on every chain length. No classification or partition assumption is imposed on the intermediate matrices.

The prescribed single-chain subfamily.

Fix n at least two. For each t from one to n, take the actual padded partition p_t=(t,1,...,1,0,...,0), with n-t ones and t-1 zeros. Its length and total mass are both n. Use the existing prefix-sum block coordinates, without changing the endpoint numbering. In these coordinates its partition shift is literally T_t: the only nonzero entries are (a,a+1) for one-based indices 1<=a<t. Let D_t have ones in its first t-1 diagonal positions and zeros elsewhere, and let J be the n by n all-one matrix.

$\operatorname{A}\left(t\right) = \operatorname{power}\left(q, 3\right) \cdot n \cdot J \cdot u + q \cdot z \cdot \operatorname{T}\left(t\right) \land \left(\operatorname{U}\left(t\right) = q \cdot J \cdot u + z \cdot \operatorname{D}\left(t\right) \land \operatorname{V}\left(t\right) = q \cdot J \cdot u + z \cdot \operatorname{T}\left(t\right)\right)$

Here every displayed integer group-ring matrix is interpreted coefficientwise in the natural group ring after positivity is proved. An activated entry of either factor has coefficient 2q-1 at the identity and q-1 elsewhere; every inactive entry has coefficient q. Each coefficient of A_t is at least q cubed times n minus q, which is positive. The identities u squared=qu, uz=zu=0 and z squared=qz, together with D_t T_t=T_t and T_t D_t=T_(t-1), give the actual products U_t V_t=A_t and V_t U_t=A_(t-1). The fixed partition endpoint is therefore this literal A_t.

$\operatorname{power}\left(\operatorname{A}\left(t\right), j\right) = \operatorname{power}\left(\operatorname{power}\left(q, 3\right) \cdot n \cdot J \cdot u, j\right) + \operatorname{power}\left(q, 2 \cdot j - 1\right) \cdot z \cdot \operatorname{power}\left(\operatorname{T}\left(t\right), j\right)$

The power formula holds for every positive j. The entry of T_t to the j at (a,b) is one exactly when b=a+j and b<=t, and is zero otherwise. Thus T_t to the t is zero, while every positive power below t has its (1,1+j) entry equal to one. Augmentation kills z, so the actual augmentation matrix is q to the fourth times n times J. The uniformity threshold is exactly t. In particular the action of H on the actual stationary dimension group of A_t is the identity: advancing a representative by t stages multiplies it by a uniform matrix, which makes each group translate equal in the direct limit. This supplies inertness of the constructed matrix rather than assuming it.

Rectangular competitors and the same four maps.

For the general depth bound, put e=u/q in the rational group ring. It is central and idempotent, and the map x to (1-e)x equals x-e times its augmentation. This map preserves addition, zero and multiplication, including rectangular matrix products. Applying it to an arbitrary natural group-ring SSE chain gives a chain between the actual augmentation-zero endpoint matrices. The rectangular nilpotence barrier gives a<=b+L and b<=a+L for their exact positive depths a,b. Intermediate dimensions may vary and may be zero; no essentiality or intermediate inertness is needed.

Starting at A_t, use the displayed factors successively in decreasing t, and interchange them for the increasing direction. This prescribes a Type-valued chain of length D=|t-r| with its actual cumulative matrices R,S. The padded-partition distance is D. The partition lower bound applies to every competing rectangular chain and to arbitrary R,S satisfying all four SE equations, so D is the minimum SSE length, and for unequal endpoints it is the minimum positive SE lag. At t=r the prescribed chain transports to the nil chain and its history map is the identity.

Choose a numbering of the finite group once. Use its induced order and the same whole-fibre rank at every occurrence of R and S in matrixPhiR, matrixPhiS, matrixPsi0 and matrixPsiL. Conjugating the original recursive sweeps by these ranks cancels the adjacent inverse rank maps at every step. Hence these literal sweeps satisfy both long equations, both positive-lag alignment equations and both balance equations. FixedCutCoherence.full_overlap and full_inverse_coherence then give both complete overlap and inverse laws at every extra length on these same maps. An arbitrary complete compatible, aligned or balanced certificate gives its own four SE equations by counting each total-label fibre; its positive lag is consequently at least D.

Actual histories and every positive period.

Apply OrderedGroupChainHistories to that prescribed chain. Its actual expanded bilateral histories are related by the constructed history homeomorphism f, with continuous inverse, shift equivariance and H equivariance. In anchored coordinates it is (x,h) to (F(x),h gamma(x)), where gamma is the ordered product of the transfers along this same chain; the inverse uses gamma(F inverse(y)) inverse. For every signed time i, the forward value at i depends only on input times from i to i+D, and the inverse value only on times from i-D to i. Consequently, for every natural N both centered observations q_N after these maps factor through q_(N+D). The sharper forward window is [-N,N+D] and the sharper inverse window is [-N-D,N]. These statements include D=0 and make no claim that the displayed windows are minimal among all conjugacies.

For every h in H and every positive j, twistedPeriod_card counts the actual h-twisted histories by the corresponding diagonal group coefficients of A_t to the j. Every positive power of T_t has zero diagonal, including when j<t. The nonuniform term in the displayed power formula therefore contributes zero to this count at every positive j, not only after uniformization.

$\operatorname{F}\left(h, j, \operatorname{A}\left(t\right)\right) = \operatorname{trace}\left(\operatorname{power}\left(\operatorname{power}\left(q, 4\right) \cdot n \cdot J, j\right)\right)$

The right-hand side is independent of t. For each d from zero to n-1, the two members t=1 and r=d+1 lie in this same full observation fibre and have prescribed-presentation distance d. Numbering and the discrete topology are constructed choices for a finite group, not extra order or topological-group hypotheses; the chosen numbering is used throughout the four maps and history formulas.

**Theorem 1.2 (Arbitrary shift equivalences bound the partition distance).**

Lean statement: `D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.rational_shift_equivalence_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.rational_shift_equivalence_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be finite and nontrivial, n be positive, and p,r be any padded partitions of n. Let X,Y be arbitrary rational group-ring n by n matrices and let L be any natural number. Assume only the four shift-equivalence equations: A(p)X=XA(r), A(r)Y=YA(p), XY=A(p)^L and YX=A(r)^L. Then dInf(p,r)<=L. In particular, no competing exchange chain is an input, and natural positive SE data are covered by their rational coefficient cast.

The original quotient-layer proof is used twice, once in each direction. The original endpoint action evaluates the two image-rank filtrations, and the original coordinate-bound argument gives the maximum-coordinate bound. The existing theorem32_2 now consumes this chain-free result after extracting its cumulative factors. This theorem does not identify the prescribed single-chain matrices or construct aligned certificates.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.rational_shift_equivalence_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.theorem32_2`
- Dependency: [D5/S3/Combinatorics/Partitions/PartitionLInftyGeodesic](../../Combinatorics/Partitions/PartitionLInftyGeodesic.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy](InertGroupBlockConjugacy.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange](InvolutionUniformExchange.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](RectangularNilpotenceBarrier.md)
