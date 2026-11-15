# Cycle Correlations in Three Real Dimensions

## Abstract

Closed spherical-angle inequalities characterize real cycle completions of rank at most three.

**Theorem 1.1 (The complete cycle criterion).**

$$\forall (n : \mathbb{N}), \forall (a : \operatorname{Fin}\left(n\right) \to \mathbb{R}), (3 \leq n \land \forall (i : \operatorname{Fin}\left(n\right)), -1 \leq \operatorname{value}\left(a, i\right) \land \operatorname{value}\left(a, i\right) \leq 1) \Rightarrow ((\exists (B : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), \operatorname{PosSemidef}\left(B\right) \land \operatorname{rank}\left(B\right) \leq 3 \land (\forall (i : \operatorname{Fin}\left(n\right)), \operatorname{entry}\left(B, i, i\right) = 1) \land \forall (i : \operatorname{Fin}\left(n\right)), \operatorname{entry}\left(B, i, \operatorname{next}\left(i\right)\right) = \operatorname{value}\left(a, i\right)) \iff \forall (F : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{Odd}\left(\operatorname{card}\left(F\right)\right) \Rightarrow \sum_{i \in F} \operatorname{arccos}\left(\operatorname{value}\left(a, i\right)\right) - \sum_{i \in \operatorname{complement}\left(F\right)} \operatorname{arccos}\left(\operatorname{value}\left(a, i\right)\right) \leq (\operatorname{realcard}\left(F\right) - 1) \pi)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/CycleRankThreePsdCompletion.cycle_rank_three_iff` (`✓ std3`). ∎

*Citation.* Marianna E.-Nagy, Monique Laurent and Antonios Varvitsiotis (2012). *Complexity of the positive semidefinite matrix completion problem with a rank constraint*. URL: <https://arxiv.org/abs/1203.6602v2>.

*Commentary.*

Let n be any natural number at least three and a any real-valued function on Fin n with every value in the closed interval [-1,1]. The successor next(i) is i+1 modulo n, implemented by finRotate n. There exists a real n by n positive semidefinite matrix B of real matrix rank at most three, with B(i,i)=1 and B(i,next(i))=a(i) for every i, if and only if every odd-cardinality subset F of Fin n satisfies the displayed inequality. Complement means complement inside Fin n; the cardinality on the right is cast to the real numbers. No unspecified matrix entries or global realization are given as premises.

The angles are arccos(a(i)), with values in [0,pi]. The criterion is Corollary 2.1, equation (5), of E.-Nagy, Laurent and Varvitsiotis after scaling their normalized angles by pi. Their subsequent discussion supplies the uniform rank-three bound. The statement is established classical mathematics. The closed intervals include a(i)=1 and a(i)=-1. Repeated vectors, nonspanning realizations and singular completions are retained; there is no strict positivity, genericity, orientation or distinctness assumption.

For a subset F define its cost as the sum of pi minus the angle on F and of the angle on its complement. An odd-subset inequality is exactly the assertion that this cost is at least pi. Eliminating two consecutive angles alpha and beta requires one gamma satisfying their triangle interval and every shorter-cycle inequality simultaneously. Take gamma to be the maximum of abs(alpha-beta) and the largest odd-subset lower bound. The original inequalities bound gamma above by alpha+beta and by 2pi-alpha-beta. Costs of two distinct subsets have sum at least pi, which supplies every remaining upper bound for the same gamma.

A spherical triangle with possibly repeated vertices exists whenever its three pairwise angular side lengths are in [0,pi], each is at most the sum of the other two, and their sum is at most 2pi. Use coordinates (cos(alpha),sin(alpha)cos(t),sin(alpha)sin(t)); their norm is one. The intermediate value theorem chooses t with the required inner product. Equal pairwise Gram data align the two endpoints with any existing pair in the same real three-dimensional space. The ambient isometry does not require independent or spanning endpoints, so no division by a degenerate overlap is introduced.

Induction on the number of edges constructs a closed unit-vector chain in the unchanged space R cubed. Insert the triangle vector into the eliminated edge and preserve all other vectors. Taking the Gram matrix gives positive semidefiniteness and diagonal one; its three-row factor bounds real matrix rank by three. Conversely, factor any proposed rank-three PSD matrix in that space. Remove the middle vector of two consecutive edges. The angle triangle inequality, also applied with the middle vector negated, gives the triangle interval and perimeter bound. Induction and the reverse cost identities recover every original odd-subset inequality.

This is an existence characterization of static real correlation data. It does not select a unique completion, provide a computational complexity bound, or assert a physical dynamics or empirical model. The fixed three-dimensional bound is uniform in n.

## References

- Truth anchor: `D5/S3/QuadraticForms/CycleRankThreePsdCompletion.cycle_rank_three_iff`
- Dependency: [D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion](RankBoundedChordalPsdCompletion.md)
