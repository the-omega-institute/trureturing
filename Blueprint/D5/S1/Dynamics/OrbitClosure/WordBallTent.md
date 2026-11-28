# Continuous Word-Ball Tents

## Abstract

Infinite-image finitely generated continuous actions have bounded continuous tents with arbitrarily small generator defects and fixed orbit oscillation.

**Theorem 1.1 (One almost-invariant function with full orbit oscillation).**

$$\forall G: \operatorname{Type}, \forall X: \operatorname{Type}, [\operatorname{Group}\left(G\right)] [\operatorname{TopologicalSpace}\left(X\right)] [\operatorname{T2Space}\left(X\right)] [\operatorname{CompactSpace}\left(X\right)] [\operatorname{MulAction}\left(G, X\right)], \forall S: \operatorname{Finset}\left(G\right), \forall R: \mathbb{N}, (\left(\left(\left((\operatorname{InverseClosed}\left(S\right)) \land (\operatorname{Generates}\left(S\right))\right) \land (\forall g: G, \operatorname{Continuous}\left(\operatorname{actionSlice}\left(g\right)\right))\right) \land (\operatorname{Infinite}\left(\operatorname{permutationImage}\left(G, X\right)\right))\right) \land (1 \le R)) \Rightarrow \exists u: \operatorname{ContinuousMap}\left(X, \mathbb{R}\right), \exists b: X, \exists h: G, \left(\left(\left((\forall x: X, (0 \le \operatorname{u}\left(x\right)) \land (\operatorname{u}\left(x\right) \le 1)) \land (\operatorname{u}\left(b\right) = 1)\right) \land (\operatorname{u}\left(\operatorname{smul}\left(h, b\right)\right) = 0)\right) \land (\forall s: G, (s \in S) \Rightarrow \forall x: X, |\operatorname{u}\left(\operatorname{smul}\left(s, x\right)\right)-\operatorname{u}\left(x\right)| \le \frac{1}{R})\right) \land (\forall v: \operatorname{ContinuousMap}\left(X, \mathbb{R}\right), (\forall g: G, \forall x: X, \operatorname{v}\left(\operatorname{smul}\left(g, x\right)\right) = \operatorname{v}\left(x\right)) \Rightarrow \frac{1}{2} \le \operatorname{supnorm}\left(u-v\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/OrbitClosure/WordBallTent.exists_continuous_wordBall_tent` (`✓ std3`). ∎

*Citation.* Boris Petković (2026). *Classification of some cohomologically C0-stable continuous group actions on metric spaces*. URL: <https://arxiv.org/abs/2607.11171v1>.

*Commentary.*

G and X range over independent universes, and X is an arbitrary compact Hausdorff space. The finite set S is inverse closed: s in S implies its inverse lies in S. Generates(S) means that the subgroup closure of S is all of G. The notation smul(g,x) is the given action, actionSlice(g) is x mapped to g acting on x, and permutationImage(G,X) is the range of MulAction.toPermHom for this action. Only each individual action slice is assumed continuous; there is no topology on G. ContinuousMap(X,R) denotes real-valued continuous functions, and supnorm is their usual supremum norm on the same compact Hausdorff space. The natural R in the denominator is cast to the real numbers.

For each positive natural R, the same function u satisfies every displayed clause. The points b and h acting on b lie in one actual orbit, with values 1 and 0 respectively. The generator estimate holds at every point for every generator simultaneously. The final quantifier ranges over every continuous invariant real function for this same action. In particular the conclusion includes the source's compact metric spaces and radii R at least 2.

First suppose a finite set B of group elements covers every orbit from its base point. Then each orbit is finite with cardinality at most card(B). A homomorphism from G to any fixed finite symmetric group is determined by its values on S, so there are finitely many such homomorphisms. Intersect their kernels for all orbit sizes at most card(B). The intersection has finite index and acts trivially on every orbit, as seen by transporting the actual action on each orbit to a finite labelled set. The permutation image is therefore finite. Contraposition supplies a single point b and a point z=h acting on b outside the finite orbit ball B_R acting on b. This argument includes infinite orbits directly and finite orbits of unbounded sizes; it does not infer that each orbit is infinite.

Let B_R consist of products of at most R letters from S. Recursive finite unions and images construct this finite ball; the checked word representation identifies membership with word length at most R. The identity belongs to B_R even when S is empty. For each g in B_R, the point g inverse acting on z differs from b. These form a finite closed set F disjoint from {b}. Compactness and the Hausdorff property make X normal. Urysohn separation gives a continuous phi with values in [0,1], value 1 at b and value 0 on F.

Write tau(g)=max(0,1-length(g)/R), and define u(y) as the maximum over g in B_R of tau(g) times phi(g inverse acting on y). The finite maximum is continuous and lies in [0,1]. Its identity term gives u(b)=1, and every term vanishes at z. Outside B_R the weight is zero, so the same maximum bounds every transported term indexed by any group element.

For s in S, set k=s inverse times g. The length bound length(k) at most length(g)+1 gives tau(g) at most tau(k)+1/R. The action identity identifies phi(g inverse acting on s acting on y) with phi(k inverse acting on y). Multiplication by a number in [0,1] and the maximum bound give u(s acting on y) at most u(y)+1/R. Apply this also to s inverse and s acting on y for the reverse inequality. No separation between supports or assumption about stabilizers is needed.

An invariant v has v(b)=v(z). Evaluating u-v at these two points bounds both absolute values |1-v(b)| and |v(b)| by its supremum norm, forcing that norm to be at least 1/2. Identity generators are allowed and have zero defect. Empty S together with the generation hypothesis forces a trivial group, contradicting infinite image. Empty X likewise cannot satisfy infinite image. No additional nonemptiness premise is needed.

Petkovic's orbit lemmas, Construction con:tent and Lemma lem:tent-properties supply the continuous weighted-maximum mechanism. Finite separation of the transported endpoint replaces the source's choice of a metric bump radius and an endpoint at exact orbit distance R+1. These functions obstruct a uniform supremum-norm estimate of distance to invariants by generator defects. They give no derivative control, no smooth transfer theorem and no resolution of the simultaneous-Diophantine smooth stability conjecture, including its non-linearizable necessity direction.

## References

- Truth anchor: `D5/S1/Dynamics/OrbitClosure/WordBallTent.exists_continuous_wordBall_tent`
