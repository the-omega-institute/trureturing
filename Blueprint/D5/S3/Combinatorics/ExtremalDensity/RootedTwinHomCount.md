# The rooted-twin homomorphism bound

## Abstract

Two rooted copies joined through a centre satisfy a general quarter-square homomorphism bound.

**Theorem 1.1 (A fixed centre in an asymmetric host).**

$$\forall A: Type_{u}, \forall B: Type_{v}, [\operatorname{Finite}\left(A\right)] [\operatorname{Finite}\left(B\right)] \forall H: \operatorname{Digraph}\left(A\right), \forall w: A, \forall R: B \to \left(B \to Prop\right), (\forall x: B, \forall y: B, \operatorname{R}\left(x, y\right) \Rightarrow \neg \operatorname{R}\left(y, x\right)) \Rightarrow \forall t: B, 4 \cdot \operatorname{Nat}.\operatorname{card}\left(\{f: \operatorname{RelHom}\left(\operatorname{rootedTwin}\left(H, w\right).\operatorname{Adj}, R\right) \mid \operatorname{f}\left(none\right) = t\}\right) \le \operatorname{Nat}.\operatorname{card}\left(\operatorname{RelHom}\left(H.\operatorname{Adj}, R\right)\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/RootedTwinHomCount.quarter_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A : Type u and B : Type v be arbitrary finite types in independent universe levels u and v, H a digraph on A, w a vertex of H, R an asymmetric relation on B, and t a vertex of B. Put D = rootedTwin H w. Its vertex type is Option (Bool × A): none is the new centre, and some (false,a) and some (true,a) are the two copies of a. Within either copy the arcs are exactly those of H. The only additional arcs are some (false,w) → none and none → some (true,w). There are no other cross-copy or centre arcs. RelHom counts every adjacency-preserving map; neither injectivity nor disjoint images of the two copies is required.

The proof is Omega.RootedTwinHomCount.quarter_bound in OmegaMath.Combinatorics.RootedTwinHomCount. Restriction to the two copies gives an equivalence between the fibre f(none)=t and the product of the H-homomorphisms g with R(g(w),t) and the H-homomorphisms h with R(t,h(w)). Assembly assigns t to the centre and uses g and h on their respective copies. All internal and centre arcs are preserved, and restriction and assembly are inverse. This correspondence requires neither finiteness nor asymmetry.

Write a and b for the sizes of these two homomorphism classes and N for the number of all H-homomorphisms into R. Asymmetry prevents any homomorphism from belonging to both classes, so their disjoint sum injects into all H-homomorphisms. Thus a+b≤N and 4ab≤(a+b)²≤N². This division-free bound includes N=0, loops in H and singleton hosts. A chosen t already supplies an element of B. Completeness of the host and positivity of a homomorphism count are not assumptions.

This is the structural counting step of Proposition 5.2 in Xiaoyu He, Nitya Mani, Jiaxi Nie, Nathan Tung and Fan Wei, New Sidorenko-type inequalities in tournaments, https://arxiv.org/html/2512.11222v1 . The proposition uses tournament hosts and feeds the construction toward Theorem 1.3 and the conjecture that every tree admits a tournament anti-Sidorenko orientation. Here the counting inequality holds for every asymmetric host relation. The final comparison uses a+b≤N: maps whose root is sent to t, or to a vertex unrelated to t, need not belong to either class. This theorem establishes this counting step; the general tree conjecture remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/RootedTwinHomCount.quarter_bound`
