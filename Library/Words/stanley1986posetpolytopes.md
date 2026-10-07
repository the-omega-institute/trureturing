---
bibkey: stanley1986posetpolytopes
authors: Richard P. Stanley
year: 1986
title: Two Poset Polytopes
doi: 10.1007/BF02187680
url: https://math.mit.edu/~rstan/pubs/pubfiles/66.pdf
claim: "The chain polytope has antichain indicators as vertices and Ehrhart polynomial equal to the order polynomial at m+1; the fence specializes to nonnegative adjacent-sum inequalities."
strata_touched:
  - D5/S1/Words/AdmissibleWords/PathStableSetPolytope
license: citation-only
triage: anchor
---

# Fence chain polytopes and the three-position occupancy pyramid

Richard P. Stanley, *Two Poset Polytopes*, Discrete & Computational Geometry
1, 9–23. The author's PDF supplies the following precise clauses.

Definition 2.1, printed p. 12, defines the chain polytope by nonnegative
coordinates and a sum at most one on each chain. The maximal-chain
inequalities suffice and, with nonnegativity, define its facets.
Theorem 2.2, pp. 12–13, identifies its vertices as antichain indicators.
Theorem 4.1, p. 15, states

$$
i(\mathcal O(P),m)=i(\mathcal C(P),m)=\Omega(P,m+1).
$$

Example 4.3, pp. 15–16, uses the fence with alternating cover relations;
its chain polytope has inequalities $u_i\ge0$ and $u_i+u_{i+1}\le1$.
These are the original paper's clauses, rather than a perfect-graph
exposition or an attribution based only on bibliographic metadata.

For the three-element fence $a<b>c$, use coordinates
$(u_a,u_b,u_c)=(X,Z,Y)$. Its maximal chains are $a<b$ and $c<b$.
Its five antichains are $\varnothing,\{a\},\{c\},\{a,c\},\{b\}$.
Thus the chain polytope is the same occupancy hull as the three-vertex
path stable-set polytope: $X,Y,Z\ge0$, $X+Z,Y+Z\le1$.
The two existing notes [Chvátal](chvatal1975polytopes.md) and
[the path pyramid](standard2026pathpyramid.md) retain their own ownership
and verification boundaries. This paper supplies an independently
specified primary source, not a replacement claim that those notes had
inspected Chvátal's full text.

For $m\ge0$, an integer layer with middle coordinate $W$ has
$(m-W+1)^2$ choices of the two endpoint coordinates. Equivalently an
order-preserving map to $\{0,\ldots,m\}$ with value $W$ at the top
element has $(W+1)^2$ choices below it. Summing gives the exact
specialization of Theorem 4.1:

$$
i(\mathcal C(P),m)=\sum_{k=1}^{m+1}k^2
=\frac{(m+1)(m+2)(2m+3)}6.
$$

This classical Ehrhart count concerns geometric lattice resolution.
It does not count temporally concatenated FIB histories, establish a
probability coupling, or attest the native reader obstruction in
[the occupancy-pyramid volume](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md).
