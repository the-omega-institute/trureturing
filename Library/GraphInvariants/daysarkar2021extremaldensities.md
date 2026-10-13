---
bibkey: daysarkar2021extremaldensities
authors: A. N. Day; A. Sarkar
year: 2021
title: "On a Conjecture of Nagy on Extremal Densities"
doi: 10.1137/19M1296525
url: https://arxiv.org/abs/1910.13465
claim: "Conjecture 2. For each graph G_l, we have that q(G_l, β) is an increasing function of β."
strata_touched:
  - D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit
  - D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1137/19M1296525

Source: https://arxiv.org/abs/1910.13465

The journal reference is SIAM Journal on Discrete Mathematics 35 (2021), 294–306.
The page locators below refer to the arXiv v1 PDF.

## Source statements

Section 5, p. 14, verbatim:

> **Conjecture 2.** For each graph $G_l$, we have that $q(G_l,\beta)$ is an increasing function of $\beta$.

The optimiser is introduced on pp. 13–14 by
$f_T(G_l,\beta)=\sup_{q\in[0,1]}t(G_l,T_n^e(q))$, with $e=\beta n^2/2$, followed by:

> and let $q(G_l,\beta)\in[0,1]$ be the value of $q$ at which the supremum is attained.

Section 2, p. 3, verbatim:

> A graph homomorphism from $G_l$ to $H$ is a map $f:V(G_l)\rightarrow V(H)$ such that $\{f(u),f(w)\}\in E(H)$ for all $\{u,w\}\in E(G_l)$. We write ${\rm hom}(G_l,H)$ for the number of homomorphisms from $G_l$ to $H$.

The homomorphism density is the literal limit
$t(G_l,H_n)=\lim_{n\rightarrow\infty}{\rm hom}(G_l,H_n)/n^v$.
For the three-class graph, pp. 3–4 give the sizes

$$
|Y_T|=\sqrt\beta qn,\qquad
|R_T|=(1-\sqrt{1-\beta(1-q^2)})n,\qquad
|B_T|=(\sqrt{1-\beta(1-q^2)}-\sqrt\beta q)n.
$$

Section 2, p. 4, verbatim:

> The sets $Y_T$ and $R_T$ both span cliques, while $B_T$ is an independent set. Also, every vertex in $R_T$ is connected to every vertex in $Y_T$ and $B_T$.

There are no yellow–blue edges. The source omits floors for asymptotic notation.
The finite encoding uses the first $\lfloor yn\rfloor_+$ vertices as yellow,
the next $\lfloor rn\rfloor_+$ as red, and all remaining vertices as blue.
Adjacency also requires distinct vertices.

Section 2, p. 3, verbatim:

> Given a graph $G$, a function $\phi:V(G)\rightarrow[0,1]$ such that $\phi(u)+\phi(w)\leqslant1$ for all $\{u,w\}\in E(G)$ is known as a fractional independence weighting of $G$.

Section 3 restricts these weights to $\{0,\tfrac12,1\}$.
The encoding represents them by $a/2$ for $a:\mathrm{Fin}\,3$;
red has index 0, yellow index 1 and blue index 2.
Lemma 1, p. 5, gives the corresponding sum of vertex-weight products for $t(G_l,T_n^e(q))$.

## Scope of the refutation

The triangle on vertices 0, 1 and 2, with edge 03 and leaves 4, 5 and 6 attached
to vertex 3, has a unique optimal parameter at each of $\beta=10^{-6}$ and
$\beta=10^{-4}$. The first exceeds $7743/10000$ and the second is below
$7719/10000$. Thus even the weak interpretation that some selection of
maximisers is nondecreasing fails.

The counting argument permits nonadjacent vertices to share an image. Its
collision error is bounded by $v^2n^{v-1}$. The rational coordinate used in
the optimisation is restricted to $0<s\le1/100$, with $1-sx\ne0$ explicit;
both selected densities satisfy this restriction.

This refutation concerns Conjecture 2. It does not settle Conjecture 1 or
change the separate scope of Conjecture 3. The source's proposed STK
classification assumes Conjecture 2 and therefore needs separate analysis
for graphs with pendant-star configurations.
