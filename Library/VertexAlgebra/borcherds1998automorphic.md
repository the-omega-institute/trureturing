---
bibkey: borcherds1998automorphic
authors: Richard E. Borcherds
year: 1998
title: Automorphic forms with singularities on Grassmannians
doi: 10.1007/s002220050232
claim: "Classical lattice theta inversion, finite Weil operators and Milgram's positive Gauss-sum formula, with the signature phase removed from S."
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/borcherds1998automorphic -->

Borcherds, *Inventiones mathematicae* 132 (1998), 491–562.
Primary text: [author's PDF](https://math.berkeley.edu/~reb/papers/aut/aut.pdf)
and [TeX](https://math.berkeley.edu/~reb/papers/aut/aut.tex), author-hosted
corrected version containing the 2018-02-23 correction remarks.
The locators below use this version's printed pages, rather than journal pagination.

## Verified locator

DOI: 10.1007/s002220050232.

Section 4, p. 13, defines the two Weil generators and their central
relation on the entire group ring. Theorem 4.1 and its S-generator calculation,
p. 14, give the theta transformation. Corollary 4.2 (Milgram), p. 15, states
$\sum_{a\in M'/M} e(a^2/2)=\sqrt{|M'/M|}\,e((b^+-b^-)/8)$;
its proof displays the finite triple-sum calculation for the cubic relation.
Here $e(x)=\exp(2\pi i x)$.

**Original lattice and signs.** For the repository's positive even Gram lattice
$M=(\mathbb Z^r,G)$, take $(b^+,b^-)=(r,0)$.
The Gram-cokernel class $[u]$ corresponds to $G^{-1}u+M$ in $M'/M$.
Thus $q([u])=u^tG^{-1}u/2$ and $B([u],[v])=u^tG^{-1}v$ modulo integers.
Under $f\mapsto\sum_a f(a)e_a$, the whole function space is the source's group
ring, with no restriction to even functions. Write $n=|M'/M|=\det G$,
$\rho=\sqrt n>0$, $C f(a)=f(-a)$ and

$$
S f(a)=\rho^{-1}\sum_b e(-B(a,b))f(b),\qquad
T f(a)=e(q(a))f(a),\qquad
\gamma=\rho^{-1}\sum_a e(q(a)).
$$

The source's operators are $S_B=e(-r/8)S$ and $T_B=T$; its central element
acts as $Z=e(-r/4)C$. The quadratic character and Fourier kernel have exactly
the positive and negative signs, respectively, used here; the translation is
removal of the signature scalar on $S_B$. Character orthogonality yields
$S^2=C$, $S^4=1$, and $S^{-1}=S^+=CS=SC$, where $S^+$ uses $e(+B(a,b))$.
In the displayed calculation in the proof of Corollary 4.2,
$\sqrt n\sqrt i^{\,r}S_BT_B=\sqrt n ST$; dividing its cubed identity by
$n^{3/2}$ gives $(ST)^3=\gamma C$. The corollary then gives
$\gamma=e(r/8)=\exp(\pi i r/4)$.

For `sector_S`, specialize Theorem 4.1 to $p=1$, $\alpha=\beta=0$ and positive
signature. Its factor $\tau^{r/2}e(-r/8)$ equals $(-i\tau)^{r/2}$ with the
principal branch: for $\operatorname{Im}\tau>0$,
$\operatorname{Log}(-i\tau)=\operatorname{Log}\tau-i\pi/2$.
The result is the negative-kernel sector sum divided by $\sqrt{\det G}$.
Rank zero gives the trivial discriminant and both sides equal one.

These are classical mathematical statements. The repository supplies its own
Lean derivations of `sector_S`, `finite_weil_relations` and `milgram` for the
original `LatticeData`; the attribution does not claim a source-authored Lean
proof, an abstract quadratic-module API, or a CFT realization.
