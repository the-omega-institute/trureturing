---
bibkey: abdesselam2022nonabelian
authors: Abdelmalek Abdesselam
year: 2022
title: "Non-Abelian correlation inequalities and stable determinantal polynomials"
doi: 10.48550/arXiv.2207.07603
url: https://arxiv.org/abs/2207.07603v2
claim: "Problem 2 asks whether the XY model satisfies the PGG inequalities; Problem 3 asks whether Theorem 2.3, the PGG inequalities for stable determinantal polynomials, holds for every positive real exponent eta in place of positive half integers."
strata_touched:
  - D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation
  - D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation
license: citation-only
triage: anchor
---

# Non-Abelian correlation inequalities and stable determinantal polynomials

The following quotations are from arXiv:2207.07603v2, with the printed page numbers.

Page 4 defines row multiplication:

> Indeed, the multiindex $\alpha$ is here considered as a row vector of length $m$ while $V$ is a $m \times n$ matrix and $\alpha V$ simply denotes the matrix product.

Page 5 defines parity:

> Suppose we are given a group homomorphism ρ : ℤⁿ → (ℤ/2ℤ)ᴸ, for some integer L ≥ 0.

> We will say that a is even iff ρ(a) = 0.

Page 9 gives the matrix setting:

> Let q ∈ ℕ_{>0}, and let A₁, …, Aₙ be n real symmetric positive semidefinite matrices of q × q format. Suppose that A₁ + ⋯ + Aₙ is positive definite and define the polynomial P(x) = det(x₁A₁ + ⋯ xₙAₙ) which is then strictly positive for x ∈ (0, ∞)ⁿ.

> We also assume we have at our disposal a parity check homomorphism ρ : ℤⁿ → (ℤ/2ℤ)ᴸ and an associated definition of being even for multiindices $a\in\mathbb{N}^n$, as in the previous section.

Page 10 states Theorem 2.3:

> (The PGG inequalities for stable determinantal polynomials) For any $r\in\mathbb{N}_{>0}$, the substitute $a\mapsto\mathbb{1}\{a\ {\rm even}\}P(a)^{-\frac{r}{2}}$ for the map $a\mapsto\langle\mathcal{O}^a\rangle$ satisfies all the PGG inequalities. More precisely, $\forall m\ge 0$, $\forall V\in\mathbb{N}^{m\times n}$ such that $\mathbf{1}_m V$ is even, $\forall (\varepsilon_1,\ldots,\varepsilon_m)\in\{-1,1\}^m$, and for all even $u\in\mathbb{N}_{>0}^n$, we have
> $$\sum_{\substack{\alpha,\beta\in\mathbb{N}^m\\\alpha+\beta=\mathbf{1}_m}}\mathbb{1}\{\alpha V\ {\rm even}\}\varepsilon^{\beta}P(u+\alpha V)^{-\frac{r}{2}}P(u+\beta V)^{-\frac{r}{2}}\ge 0.$$

Page 14 asks:

> **Problem 3:** In the light of investigations of spin models with non-integer number of components N, as in [8], it would be interesting to see if Thm. 2.3 still holds for P^{−η} where η is any positive real number instead of being restricted to half integers.

The encoding uses zero-based `Fin` indices, real matrices, the additive homomorphism
`(Fin n → ℤ) →+ (Fin L → ZMod 2)`, and natural multi-indices cast to integers for
parity. A binary vector `α : Fin m → Fin 2` indexes each pair `α + β = 1` once,
with `β_i = 1 - α_i`. The sign is `ε^β = ∏ i, ε_i^{β_i}` (p. 6).
Row-vector multiplication uses Mathlib `Matrix.vecMul`.
All fractional powers are `Real.rpow`.


The following passages give the O(N) model, its parity convention, the PGG collection,
and Problem 2 verbatim from the source TeX. Pair indices in the formal encoding are
zero-based, so a pair is the subtype `{e : Fin p × Fin p // e.1 < e.2}`.
The O(2) measure convention uses the image of normalized Haar measure on angles
under θ ↦ (cos θ, sin θ), the rotation-invariant probability measure on S¹.

Page 14, Problem 2 (TeX lines 733–734):

> For the XY model, or O(2) model, the GG inequalities were proved by Ginibre [18]. What about the padded generalizations given by the PGG inequalities?

```tex
\medskip\noindent{\bf Problem 2:}
For the XY model, or $O(2)$ model, the GG inequalities were proved by Ginibre~\cite{Ginibre2}. What about the padded generalizations given by the PGG inequalities?
```

Page 2, the O(N) model (TeX lines 95–98):

```tex
The $O(N)$ model example corresponds to taking $\Lambda$ a finite subset of $\mathbb{Z}^d$, say of cardinality $p$, and letting $X=(\mathbb{S}^{N-1})^{\Lambda}$ where $\mathbb{S}^{N-1}$ is the unit sphere in $\mathbb{R}^N$, $N\in\mathbb{N}_{>0}$.
The free measure $\mu$ is the product of copies of the unique $O(N)$-invariant Borel probability
measure on the sphere $\mathbb{S}^{N-1}$. Elements of $X$ are spin configurations $(\sigma_1,\ldots,\sigma_p)$ where we have chosen some ordering of the $p$ elements of $\Lambda$, for the sake of notational simplicity. Each spin $\sigma_i$ is a column vector $(\sigma_{i,1},\ldots,\sigma_{i,N})^{\rm T}$ in $\mathbb{S}^{N-1}$, i.e., which satisfies $\sum_{\ell=1}^N \sigma_{i,\ell}^2=1$. The action of an element $R$ of the orthogonal group $O(N)$ on a vector $\sigma\in\mathbb{S}^{N-1}$ is by matrix multiplication $(R,\sigma)\mapsto R\sigma$.
The basic observables are the inner products $\sigma_i\cdot\sigma_{i'}:=\sum_{\ell=1}^{N}\sigma_{i,\ell}\sigma_{i',\ell}$, with $1\le i<i'\le p$. Namely, $n=\binom{p}{2}$, and $\mO_1,\ldots,\mO_n$ are just some choice of ordering of the functions on $X$ given by the inner products of pairs of spins $\sigma_i\cdot\sigma_{i'}$. These are invariant observables, because they are invariant under the diagonal action of $O(N)$, namely changing all the spins by the same orthogonal matrix $R$.
```

Page 5, parity (TeX lines 220–222):

```tex
Suppose we are given a group homomorphism $\rho:\mathbb{Z}^n\rightarrow (\mathbb{Z}/2\mathbb{Z})^L$, for some integer $L\ge 0$. We think of the image $\rho(e_j)$ of the $j$-th canonical basis vector as the parity check vector for the basic observable $\mO_j$. Therefore $\rho(a)$ for a multiindex $a\in\mathbb{N}^n\subset\mathbb{Z}^n$ is the parity check vector for the monomial $\mO^a$. We will say that $a$ is even iff $\rho(a)=0$. In the case of the $O(N)$ model as described above, we take $L=p$ and for $j$ corresponding to a pair of vertices $(i,i')$, with $1\le i<i'\le p$,
we define $\rho(e_j)$
as the vector with all components equal to 0 except the $i$'-th and $i'$-th components which are set equal to 1.
```

Page 6, the PGG inequalities (TeX lines 250–270):

```tex
{\bf The PGG inequalities:}
We will say that the system $(X,\mu,\mO,L,\rho)$ satisfies the PGG collection of inequalities iff
$\forall m\ge 0$, $\forall V\in\mathbb{N}^{m\times n}$,
$\forall (\varepsilon_1,\ldots,\varepsilon_m)\in\{-1,1\}^m$, and all even $u\in\mathbb{N}^n$
we have
\[
\int_{X^2}{\rm d}\mu(x){\rm d}\mu(y)\ \mO(x)^u\ \mO(y)^u\
\prod_{i=1}^{m}\left[
\mO(x)^{V_{i\ast}}+\varepsilon_i\mO(y)^{V_{i\ast}}
\right]\ge 0\ .
\]
If one prefers not to
use the variable duplication trick, then the last inequality can be rewritten as
\begin{equation}
\sum_{\substack{\alpha,\beta\in\mathbb{N}^m\\ \alpha+\beta=\mathbf{1}_m}}
\varepsilon^{\beta}
\langle\mO^{u+\alpha V}\rangle\ \langle\mO^{u+\beta V}\rangle
\ge 0\ ,
\label{PGGnodup}
\end{equation}
where $\mathbf{1}_m:=(1,\ldots,1)\in\mathbb{N}^m$, $\varepsilon^{\beta}=\varepsilon_{1}^{\beta_1}\cdots\varepsilon_{m}^{\beta_m}$, and the binomial is not needed.
```

Page 2, observable monomials (TeX line 45):

```tex
we will write $\mO(x)^a$ or just $\mO^a$ for the monomial $\mO_1(x)^{a_1}\cdots\mO_n(x)^{a_n}$ in the basic observables.
```

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2207.07603
- URL: https://arxiv.org/abs/2207.07603v2
- PDF: https://arxiv.org/pdf/2207.07603v2, pp. 5, 9, 10 and 14.
