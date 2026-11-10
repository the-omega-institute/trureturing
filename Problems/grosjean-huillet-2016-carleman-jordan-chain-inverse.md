---
slug: grosjean-huillet-2016-carleman-jordan-chain-inverse
bibkey: grosjeanhuillet2016carleman
doi: 10.1016/j.chaos.2016.10.004
url: https://arxiv.org/abs/1610.05919v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.result
---

# The inverse of a critical Carleman Jordan chain is an increasing-path sum

## Problem

N. Grosjean and T. Huillet, *Some combinatorial aspects of discrete non-linear population dynamics*, Chaos, Solitons & Fractals 93, 71–79 (2016), arXiv:1610.05919v1, §2.2, state the following conjecture (`snlmatrixRR.tex`, lines 449–452; the displayed formula is rendered inline):

> Then, we conjecture that $W^{-1}(k,k^{\prime })=\sigma (k-1,k^{\prime })$, $k^{\prime }\geq k\geq 1$.

The paper defines $\phi(x)=\sum_{r\geq1}\alpha_rx^r$ and $P(k,k')=[x^{k'}]\phi(x)^k$ in Eq. (2) (lines 126–141). In the critical case $\alpha_1=1$, its normalized columns satisfy $P\mathbf w_1=\mathbf w_1$, $P\mathbf w_k=\mathbf w_{k-1}+\mathbf w_k$ for $k>1$, $\mathbf w_1=e_1$, $\mathbf w_k(1)=0$ for $k>1$, and $\mathbf w_k(r)=0$ for $r>k$ (lines 403–428). Its recursion divides by $P(r,r+1)=r\alpha_2$ (lines 420–436), so this construction requires $\alpha_2\ne0$.

For $m\geq1$, $\sigma(m,j)$ is the sum of $\prod_{\ell=1}^mP(i_\ell,i_{\ell+1})$ over $1=i_1<\cdots<i_{m+1}=j$; it is zero when $j\leq m$, and $\sigma(0,j)=\delta_{1,j}$ (lines 442–447). The definitions and quotation are also recorded in [the literature note](../Library/Eigenstructure/grosjeanhuillet2016carleman.md).

Issue [#24105](https://github.com/the-omega-institute/trureturing/issues/24105) fixes the finite reading: for every real coefficient sequence with $\alpha_0=0$, $\alpha_1=1$, $\alpha_2\ne0$, and every size $N\geq1$, a normalized upper triangular Jordan-chain matrix exists for the principal truncation, and every such matrix is invertible with the stated inverse entries for $1\leq k\leq k'\leq N$. This is proved.

## Motivation

The inverse coefficients supply the increasing-path weights in the paper's critical-iteration representation immediately following the conjecture (lines 456–466). Determining them replaces inversion of the normalized Jordan-chain matrix by finite path sums at each coefficient degree. The finite formulation isolates this algebraic question from convergence of power series and infinite matrix operations.

## Gap

The bounded literature check in #24105 reports:

- OpenAlex record `W2530731495` and Crossref list three citing works;
- the readings of M. Myszkowski (2021), arXiv:2109.13165, and J. Brechtl, X. Xie, K. A. Dahmen and P. K. Liaw (2017 preprint), arXiv:1712.07036, found no settlement of this identity; the former gives a general triangular inverse formula in Lemma 2.5 and leaves Jordanization to future work in §5;
- the third citing work, Hernández-Ortega–Messina, Electr. Power Syst. Res. 209, 107974 (2022), was checked through metadata;
- the author-and-topic web searches and repository searches found no existing settlement.

The source text at arXiv:1610.05919v1 contains the conjecture at the location quoted above. The other literature readings are reported by the preregistration and are not independently reproduced here.

`not-found-in-searched-scope`.

## Route

Use zero-based indices $i,j\in\mathrm{Fin}\,n$ in this section, with comparisons and arithmetic taken on their natural values. The definition `carleman` sets $P(i,j)=[x^{j+1}](\sum_{r\geq0}\alpha_rx^r)^{i+1}$, and put $A=P-I$. The predicate `IsJordanChain` requires $Aw_0=0$, $Aw_j=w_{j-1}$ for $j>0$, first row $(1,0,\ldots)$, and zeros below the diagonal. The definition `sigma` starts with $\sigma_0(j)=\delta_{0,j}$ and uses $\sigma_{m+1}(j)=\sum_{i<j}\sigma_m(i)P(i,j)$.

1. **Matrix structure.** For any real sequence $\alpha$ and any $n\in\mathbb N$, assuming $\alpha_0=0$ and $\alpha_1=1$, `carleman_structure` gives $A(i,j)=0$ whenever $j\leq i$ and $A(i,j)=(i+1)\alpha_2$ whenever $j=i+1$. The additional assumption $\alpha_2\ne0$ makes every existing first-superdiagonal entry nonzero.
2. **Existence.** For any real $n\times n$ matrix $a$ with $a(i,j)=0$ for $j\leq i$ and $a(i,i+1)\ne0$ for every existing adjacent pair, any $k<n$, and any vector $b$ vanishing at indices $i\geq k$, `back_substitution` constructs $v$ with $av=b$, zero coordinate at index zero, and $v(i)=0$ for $i>k$. Its induction cancels row $k-1$ with the nonzero coefficient $a(k-1,k)$ when $k>0$; for $k=0$, $b=0$ and $v=0$. For any $\alpha$ and $n>0$ such that $A$ has those strict-triangular and nonzero-adjacent-entry properties, `chain_exists` uses this construction to obtain `IsJordanChain`: the initial column is $e_0$, and each later column solves for the preceding column with the required support and first coordinate.
3. **Dual rows.** For any $\alpha,n,W$ satisfying `IsJordanChain`, any $m\in\mathbb N$, and any $j\in\mathrm{Fin}\,n$, `chain_power` gives $A^mw_j=w_{j-m}$ if $m\leq j$ and zero otherwise. For any $\alpha$, $n>0$, and $W$ satisfying that predicate, `krylov_inverse` defines $Q(k,j)=(A^k)(0,j)$ and obtains $QW=I$ from the first-row normalization. It concludes that the determinant of $W$ is a unit and $W^{-1}=Q$.
4. **Paths.** For any $\alpha$, $n>0$, and $A=\operatorname{carleman}(\alpha,n)-I$ satisfying $A(i,j)=0$ for $j\leq i$, `path_expansion` identifies $(A^m)(0,j)$ with `sigma` for every $m\in\mathbb N$ and $j\in\mathrm{Fin}\,n$. Matrix multiplication appends the final edge; only $i<j$ contributes, and there $A(i,j)=P(i,j)$. With the coefficient hypotheses and $n>0$, `result` combines these lemmas and asserts the inverse-entry identity for $k\leq j$.

## Falsifier

The proof would miss the source's question if the indexing, normalization, or path weights differed. The formal definitions use the following correspondence:

- `carleman` at indices $i,j$ is the paper's $P(i+1,j+1)$;
- `IsJordanChain` has exactly the chain equations, first-row normalization and upper triangular support stated above; together these make its initial column $e_0$ when $n>0$;
- `sigma` with edge count $m$ and endpoint $j$ corresponds to the paper's $\sigma(m,j+1)$ by decomposing every strictly increasing path at its final edge, including the zero-edge case.

The claim includes existence, so its universal assertion about every normalized chain is not vacuous. It also asserts that the determinant is a unit, which supplies the invertibility needed for the inverse notation. No sign assumptions on the remaining real coefficients or analytic convergence assumptions are imposed. The case $\alpha_2=0$ and the zero-size truncation are outside `claim`.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.lean.json`.

Declaration statements:

- `result`: `sha256:28e83658ed0be2c8e6a6f28f60e86fc0189a6c28d902b56789a980520984551e`;
- `claim`: `sha256:5351097207287d277516921d1fa7918577cca3c8beef9e8179ee92372069e419`.

## Triage

Tier 1 conjecture of a 2016 paper, with no settlement found in the bounded literature check, preregistered in issue #24105 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real sequence $\alpha$ with $\alpha_0=0$, $\alpha_1=1$ and $\alpha_2\ne0$, and every $N\geq1$, there exists an $N\times N$ matrix satisfying the normalized upper triangular Jordan-chain conditions. Every matrix satisfying those conditions has determinant a unit in $\mathbb R$ and inverse entries $W^{-1}(k,k')=\sigma(k-1,k')$ for every $1\leq k\leq k'\leq N$, with the source indexing.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Decisive mechanism and scope.* Under `IsJordanChain` and $n>0$, `krylov_inverse` identifies the entire inverse with the rows $e_0^{\mathsf T}A^k$; no assumptions on the coefficient sequence are needed for this conditional lemma. The chain equations lower the column index, and its first-row normalization detects precisely the column that has reached index zero. Thus the inverse step uses the normalized chain rather than any further analytic property of $\phi$. The separate strict-triangular hypothesis of `path_expansion`, together with $n>0$, makes these rows increasing-path sums.
- *Compatible truncations.* Under the coefficient hypotheses of `claim`, the formula for $Q=W^{-1}$ in `krylov_inverse` determines every chain uniquely at each positive size: two such matrices have the same inverse and hence coincide. Restricting a larger chain to a smaller positive principal block preserves its chain equations, since column $j$ has no support beyond $j$. Its normalization and triangular support are preserved as well. Uniqueness therefore makes these restrictions agree. Each path ending at $k'$ stays within $1,\ldots,k'$, so its weight is independent of any larger truncation. This supplies the entrywise interpretation of the source's infinite triangular inverse; it asserts no convergence of infinite operator products.
- *Sharp coefficient boundary.* If $\alpha_0=0$, $\alpha_1=1$, but $\alpha_2=0$, no chain with this normalization and support exists at any size $N\geq2$: its second column is supported on the first two coordinates, while $A(1,1)=A(1,2)=0$, so the first coordinate of $Aw_2$ is zero and cannot equal the first coordinate one of $w_1=e_1$. For size one, $P=(1)$ and $W=(1)$ satisfies the chain conditions without a restriction on $\alpha_2$. These boundary conclusions are not part of `result`.
- *Effect on the paper.* Under the hypotheses of `claim` and $N>0$, let $S$ be the $N\times N$ shift with ones on its first superdiagonal. The chain equations give $PW=W(I+S)$. For every integer $t\geq0$, the binomial expansion of $(I+S)^t$, the first-row normalization, and the inverse formula yield $(P^t)(1,j)=\sum_{m=0}^{\min(t,N-1)}\binom{t}{m}\sigma(m,j)$ for $1\leq j\leq N$. Consequently the inverse substitution in the critical-iteration representation following the conjecture (source lines 456–466) is justified at every finite coefficient degree. The module does not formalize this additional matrix-power identity, the representation as an analytically evaluated infinite series, the slow-extinction assertions at lines 468–495, or the non-critical dynamics. Analytic convergence and the validity of those asymptotic assertions remain unverified here.

## ASSUMED-UNVERIFIED

The literature check is bounded by the sources and searches reported in #24105 and does not establish exhaustive novelty or priority. The citation counts, the substantive readings of Myszkowski (2021), arXiv:2109.13165, and Brechtl et al. (2017), arXiv:1712.07036, the metadata check of Hernández-Ortega–Messina (2022), the author-and-topic web searches, the earlier repository search, and the reported arXiv/HAL version inventory were not independently reproduced. The author and year metadata of the two citing arXiv preprints was checked on their abstract pages. The source reading verified here is arXiv:1610.05919v1, `snlmatrixRR.tex`, particularly lines 126–141 and 400–495.

The path-sum interpretation of the recurrence and all further consequences grouped under "Argued, not formalized" are mathematical arguments rather than additional claims of `result`. Uniqueness and compatibility across truncations, the excluded-coefficient boundary, and the finite matrix-power consequence are not separately formalized in this module. Infinite analytic convergence, slow-extinction asymptotics, the non-critical case, and other source conclusions are not settled by this theorem.
