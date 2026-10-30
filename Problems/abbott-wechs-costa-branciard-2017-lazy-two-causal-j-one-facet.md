---
slug: abbott-wechs-costa-branciard-2017-lazy-two-causal-j-one-facet
bibkey: abbottwechscostabranciard2017gmnc
doi: 10.22331/q-2017-12-14-39
url: https://arxiv.org/abs/1708.07663v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.result
---

# The lazy two-causal inequality $J_1$ induces a facet for every $N\ge2$

## Problem

A. A. Abbott, J. Wechs, F. Costa and C. Branciard, *Genuinely Multipartite Noncausality*, arXiv:1708.07663v2 (Quantum 1, 39, 2017), Section III.C, ask in `genuine_multi_noncausal.tex`, line 343:

> It is interesting to ask if this inequality is tight (i.e., facet inducing) for all $N$.

Their conjecture is stated at line 344:

> By explicitly enumerating the vertices of the 2-causal polytope for $N=4$ (of which there are $136\,818\,592$) we were able to verify that $J_1(4)\ge 0$ is indeed also a facet, and we conjecture that this is true for all $N$.

Let $U=\{0,\ldots,N-1\}$ and represent binary inputs and outputs by their supports $T,A\subseteq U$. A deterministic lazy two-causal strategy consists of a nonempty proper first group $K\subsetneq U$ and a function $f$ on input supports such that $f(T)\subseteq T$ for every $T$, and
$T\cap K=S\cap K$ implies $f(T)\cap K=f(S)\cap K$ for every $T,S$. The complementary group's outputs may depend on the entire input. Its deterministic table is $P_f(T,A)=1$ when $f(T)=A$ and $0$ otherwise. Let $C_N$ be the real convex hull of these tables.

In these coordinates, Eq. (10) is
$J_1(p)=\sum_{\varnothing\ne K\subsetneq U}p(K,K)-p(U,U)\ge0$.
Laziness makes $p(K,K)$ exactly the marginal event in the source's formula. Definition 2, the deterministic characterization, and the lazy convention occur at TeX lines 146–151, 203–205, and 213–214; Eq. (10) is at lines 333–337. See [the literature note](../Library/Observer/abbottwechscostabranciard2017gmnc.md).

Issue [#23904](https://github.com/the-omega-institute/trureturing/issues/23904) fixes the reading: for every natural $N\ge2$, $J_1$ is nonnegative on $C_N$, and $F_N=C_N\cap\{p\mid J_1(p)=0\}$ has affine dimension one less than $C_N$. This is proved. Precisely, the module uses $d(S)=\dim_{\mathbb R}\operatorname{span}\{p-q\mid p,q\in S\}$ and asserts $d(F_N)+1=d(C_N)$.

## Motivation

The source uses two-causal inequalities to distinguish correlations admitting a causal order between two complementary groups from genuinely multipartite noncausal correlations. Validity of $J_1\ge0$ gives such a test. Facetness additionally identifies a maximal proper face of the polytope, establishing the geometric strength of this family for arbitrarily many parties without enumerating the entire polytope.

## Gap

The bounded literature check recorded in #23904 reports:

- both arXiv versions retain the conjecture;
- an INSPIRE inventory contains 26 citing records, with sources available for 19; searches for "facet" in those sources found six relevant keyword matches, none addressing facetness of $J_1(N)$ for general $N$;
- a further report covers full-text screening of thirteen citing or related works without a settlement;
- repository searches found no prior treatment of this conjecture.

`not-found-in-searched-scope`.

## Route

Write $R_N=\{(T,A)\mid\varnothing\ne A\subseteq T\subseteq U\}$, $r=|R_N|$, and $I_N=R_N\setminus\{(U,U)\}$. The following helper names refer to private lemmas in the canonical module.

1. **Validity.** For every $N$, nonempty proper $K$, and $f$ satisfying all the laziness and first-group independence conditions defining `IsLazyTwoCausalStrategy K f`, `vertex_valid` proves $J_1(P_f)\ge0$. Indeed, $f(U)=U$ forces $f(K)=K$, so $P_f(U,U)\le P_f(K,K)$, and the positive sum includes this term. `validity N` extends the inequality to every $p\in C_N$ by convexity of the nonnegative half-space of the linear functional `jLinear N`.
2. **Dimension bound.** For every $N$ and $p\in C_N$, `polytope_laws` gives zero entries whenever $A\nsubseteq T$ and row sums equal to one. Thus `polytope_span_le` places the direction space in `homogeneousSpace N`, consisting of tables with the same forbidden zeros and row sums zero. For every $N$, `restriction_injective` proves that restriction of this space to $R_N$ is injective: each empty-output entry is recovered from its zero row sum. Consequently `dimension_upper N` gives $d(C_N)\le r$.
3. **Points on the zero face.** For $N\ge2$, `zero_on_face` puts the always-empty-output table $Z$ in $F_N$. For every $N$ and $\varnothing\ne A\subsetneq T\subseteq U$, `spike_on_face` puts $V_{T,A}$ in $F_N$, where the strategy outputs $A$ exactly at input $T$ and outputs the empty set otherwise; its first group is $U\setminus A$. For every $N$ and nonempty proper $K\subsetneq U$, `block_on_face` puts $B_K$ in $F_N$: at input $T$, its strategy outputs $K$ if $K\subseteq T$, and additionally outputs $U\setminus K$ exactly when $T=U$. Its first group is $K$.
4. **Independence.** For each $i=(T,A)\in I_N$, `facePoint` selects $B_T$ when $A=T$ and $V_{T,A}$ otherwise; `facePoint_mem` puts every such point in $F_N$. For $i,j\in I_N$ with $j$ diagonal, `diagonal_coordinate` gives value $1$ at coordinate $j$ of $\operatorname{facePoint}(i)-Z$ exactly when $i=j$, and $0$ otherwise. For $i,j\in I_N$ with $i$ off-diagonal, `off_diagonal_coordinate` gives the same coordinate formula. Evaluating a linear relation at diagonal coordinates eliminates all block coefficients; the remaining coordinates eliminate all spike coefficients. `face_independent N` establishes independence for every $N$. For $N\ge2$, `dimension_lower` therefore gives $|I_N|\le d(F_N)$, and `index_count` gives $|I_N|+1=r$.
5. **A strict dimension increase.** For $N\ge2$, `identity_positive` puts the identity strategy $f(T)=T$ in $C_N$ with strictly positive $J_1$. Differences of zero-face points lie in the kernel of `jLinear N`, while the identity table minus $Z$ has positive value. Under the same hypothesis $N\ge2$, `dimension_strict` gives $d(F_N)+1\le d(C_N)$. Together with the preceding bounds this forces $d(F_N)+1=d(C_N)$, as assembled by `result`.

## Falsifier

The proof would not answer the source's conjecture if the strategy class, functional or dimension differed from the source's. The module:

- permits arbitrary correlations within each first group, with only independence from complementary inputs imposed, matching the deterministic description of Definition 2;
- takes the convex hull over every nonempty proper first group, with the lazy condition imposed at every input;
- uses the source's marginal probabilities because at input support $K$ all outputs outside $K$ are forced to zero;
- uses `vectorSpan`, the span of pairwise differences, so its real `finrank` measures affine dimension for these nonempty sets. For $N\ge2$, `zero_on_face` supplies a point of both $F_N$ and $C_N$.

The theorem's range is $N\ge2$; it makes no assertion about facetness for a single party, enlarged alphabets, or a different inequality.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.lean.json`.

Declaration statements:

- `result`: `sha256:109885ef4f5bc2b8f978299d8cc2b7038afdbe01032fc55fc7c5501e6a7e1fe5`;
- `claim`: `sha256:b8178e260347472f7284aa0d7b95b3ba8f90e148c36b7f0fcff98af37fed7ecb`.

## Triage

Tier 1 conjecture of a 2017 Quantum paper, preregistered in issue #23904 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $N\ge2$, every $p\in C_N$ satisfies $J_1(p)\ge0$, and the real dimension of the span of differences of points of $F_N$ plus one equals the real dimension of the span of differences of points of $C_N$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Decisive mechanism.* For every $N$, `spike_on_face` applies to $\varnothing\ne A\subsetneq T\subseteq U$, and `block_on_face` applies to nonempty proper $K\subsetneq U$. For $i,j\in I_N$, `diagonal_coordinate` assumes that the target index $j=(T,A)$ has $A=T$, while `off_diagonal_coordinate` assumes that the source index $i=(T,A)$ has $A\ne T$; each gives the corresponding coordinate of $\operatorname{facePoint}(i)-Z$ as $1$ if $i=j$ and $0$ otherwise. Thus the block coefficients in any zero linear relation vanish at the diagonal coordinates, and the remaining spike coefficients vanish at their own coordinates. For $N\ge2$, `zero_on_face` and `facePoint_mem` put the endpoints of these independent differences in $F_N$. This triangular structure supplies the zero face's directions without requiring a classification of all deterministic strategies.
- *Explicit dimensions.* Each party has three possibilities in a pair $A\subseteq T$: outside $T$, in $T\setminus A$, or in $A$. There are $3^N$ pairs, of which $2^N$ have $A=\varnothing$, giving $r=3^N-2^N$. For $N\ge2$, `dimension_upper`, `dimension_lower`, `index_count` and `dimension_strict` give $r-1\le d(F_N)<d(C_N)\le r$. Hence $d(C_N)=3^N-2^N$ and $d(F_N)=3^N-2^N-1$. The closed counting formula is not a separate declaration of the module.
- *Sharpness and boundary.* For $N\ge2$, `zero_on_face` shows that the lower bound zero is attained, while `identity_positive` shows that the functional is not constant on $C_N$. For $N=0$ or $N=1$ there is no nonempty proper first group, so the defining generating set and its convex hull are empty; these cases do not describe the source's two-group scenario. Facetness in other input/output scenarios and analogous classifications for other inequalities remain open relative to this settlement.
- *Effect on the paper.* The conjectured facet status following Eq. (10) is affirmed throughout its lazy-scenario range $N\ge2$. The source's validity proof in Appendix A, TeX lines 684–693, uses first-group independence and does not assume the facet conjecture. Its game reformulation at lines 338–342 likewise needs no facet premise. The settlement changes the geometric status of Eq. (10) and supplies no new process-matrix realizability statement or conclusion about $J_2$.

## ASSUMED-UNVERIFIED

The literature check in #23904 is bounded and does not establish exhaustive worldwide novelty or priority. Its v1 reading, INSPIRE inventory, nineteen-source keyword search, thirteen-work full-text report, and repository search were not independently reproduced for this dossier. The v2 TeX source and the cited passages were checked directly; its member `genuine_multi_noncausal.tex` has MD5 `03974e3e48407d2a35b64870af0654f3`.

The arguments under "Argued, not formalized" are not additional formalized conclusions of `result`; in particular, the closed dimension formula and the degenerate-party discussion are not separately stated there. The correspondence with the source's probabilistic Definition 2 is a mathematical reading of its deterministic characterization, not a separately formalized equivalence with that probabilistic decomposition. The source's enumeration of all vertices at $N=4$, its numerical process-matrix searches, and its supplementary material were not reproduced. Facetness outside the lazy scenario, a full facet classification, and physical realizability of violations are outside the proved claim.
