---
slug: gao-li-2020-complete-maximal-identity-clique-path
bibkey: gaoli2020sandpileidentity
doi: 10.1016/j.dam.2020.08.028
url: https://arxiv.org/abs/2008.10079v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.result
---

# Complete maximal identity for clique–path products occurs exactly at $K_4\square P_2$

## Problem

Yibo Gao and Rupert Li, *Compatible recurrent identities of the sandpile group and maximal stable configurations*, arXiv:2008.10079v1 (2020; Discrete Appl. Math. 288, 123–137, 2021; DOI 10.1016/j.dam.2020.08.028), Section 6, Conjecture 6.4, state verbatim in `Paper/Conjectures.tex`, line 139:

> For $i,j \in \mathbb{Z}_{>1}$, the only graph $K_i \cp P_j$ which has the complete maximal identity property is $K_4 \cp P_2$.

The source macro `\cp` denotes the Cartesian product, written $\square$ below; $P_j$ has $j$ vertices. The source defines the maximal stable configuration by $m_G(v)=\deg_G(v)-1$ and the complete maximal identity property by requiring that this configuration be the recurrent identity for every choice of sink (`Paper/Preliminaries.tex`, lines 19–29; `Paper/CMIP.tex`, lines 8–10 and 37–41). The definitions and source identifier are also recorded in [the literature note](../Library/StatisticalMechanics/gaoli2020sandpileidentity.md).

Issue [#26439](https://github.com/the-omega-institute/trureturing/issues/26439) fixes the reduced-Laplacian reading. For $i,j\in\mathbb N$ with $i,j\ge2$, let $G=K_i\square P_j$, let $L_s$ be its integer Laplacian with the row and column of $s$ removed, and let $m_s$ be the restriction of $m_G$ to the non-sink vertices. The proposition `claim` is

$\forall i,j\in\mathbb N,\quad i\ge2\ \Longrightarrow\ j\ge2\ \Longrightarrow\ \bigl[(\forall s\in V(G),\ m_s\in L_s\mathbb Z^{V(G)\setminus\{s\}})\ \Longleftrightarrow\ (i=4\ \land\ j=2)\bigr].$

This proposition is proved by `result`.

## Motivation

The source studies whether recurrent identities for different sinks are compatible. Complete maximal identity asks for the specific configuration given by the vertex degrees to represent the zero sandpile-group class at every sink. The conjecture classifies this property throughout a natural family of Cartesian graph products, rather than at one sink or for finitely many graph sizes.

## Gap

The bounded literature check recorded in #26439 reports:

- the conjecture in arXiv:2008.10079v1;
- a search-seat report of zero citing works from Crossref and OpenAlex, and arXiv searches for “complete maximal identity” and “maximal identity property” returning only the source;
- a preregistration repository search reporting no matching dossier, literature note or issue for the paper or property.

`not-found-in-searched-scope`.

The source's stated partial result is explicit (`Paper/Conjectures.tex`, line 144):

> We provide a proof of the special cases of \cref{conjecture:C-KxP} when $j=2,3$.

The missing range is unbounded path length $j\ge4$ for every clique size $i\ge2$.

## Route

Write $L$ for the full integer Laplacian, $m(v)=\deg_G(v)-1$, and $u_j=(S_{j-1})(i+2)$, where $S_n$ denotes `Polynomial.Chebyshev.S ℤ n`. Its normalization is $S_0=1$, $S_1=X$ and $S_{n+2}=XS_{n+1}-S_n$; the subscript $j-1$ is an integer.

1. **Mass and the missing sink equation.** For $i,j\in\mathbb N$ with $i,j\ge2$, `total_mass` gives $M=\sum_{v\in V(G)}m(v)=i(ij-2)$. Under these same bounds, for any $s\in\mathrm{Fin}\,i\times\mathrm{Fin}\,j$ satisfying `maximalIdentityAt i j s`, `lift_equations` gives an integer vector $f$ on all vertices with $(Lf)(v)=m(v)-M\mathbf1_{v=s}$ for every $v$. Its proof extends a reduced solution by setting its sink coordinate to zero and uses the zero sum of the full Laplacian image to recover the sink equation.
2. **A path recurrence.** For $i,j\ge2$ and `maximalIdentityAt i j (0,0)`, `path_reduction` gives $x:\mathbb N\to\mathbb Z$ with $x_1=(i+1)x_0$, with $x_{k+2}=(i+2)x_{k+1}-x_k$ for every $k\in\mathbb N$ satisfying $k+2<j$, and with $(i+1)x_{j-1}-x_{j-2}=-i(ij-2)$. Its proof subtracts the equations at clique coordinates $0$ and $1$ and reverses the path; both clique coordinates exist under $i\ge2$.
3. **Integer divisibility.** For any $i\in\mathbb N$, $j\ge2$ and integer sequence $x$ satisfying $x_1=(i+1)x_0$ and the recurrence for every $k\in\mathbb N$ with $k+2<j$, `path_elimination` gives $(i+1)x_{j-1}-x_{j-2}=i u_j x_0$. Consequently, under $i,j\ge2$ and `maximalIdentityAt i j (0,0)`, `identity_divisibility` gives $u_j\mid ij-2$: comparison with the sink equation cancels the nonzero integer $i$ and supplies the integer quotient $-x_0$.
4. **Exclusion of all other parameters.** For $i\ge2$ and $j\ge3$, `continuant_growth` gives $ij-2<u_j$. Here $ij-2>0$, so divisibility is impossible. For $i\ge2$ and $j=2$, $u_2=i+2$, and $u_2\mid 2i-2$ implies $i+2\mid6$, leaving $i=4$. Precisely, `divisibility_classification` assumes $i,j\ge2$ and $u_j\mid ij-2$ and concludes $i=4$ and $j=2$.
5. **The exceptional product at every sink.** The reverse direction of `result` proves `maximalIdentityAt 4 2 s` for every $s\in\mathrm{Fin}\,4\times\mathrm{Fin}\,2$. It assigns zero at $s$, five at other vertices in the same path layer, six at the vertex in the other layer with the same clique coordinate, and seven otherwise. Restricted to the non-sink vertices, this integer vector has reduced Laplacian image constantly three, equal to degree minus one. The forward direction of `result` uses the condition at $(0,0)$; the reverse direction uses this all-sink construction.

## Falsifier

A mismatch between the source property and the encoded lattice condition would invalidate the interpretation as a settlement of the source conjecture. The module uses:

- the vertex set $\mathrm{Fin}\,i\times\mathrm{Fin}\,j$ and Mathlib's `boxProd` of the complete graph and `pathGraph j`, so adjacency changes one coordinate along an edge of its factor and fixes the other;
- Mathlib's integer `lapMatrix`, degree matrix minus adjacency matrix, restricting both matrix indices to the subtype of vertices unequal to the sink;
- the degree in the original graph, cast from $\mathbb N$ to $\mathbb Z$ before subtracting one;
- an existential integer vector with no requirement that its firings form a legal nonnegative firing sequence.

The source supplies the interpretation: $m_G$ is recurrent, equivalence to zero means membership in the reduced integer Laplacian image, and the recurrent identity is the recurrent representative of the zero class (`Paper/Preliminaries.tex`, lines 29, 157–172 and 192–196; `Paper/CMIP.tex`, lines 27–32). Since $m_G$ is already recurrent, that membership identifies it with the recurrent identity. This sandpile interpretation is not formalized in the module; `result` proves the displayed integer-image proposition. The bounds $i,j\ge2$ and the quantifier over every sink are part of that proposition.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.lean.json`.

Declaration statements:

- `result`: `sha256:f748bed9eb939dec423182a6165ed3ae1acfc6dac7179c29196033aa0361e860`;
- `claim`: `sha256:cf0fbd4e174f585b8855d38f5a38ee7f8ff0185aa763c617396167f568b1ed3b`.

## Triage

Tier 1 conjecture of a 2020 preprint published in Discrete Applied Mathematics in 2021, preregistered in issue #26439 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $i,j\in\mathbb N$ with $i,j\ge2$, the degree-minus-one vector belongs to the reduced integer Laplacian image for every sink of $K_i\square P_j$ if and only if $i=4$ and $j=2$.

**Computed, not formalized.** None.

**Argued, not formalized.**

- *One endpoint decides the complete property.* For $i,j\ge2$, assume the image condition only at $(0,0)$. `identity_divisibility`, with exactly these bounds and that sink condition, gives $u_j\mid ij-2$; `divisibility_classification`, with the same bounds and that divisibility, forces $(i,j)=(4,2)$. The reverse direction of `result` supplies the condition at every sink for this pair. Conversely, an all-sink condition includes $(0,0)$. Thus within this family a single endpoint sink suffices to decide the all-sink property. The decisive obstruction is the integer divisibility forced by a difference between two clique coordinates, together with the growth of its recurrence coefficient. No classification of individual interior sinks in the excluded products is supplied here; that neighbouring question remains open here.
- *The path-length boundary matters.* For $i\ge2$ and $j=1$, the product is $K_i$. At any sink its reduced Laplacian is $iI-J$ on $i-1$ coordinates, where $J$ is the all-ones matrix. The constant integer vector with value $i-2$ is sent to the same constant vector, because $i-(i-1)=1$; this vector is degree minus one. Hence removing $j\ge2$ would introduce additional products with the integer-image property at every sink. This boundary argument is not a declaration of the module.
- *Effect on the source.* With the source interpretation stated above, the classification settles its conjecture for all $i,j\ge2$ and includes the source's $j=2,3$ cases. In the v1 TeX the only cross-reference to `conjecture:C-KxP` is the special-case proof at `Paper/Conjectures.tex`, line 144; there is no subsequent theorem stated conditional on it. The separate strong-product conjecture for paths, Conjecture 6.2 (`conjecture:S-PxP`, lines 124–126), remains outside this settlement. The source identifies that product as the strong product, not the Cartesian product (`Paper/Conjectures.tex`, lines 3–5).

## ASSUMED-UNVERIFIED

The bounded literature check in #26439 does not establish exhaustive worldwide novelty or priority. Its Crossref, OpenAlex and arXiv search readings and its repository-search reading are reported by the preregistration and were not independently reproduced; no other arXiv version or the journal text was checked. The quoted conjecture and the cited definition passages were checked in the v1 TeX source.

Recurrence theory, stabilization and the identification of the integer-image predicate with the source's recurrent-identity property are not formalized in this module. The endpoint equivalence and the $j=1$ boundary argument in “Argued, not formalized” are not separate compiled declarations. The interior-sink question and the source's other conjectures are not settled here.
