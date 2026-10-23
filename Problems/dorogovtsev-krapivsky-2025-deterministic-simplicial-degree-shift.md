---
slug: dorogovtsev-krapivsky-2025-deterministic-simplicial-degree-shift
bibkey: dorogovtsevkrapivsky2025deterministic
doi: 10.1088/1742-5468/ae2092
url: https://arxiv.org/abs/2507.07402v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.result
---

# The distinct upper degrees of deterministic simplicial complexes shift by dimension

## Problem

S. N. Dorogovtsev and P. L. Krapivsky, *Deterministic simplicial complexes*, arXiv:2507.07402v1; J. Stat. Mech. (2025) 123404, Section II.3, equation (34). The source TeX `DSC-7.tex`, lines 505–510, states:

> Another useful general relation
>
> $K^{(d)}(n) = 0 \cup K^{(0)}(n-d)$
>
> is conjecturally valid for all $n \geq d + 1$ and $d \geq 1$.

Here $K^{(d)}(n)$ lists the distinct upper degrees in ascending order, without multiplicities (TeX lines 415–425); the $0$ on the right denotes adjoining the value zero. The growth rule and upper degrees are also described in [the literature note](../Library/StatisticalMechanics/dorogovtsevkrapivsky2025deterministic.md).

Issue [#20715](https://github.com/the-omega-institute/trureturing/issues/20715) fixes the precise reading. Let $V$ be a type with decidable equality, let $v_0\in V$, and let $v:\mathbb N\to\operatorname{Finset}(V)\to V$ be injective as a function of the pair $(s,\sigma)$, with $v(s,\sigma)\ne v_0$ for every $s,\sigma$. Define the finite families of nonempty faces by

$C_0=\{\{v_0\}\}$,

$C_{s+1}=C_s\cup\bigcup_{\sigma\in C_s}\{\{v(s+1,\sigma)\}\cup\beta:\beta\subseteq\sigma\}$.

Every existing nonempty face receives its own fresh vertex, all subsets $\beta$ including the empty subset are used, and earlier faces persist. The labeling hypotheses ensure that a new vertex differs from every earlier vertex and from the other vertices added in the same step.

For a finite family $C$ and a finite vertex set $\tau$, define

$\operatorname{upperDegree}(C,\tau)=\#\{\rho\in C:\tau\subseteq\rho,\ |\rho|=|\tau|+1\}$,

$\operatorname{degreeSet}(C,d)=\{k\in\mathbb N:\exists\tau\in C,\ |\tau|=d+1,\ \operatorname{upperDegree}(C,\tau)=k\}$.

Write $K^d(n)=\operatorname{degreeSet}(C_n,d)$. The claim is that, for every such $V,v_0,v$ and all natural numbers $d,n$ with $d\geq1$ and $n\geq d+1$,

$K^d(n)=\{0\}\cup K^0(n-d)$.

Subtraction is natural subtraction; the hypotheses imply $n-d\geq1$. Equality of these sets expresses equality of the source's lists of distinct values. This claim is proved.

## Motivation

The source studies local structure through upper degrees, alongside simplex counts and Hodge Laplacian spectra. The identity reduces the distinct upper degrees in every positive dimension to vertex degrees at an earlier generation. It explains why the same degree lists recur along fixed generation-minus-dimension offsets and supplies the dimension shift used for the largest and second-largest distinct upper degrees. It concerns which values occur; their multiplicities and degree distributions require additional information.

## Gap

The bounded literature check is recorded in #20715:

- The independently read v1 TeX retains the conjecture. The arXiv abstract page lists only v1 and identifies the journal DOI above.
- The orchestrator's OpenAlex listing for W4417190118 contained one citing work; the search seat reported that its reading did not settle the relation. The orchestrator reported that Krapivsky–Lucas (2026), arXiv:2608.26547, cites the source only in proposing computations for random models.
- The orchestrator's web search for the model and the degree-set relation found no proof; the search seat's exact-title arXiv search found only the source.
- The orchestrator's searches of issues, `Library/` and `Problems/` on `dev` found no prior repository record.

Except for the source TeX and abstract page, these are attributed preregistration readings, not independently reproduced literature searches.

`not-found-in-searched-scope`.

## Route

For a face $\tau$, let $L_C(\tau)=\{\rho\setminus\tau:\rho\in C,\ \tau\subseteq\rho\}$. Equivalently, its members are the sets $\alpha$ disjoint from $\tau$ with $\tau\cup\alpha\in C$. This residual family includes the empty face when $\tau\in C$, although $C$ itself contains only nonempty faces.

1. **Link evolution.** One growth step preserves $L=L_C(\tau)$ and adds $\{u_\alpha\}\cup\beta$ for every $\alpha\in L$ and $\beta\subseteq\alpha$, where $u_\alpha=v(s+1,\tau\cup\alpha)$. Freshness makes these new families disjoint from $L$ and from each other. Upper degree is the number of singleton members of the link.
2. **Weighted counting.** Put $B_f(r)=\sum_{j=0}^r\binom rj f(j)$, let $w_0(r)$ be $1$ when $r=1$ and $0$ otherwise, and define $w_{q+1}(r)=w_q(r)+\sum_{j=0}^r\binom rj w_q(j+1)$ and $g(t,r)=B_{w_t}(r)$. Counting subsets by cardinality gives this recurrence for weighted link sums.
3. **Birth types.** A face born at step $s+1$ has the form $\{v(s+1,\sigma)\}\cup\eta$ with $\eta\subseteq\sigma$. Its link at birth is the powerset of $\sigma\setminus\eta$. At generation $s+1+t$ its upper degree is $g(t,|\sigma|-|\eta|)$. The primordial vertex has degree $g(n,0)$ at generation $n$.
4. **Realized pairs.** Every generation-$s$ face has between $1$ and $s+1$ vertices, and every cardinality in that range occurs. Consequently, for $d\geq1$ and $n\geq d+1$, the distinct $d$-degrees are exactly $g(t,r)$ with $t,r\in\mathbb N$ and $t+r\leq n-d$. At generation $m$, the vertex degrees are $g(m,0)$ and the values $g(t,r)$ with $r\geq1$ and $t+r\leq m$.
5. **Comparison.** The recurrence gives $g(0,0)=0$ and $g(t+1,0)=g(t,1)$. Thus every pair with $r=0$ and positive age has a vertex-type representative with the same value and an admissible parameter sum. The remaining pair $(0,0)$ supplies zero. Conversely, the primordial vertex value and all other vertex types occur among the $d$-degree types when $m=n-d\geq1$.

## Falsifier

The proof would not answer the conjecture if the module used a different growth process or a different notion of degree. Its definitions:

- start with the single primordial vertex, grow every existing nonempty face at every step, and add all subsets containing its assigned new vertex;
- require distinct labels for distinct step-parent pairs and exclude the primordial vertex as a label;
- count containing faces with exactly one more vertex, matching the source's upper degree (TeX line 106);
- discard multiplicities, matching the lists of distinct values rather than the source's full degree arrays.

The empty subset in the growth rule produces a new singleton vertex; it does not insert the empty face into $C_s$. The empty member of a link must still be retained: omitting it would lose the parent $\sigma=\tau$ in link evolution and invalidate the comparison.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.lean` (459 lines).

- **Proof.** It proves `result : claim`. A scratch file importing the module successfully checked `claim`, `result` and the definitions `dsc`, `upperDegree` and `degreeSet`.
- **Axioms.** `#print axioms` on `result` reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. The source scan for those constructs returned no matches.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.lean.json`, statement `sha256:309ffca36007b8b500e220d54916df8a6ea40a4dabcd04d4d689d6e10a92b0ea`.

Declaration statements:

- `result`: `sha256:9fb38889c93066684fc2956b4b4dd7f2f8bdbb9f7d07a23c074ce425fa97c25c`;
- `claim`: `sha256:2bcac02ba9a4f53bba81f189e98df0c4773588747551b626e71e90ab0067b3df`.

## Triage

Tier 1 conjecture of a 2025 paper, based on degree lists from finite generations, preregistered in issue #20715 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every type $V$ with decidable equality, every $v_0\in V$ and every labeling $v:\mathbb N\to\operatorname{Finset}(V)\to V$ that is injective on step-parent pairs and never equals $v_0$, the families $C_n$ defined above satisfy $K^d(n)=\{0\}\cup K^0(n-d)$ for all natural $d\geq1$ and $n\geq d+1$.

**Computed, not formalized** (by hand from the definition):

- On the boundary $n=d\geq1$, both sides are $\{0\}$: the generation-$d$ complex has no face with $d+2$ vertices, so every face with $d+1$ vertices has upper degree $0$, and the single vertex of generation $0$ has degree $0$.
- At $(n,d)=(2,1)$, the two sets are $K^1(2)=\{0,1\}$ and $K^0(1)=\{1\}$, so dropping the adjoined zero changes this example. At $(n,d)=(1,0)$, the proposed extension would compare $\{1\}$ with $\{0,1\}$. At $(n,d)=(0,1)$, using natural subtraction would compare the empty set with $\{0\}$.

**Argued, not formalized.**

- *Decisive mechanism.* Dimension does not enter the link-growth operation. It enters only through the available birth types and their bound $t+r\leq n-d$. A link initially consisting only of the empty face becomes a one-vertex simplex in one step; this is the structural content of $g(t+1,0)=g(t,1)$. It represents every positive-age type with an empty residual by a vertex type, leaving only the newborn degree zero. No equality of the numbers of faces of each type is used.
- *Boundary and scope.* The range can be extended in ordinary mathematics to $n=d\geq1$: each step increases maximum face size by at most one, and adjoining a fresh vertex to a largest face realizes that increase. Thus there is a face of size $d+1$ at generation $d$ and no larger face, so every $d$-face there has degree zero. Also $K^0(0)=\{0\}$. This boundary extension is not stated by `result`. For $n<d$, there are no $d$-faces, whereas the right side with natural subtraction contains zero. Thus $n\geq d$ is the boundary for that extension. At $d=0,n=1$, $C_1$ consists of two vertices and their edge, so the two sides are $\{1\}$ and $\{0,1\}$. The single-vertex seed and unconstrained growth remain part of the settlement; arbitrary seeds and the source's constrained DSC models are not covered.
- *Stationary slices.* Fix $p\geq1$ and take $n\geq p+1$. Substituting $d=n-p$ gives $K^{n-p}(n)=\{0\}\cup K^0(p)$, independent of $n$. This supplies the general stationarity mechanism discussed in the source at TeX line 505 and Appendix A, lines 1901–1960. It reduces any such slice to one finite vertex-degree calculation; it does not independently certify every printed entry of the appendix.
- *Extremal degrees and effect on the paper.* Every vertex at generation $m\geq1$ lies on an edge: an earlier vertex receives an edge from its singleton parent, and a newborn vertex attaches to a nonempty parent. Hence all vertex degrees are positive, so adjoining zero preserves their maximum. When $m\geq2$, a vertex newly attached to a singleton has degree one, while the primordial vertex gains at least one distinct neighbor per step and has degree at least $m$; there are therefore at least two distinct positive degrees. Adjoining zero then also preserves the second-largest distinct value. With $m=n-d$, these arguments justify the source's dimension shifts for the largest degree for $d\geq1$, $n\geq d+1$, and for the second-largest distinct degree for $d\geq1$, $n\geq d+2$ (TeX lines 512–527). They supply the dimension-transfer step used in the extremal asymptotics at lines 594–608; the vertex estimates, including the conjectured largest-to-second-largest gap at lines 579–590, still require their own justification. These consequences are not additional statements of `result`.
- *Neighbouring questions.* Recovering multiplicities requires counting how often each birth type occurs and how many types share a value of $g$. Equality of degree sets supplies neither count. The degeneracy conjectures at TeX line 747 and Appendix A, lines 1962–1980, remain outside this settlement, as do the distributional and spectral claims and the constrained-model Laplacian recurrence conjecture at line 1574.

## ASSUMED-UNVERIFIED

The literature check is bounded and establishes no exhaustive worldwide novelty or priority. The OpenAlex citation count and citing-work reading, the reading of Krapivsky–Lucas (2026), arXiv:2608.26547, the web and exact-title arXiv searches, and the prior-`dev` repository searches are attributed to the authors of those readings in #20715 and were not independently reproduced. The independently fetched source was `DSC-7.tex` from arXiv:2507.07402v1, md5 `49162ddd2644bf0933cad90accf4238f`; its abstract page supplied the version listing and DOI. The publisher's typeset article was not compared with the arXiv source.

The statements grouped as "Computed, not formalized" and "Argued, not formalized" are not additional formal conclusions of `result`. In particular, the boundary extension, stationarity substitution, extremal-degree consequences, and their source correspondence are explained above but have no separate compiled conclusion here. The finite face counts reported by the search seat in #20715 are not used as evidence here. The source's generation-$8$ computations, full degree arrays, vertex asymptotic estimates and spectra were not reproduced. No multiplicity, distributional, asymptotic, arbitrary-seed or constrained-growth theorem is claimed by this settlement.
