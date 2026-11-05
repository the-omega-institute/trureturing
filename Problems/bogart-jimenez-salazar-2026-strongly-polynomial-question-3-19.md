---
slug: bogart-jimenez-salazar-2026-strongly-polynomial-question-3-19
bibkey: bogartjimenezsalazar2026twolevel
doi: 10.48550/arXiv.2609.32077
url: https://arxiv.org/abs/2609.32077v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.result
---

# Strongly polynomial graph families with constant depth

## Problem

Tristram Bogart and Santiago Jiménez-Salazar, *Strongly regular graphs, strongly polynomial sequences, and two-level polynomials*, arXiv:2609.32077v1, Question 3.19, p. 14:

> More dramatically, do there exist strongly polynomial families $G_q$, $H_n$ such that the depth function of $\hom(G_q,H_n)$ is constant while the degree function is a polynomial of positive degree?

The binding assertion in [#21296](https://github.com/the-omega-institute/trureturing/issues/21296) reads depth as maximal uniform integer constant depth. Definition 1.2 is downward closed in depth and does not select a pointwise greatest function. The assertion requires one integer $d\geq-1$ for which the coefficient condition holds at every nonnegative parameter, and excludes every larger integer constant. Pointwise greatest depth and maximality on every tail are separate assertions.

### Statement echo

All Lean names below belong to `D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom` unless an owner is stated.

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Definition 1.1: numerical on every integer | `Numerical` | Integer inputs and integer outputs, cast to rational numbers; negative inputs included. |
| Definition 1.2: eventually nonnegative degree and the set $S$ | `TwoLevel` | Numerical degree, eventual nonnegativity and guards $0\leq g(q)$. |
| Definition 1.2(a): degree and descending coefficients | `TwoLevel` | Nonzero $f_q$, degree $g(q)$, and polynomial coefficient functions; coefficients beyond the degree are zero. |
| Definition 1.2(b): extension outside $S$ | `TwoLevel`, `constantDepth` | Zero polynomial and depth $-1$ outside $S$. |
| Definition 3.2: every fixed finite graph and every natural parameter | `StronglyPolynomial` | Fin-labelled finite simple graphs and the existing `ThreeClassHomomorphismLimit.homCount`; all adjacency-preserving maps. |
| Question 3.19: existence of both graph families and their counting polynomials | `claim`, proved by `result` | Independent strong polynomiality of both families and equality for every $q,n\in\mathbb N$. |
| Positive degree and constant depth | `claim` | Positive natural degree of $g$, a finite integer depth at least $-1$, and failure of every larger uniform integer depth. |

The finiteness encoding by `Fin` is a labelling choice; no injectivity, connectivity or positive-parameter assumption is added. Rational polynomial coefficients suffice for polynomial integer-count functions. The eventual-nonnegative and guarded coefficient bodies are inlined literally, without duplicate aliases; `Polynomial.reverse` is used inside the private proof through `reverse_coeff`.

## Motivation

The question separates the growth of the degree of a homomorphism polynomial from the number of its leading coefficients that vary polynomially with the source parameter. An explicit pair with degree $q+5$ and maximal uniform depth $1$ gives this separation for unbounded parameters.

## Gap

The literature screen recorded in #21296 inspected the source v1, native arXiv full-text and author searches, MathOverflow, and the accessible citation records. It found no settlement in that scope. The predecessor arXiv:2507.05473v3 has growing finite depths in the inspected graph sections. Goodall–Nešetřil–Ossona de Mendez, arXiv:1405.2449, supplies the standard polynomial vertex-blow-up ingredient, rather than the fixed-codegree obstruction here.

Literature completeness is **ASSUMED-UNVERIFIED**. OpenAlex citation and broader author queries were rate-limited; the 1995 de la Harpe–Jaeger paper was not read in full; no MathDB candidate or per-solution reading was established. An empty returned citation list does not exclude unindexed or later work. The pair and its obstruction are suspected-novel within the searched scope; the general strong-polynomiality ingredient is literature-attested.

## Route

Set $m=q+3$, $G_q=K_{m,2}$ and $H_n=K_{1,n,n}$. For the two vertices in the size-two source part, fix their ordered images $u,v$ in $H_n$. Each of the other $m$ vertices independently chooses a common neighbour. The private theorem `bipartite_common_neighbours` makes this correspondence for every finite target graph and every $m\in\mathbb N$.

The three target parts have sizes $1,n,n$. Ordered pairs in the singleton part contribute $(2n)^m$; pairs within either large part contribute $2n^2(n+1)^m$; pairs meeting the singleton and a large part contribute $4n^{m+1}$; and pairs in the two different large parts contribute $2n^2$. Thus `exact_count` gives

$$\hom(K_{m,2},K_{1,n,n})=2n^2(n+1)^m+4n^{m+1}+2^mn^m+2n^2.$$

For $m=q+3$, `f_degree` gives degree $q+5$, and `f_codegrees` gives leading codegree coefficients

$$c_0(q)=2,\qquad c_1(q)=2q+10,\qquad c_2(q)=(q+3)(q+2)+2^{q+3}.$$

The first two coefficient functions give depth one. Any larger constant depth would make $c_2$ polynomial. Subtracting $(q+3)(q+2)$ would give a polynomial equal to $2^{q+3}$ on all naturals. Its sufficiently high forward difference vanishes, whereas every iterated forward difference of this exponential equals the exponential. The private theorem `exponential_not_polynomial` uses `Polynomial.fwdDiff_iter_degree_add_one_eq_zero` for the contradiction; `no_larger_depth` applies it to the coefficient condition.

For a fixed finite source graph, a map into a multipartite target determines a proper colouring by target part. `target_colour_sum` partitions maps by that colouring, and `multipartite_polynomial` sums products of polynomial part sizes over the fixed finite set of proper colourings. `source_polynomial` and `target_polynomial` apply this to the two families. The argument includes the empty source and zero parameters.

## Falsifier

The claim would not faithfully represent the binding question if depth were read as a pointwise greatest function, homomorphisms were required to be injective, negative integer inputs were omitted from numericality, or the coefficient beyond the degree lacked its zero guard. The definitions retain these distinctions. A finite computation alone would not establish either unbounded strong polynomiality or the exponential obstruction.

## Evidence

Canonical source: `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.lean`; the sole public theorem is `result : claim`. The supporting theorems are private and consumed. The admission basis is `open-problem-resolution (#21296; Proved)`; the conservative proof-shape classification is bind-only, without a separate escape-witness claim. The module has `utility: none`: the deliverable is an unbounded existence statement and symbolic identities, rather than a finite numerical certificate.

The four-slot escape audit of `result` is unfinished in [#21427](https://github.com/the-omega-institute/trureturing/issues/21427). The existential and dependent-family enrollments do not by themselves supply a faithful reconstruction bridge, complete occurrence ties, whole-family variation and sensitivity, or actual observational dependence for the dependent graph and polynomial operands. No validated registration is claimed.

### Independent finite computation

Experiment: [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/8c0c2a7aedd50a6cb26a93acf5640fb2c8f876ab/docs/reports/bogart-jimenez-salazar-2026-strongly-polynomial-question-3-19), script `check.py`, SHA-256 `39c7624d5e37cb57b49922429df5a076c420dd2fcace3e80496a3a72b62c3ec2`. The command `python3 /Users/auric/.sshx/af6779990bbd52288a30230f/attempt-1/experiment-check.py`, applied to the exact script extracted from that commit, exits 0 with `ALL_CHECKS_OK`.

The readings are 30 fidelity cases ($0\leq q\leq5$, $0\leq n\leq4$), 9 full-map construction cases ($3\leq m\leq5$, $0\leq n\leq2$), 42 common-neighbour cases ($3\leq m\leq8$, $0\leq n\leq6$), and 608 colouring comparisons for all 76 labelled simple graphs on at most four vertices and parameters $0,1,2,3$ in both families. Coefficients are checked for $q=0,\ldots,30$, and residual forward differences through order 10. These are finite computations, independent of the universal proofs.

## Triage

Tier 1; resolution **Proved** under the preregistered maximal-uniform-depth interpretation. There is no digestion atom.

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Unchanged maximal-uniform-depth assertion | Proved, kernel-checked | `result`: $G_q=K_{q+3,2}$, $H_n=K_{1,n,n}$, degree $q+5$, depth $1$. |
| Exact homomorphism identity | Proved, kernel-checked | Private `exact_count`, for every natural $m,n$, including $m=0$ and $n=0$. |
| First three codegree coefficients | Proved, kernel-checked | Private `f_codegrees`: $2$, $2q+10$, $(q+3)(q+2)+2^{q+3}$. The singleton-part contribution explains the exponential in the four-case count above. |
| Strong polynomiality and degenerate parameters | Proved, kernel-checked | Private `multipartite_polynomial`, `source_polynomial`, `target_polynomial`; all finite source graphs, including the empty graph, and all natural parameters. |
| Common-neighbour correspondence beyond this target | Proved, kernel-checked | Private `bipartite_common_neighbours`, for every finite target graph and every natural $m$. |
| Independent checker | Computed | The exact script, command, exit code, SHA-256 and finite ranges are in the experiment entry above: 30, 9, 42 and 608 cases, $q=0,\ldots,30$, differences through order 10. |
| Separate formal settlement of Question 3.18 | Open | No separate Lean statement is delivered. Under the same depth interpretation, the mathematical implication uses $\deg(1)=0<1=\deg(q+5)$; this is a prose consequence. |
| Every-tail maximality, prescribed constant depths and connectedness | Open | No separate proved declarations for these assertions are delivered. |

The decisive separation is a fixed codegree containing an exponential in the source parameter, with polynomial coefficients above it. The common-neighbour correspondence extends to arbitrary finite targets, and the proper-colouring sum extends to polynomial multipartite sizes under its stated hypotheses. Arbitrary prescribed depths and a uniform every-tail theorem are additional questions. No revision of the source's other proved results is asserted; the separate Question 3.18 formulation remains outside the delivered Lean surface.

## ASSUMED-UNVERIFIED

Literature completeness and absence of an unindexed settlement remain **ASSUMED-UNVERIFIED**, with the coverage gaps listed above. The selected maximal-uniform-depth reading is the explicit preregistered interpretation, not a theorem that the source defines a unique pointwise greatest depth. The finite checker does not certify any range beyond its stated bounds. The unfinished escape registration is tracked by #21427 and does not supply a validated four-slot audit.
