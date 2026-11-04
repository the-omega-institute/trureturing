---
slug: brask-chaves-2017-outcome-communication-chained-inequality
bibkey: braskchaves2017bellcommunication
doi: 10.1088/1751-8121/aa5840
url: https://arxiv.org/abs/1607.08182v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.result
---

# The relabelled chained inequality holds for every odd-input binary COD model

## Problem

J. B. Brask and R. Chaves, *Bell scenarios with communication*, J. Phys. A: Math. Theor. 50(9), 094001 (2017), arXiv:1607.08182v1, subsection “Generalization to more inputs”, conjecture following Eq. (25). The source member `Bell_comm_arXiv_v1.tex`, line 325, states verbatim:

> For the inequality to hold for the COD model, Alice's outputs must be relabelled for every second input. That is $a=0 \leftrightarrow a=1$ for even $x$. With this relabelling, we conjecture that \eqref{eq.validchained} holds for any odd number of inputs.

The source label `eq.validchained` denotes Eq. (25), at TeX lines 318–324:

$$[a_1-b_1]+[b_1-a_2]+[a_2-b_2]+\cdots+[a_n-b_n]+[b_n-a_1-1]\geq1.$$

At line 325, the bracket is defined by $[a_x-b_y]=\sum_{j=0}^1j\,p(a-b=j\bmod2\mid x,y)$. For binary outputs, the ordinary brackets are unequal-output probabilities and the closing bracket is an equal-output probability.

Issue [#24183](https://github.com/the-omega-institute/trureturing/issues/24183) fixes the finite hidden-variable reading of the source's causal outcome-dependent (COD) model, Eq. (7), TeX lines 150–155:

$$p(a,b\mid x,y)=\sum_{\lambda\in\Lambda}w_\lambda A_x(a\mid\lambda)B_y(b\mid a,\lambda),$$

where $\Lambda$ is finite, $w_\lambda\geq0$, $\sum_\lambda w_\lambda=1$, and both response functions are nonnegative and normalized over their binary output, including Bob's normalization for each raw Alice output. Let $r_x=1$ for even one-based inputs $x$, and $r_x=0$ otherwise. The inequality reads Alice's relabelled output $c=a\oplus r_x$, while Bob receives the raw $a$. Writing $q(c,b\mid x,y)=p(c\oplus r_x,b\mid x,y)$, the statement is

$$\sum_{i=1}^nq(c\ne b\mid i,i)+\sum_{i=1}^{n-1}q(c\ne b\mid i+1,i)+q(c=b\mid1,n)\geq1$$

for every odd natural $n$ and every such model. This is proved by `result : claim`. The definitions and source locator are also in [the literature note](../Library/Observer/braskchaves2017bellcommunication.md).

## Motivation

The inequality constrains classical explanations that allow Alice's outcome to influence Bob's outcome. For odd $n$, a distribution with chained value below one cannot have the specified finite COD factorization. An inequality valid at every odd input count supplies a family of such tests without enumerating a new causal polytope at each size. The distinction between the communicated raw output and the relabelled output read by the inequality is essential to this question.

## Gap

The bounded literature check recorded in #24183 reports:

- Crossref lists 30 citations and OpenAlex `W2489719182` lists 34;
- the preregistration's search seat found 29 distinct citing works through OpenCitations and read 27 citing arXiv full texts;
- the closest works identified there, arXiv:1804.04119, 2112.11223, 2510.12886 and 2603.08610, concern other inequalities or models;
- the orchestrator's web search for the paper, chained inequalities, COD models and odd inputs found no settlement.

`not-found-in-searched-scope`.

## Route

All input indices in the following Lean lemmas are zero-based elements of $\mathrm{Fin}\,n$; input $x$ corresponds to source input $x.\mathrm{val}+1$.

1. **Deterministic tables.** For every natural $n$, every $f:\mathrm{Fin}\,n\to\mathrm{Fin}\,2$ and every $g:\mathrm{Fin}\,n\times\mathrm{Fin}\,2\to\mathrm{Fin}\,2$, `deterministic_value` expresses the chained value of `deterministicBehaviour f g` as a sum of zero-or-one event indicators. For $x,y:\mathrm{Fin}\,n$ with $x.\mathrm{val}=y.\mathrm{val}+1$ and any $a:\mathrm{Fin}\,2$, `relabel_adjacent` says the two relabellings of that same raw bit differ. Under the additional hypothesis $\mathrm{Odd}\,n$, `deterministic_bound` proves the value is at least one: a value below one forces every indicator to vanish, so consecutive raw outputs must differ. Binary alternation and odd $n$ make the endpoint raw outputs equal; both endpoint relabellings are the identity. The last diagonal condition then contradicts the vanishing closing indicator. These are the hypotheses of `deterministic_bound`; there is no requirement that $n\geq3$.
2. **Stochastic decomposition.** For any natural $n$, a finite hidden-variable type, and response data satisfying `IsCODModel`, `tableWeight_nonneg`, `tableWeight_sum` and `decomposition` give nonnegative deterministic-table weights summing to one and reproducing `codBehaviour`. For a table $(f,g)$ the weight is
   $$W(f,g)=\sum_{\lambda\in\Lambda}w_\lambda\prod_x A_x(f(x)\mid\lambda)\prod_{(y,a)}B_y(g(y,a)\mid a,\lambda).$$
   The normalization step `response_marginal` assumes a finite decidable index type $\iota$, real binary response entries $P_i(a)$, and $\sum_aP_i(a)=1$ for every $i$; its identity does not require nonnegativity. Nonnegativity of the mixture weights uses the full `IsCODModel` hypotheses.
3. **Linearity.** For any natural $n$, any finite mixture index type, arbitrary real coefficients and arbitrary real-valued behaviour arrays, `chained_mixture` identifies the chained value of their weighted sum with the weighted sum of their chained values. Applying it to the preceding normalized nonnegative weights, and applying `deterministic_bound` with $\mathrm{Odd}\,n$ to each table, gives `result`.

## Falsifier

The proof would not settle the registered statement if the factorization, relabelling or closing event differed from the source. The Lean definitions fix each correspondence:

- `IsCODModel` imposes nonnegative normalized hidden weights and normalized binary responses, with Bob conditioned on the raw Alice output; `codBehaviour` is their finite sum of products.
- `relabel x a` leaves $a$ unchanged when $x.\mathrm{val}\bmod2=0$ and reverses it otherwise, exactly the flip on even one-based inputs. It is involutive by `relabel_involutive` for every natural $n$, $x:\mathrm{Fin}\,n$ and $a:\mathrm{Fin}\,2$, so evaluating $p$ at `relabel x c` implements the stated $q$.
- `chainedValue` uses unequal-output events on the diagonal and consecutive off-diagonal pairs, and an equal-output event on the closing pair. It imposes no no-signalling premise.
- `claim` quantifies over every odd natural $n$ and every finite hidden-variable type; it includes stochastic responses and zero hidden weights. It makes no claim about even $n$, larger output alphabets, other symmetries, quantum violations or mixtures of the two causal directions.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.lean.json`.

Declaration statements:

- `result`: `sha256:223bde8fadaaba19ca1af0573e51ca8af25013d6561f15a7cb736474c02ab481`;
- `claim`: `sha256:f806f8db62c155be567292aeeb55f73225633ff1bd4fd76f3e3d16858d55e01e`.

## Triage

Tier 1 conjecture of a 2017 paper, preregistered in issue #24183 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every odd natural $n$, every finite hidden-variable type, and all nonnegative normalized hidden weights and binary response functions satisfying `IsCODModel`, the `chainedValue` of `codBehaviour` is at least one, with Alice's every-second-input relabelling used only in the inequality and Bob conditioned on her raw output.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Decisive mechanism.* For odd $n$ and binary deterministic tables, the contradiction inside `deterministic_bound` arises from demanding that the same Bob response to the same raw bit equal two different relabelled bits at consecutive inputs. Vanishing diagonal and consecutive indicators force raw alternation; odd $n$ then makes the endpoint requirements incompatible with a vanishing closing indicator. The stochastic part adds no escape from this contradiction because the weights are nonnegative and sum to one under `IsCODModel`, as `tableWeight_nonneg`, `tableWeight_sum` and `decomposition` establish for finite hidden-variable types and arbitrary $n$.
- *Sharpness.* For every odd $n$, take a single hidden value with weight one, deterministic raw outputs $a_i=r_i$, and Bob's output constantly zero. The displayed Alice output is then constantly zero. Every unequal-output term is zero and the closing equal-output term is one, so the lower bound is attained. These deterministic responses satisfy every normalization and nonnegativity condition.
- *Why oddness matters.* For every positive even $n$, use the same deterministic Alice outputs, let Bob output zero for $y<n$, and let him output $1-a$ for $y=n$. Every displayed Alice output is zero. All diagonal and consecutive terms vanish, including the last diagonal because $a_n=1$; the closing equality event also vanishes because $a_1=0$ and Bob's last response is one. Thus this particular relabelled expression has value zero. This construction concerns the specified symmetry, not every symmetry of the chained inequality.
- *Neighbouring questions.* The binary step that two consecutive changes restore the original raw value does not extend to larger output alphabets. The more-output question explicitly raised at TeX line 327, arbitrary hidden-variable probability spaces, mixtures of the two causal directions, and classification of other symmetries are not settled by the module.
- *Effect on the paper.* At TeX line 325 Brask and Chaves infer that COD models cannot reproduce certain quantum correlations from quantum violation of this family. For every odd $n\geq3$, the settlement supplies the classical-validity part of that inference for the finite $A\to B$ model: a distribution with chained value below one cannot admit this factorization, since `result` would force the opposite bound. The existence and size of quantum violations remain a separate premise, not a conclusion of this formalization. The paper's other results concerning input or message communication and its separate more-output constructions are not consequences of this conjecture.

## ASSUMED-UNVERIFIED

The bounded literature check in #24183 does not establish exhaustive worldwide novelty or priority. Its citation-service counts, 27 citing-full-text readings, comparison with the four later arXiv works, and web-search results were not independently reproduced here. The source conjecture, COD factorization, bracket definition and relabelling were checked in `Bell_comm_arXiv_v1.tex` from arXiv:1607.08182v1, md5 `e207a0023fa9c95a83583eef1d7d0158`.

The computations and arguments under their labelled groups are not additional Lean theorems. In particular, sharpness and the all-even-input construction are not stated by `result`. Quantum realizations, their physical interpretation, nonbinary outputs, arbitrary hidden-variable probability spaces, reverse-direction mixtures and other symmetries are outside the formalized claim. The source's vertex-enumeration results were not reproduced at its full reported input range.
