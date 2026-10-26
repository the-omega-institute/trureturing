---
slug: bavaresco-murao-quintino-2022-classical-permutation-sequential-advantage
bibkey: bavarescomuraoquintino2022unitarydiscrimination
doi: 10.1063/5.0075919
url: https://arxiv.org/abs/2105.13369v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.result
---

# Classical permutations admit a strict two-query sequential advantage

## Problem

J. Bavaresco, M. Murao and M. T. Quintino, *Unitary channel discrimination beyond group structures: Advantages of sequential and indefinite-causal-order strategies* (Journal of Mathematical Physics 63, 042203, 2022; arXiv:2105.13369v3), ask in the Conclusion, `main.tex`, line 514:

> Assuming the analog of a unitary channel in classical information theory to be a classical channel that maps deterministic probability distributions into deterministic probability distributions, i.e., channels that can be described by a permutation matrix, it would be interesting to investigate whether their discrimination could also be enhanced by sequential strategies.

The quotation is from the v3 TeX source (`main.tex`, md5 `7b7f57add94cbe20dcb088bf7c16f071`); see also [the literature note](../Library/Entropy/bavarescomuraoquintino2022unitarydiscrimination.md).

Issue [#22253](https://github.com/the-omega-institute/trureturing/issues/22253) fixes the existential reading: there are a finite alphabet, a finite permutation ensemble with a probability vector, and a two-use sequential strategy whose average success exceeds a real number $c$ bounding every two-use parallel strategy. Both strategies query the same unknown permutation twice. This is proved.

## Motivation

The question separates the benefit of adapting a later query to an earlier answer from the quantum features of the source's discrimination tasks. A positive answer for permutation channels exhibits that benefit even for reversible deterministic classical dynamics. The comparison must include randomized parallel inputs and decoders, rather than only a selection of deterministic strategies.

## Gap

The bounded literature check recorded in #22253 reports no settlement among the relevant citing texts, selected author follow-ups and classical-discrimination papers, or in MathDB and formal-conjectures. The cited-text scope includes arXiv:2411.08110, 2307.10285, 2109.08202, 2501.09312, 2412.13067, 2602.09655 and 2510.15506; the additional papers listed are arXiv:2011.08300, 2609.40218, 2303.02016 and 2504.12989. The v3 source retains the question.

`not-found-in-searched-scope`.

## Route

Use the uniform prior on four permutations of $X=\{0,\ldots,5\}$: $\pi_0=\mathrm{id}$, $\pi_1=(2\;3)$, $\pi_2=(0\;1)$ and $\pi_3=(0\;1)(4\;5)$, as defined by `channels`.

1. **Adaptive identification.** For this ensemble and uniform prior, `sequential_perfect` states that the strategy with first input $0$, second-input rule `secondInput`, and decision rule `decoder` has `sequentialSuccess` equal to $1$. The second input is $2$ when the first output is $0$, and $4$ otherwise. When the first output is $0$, the decoder guesses $0$ if the second output is $2$, and $1$ otherwise; when the first output is not $0$, it guesses $2$ if the second output is $4$, and $3$ otherwise.
2. **A collision at every fixed pair.** For every ordered input pair $x\in X^2$, including repeated inputs, `transcript_collision` states that the output pairs of labels $0,1$ coincide, or those of $0,2$ coincide, or those of $2,3$ coincide. Two input symbols cannot meet all three disjoint blocks $\{0,1\}$, $\{2,3\}$ and $\{4,5\}$. Omitting these blocks gives the collisions $0,2$, $0,1$ and $2,3$, respectively.
3. **Arbitrary randomized decoding.** For every natural number $m$, probability vector $d$ on $\mathrm{Fin}\,m$, and distinct $a,b\in\mathrm{Fin}\,m$, `two_weights_le_one` gives $d(a)+d(b)\le1$. For this four-permutation ensemble, every decoder $\delta:X^2\to X^2\to\operatorname{StdSimplex}(\mathbb R,\mathrm{Fin}\,4)$ and every $x\in X^2$, `fixed_input_bound` gives $\sum_{i=0}^3\delta(x,(\pi_i(x_1),\pi_i(x_2)))(i)\le3$: a colliding pair shares one decision distribution, while each remaining label contributes at most $1$.
4. **Arbitrary randomized parallel inputs.** With this ensemble and uniform prior, `parallel_bound` gives `parallelSuccess` at most $3/4$ for every probability vector $q$ on $X^2$ and every decoder of the preceding type. It averages the fixed-pair bound using the nonnegative weights of $q$, whose sum is $1$. The theorem `result : claim` supplies these strategies and $c=3/4$, using `sequential_perfect` and $3/4<1$.

## Falsifier

The settlement would not answer the question if its strategy classes excluded classical randomness or allowed the sequential strategy a different unknown channel. The module uses:

- `Convexity.StdSimplex` over $\mathbb R$, whose weights are nonnegative and sum to $1$;
- permutations $\pi_i:\mathrm{Fin}\,n\simeq\mathrm{Fin}\,n$, with the same label $i$ in both channel uses;
- `parallelSuccess`, which sums $p_iq(x_1,x_2)d_{(x_1,x_2),(\pi_i(x_1),\pi_i(x_2))}(i)$ over labels and ordered input pairs, with arbitrary input distribution $q$ and decision distribution $d$;
- `sequentialSuccess`, which sums $p_iq_1(x_1)q_2(x_1,\pi_i(x_1))(x_2)\delta(x_1,\pi_i(x_1),x_2,\pi_i(x_2))(i)$ over labels and both inputs, with arbitrary probability vectors at each conditional choice.

The decoder sees the inputs as well as the outputs. The model concerns classical symbol queries and stochastic decisions; coherent quantum access to permutation unitaries is outside its strategy classes. The conclusion is existence of an advantage, not an advantage for every permutation ensemble.

## Evidence

The canonical source is `D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage.lean.json`.

Declaration statements:

- `result`: `sha256:467563065d0417fc5ab18fa575c5fcd9ba2bf6a1c97d69198a3acd8630e378eb`;
- `claim`: `sha256:2f22790a7737ad899abf92d5db2cc1d043d6aa339cbb92e08046175acc8af719`.

## Triage

Tier 1: an explicit open question in the conclusion of a 2022 journal article, preregistered in issue #22253 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** there are natural numbers $n,m$, a probability vector on $m$ labels, a family of permutations of $\mathrm{Fin}\,n$, a two-use sequential strategy, and a real number $c$, such that every parallel input distribution and every parallel decoder have average success at most $c$, while the chosen sequential strategy has average success strictly greater than $c$.

**Computed, not formalized** (exact enumeration):

- For the designated four-permutation ensemble on six symbols, evaluation of all $36$ ordered input pairs gives maximal fixed-pair uniform-prior success $3/4$.
- The specified adaptive rule returns the correct label for all four permutations.

**Argued, not formalized.**

- *Mechanism.* For the designated ensemble with uniform prior, `sequential_perfect` certifies the specified adaptive rule. Its second query probes the block selected by the first answer. By contrast, `transcript_collision` gives one of the three listed collisions for every ordered pair of the six symbols. The separation comes from adapting the location of the second query, even though every channel is deterministic and invertible.
- *Sharpness for this ensemble.* Querying $(0,2)$ gives distinct transcripts for label $0$, label $1$, and the pair of labels $2,3$. Guessing $0$, $1$ and $2$ on those three transcripts succeeds on three of the four equally likely labels, attaining $3/4$. Together with `parallel_bound`, whose hypotheses are the designated ensemble, uniform prior, an arbitrary probability vector on $X^2$ and an arbitrary parallel decoder, this makes the parallel bound exact. Attainment is not a declaration of the module. Likewise, any sequential success is at most $1$, since it averages decision probabilities bounded by $1$ with normalized conditional input distributions and a normalized prior; `sequential_perfect` attains this limit for the designated ensemble, uniform prior and specified strategy.
- *Strictly positive priors.* Keep the same four permutations and assume every prior weight $p_i$ is strictly positive. Set $r=\min_i p_i>0$. For every $x\in X^2$, `transcript_collision` for this four-permutation ensemble supplies distinct labels $a,b$ with identical outputs. For any parallel decoder, its common decision distribution on the four labels satisfies $d(a)+d(b)\le1$ by `two_weights_le_one`, applied to these distinct labels. Their combined correctly guessed prior mass is therefore at most $\max(p_a,p_b)$. The other two labels contribute at most their prior masses. Thus fixed-pair success is at most $1-\min(p_a,p_b)\le1-r$, and averaging preserves this bound. The same adaptive rule identifies every label and has success $1$. Positivity cannot simply be omitted from this argument: if only labels $0,1,2$ have positive weight, the pair $(0,2)$ already distinguishes that support perfectly.
- *Larger alphabets.* Adjoin any finite number of symbols fixed by all four permutations. Each input pair still misses one of the three original blocks, so the same collision argument and uniform-prior $3/4$ bound apply, while the adaptive rule using $0,2,4$ still identifies every label. This extension is not formalized. The smallest alphabet and smallest number of labels permitting a strict two-use advantage are not determined here.
- *Effect on the source.* The question in Bavaresco, Murao and Quintino (2022), arXiv:2105.13369v3, Conclusion, line 514, is posed as future work rather than a hypothesis for the paper's earlier theorems. The settlement supplies the requested positive classical example. It leaves the separate questions about scaling gaps with the number of uses and about indefinite causality as a resource for classical channel discrimination unresolved.

## ASSUMED-UNVERIFIED

The bounded literature check in #22253 does not establish exhaustive worldwide novelty or priority. Its citing-paper readings, author-follow-up readings, classical-discrimination readings, citation-database queries, MathDB search and formal-conjectures search were not independently reproduced. The journal text was not compared line by line with arXiv v3; the source quotation was checked against the v3 TeX.

The computations and arguments in the corresponding labelled groups are not formalized. In particular, exact optimality, robustness under strictly positive nonuniform priors, and extension by fixed symbols go beyond the type of `result`. The interpretation of the conditional distributions as covering arbitrary classical private randomness and memory is not a Lean equivalence theorem. No claim about quantum coherent strategies, classical indefinite-causal-order strategies, minimal alphabet size or minimal ensemble size is formalized here.
