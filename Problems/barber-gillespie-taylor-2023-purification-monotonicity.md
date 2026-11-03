---
slug: barber-gillespie-taylor-2023-purification-monotonicity
bibkey: barbergillespietaylor2023purification
doi: 10.22331/q-2023-05-04-994
url: https://arxiv.org/abs/2209.05391v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.result
---

# Tight purification circuits need not have monotone output error

## Problem

B. Barber, N. I. Gillespie and J. M. Taylor, *Post-selection-free preparation of high-quality physical qubits*, Quantum 7, 994 (2023), arXiv:2209.05391v3, Section 3.2, PDF page 20 (`purification.tex`, lines 859–862), ask:

> We conjecture that it should be possible to prove monotonicity under some reasonable set of conditions. For instance, suppose that $\big|\binom n 0 + \cdots + \binom n e\big| = 2^{n-k}$ and $p_0 < 0.5$. Is $p_{\text{out}}(p_0,p_I,p_C,p_T)$ an increasing function of $p_0$, $p_I$, $p_C$ and $p_T$? We leave this as an open question.

Their $(n,k,e)$ purification circuit consists of CNOT and Toffoli gates and sends every input bitstring of Hamming weight at most $e$ to a bitstring zero in $k$ nominated output positions (Section 2, line 203). Each input bit independently starts at one with probability $p_0$. Each idle qubit depolarises independently with probability $p_I$, and each CNOT or Toffoli independently depolarises its entire support with probability $p_C$ or $p_T$. Depolarisation replaces that support by uniformly random bits (Section 2.1, lines 219–243). The quantity $p_{\text{out}}$ is the expected number of erroneous output bits divided by $k$ (lines 711–713).

Issue [#22506](https://github.com/the-omega-institute/trureturing/issues/22506) fixes the nondecreasing reading: for all natural $n,k,e$ with $1\le k\le n$ and $1\le e\le n$, every gate list executed one gate per round, and every set of exactly $k$ outputs, purification through weight $e$ together with $\sum_{j=0}^{e}\binom nj=2^{n-k}$ implies separate nondecreasing dependence on each noise coordinate. Both parameter vectors must lie in $0\le p_0<1/2$, $0\le p_I,p_C,p_T\le1$, and the other three coordinates are held fixed in each comparison. This is `claim`. Its refutation already occurs in the preparation coordinate. One gate per round is an allowed subclass of the source's scheduled circuits.

The definitions and source locators are also in [the literature note](../Library/Hamming/barbergillespietaylor2023purification.md).

## Motivation

The source uses purification circuits to improve preparation quality without post-selection. Its tight space bound describes an ideal permutation that assigns the most probable preparation patterns to clean outputs when $p_0<1/2$ (Section 2.2, line 275). Monotonicity would justify comparing output quality at different noise rates for a fixed circuit and would support reasoning about improvement regions as error rates vary. The question tests whether tightness alone supplies that extra structure.

## Gap

The bounded literature check in #22506 records:

- the monotonicity question in arXiv:2209.05391v3;
- the orchestrator's web and Zenodo searches, which found no settlement, and its repository search, which found no existing record of the source;
- the search seat's report that arXiv:2210.06212 and arXiv:2402.12361 do not settle the question and that formal-conjectures has no match; MathDB returned HTTP 403.

`not-found-in-searched-scope`. These reported searches do not establish exhaustive novelty or priority.

## Route

1. **A tight purification witness.** Take $n=3$, $k=e=1$, output set $\{0\}$, and the ordered gates $\mathrm{CNOT}(0\to1)$, $\mathrm{CNOT}(1\to2)$, $\mathrm{CNOT}(1\to0)$, $\mathrm{CNOT}(0\to2)$, $\mathrm{CNOT}(1\to0)$, $\mathrm{Toffoli}(1,2\to0)$. The private lemma `witness_purification` establishes `IsPurification` for exactly this circuit, output set and error bound. Its eight input cases use `weight_ge_two`: for any bitstring and two distinct indices whose bits are both true, its Hamming distance from the all-false string is at least two. Thus only the zero-weight and three weight-one inputs need ideal gate evaluation. The private lemma `witness_space` gives $\binom30+\binom31=4=2^{3-1}$.
2. **Exact noisy values.** With $p_I=p_T=0$ and $p_C=1/4$, `witness_evaluation_zero` gives $p_{\text{out}}(0,0,1/4,0)=1481/4096$ for this witness, and `witness_evaluation_small` gives $p_{\text{out}}(1/100,0,1/4,0)=23121347/64000000$. The reductions use `depolarize_zero`, which is an identity for any support and any real-valued distribution at depolarisation probability zero, and `idle_zero`, which is an identity for any list of idle qubits and any real-valued distribution at idle probability zero. The private lemma `state_univ_three` supplies the complete eight-state sum on three qubits.
3. **Contradiction.** `result` applies the first conjunct of `claim` using the witness's purification, tightness, output cardinality and the bounds $1\le k\le n$, $1\le e\le n$. Both $(0,0,1/4,0)$ and $(1/100,0,1/4,0)$ are admissible; their last three coordinates agree and $0\le1/100$. The asserted inequality contradicts the exact values, whose decrease is $9639/32000000>0$. Thus `result : ¬ claim`.

## Falsifier

The refutation would not answer the source's question if the formal circuit or noise semantics differed from the source's. `Gate` requires distinct CNOT control and target, and pairwise distinct Toffoli controls and target. `IsPurification` uses the ideal gates in list order. `pOut` starts with independent Bernoulli preparation masses and, in each round, applies the ideal permutation, depolarises the gate's support, and independently depolarises each remaining qubit. It averages over exactly the nominated outputs. In `claim`, their cardinality is positive.

The gate depolarisation probability is the probability of replacing the whole support by uniform bits, rather than a separate failure probability for each qubit. The witness uses exactly this convention. Neither the source question nor `claim` imposes minimal circuit length or a relation between CNOT and Toffoli error probabilities. The witness has $p_T=0$ and $p_C=1/4$. A strict decrease refutes even weak monotonicity, and therefore also the stronger increasing reading.

## Evidence

The canonical source is `D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:ebb601b80377dc19e74410d848281d7b9e69d9dcc74936eb7a36e9cdd6f9a99f`;
- `claim`: `sha256:9ad9122944a6bdf9fbb62cc4be4db98303fc3f26016d56304084c859a62644cd`.

## Triage

Tier 1 open question of a 2023 paper, preregistered in issue #22506 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that every one-gate-per-round CNOT/Toffoli circuit with $1\le k\le n$, $1\le e\le n$, exactly $k$ nominated outputs, ideal purification through weight $e$ and $\sum_{j=0}^{e}\binom nj=2^{n-k}$ has output error nondecreasing separately in all four coordinates throughout $0\le p_0<1/2$, $0\le p_I,p_C,p_T\le1$, holding the other three coordinates fixed in each comparison.

**Computed, not formalized** (exact calculations for this dossier):

- Evaluating all eight three-bit inputs gives the same ideal permutation for the six-gate witness and the source's three-gate $(3,1,1)$ circuit at lines 705–709.
- For the witness at $p_I=p_T=0$, $p_C=1/4$, the mean conditional output-error probability over inputs with exactly one preparation error is smaller than the conditional output-error probability of the error-free input.
- Exact symbolic propagation for the witness at $p_I=p_T=0$ gives $\partial_{p_0}p_{\text{out}}(0,0,p_C,0)<0$ throughout $0<p_C<1$.
- Exact rational propagation for the witness at $p_I=p_T=0$, $p_C=1/1000$ gives a strict decrease between $p_0=0$ and $p_0=1/10000$.

**Argued, not formalized.**

- *Mechanism.* Fix the gate and idle noise, and let $r(x)$ be the conditional average output error for initial bitstring $x$. Independent preparation gives derivative $\sum_{i=0}^{n-1}r(e_i)-nr(0)$ at $p_0=0$: the zero-error input loses probability at rate $n$, each singleton error gains it at rate one, and all higher-weight inputs have zero first derivative there. The computed singleton average is below $r(0)$ for the witness, so introducing a small preparation error can compensate for the noisy computation. Tightness constrains the ideal map; it does not impose the needed order on this conditional noisy response. The identical ideal permutations above therefore do not imply identical noisy behaviour.
- *A sufficient additional structure.* If, for fixed gate and idle noise, $r(x)\le r(y)$ whenever every bit of $x$ is at most the corresponding bit of $y$, then preparation monotonicity follows. Couple preparation at rates $p\le q$ using the same independent uniform random number for each bit; every prepared bit at rate $p$ is at most its counterpart at rate $q$. Applying the assumed inequality pointwise and averaging gives the required output comparison. Which noisy purification circuits satisfy this response condition remains open here.
- *A surviving special case.* With perfect gates and no idle noise, a tight circuit with $k=1$ maps the low-weight input set onto the entire set of states with clean output: the gates are permutations, and both sets have cardinality $2^{n-1}$. Hence its output error is exactly the event that the preparation weight exceeds $e$. The same coupling shows nondecreasing dependence on preparation error. This argument does not cover multiple outputs or noisy gates.
- *The near-origin assertion.* The source states, “Since $p_{\text{out}}$ is a polynomial, continuity of the partial derivatives shows that it is increasing in some neighbourhood of $0$.” (Section 3.2, PDF page 20; `purification.tex`, line 853). The symbolic calculation above gives points $(0,0,p_C,0)$ with negative preparation derivative for arbitrarily small positive $p_C$, and therefore preparation comparisons violating monotonicity in every admissible neighbourhood of the origin for this witness. This extension is not formalized by `result`. Nondecreasing behaviour along individual noise axes does not justify the asserted joint neighbourhood when a derivative vanishes at the origin.
- *Effect on the paper.* The existence proposition and the ideal tightness argument in Section 2.2 do not use the conjecture. The threshold-contour discussion in Section 3.1, lines 816–823 and the caption at lines 832–835, reports improvement below and left of contours for the simulated circuits; tightness alone cannot turn such observations into a universal coordinatewise guarantee. The formal preparation-coordinate counterexample does not refute those observations about gate-noise coordinates, establish a failure for the source's three-gate implementation, or recompute any of its performance plots. Monotonicity in the other noise coordinates and sufficient conditions for shortest circuits remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check is the one reported in #22506, not an exhaustive search for worldwide novelty, priority, later versions or errata. Its web, Zenodo and repository searches, the orchestrator's reading of arXiv:2405.06291 as unrelated, and the search seat's readings of arXiv:2210.06212, arXiv:2402.12361 and formal-conjectures were not independently reproduced for this dossier. MathDB was unavailable in that reported check. The reported exhaustive short-gate-list search and its tested parameter grid were not reproduced; no minimality conclusion is asserted.

The computations and arguments under “What the settlement shows” are not formalized. The correspondence between the finite probability-vector semantics and the paper's physical error interpretation is a source-reading argument rather than a separate Lean equivalence theorem. The paper's performance plots, practical hardware claims and threshold computations were not reproduced. No conclusion is asserted for arbitrary physical noise models, for monotonicity in the other three coordinates, or for proposed additional circuit restrictions.
