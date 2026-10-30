---
slug: giuffrida-squartini-grunwald-garlaschelli-2023-ensemble-equivalence-converse
bibkey: giuffrida2025descriptionlength
doi: 10.1103/1sd2-rxmy
url: https://arxiv.org/abs/2307.05645v4
triage: theorem
motivation_gids:
  - D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.result
---

# Model-level ensemble equivalence does not imply measure-level equivalence

## Problem

F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli, *Description length of canonical and microcanonical models*, arXiv:2307.05645v4, Physical Review Research 7, 043057, Section IV.C, following (71):

> i.e., whenever ensemble equivalence holds, the corresponding microcanonical and canonical models are equivalent on the model level. The reverse implication, verified here in the specific case of one-sided local constraints, will be investigated in future work.

Issue [#18580](https://github.com/the-omega-institute/trureturing/issues/18580) preregisters its refutation. The source and equations are recorded in the [Library note](../Library/StatisticalMechanics/giuffrida2025descriptionlength.md).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Binary $n\times m$ matrices, (12) | $\mathrm{Fin}(n)\to\mathrm{Fin}(n)\to\mathrm{Bool}$ | Specialize $m=n$; a counterexample in this subclass refutes the general implication. |
| Scalar statistic and fiber cardinality, (15) | `omega` | Count every binary matrix with the observed statistic. |
| Microcanonical uniform law, (16) | `pMic` | Reciprocal fiber size on the fiber, zero off it. |
| Canonical exponential law, (20), and matching, (21) | Exponential expression in `IsMatched` | Sum over every binary matrix; the parameter is real and finite. |
| Matched measure divergence, (22), and equivalence scale, (35) | `measureDiv` and the conclusion of `claim` | Matching holds eventually; divergence is divided by $n$. |
| Maximized likelihoods, (5), (17) | `lCan`, `lMic` | The real supremum includes limiting endpoint likelihoods. |
| Normalized maximum likelihood, (8) | `nmlMic`, `nmlCan` | The literal likelihood-over-sum expressions. |
| Model divergence and its vanishing rate, (69)–(70) | `modelDiv` and the premise of `claim` | The normalization scale is $n$, not $n^2$. |
| Reverse implication after (71) | `result : ¬ claim` | Universal statistics and observation sequences, restricted to eventual finite matching. |

The exponential formula is literal in the public definitions. Private proofs use the existing `gibbs` and `meanEnergy` constructions; private consumed bridges relate the literal NML quotients to the existing `normalized` construction. Restricting the source assertion to square matrices, one scalar statistic and eventually matched observations weakens it, so refuting this restriction refutes the general converse.

## Motivation

Model equivalence compares two normalized maximum-likelihood laws averaged over all data. Measure equivalence compares a selected microcanonical fiber with its matched canonical law. The question is whether small divergence in the former comparison controls every observation in the latter comparison.

## Gap

The source proves the forward implication and verifies the converse for one-sided local constraints. The preregistration records a source-v4 reading and a literature screen: the first author's thesis retains the question, and the screened later works arXiv:2509.01064 and arXiv:2505.10373 do not supply a settlement. The thesis and later-work screen are seat-reported; literature-search completeness is `ASSUMED-UNVERIFIED`. Within the searched scope no prior settlement was found.

## Route

Use the scalar statistic

$$c_n(G)=\sum_{i=0}^{n-1}(1+2^{-i-1})g_{i0}.$$

The finite dyadic fraction lies in $[0,1)$, while the integer part counts first-column ones. Finite binary expansions make the statistic injective on first columns. Its matrix fibers consequently have equal size, and the microcanonical NML law is uniform.

For sorted energies, a canonical mass at rank $k$ is at most $1/(k+1)$ for a nonnegative parameter and at most $1/(N-k)$ for a nonpositive parameter. Summing the rank bounds and using a harmonic estimate controls the canonical NML normalization. The checked argument bounds model divergence by $\log(4(n+1)^2)$ and proves that its quotient by $n$ tends to zero.

For checkerboard observations at size $n=2m$, product factorization bounds first-column canonical probability by $2^{-m}$ for every parameter. Thus measure divergence is at least $m\log2$. Continuity of the finite canonical mean and its limits at the extreme energies provide a finite matched parameter for every $n\ge2$. The scaled measure divergence is at least $\log2/2$ along the positive even subsequence, contradicting the asserted zero limit.

## Falsifier

The settlement depends on the literal likelihood normalization, the source's scale $n$, equal matrix-fiber sizes, and finite expectation matching. A refutation at scale $n^2$, a law supported on fewer matrices, or observations without eventual matching would not refute `claim`. The theorem uses the source laws at scale $n$ on the entire binary-matrix space and constructs eventual matching.

## Evidence

The settling node is `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.result`; its Lean name is `D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.result`. Its ten public definitions mirror the source formulas, and its only authored public theorem is `result`.

Admission basis: `open-problem-resolution (#18580; Refuted)`. Utility: `kind=certified-instance; basis=refutes`, with the module's `claim` and `result` selectors. This is `deposit-uncovered`, without an atom or coverage operation.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Published experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/a625a82a5b3a7d19bcf589fd66f10b62bdcd2213/docs/reports/giuffrida-squartini-grunwald-garlaschelli-2025-model-equivalence-converse).

Command: `python3 /Users/auric/trureturing-experiments/docs/reports/giuffrida-squartini-grunwald-garlaschelli-2025-model-equivalence-converse/check.py`, exit 0, `RESULT PASS`. Script SHA-256: `9a8f46cbfb6b441cb15c11397c70438d94d93e133ea1a9215a6bbacd93f06dab`. Direct enumeration covers $n=2,4$ (16 and 65536 matrices); fiber computations cover even $n=2,4,6,8,10,12,14$; the polynomial-root identity is checked at $n=4$.

| $n$ | Direct model divergence | Direct matched measure divergence |
| --- | --- | --- |
| 2 | 0.220686453781 | 1.378086039432 |
| 4 | 0.559269505558 | 2.764716572927 |

The finite computations verify $W_n\le2n$, $0\le D_{\rm NML}\le\log W_n$, and $n\log2-\log4\le D_{\rm KL}(c^*)\le n\log2$ on those even sizes. At $n=14$, $D_{\rm NML}/n=0.083317$ and $D_{\rm KL}(c^*)/n=0.692904$. At $n=4$, $q_4=1.006322080404167$ and $-16\log q_4=-0.100834878158888$, equal to the computed matched parameter. These numerical readings do not establish a uniform extension beyond the tested sizes.

## Triage

Tier 1 external named open question; settlement **Refuted** by `result`. Literature-search completeness is `ASSUMED-UNVERIFIED`.

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Family $\sum_i(1+2^{-i-1})g_{i0}$ | Kernel-checked: private `dyadicStat`, `energy_formula`, `dyadicStat_succ`, consumed by `result` | Scalar bounded dyadic weights on binary square matrices; zero size is defined as zero. |
| Scalar statistic separates the two limits | Kernel-checked: `result`, private `dyadic_model_tendsto`, `matchedTheta_eventually`, `checker_scaled_lower` | Model divergence divided by $n$ tends to zero; eventual finite matching holds; measure divergence divided by $n$ does not tend to zero. |
| Empirical direct evaluation | Computed: the experiment entry, exit 0 | All matrices at $n=2,4$, with agreement to fiber reduction within the checker's $10^{-9}$ tolerance. |
| Empirical fiber bounds | Computed: the experiment entry, exit 0 | Even $n=2$ through $14$ only. |
| Root identity | Computed: the experiment entry, exit 0 | $n=4$ only. |
| General matched-parameter root formula and uniqueness | Open | The finite root computation does not prove these uniformly. |
| Natural constraints in the source | Literature reading: source IV.C | One-sided local constraints are verified by the source; its total-link, row-sum and degree-sequence results are unchanged. |
| Uniformly bounded integer-weight constraints | Open | The general converse for linear constraints with $O(1)$ integer weights is not settled here. |
| Model bound and vanishing quotient | Kernel-checked: private `dyadic_model_bounds` and `dyadic_model_tendsto`, consumed by `result` | $0\le D_{\rm NML}\le\log(4(n+1)^2)$ for positive $n$; its quotient by $n$ tends to zero. |
| Model scale $O(\log n)$ | Proved in prose from the checked model bound | For $n\ge2$, $n+1\le2n$, so $\log(4(n+1)^2)\le\log16+2\log n\le6\log n$. |
| Stronger measure bounds and nonzero matched parameters at tested sizes | Computed: the experiment entry, exit 0 | Even sizes $2$ through $14$ for the bounds; direct matched parameters at $n=2,4$ and the root identity at $n=4$. |
| Uniform sharper measure estimate and parameter nonzeroness | Open | The kernel-checked lower bound $D_{\rm KL}/n\ge\log2/2$ along positive even sizes suffices for refutation; the stronger uniform statements are not claimed. |
| Restriction to scalar square-matrix families with matching | Proved in prose: Statement echo | A universal implication entails this restricted implication, so the latter's negation refutes the former. |

### What the settlement shows

The failure mechanism is that uniform NML averaging does not control the canonical probability of the selected balanced fiber. Equal matrix-fiber sizes and the harmonic rank bound make model divergence sublinear, while bit factorization gives a positive lower bound for the scaled selected-fiber divergence. These ingredients are kernel-checked private dependencies of `result`.

The nearest surviving source statement is the converse for one-sided local constraints, established in the source; this is a literature reading, not a theorem newly proved here. The forward implication (71) and the source's results for its natural constraint classes are unchanged. Whether bounded integer-weight linear statistics admit the same separation is open.

| Declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.result` | content | The finite dyadic injectivity construction and the resulting equal-fiber/vanishing-model-limit versus positive-even-measure-limit argument, through private `fraction_injective`, `dyadic_model_tendsto`, `matchedTheta_eventually`, and `checker_scaled_lower` | open-problem-resolution (#18580; Refuted) |

## ASSUMED-UNVERIFIED

Literature completeness, the seat-reported thesis reading and later-work screen. The finite numerical bounds have exactly the experiment's stated scope. The sharper uniform measure bounds, uniqueness/nonzeroness of the matched parameter and the bounded-integer-weight converse are open beyond the module's settlement.
