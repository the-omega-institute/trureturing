---
slug: akhmet-tilessov-alpha-unpredictable-average
bibkey: akhmettilessov2026integral
doi: 10.3390/math14183391
url: https://arxiv.org/abs/2608.09809v2
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.result
---

# Alpha unpredictability does not ensure an ordinary average

## Problem

Akhmet and Tilessov, *Integral of an Alpha Unpredictable Function*, Mathematics 14(18), 3391, journal §3 Remark 1, page 7, asks:

> Nevertheless, whether every alpha unpredictable function possesses an average is still an open question.

The question is in the journal article, not arXiv:2608.09809v2. [Preregistration #26750](https://github.com/the-omega-institute/trureturing/issues/26750) fixes both ordinary Cesàro conventions because the source leaves “average” unspecified. For real-valued functions on the whole real line, the claim is the disjunction of universal existence of the one-sided limit and universal existence of the symmetric limit. Negating this disjunction refutes both readings.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Definition 1: uniformly continuous and bounded on the real axis | `PoissonReturn` requires uniform continuity and a uniform absolute-value bound | Literal source condition |
| Strictly increasing return sequence approaching infinity | Real sequence $q$ with strict monotonicity and limit $+\infty$ | No integer restriction on the claim |
| Uniform convergence on every bounded interval | Eventual epsilon estimate on each real closed interval $[a,b]$ | Equivalent compact-interval formulation |
| Definition 2: increasing divergence sequence and positive constants | Real sequence $s$, positive $\epsilon_0,\delta$, and divergence to $+\infty$ | All source quantifiers retained |
| Separation on $[s_n,s_n+\delta]$ using the same return sequence | `IsAlphaUnpredictable` shares $q$ between recurrence and strict separation | Follows the displayed source formula; the source's following prose uses a different symmetric interval |
| Every alpha unpredictable function possesses an average | `claim` disjoins the two universal ordinary limit assertions; `result` negates the disjunction | Both ordinary interpretations refuted |
| No source assumption of smoothness or evenness | These are properties of the constructed witness only | No extra hypothesis on the universal claim |

The one-sided mean is $T^{-1}\int_0^T f(t)\,dt$ and the symmetric mean is $(2T)^{-1}\int_{-T}^T f(t)\,dt$, with $T\to+\infty$. Division at $T=0$ does not affect either limit. Uniform continuity implies compact-interval integrability, so no nonintegrability default supplies an average.

## Motivation

This is a tier-1 external named open question. The settling GID is `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.result`, with admission basis `open-problem-resolution (#26750; Refuted)`, generality `I` and utility `none`. The result is a symbolic infinite construction; the supplementary finite experiment does not provide its mathematical conclusion.

## Gap

Local recurrence controls bounded windows but need not control the global proportions of zero and one cells. The construction retains arbitrarily late copies of every finite word while successively dominant constant blocks force incompatible endpoint averages.

## Route

Let $W_0$ be empty. At stage $n+1$, append an enumeration of every binary word of length $n+1$, then append a constant block of length $(n+1)^2(L+1)$, where $L$ is the preceding length and the final letter is the parity of $n+1$. Prefix compatibility defines one infinite binary word. Every finite word occurs arbitrarily late; the frequency of ones at endpoint $n>0$ differs from its final letter by at most $1/(n^2+1)$.

Reflect integer cells by $k\mapsto-k-1$ and smooth the resulting zero-one step function with Mathlib's normalized even smooth bump of outer radius $1/4$. Central-word copies provide exact local return. For each of those same shifts $q_n$, a late occurrence of $0^{q_n}1$ supplies a zero plateau whose translate is a one plateau. The fixed separation constants are $\epsilon_0=1/2$ and $\delta=1/8$.

Translating an interval changes a bounded step-function integral by at most twice the translation distance. Normalized smoothing therefore changes each total integral from zero to $T\ge0$ by at most $1/2$. The endpoint smoothed mean differs from the alternating final letter by at most $2/n$. A hypothetical mean would make both the constant-zero and constant-one subsequences converge to the same number. Evenness identifies the symmetric and one-sided means.

## Falsifier

A source-definition mismatch, a missing same-shift requirement, or a verified earlier settlement would invalidate the claimed correspondence to this published question. The public theorem retains the literal source predicates and both averaging expressions. No generalized invariant mean is asserted or refuted.

## Evidence

The module's public theorem `result : ¬ claim` is the kernel-checked settling declaration. Its proof uses one and the same normalized convolution of the reflected binary step function in both branches. All mathematical imports are from pinned Mathlib; there are no D5 imports or frozen prerequisites.

### Supplementary exact finite computation

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/8a5ad4a43297e68ef131028eddf08d0eb60c04f2/docs/reports/akhmet-tilessov-2026-alpha-unpredictable-average), script `check.py`, SHA-256 `28eafdc7ea3bdac010b391cae6d106e24cba1e51b1e7a7d2f20c27a462349a43`. The implementation seat verified the pinned object in the local experiments clone and executed `python3 /Users/auric/.op-scratch/op/at2609avg/stageb/check.py`, exit 0, with final result `ALL_CHECKS_OK`.

The tested scope is independent expanded stages 1–5, frequency bounds through stage 40 for both parities and three affine families, five explicit return shifts with full-window support certificates, exact rational convolution samples and evenness samples. The first six raw frequencies are $4/5$, $8/69$, $866/939$, $898/17067$, $431678/447927$, and $431870/16587543$. The finite checker uses a polynomial test kernel, not the smooth Mathlib bump. Its enumeration order and sampled shifts are not identified with the noncomputable Lean witness. It proves no infinite limit or smoothness claim.

### Escape audit

The only public theorem, `D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation.result`, is an audit target: utility `none` gives no designated-refutation exemption. Its four-slot audit is unfinished in [issue #27238](https://github.com/the-omega-institute/trureturing/issues/27238). The existing existential template reads a single existential acceptance law; the delivered statement is a negated disjunction of universal analytic limit assertions. The dependent-family template needs faithful operand reconstruction, the source-equivalence bridge, variation, sensitivity and observational-dependence evidence. Those data have not been supplied. No Reg source or validated registration is claimed.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Local recurrence does not force convergence of global occupation proportions; one smooth bounded alpha-unpredictable witness has neither ordinary mean | proved | Kernel-checked `result`, with private `smooth_alpha`, `no_one_sided_mean` and `symmetric_mean_eq` for the identical convolution witness |
| The witness is even, smooth, uniformly continuous and bounded in absolute value by one; both conventions use the same function | proved | Kernel-checked private `smooth_even`, `smooth_contDiff`, `smooth_uniformContinuous`, `smooth_bound` and their actual common witness in `result` |
| Return and separation use the same shift sequence, with $\epsilon_0=1/2$ and $\delta=1/8$ | proved | Kernel-checked private `smooth_alpha`, whose construction shares $q$ in `IsAlphaUnpredictable` |
| Endpoint frequency error is at most $1/(n^2+1)$; smoothing changes totals by at most $1/2$; smoothed endpoint mean error is at most $2/n$ for $n>0$ | proved | Kernel-checked private `endpoint_occupation_bound`, `smooth_integral_error` and `endpoint_error` |
| Exact finite stage counts, rational samples and support certificates | computed | Pinned experiment entry above, command exit 0 and specified SHA-256; finite scope only, without infinite limits or smoothness |
| The full affine family for all $a<b$, full cluster set $[a,b]$, all higher derivative bounds, strict-positive specialization and symmetric divergence-window variant | open | Not separately formalized in this module; the preregistration gives mathematical candidates beyond the settling statement |
| The source bounded-primitive theorem and bounded-remainder equivalence | open | Not assessed; the refutation of average existence supplies no refutation of those hypotheses or conclusions |
| Generalized invariant means, stronger recurrence notions and extra bounded-remainder assumptions | open | Outside the delivered theorem |

The failure mechanism is compatible with exact local returns: successively dominant blocks can change global occupation without removing late copies of any fixed window. What survives here is smooth bounded recurrence and same-shift separation, together with bounded smoothing error and equality of the two means for this even witness. Convergence under stronger hypotheses remains a separate question. No conclusion about another source theorem follows merely from refuting Remark 1's average-existence question.

### Literature status

The preregistration's source and literature screen located no verified exact settlement within its searched scope. Akhmet–Fen, arXiv:1608.07301, and Akhmet–Fen–Alejaily, arXiv:1910.12758v2, supply prior symbolic and convolution constructions. Historic behavior and nonconvergent time averages are classical. The formalized settlement combines late-word recurrence, alternating occupation and an even smooth scalar realization; it does not claim invention of those methods.

## ASSUMED-UNVERIFIED

Exhaustive literature completeness and novelty remain `ASSUMED-UNVERIFIED`. The full Sigmund article on time averages, the relevant Levitan–Shcherbakov works and the full IOP monograph chapters were not independently verified in the literature screen. The finite checker does not identify its samples with the literal Lean witness. The four-slot escape audit is unfinished as linked above.
