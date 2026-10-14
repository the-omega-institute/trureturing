---
slug: atashpendar-mestel-roscoe-ryan-2018-kappa2-entropy-ordering
bibkey: atashpendar2018deletionentropy
doi: null
url: https://arxiv.org/abs/1807.11609v1
triage: theorem
motivation_gids:
  - D5/S3/Entropy/DeletionChannelEntropyOrdering.result
---

# Positional autocorrelation does not determine finite deletion-channel entropy ordering

## Problem

A. Atashpendar, D. Mestel, A. W. Roscoe and P. Y. A. Ryan, *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*, arXiv:1807.11609v1, Section V, state:

> Beyond establishing this maximization, proving the entropy ordering of x strings determined by κ2(x) for finite n and m represents another open problem.

Section IV-E.3 and Table I specify the direction: larger $\kappa^2$ predicts smaller posterior entropy. The finite claim is false at the source's own parameters $n=8$, $m=5$: for $u=00100$, $v=01110$, $\kappa^2(u)=450>410=\kappa^2(v)$, but $H_8(u)>H_8(v)$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Section III-A.f: the number of masks projecting $y$ to $x$ | `embeddings` | `List.sublists` retains index-subsequence multiplicities; filtering and taking the length counts masks. |
| Equation (1): $\mu_{n,m}=\binom{n}{m}2^{n-m}$ | `D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.pref` | Reuses the frozen binomial factor, with natural coefficients and subtraction; `claim` restricts $m<n$. |
| Equation (3): Shannon entropy in bits of $\omega_x(y)/\mu_{n,m}$ | `entropyBits` | Reuses `D5.S3.Entropy.MaxEntropy.shannonEntropy` on the posterior law, dividing nats by $\log 2$; incompatible words contribute zero. |
| Equation (11): $\sum_{1\le r,s\le m}\binom{r+s-2}{r-1}\binom{2m-r-s}{m-r}[[x_r=x_s]]$ | `kappa2` | The literal expression uses zero-based indices and natural coefficients. |
| Section V and the decreasing-$\kappa^2$ ordering of Table I | `claim` | Every positive $m$, every $n>m$, and every pair of binary words of length $m$; strict $\kappa^2$ comparison predicts weak entropy comparison. |
| Negation of that ordering | `result` | A counterexample at $m=5,n=8$ refutes the universal statement. |

The added binders are representations of the source's lengths and strings, not extra hypotheses. `Bool` encodes binary letters (`false` is zero); `List.ofFn` reads increasing positions. The domain excludes only zero output length and the no-deletion case, neither of which is needed for the counterexample.

## Motivation

The finite ordering is a separate question from the asymptotic minimization theorem. Its failure shows that the positional coincidence statistic cannot provide the proposed pairwise entropy order for finite lengths. The settling GID is `D5/S3/Entropy/DeletionChannelEntropyOrdering.result`; preregistration is [#16040](https://github.com/the-omega-institute/trureturing/issues/16040). No digestion atom is involved.

## Gap

The preregistration's bounded literature screen covers the source, the restatement in arXiv:2003.11663, arXiv searches for Atashpendar and deletion-channel entropy, and the follow-ups arXiv:2202.03024 and arXiv:2407.10026. It finds no settlement of this finite $\kappa^2$ ordering in that scope. The follow-ups establish run-length entropy formulas and extremal results; they do not supply this finite ordering.

## Route

At $n=8,m=5$, both posterior laws have mass $\mu=448$. Enumerating all 256 input words gives the embedding histograms below. For any such histogram,

$$H=\log_2\mu-\frac{1}{\mu}\log_2\prod_y\omega_x(y)^{\omega_x(y)},$$

where zero-weight factors are one. A strict integer-product comparison therefore gives the reversed entropy order. `embeddings_eq_count` uses the existing scattered-count implementation and the fixed-length sublist-count theorem; `entropy_from_hist` directly applies `OrientationEntropyBalance.sum_entropy_formula`. `result` instantiates the proposed order and contradicts `entropy_order`.

## Falsifier

The settlement would not address the source if its weights counted distinct subword values rather than index masks, if $\kappa^2$ used different binomial factors, or if the claimed entropy order had the opposite direction. The source's mask definition, Equation (11), and Table I fix those choices; the literal conventions are recorded in #16040 and displayed in the Scribe.

## Evidence

Canonical module: `D5/S3/Entropy/DeletionChannelEntropyOrdering.lean`. Its public definitions are `embeddings`, `entropyBits`, `kappa2`, `claim`; its only public theorem is `result : ¬ claim`. All thirteen private theorem helpers are bind-only and consumed. The settling theorem is bind-only, with no escape witness claimed, and has `admission_basis: open-problem-resolution (#16040; Refuted)`. Its utility is `certified-instance` with `basis=refutes` of `claim`.

The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/7e17771c401e63527728b13f86c5c9ca49994fed/docs/reports/atashpendar-mestel-roscoe-ryan-2018-kappa2-entropy-ordering). Run `python3 docs/reports/atashpendar-mestel-roscoe-ryan-2018-kappa2-entropy-ordering/check.py` from that repository at commit `7e17771c401e63527728b13f86c5c9ca49994fed`: exit 0. Script SHA-256: `9b4fa593c5a2d5ab611abdc5ad9d75f6d6bbbb594db7a6087fa02bae7c2e3ddd`. Integer products decide the strict inversions exactly; the entropy decimals below are rounded floating-point displays.

| $n$ | $m$ | strict inversions among ordered pairs of binary words | $H_n(00100)$ | $H_n(01110)$ |
| --- | --- | --- | --- | --- |
| 6 | 5 | 4 | 2.625815 | 2.584963 |
| 7 | 5 | 4 | 4.524791 | 4.464361 |
| 8 | 5 | 4 | 6.087651 | 6.023315 |
| 9 | 5 | 4 | 7.463162 | 7.404656 |
| 6 | 4 | 0 | outside the word-length scope | outside the word-length scope |
| 8 | 6 | 128 | outside the word-length scope | outside the word-length scope |

At $n=8,m=5$, the computed Table I controls are $\kappa^2(11111)=630$, $H_8(11111)=5.4650$, $H_8(01010)=6.3498$.

The kernel-certified histogram for $00100$ is $\{0:163,1:20,2:10,3:24,4:1,6:20,9:8,10:2,12:3,15:2,18:3\}$; for $01110$ it is $\{0:163,1:20,2:20,3:8,4:12,5:6,6:5,8:6,9:2,10:4,11:2,12:2,14:2,16:1,20:3\}$ (`hist_u`, `hist_v` inside the proof of `result`). Each has 256 entries and weighted sum 448. The exact strict product inequality is `product_lt`.

## Triage

Tier 1 external published open problem, refuted by `result` under #16040. The result settles the proposed universal finite order; the finite computations below have only their stated scope.

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Positional coincidence weighting | Computed: the experiment evaluates Equation (11) as 450 for $00100$ and 410 for $01110$; the binomial factors weight each equal letter pair. The same two finite values are kernel-checked by private `kappa_u`, `kappa_v` on the proof path of `result`. |
| Posterior concentration mechanism | Proved in prose: with common mass $\mu$, expanding $-\sum_y(w_y/\mu)\log_2(w_y/\mu)$ gives the formula in Route. The larger product of $w_y^{w_y}$ has the smaller entropy. At $n=8,m=5$ this comparison is kernel-checked by private `product_lt`, `entropy_from_hist`, `entropy_order` on `result`'s proof path. |
| One-deletion run structure | Literature reading: [arXiv:2202.03024v2](https://arxiv.org/abs/2202.03024v2), Corollary 1, and [arXiv:2407.10026v2](https://arxiv.org/abs/2407.10026v2), Section III, give $H_{m+1}(x)=\log_2(2(m+1))-\frac{1}{2(m+1)}\sum_i(a_i+1)\log_2(a_i+1)$ for run lengths $a_i$. Extending each run produces one input with weight $a_i+1$; all other compatible inputs have weight one. This literature formula is not a theorem of this module. |
| $00100$ versus $01110$ at $n=6,7,8,9$ | Computed: the experiment's exact integer-product comparisons establish all four strict inversions in the table above. Kernel-checked at $n=8,m=5$ by `result`, using private `kappa_u`, `kappa_v` and `entropy_order`. No Lean claim is made for the other three lengths. |
| Other finite search scopes | Computed: the pinned experiment enumerates every ordered pair of binary output words and finds zero strict inversions at $n=6,m=4$ and 128 at $n=8,m=6$. These are exactly the tested finite scopes, not a uniform theorem. |
| Table I controls at $n=8,m=5$ | Computed: the pinned experiment gives $\kappa^2(11111)=630$, $H_8(11111)=5.4650$ and $H_8(01010)=6.3498$. The entropy decimals are rounded displays, not exact identities or a uniform extreme-string ordering. |
| Family $x_r=0\,1^{2r-1}\,0$, $y_r=0^r\,1\,0^r$ | Computed for $r=2,3,4,5$, $m=2r+1,n=2r+2$, by the pinned experiment: $\kappa^2(y_r)>\kappa^2(x_r)$ and $H(y_r)>H(x_r)$. The pairs of $\kappa^2$ values $(x_r,y_r)$ are $(410,450)$, $(8848,9380)$, $(173034,179970)$, $(3208040,3301452)$. |
| General family extension | Open: the inequality for every $r\ge2$ is a candidate theorem via the run-weight formula and strict convexity of $t\log t$; the four computed values do not prove it. |
| Asymptotic minimization | Literature reading: the source's asymptotic minimization theorem has $m$ fixed and $n\to\infty$. A finite inversion does not refute that limiting statement. No source theorem is withdrawn by this settlement. |
| Finite extreme strings | Open: whether $\kappa^2$ correctly orders the all-equal and alternating extremes for every finite $m<n$. The cited follow-ups' one-deletion entropy extremizers remain literature results. |
| Consequences for the source | Proved in prose: any extension requiring the universal finite pairwise $\kappa^2$ ordering lacks that premise, because `result` negates it. The asymptotic minimization proof and its independent hypotheses are unaffected. |

## ASSUMED-UNVERIFIED

The bounded literature screen does not establish exhaustive worldwide novelty or priority. The family for all $r\ge2$ and the uniform finite-extremes ordering remain open. The floating-point entropy displays are not exact identities. The one-deletion run formula is literature evidence, not additional Lean content in this module.
