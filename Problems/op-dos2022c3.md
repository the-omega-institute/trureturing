---
slug: op-dos2022c3
bibkey: dikshtein2022doublesided
doi: 10.3390/e24091321
url: https://doi.org/10.3390/e24091321
triage: theorem
motivation_gids:
  - D5/S3/Entropy/DoubleSidedBottleneckBSC.result
---

# Exact BSC optimality near independent binary sources

## Problem

Dikshtein, Ordentlich and Shamai, *The Double-Sided Information Bottleneck Function*, Entropy 24(9):1321, Conjecture 3, printed p. 11, asks:

> For every $(C_u,C_v)\in[0,1]\times[0,1]$, there exists $\theta(C_u,C_v)$, such that for every $p>\theta(C_u,C_v)$ the achieving test-channels $P_{U|X}$ and $P_{V|Y}$ are BSC with parameters $\alpha=h_b^{-1}(1-C_u)$ and $\beta=h_b^{-1}(1-C_v)$ respectively.

The source convention is $0\le p\le1/2$ with a threshold $0\le\theta<1/2$. Optimality means attainment, without a uniqueness assertion. Entropy and mutual information are in bits. The competitors include every finite output alphabet. The formal statement is the literal reduced-domain claim registered in [#26680](https://github.com/the-omega-institute/trureturing/issues/26680).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every budget pair in $[0,1]^2$ | `DoubleSidedBottleneckBSC.claim`, both budget binders and their four inequalities | Includes all endpoints |
| There exists a budget-dependent threshold | `claim`, threshold existential before the crossover binder | Independent of channel and output size |
| Every crossover above the threshold | `claim`, crossover in $[0,1/2]$ and strict threshold inequality | Binding reduced domain |
| Specified BSC parameters | `hbInv`, `bsc`, and both explicit inverse entropy equations in `claim` | Actual inverse branch $[0,1/2]$ |
| Achieves the information bottleneck optimum | `bscOptimal`, `R`, `achievable` | Both rate constraints and equality with the extended-real supremum over all finite channels |

The additional inverse equations and candidate feasibility conjuncts establish well-definedness and attainment; they strengthen the recorded conclusion. The $\operatorname{EReal}$ supremum prevents empty or unbounded sets from being totalized to a finite real value. The binary entropy expression is the existing `CloningMachine.binaryEntropyBits`; no new entropy alias is introduced. The source definitions and displayed bodies are in the matching Blueprint Scribes.

## Motivation

The settling declaration is `D5.S3.Entropy.DoubleSidedBottleneckBSC.result`. It proves exact optimality on a nonempty crossover interval, uniformly over finite output sizes, rather than only the leading asymptotic expansion. The supporting module is `D5/S3/Entropy/DoubleSidedBottleneckMoments`. Both new modules have generality G and utility none. The settling module has admission basis `open-problem-resolution (#26680; Proved)`; the support module has `escape-witness`, with its consumed uniform power remainder bound.

## Gap

The source's leading-order theorem does not alone bound every higher-order contribution by the quadratic loss. Exact attainment needs a uniform remainder estimate depending on the same posterior deficit. No sharp threshold or optimizer classification is asserted.

## Route

Write $\phi(u)=\log2-h_b((1+\sqrt u)/2)\log2$, using bit-valued $h_b$. A strong Jensen deficit controls the variance of each squared posterior bias. The uniform power Taylor remainder then bounds all even moment deficits, and weighted Cauchy bounds the odd ones. Their product bounds dominate the series tail by the same deficit that appears negatively in the leading quadratic term. `DoubleSidedBottleneckMoments.posterior_local_optimality` is the resulting posterior comparison. The finite-channel bridges in the settling module transport it to the actual Markov product law.

The zero-budget branch has zero output information. The full-budget branch uses the imported data-processing and Shannon combining convexity results. `DoubleSidedBottleneckBSC.result` combines those branches with the interior estimate and proves the inverse equations and feasibility of the attaining BSC pair.

## Falsifier

A counterexample to the formal conclusion requires budgets in $[0,1]$, a permitted crossover beyond every claimed threshold, and finite stochastic kernels meeting both rate constraints whose mutual information exceeds the specified BSC value. A failure of uniqueness or a crossover outside $[0,1/2]$ is a different statement. A prior settlement or a source mismatch affects attribution independently of kernel correctness.

## Evidence

The Lean theorem `D5.S3.Entropy.DoubleSidedBottleneckBSC.result : claim` is the settling node. Its supporting estimate is `D5.S3.Entropy.DoubleSidedBottleneckMoments.posterior_local_optimality`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The four-slot escape audit is unfinished for every new public theorem and every published owner declaration: [#30706](https://github.com/the-omega-institute/trureturing/issues/30706). No declaration is reported as declared_validated. The missing client evidence comprises faithful source reconstruction, the realization/equivalence bridge, positive law and intervention/sensitivity proofs for the original telescopes; no incomplete Reg module is delivered.

### Finite experiment

The independent exact checker is in [trureturing-experiments, pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/3afa6736bc3cb5a78b44d51d69b384ec0a1f9cbf/docs/reports/dikshtein-ordentlich-shamai-2022-conjecture-3-exact-low-correlation-bsc-optimality). Script: `check.py`; SHA-256 `c22d921c4aa1a19ddd334a166a3030de62024f7ac554e48f4fee216c01fc46b4`. Command: `python3 /tmp/op-dos2022c3/stageb/experiment-check.py`, an exact byte copy of that pinned script; exit 0, `ALL_CHECKS_OK`.

The tested scope is the denominator-4 row-stochastic grid with output sizes 1, 2 and 3, augmented by the target BSCs, for budget pairs $(1-h_b(1/4),1-h_b(1/4))$ and $(1-h_b(1/8),1-h_b(1/3))$, each at $p=49/100$ and $p=99/200$. Feasible pair counts are $91\times91$ and $163\times44$ at each crossover, totaling $2(91^2+163\cdot44)=30906$ comparisons without a violation. The script also verifies 125 exact fidelity identities, the tail coefficient inequalities for $k\le128$ and 256 positive-rational threshold substitutions. These finite computations establish no universal extension; the theorem supplies the general statement.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | Proved; kernel-checked `DoubleSidedBottleneckMoments.posterior_local_optimality`, with its private `entropy_moment_deficits` and `entropy_product_moment_deficits` | The strong entropy Jensen deficit controls even and odd posterior moment products. The negative quadratic term dominates their geometric tail. |
| Interior threshold | Proved; kernel-checked private `DoubleSidedBottleneckBSC.interior_bscOptimal` and public `DoubleSidedBottleneckMoments.posterior_local_optimality` | For $a=1-2h_b^{-1}(1-C_u)$, $b=1-2h_b^{-1}(1-C_v)$ and $M=\max(\phi'(a^2),\phi'(b^2))$, the construction uses $\theta=3M/(1+6M)<1/2$. The posterior comparison accepts $0\le\delta<1$ and $\delta\le1/(1+6M)$. The interior budget assumptions are $0<C_u,C_v<1$. |
| Endpoints | Proved; kernel-checked private `DoubleSidedBottleneckBSC.zero_budget_bscOptimal` and `DoubleSidedBottleneckBSC.full_budget_bscOptimal` | A zero budget forces zero output mutual information. A full budget uses data processing and Shannon combining convexity. The BSC pair is optimal throughout $0\le p\le1/2$. |
| Finite validation | Computed; pinned exact checker above, exit 0 and stated SHA-256 | 30906 comparisons, 125 fidelity checks, $k\le128$ coefficient checks and 256 threshold substitutions passed in exactly the stated finite scope. |
| Surviving neighbours | Open | Sharp thresholds, uniqueness, larger source alphabets, different source distributions and crossover relabeling beyond the reduced domain are not separately established. |

The posterior estimate applies to arbitrary finite nonnegative normalized weights and centered bounded biases satisfying the entropy budgets, as its full telescope states. No optimality or sharpness of the sufficient threshold is proved. Conjecture 3 supplies an exact-interval conclusion beyond the source's asymptotic theorem; its other independent conjectures, including the larger-alphabet question and separate zero-crossover questions, receive no new settlement here. No additional downstream theorem of the source is asserted as a Lean consequence.

### Literature status

The preregistration records the journal PDF/XML and PMC reading and Pichler's arXiv:2609.27991v1, Section 6, which retains this question as open. Within that recorded screen no external settlement was found. Literature completeness is ASSUMED-UNVERIFIED. The accessible citation search and its access limits do not establish originality or global absence of a prior proof.

## ASSUMED-UNVERIFIED

Literature-screen completeness and original-paper TeX availability are not established; the source quotations are journal PDF/XML transcriptions with normalized mathematical typography. The formal target uses the explicitly registered reduced crossover domain. The exact experiment is finite evidence only. Escape registration remains unfinished under #30706.
