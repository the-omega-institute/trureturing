---
slug: wiseman-steinberg-hallaji-2023-resolved-count-weak-values
bibkey: wisemansteinberghallaji2023weakvalue
doi: 10.1116/5.0137579
url: https://arxiv.org/abs/2211.15761v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/ResolvedCountWeakValue.result
---

# Resolved-count coherent-state weak values

## Problem

Wiseman, Steinberg and Hallaji, “Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state”, AVS Quantum Science 5, 024401 (2023), arXiv:2211.15761v2, Section V, page 6:

> This supports earlier approximate results which suggested that if a photon-number resolving detector were used, the weak value post-selected on detecting m photons would exceed the no-click weak value by precisely m times the single-photon number. We leave a rigorous proof of this conjecture for future work.

Issue #17772 fixes the finite-mode Fock conventions. For every $k+1$-mode passive network $A,B$, coherent amplitude $\alpha\ne0$, and natural count $m$ of nonzero resolved probability, the conclusion is $W_m-W_0=mw$ when $m>0$. For $m=0$ the difference is zero without requiring a single-photon denominator. The detector acts on mode zero and ignores the remaining modes; the probed mode is also indexed zero, with arbitrary passive evolution between probing and detection.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Arbitrary passive linear network | Every natural $k$ and $A,B:\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}(k+1))\simeq_{\mathbb C}^{\mathrm{iso}}\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin}(k+1))$ | No fixed dimension, network or intensity |
| Coherent input in one mode, vacuum in the others | `coherentInput k α`, `EuclideanSpace.single (0 : Fin (k+1)) α` | Literal binding conventions |
| Weak measurement of number, with other modes ignored | `number`, `numberProjector m`, `generalizedWeakValue` | Unbounded occupation; exact number-domain proofs; projector retains ignored-mode carrier |
| Detect exactly $m$ photons | Every natural $m$ with `coherentProbability A B α m ≠ 0` | Conditional values retain nonzero-denominator certificates |
| Compare with no click | Existential nonzero vacuum probability and `coherentWeakValue ... 0` | Vacuum condition is proved, not an added hypothesis |
| Precisely $m$ times the single-photon value | `claim`, proved by `result` | Same $A,B$ and probed mode; the positive-count branch proves nonzero single-photon probability |
| Zero count | The explicit `if m = 0` branch of `claim` | Difference zero; no single-photon value assigned when its probability vanishes |

All public model definitions and the claim retain the mathematical bodies fixed by #17772; its mode-amplitude carrier is written as $\operatorname{EuclideanSpace}\,\mathbb C\,(\operatorname{Fin} k)$ without a forwarding declaration. `BeamSplitter.exponentialCoeff` and `BeamSplitter.exponentialVector` supply the one-mode coefficients and vectors. The arbitrary finite-mode completion and totalness are supplied by `PassiveFockModel`.

## Motivation

`D5/S3/Quantum/ResolvedCountWeakValue.result` proves the published all-count conjecture. The supporting `D5/S3/Quantum/PassiveFockModel.exponential_total` proves that the exponential vectors are total for every finite number of modes. The public conclusion concerns exact coherent states with unbounded occupation, rather than a finite photon-number cutoff.

## Gap

The source proves its non-resolving click/no-click identity and leaves the resolved identity as a conjecture. Its earlier interferometer calculations address special networks or counts. The bounded literature screen recorded in #17772 reads the source v2, screens seven Semantic Scholar citing works, and searches arXiv:2606.11516, arXiv:2409.03680 and arXiv:2310.00432 for number-resolving detection, $m$ photons and the conjecture. It found no all-count settlement within that scope. Earlier-paper, Glauber, Wiseman, QIQC and MathDB screens are search-seat reports. Completeness is ASSUMED-UNVERIFIED.

## Route

`PassiveFockModel.exponential_total` uses induction on the number of modes and uniqueness of analytic coefficients. It supports extension of passive evolution to the completed Fock space. In the settling module, `created_inner` and `gamma_created` characterize a creation insertion and its transformation; `M1` identifies the number-inserted coherent vector. `M2` evaluates the resolved weak value as an affine function of $m$, and `M3` identifies its slope with the single-photon weak value. `M4` supplies the probability certificates. `insertion_ratio_scaling` removes the nonzero coherent amplitude from the slope, and `result` assembles the conditional proposition. These helpers are private; the public settling surface is `claim` and `result`.

## Falsifier

A finite-mode passive network, nonzero input amplitude and positive count satisfying the formal nonzero-probability conditions but violating $W_m-W_0=mw$ would contradict `result`. A mismatch between a binding convention and the source's experimental interpretation would invalidate that interpretation without invalidating the kernel-checked conditional theorem. A prior all-count settlement would invalidate a priority claim; the bounded literature screen does not prove absence outside its checked scope.

## Evidence

### Formal evidence

The frozen settling declaration is `D5/S3/Quantum/ResolvedCountWeakValue.result`; its complete proposition is displayed in the corresponding Blueprint. The supporting witness is `D5/S3/Quantum/PassiveFockModel.exponential_total`. Compilation and axiom-closure readings are tied to the delivered commit in the PR. Every public declaration's axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit is unfinished: [#18878](https://github.com/the-omega-institute/trureturing/issues/18878). It covers all fourteen public theorem targets, including the proved settling result. No successful registration is asserted. Faithful dependent-source reconstruction and intervention/sensitivity evidence over variable mode counts and completed Hilbert carriers are missing.

### Experiment

The reproducible numerical check is [the experiment directory at commit `5b0a434dd1261c177abea29807d2bee43c6707f1`](https://github.com/the-omega-institute/trureturing-experiments/tree/5b0a434dd1261c177abea29807d2bee43c6707f1/docs/reports/wiseman-steinberg-hallaji-2023-resolved-weak-values), file `check.py`, SHA-256 `764af91b11268d501a7082c839fef2bea4c0712768122ec56744083660433486`. It independently builds the truncated Fock evolution by exponentiating the second-quantized generator and checks source Eq. (2), with seed 20261016, four random networks per mode count, and $m=1,2,3,4$.

With NumPy 2.4.2, `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 -u /Users/auric/trureturing-experiments/docs/reports/wiseman-steinberg-hallaji-2023-resolved-weak-values/check.py 20261016 2,18 3,11` exits 1: the largest $|W_m-W_0-mw|$ is $3.49\times10^{-6}$, violating the registered $10^{-6}$ tolerance at the three-mode, cutoff-11, $m=4$ event. `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 -u /Users/auric/trureturing-experiments/docs/reports/wiseman-steinberg-hallaji-2023-resolved-weak-values/check.py 20261016 2,24 3,15` exits 0 with largest error $1.07\times10^{-10}$. The absolute script has the pinned SHA-256 given above. The seed and network samples are identical between the two truncation pairs. The cutoff-dependent deviation resolves at cutoff 15, as the registered truncation-error check in #17772 requires. These computed readings cover eight networks and 32 positive-count comparisons per command.

These are numerical readings on the stated finite truncations, not proofs of the infinite-occupation result or of higher factorial moments.

## Triage

### What the settlement shows

| Item | Evidence kind | Result and scope |
| --- | --- | --- |
| Mechanism | Kernel-checked: settling module `M1`, `M2`, `M3`, `result` | A number insertion creates one excitation. The detected-mode term contributes the factor $m/d$, while ignored modes give a count-independent background. Subtraction leaves slope $w$ for every admissible count. |
| Zero count and dark detector | Kernel-checked: `M4`, `coherentProbability_ne_zero_iff`, `result` | Vacuum probability is nonzero. If detector amplitude is zero, only $m=0$ has nonzero probability. Conditional weak values are never assigned at a zero denominator. |
| Consequence for the source's click/no-click theorem | Proved in prose below | Averaging the resolved identity over the positive-count distribution yields the source's factor equal to mean photon number conditioned on a click. |
| Section V conjecture | Kernel-checked: `ResolvedCountWeakValue.result` | Every finite network, every nonzero intensity and every count with nonzero resolved probability, including the zero-count branch. |
| Factorial-moment generating function | Open | The search-seat report in #17772 proposes $\sum_{q\ge0}W_m((n_1)_q)z^q/q!=e^{Cz}(1+wz)^m$, $C=W_0$. Its formalization and independent verification remain open. The experiment checks the first moment only. |
| Infinite mode spaces; finite strength; dark counts | Open | None is covered by the finite-mode ideal weak-measurement theorem. |
| Numerical check | Computed: experiment entry above | Four networks per mode count and counts $1$ through $4$, at the two stated truncation pairs; the registered-tolerance failure and its truncation resolution are reported explicitly. |
| Literature | Literature reading: #17772 | No prior settlement found in the bounded screen; completeness ASSUMED-UNVERIFIED. |

For the averaging consequence, let $p_m$ be the coherent resolved-count law and $p_+=\sum_{m\ge1}p_m>0$. The coherent detector count has a finite first moment. Since the click effect is the sum of its positive-count projectors, linearity of the weak-value numerator gives $W_{\mathrm{click}}=\sum_{m\ge1}p_mW_m/p_+$. Substitution of $W_m=W_0+mw$ gives $W_{\mathrm{click}}-W_0=w\sum_{m\ge1}mp_m/p_+=w\,\mathbb E[m\mid m\ge1]$. This is a prose consequence under the stated summability condition, not an additional Lean theorem in this delivery. The source already proves its click/no-click theorem; the resolved settlement supplies the finer conditional identity.

The totalness argument and weak-value calculation impose no finite occupation cutoff. The positive-count nonzero-probability condition is essential to the conditional value. The $\alpha\ne0$ condition supports cancellation of input scaling; zero amplitude permits no positive-count conditioning. The proof does not extend these ideal-model conclusions to finite interaction strength or detector noise.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED outside the bounded screen in #17772. The physical interpretation assumes the passive, lossless, ideal-detector and weak-measurement model of the source. The factorial-moment generating function, infinite-mode completion, finite-strength measurements and dark-count extensions remain open at the stated formal scope. Escape registration remains unfinished under #18878; it is independent of kernel verification of the mathematical statements.
