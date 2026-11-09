---
slug: ptaszynski-skewness-minus-kurtosis-lower-bound
bibkey: ptaszynski2022skewness
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.result
---

# Ptaszyński's exact lower endpoint of skewness minus kurtosis

## Problem

This dossier anchors exactly the whole lower assertion separately preregistered in [issue #25782](https://github.com/the-omega-institute/trureturing/issues/25782). Put

$$C=\frac{3(107-51\sqrt{17})}{2048},\qquad R_j(k)=\sum_{i:\operatorname{Fin}N}k_i^{-j},$$

$$S(k)=\frac{3R_2(k)^2}{R_1(k)^4}-\frac{2R_3(k)}{R_1(k)^3},\qquad K(k)=\frac{15R_2(k)^2}{R_1(k)^4}-\frac{20R_3(k)}{R_1(k)^3}+\frac{6R_4(k)}{R_1(k)^2R_2(k)}.$$

The assertion is the conjunction

$$\bigl[\forall N\in\mathbb N,\ N\ge2\ \Longrightarrow\ \forall k:\operatorname{Fin}N\to\mathbb R,\ (\forall i,\ k_i>0)\ \Longrightarrow\ C\le S(k)-K(k)\bigr]$$

and

$$\operatorname{IsGLB}\!\left(\{v\in\mathbb R\mid\exists N\in\mathbb N,\ N\ge2\ \land\ \exists k:\operatorname{Fin}N\to\mathbb R,\ (\forall i,\ k_i>0)\ \land\ v=S(k)-K(k)\},\ C\right).$$

Both expressions use the same vector; repeated rates retain their multiplicity. The domain includes arbitrary positive real coordinates, $N=2$, and unbounded finite $N$. A bound only on an exceptional-rate family, a fixed dimension, or a conjectured topology would not establish this conjunction. Neither strict finite inequality nor finite-$N$ optimizer classification is asserted.

The source is K. Ptaszyński, *Bounds on skewness and kurtosis of steady-state currents*, arXiv:2204.08421v4, source year 2022. In `main.tex`, SHA-256 `0d8f9bf311a07990b64d4746e9ec4fb1e164deec23b270503642b94766baf84e`, line 431 gives

> $\min(\mathcal S-\mathcal K)=3(107-51\sqrt{17})/2048$ for $A=(5+\sqrt{17})/4$.

The detailed displays at lines 431–432 and Figure 6 caption at line 474 select $S-K$. The summary at line 133 instead says $K-S$; this conflict is retained. Line 424 uses $a=A/N$ asymptotically. Line 417 conditions the analytic evaluation on the proposed topology, and line 792 explicitly calls the topology numerical/conjectural. The universal statement above imposes no such topology hypothesis.

## Motivation

The full assertion connects a uniform inequality for every actual positive rate vector to sharpness within that same actual value set. Here $S=C_3/C_1$ and $K=C_4/C_2$ are scaled current cumulant ratios, not standardized central moments. The target is precisely the displayed rational inverse-rate model. An analytic evaluation on a selected family supplies approximation candidates but does not alone prove the universal bound.

The owning Scribe binds one `OpenProblemResolutionClaim` of kind `Proved` to `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.result`. The actual result statement ID is `sha256:9e112720537c1dfd894f6dd624b465d17d20bff60039fe4b6d621f10bcb542a8`; the actual frozen module ID is `sha256:600dd89006d5b3c22e1ed3de8482e0263a19f08afa9c1e2ee752f7b203150ae1`. The upper endpoint is a frozen supplier, not a lower resolution.

## Gap

The source's numerical topology conjecture does not by itself prove the universal inequality or that the exact endpoint is the greatest lower bound of the entire actual set. The frozen whole-event theorem supplies these mathematical clauses. No physical process construction, renewal identification, empirical truth, global extremal-topology theorem, or finite optimizer classification follows from this publication binding.

At $N=2$ the intended interpretation uses two oriented, channel-labelled phase stages with a marked winding crossing. That physical identification is not explicitly supplied by the source notation. Physical $N=1$, bidirectional, thermal and multicyclic networks and finite-time cumulants are outside the assertion.

## Route

Reuse the original `UnicyclicSkewnessMinimum.normalized_simplex`, `UnicyclicSkewnessMinusKurtosisUpperBound.normalized_difference` and existing moment interfaces on the same vector $x_i=k_i^{-1}/R_1$. With $p=\sum x_i^2$, $q=\sum x_i^3$, $r=\sum x_i^4$ and $u=\sqrt p$, the difference is $-12p^2+18q-6r/p$. Nonnegative sums on the original common vector split at $u=1/3$: the lower interval compares with $f(u)=-12u^4+18u^3-6u^2$ and its radical factorization at $\alpha=(9-\sqrt{17})/16$, while the upper interval gives $-4/27\ge C$.

For actual sharpness, take every $m\in\mathbb N$, $N=m+2$, $k_0=1/\alpha$, and $k_i=(m+1)/(1-\alpha)$ otherwise. Every rate is positive, $R_1=1$, and $R_j=\alpha^j+(1-\alpha)^j/(m+1)^{j-1}$ for $j=2,3,4$. Continuity at $z=1/(m+1)\to0$ gives $f(\alpha)=C$, with denominator $\alpha^2>0$. Each term belongs to the asserted actual set; every lower bound of that set is therefore at most $C$.

Dividing by the common tail rate gives the relative exceptional rate $A/(N-1)$, $A=(5+\sqrt{17})/4$. This finite family differs from the source's $A/N$; their ratio $N/(N-1)$ tends to one. The proof evaluates its own finite vectors and does not identify the two finite families.

## Falsifier

A positive vector of any finite size $N\ge2$ with $S(k)-K(k)<C$ would contradict the universal clause. A lower bound of the full actual set strictly greater than $C$ would contradict the IsGLB clause. Sharpness on an unrealizable moment tuple, on a different vector for each moment, or under an extra topology restriction would fail to address the stated target. These criteria do not claim empirical realizability or classify minimizers.

## Evidence

The mathematical binding is the frozen whole conjunction, with the statement and module IDs above. Its axiom closure consists of `Classical.choice`, `Quot.sound` and `propext`; there is no new axiom or `sorry`.

All eight theorem declarations have `proof_shape: bind-only` under the repository normalization rule. This is a semantic assessment, not machine classification. The seven consumed helpers are `polynomial_lower_bound` and `coarse_lower_bound` feeding `simplex_lower_bound`; `simplex_lower_bound` feeding `universal_lower_bound`; `universal_lower_bound` feeding `result`; `sharp_rates_positive` feeding `sharp_limit` and `result`; `sharp_value` feeding `sharp_limit`; and `sharp_limit` feeding `result`. Helpers receive no independent mathematical-content or external-resolution credit. The terminal result's intended `admission_basis` is `open-problem-resolution`, with `utility: none`; no escape witness is claimed.

The owning Reg retains the original whole claim through `DependentFamily.realize` and the existing enrollment: `Params = Nat`, `State N = Fin N → Real`, `Output = Real`, `Role = Unit`, `Anchor = Empty`. Its actual law includes both clauses. Variation uses positive $N=2$ unit rates against a constant $C-1$ readout; sensitivity and observational dependence distinguish the positive vectors $(1,1)$ and $(1,2)$. No every-fiber variation claim is made. The current whole-family binding is `fb9829368b277c193c04d46777f8acb16d60e534c6c9a3dcff784d7e2bb8b245`, with `familyRecord = none` and `continuation = unknown`; the latter proves neither undecidability nor inexhaustibility.

The bounded reuse order was public and private D5, pinned Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, then eligible third-party sources. The accepted screen found no exact target in its inspected scopes; generic normalization, moments, positive-sum, natural reciprocal-limit and GLB interfaces are reused. Original consumed private suppliers were published at origin and canonically repinned with their statements and proofs preserved. This metadata adds no mathematical declaration.

## Triage

`theorem`; source-screen Tier 1, source year 2022, separately preregistered whole lower assertion in issue #25782. The accepted independent source screen establishes source readiness only, not proof or final admission. The publication item registers the exact frozen conjunction. This metadata itself supplies no proof, independent review verdict, delivery certificate or delivered credit.

## ASSUMED-UNVERIFIED

The bounded literature screen checked exact arXiv metadata and independently retrieved `2305.09759v1`, `2411.19643v3` and `2610.12652v1` without identifying settlement of this target. OpenAlex/Semantic Scholar citation-list requests returned 429, unauthenticated code search returned 401, and the journal PDF returned 401. Loogle, LeanSearch and Reservoir coverage was not completed. These limits are not no-hit evidence. No worldwide novelty, openness or priority is claimed; no broad literature enumeration is implied.

Physical identification of the $N=2$ marked-stage model, full stochastic-process/renewal construction and empirical correspondence remain outside the formal assertion.
