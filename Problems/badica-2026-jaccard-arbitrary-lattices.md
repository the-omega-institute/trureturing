---
slug: badica-2026-jaccard-arbitrary-lattices
bibkey: badica2026jaccardlattices
doi: 10.48550/arXiv.2608.18194
url: https://arxiv.org/abs/2608.18194v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.result
---

# Bădică–Bădică: the Jaccard triangle inequality on arbitrary lattices

## Problem

C. Bădică and A. Bădică, *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*, arXiv:2608.18194v1, Section 8, asks whether the generalized Jaccard distance

$$d_{f,J}(A,B)=1-\frac{f(A\wedge B)}{f(A\vee B)}$$

satisfies the triangle inequality on arbitrary lattices under either of two sets of hypotheses: strict positivity, monotonicity, supermodularity and log-submodularity of $f$; or strict positivity, monotonicity and supermodularity of both $f$ and $1/f$. These are the second and fourth questions, preregistered in [#20617](https://github.com/the-omega-institute/trureturing/issues/20617).

### Statement echo

| source clause | Lean counterpart |
| --- | --- |
| Arbitrary lattice, without distributivity or relative complementation | Universe-polymorphic $L$ with only a `Lattice L` instance in `claim` and `claimSufficiency` |
| Strict positivity | `IsStrictlyPositive`: $\forall X,\ 0<f(X)$ |
| Monotonicity | Mathlib `Monotone f` |
| Supermodularity | `IsSupermodular`: $f(X)+f(Y)\le f(X\vee Y)+f(X\wedge Y)$ |
| Submodularity and log-submodularity | `IsSubmodular` is the reversed sum inequality; `IsLogSubmodular` is strict positivity conjoined with submodularity of $\log\circ f$ |
| Equation (17) | `jaccardDist` is the literal real-valued meet-over-join quotient above |
| Second question | `claim`, proved by `result` |
| Fourth question, with Theorem 4's positivity and monotonicity | `claimSufficiency`, proved by `resultSufficiency` |

The definitions preserve the preregistered source expressions literally. The repeated strict-positivity hypothesis inside log-submodularity is part of that convention. The generic Mathlib `IsStrictlyPositive` has a corresponding pointwise specialization; its use does not replace the binding source definition.

## Motivation

Theorem 2 assumes a relatively complemented distributive lattice. Both formal statements remove those structural restrictions for the triangle inequality. Theorem 4 states necessary conditions on an arbitrary lattice; the fourth question asks whether they suffice.

## Gap

The Section 8 symmetric-difference question for submodular valuations remains open in this delivery. Neither separation of points nor a full `MetricSpace` instance is asserted. The necessity direction of Theorem 4 is literature-attested, rather than formalized in this module.

The literature screen recorded in #20617 found no settlement among the arXiv versions, citing-work searches and named formal-conjecture catalogs it checked. OpenAlex and Semantic Scholar citation queries returned HTTP 429. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Put $b=f(B)$, $x=f(A\wedge B)$, $y=f(B\wedge C)$, $z=f(A\wedge C)$, $w=f(A\vee C)$, $p=1/f(A\vee B)$ and $q=1/f(B\vee C)$. Monotonicity and the two supermodularity assumptions give

$$x,y\le b,\qquad p,q\le 1/b,\qquad x+y\le b+z,\qquad p+q\le 1/b+1/w.$$

The triangle inequality reduces to $xp+yq\le 1+z/w$. Interchanging the two terms permits $q\le p$. If $b\le z$, then

$$xp+yq\le b(p+q)\le 1+b/w\le 1+z/w.$$

If $z\le b$, then

$$xp+yq=x(p-q)+(x+y)q\le (b-z)p+z(p+q)\le 1+z/w.$$

This proves `resultSufficiency`. For the second question, write $r=f(X)$, $s=f(Y)$, $m=f(X\vee Y)$ and $t=f(X\wedge Y)$. Supermodularity gives $r+s\le m+t$; log-submodularity and positivity give $mt\le rs$. Thus

$$r^{-1}+s^{-1}=\frac{r+s}{rs}\le\frac{m+t}{rs}\le\frac{m+t}{mt}=m^{-1}+t^{-1}.$$

The reciprocal is supermodular, so `result` follows. All helper proofs use order comparisons, case distinctions and algebraic normalization; their classification is bind-only under the open-problem-resolution admission basis.

## Falsifier

A counterexample would be a lattice, a strictly positive monotone valuation satisfying one of the two exact hypothesis sets, and a triple violating the triangle inequality. The formal theorems quantify over every such triple. The numerical checks test only the finite scopes specified below and provide no universal proof.

## Evidence

The source module is `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.lean`. Its public theorems are `D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices.resultSufficiency` and `D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices.result`. The unique `OpenProblemResolutionClaim` marks `result` as Proved. The toolchain is `leanprover/lean4:v4.35.0` and pinned Mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`. Both statements have the admission basis `open-problem-resolution (#20617; Proved)`, generality I and utility none.

The escape audit is unfinished for both public theorems: [#21649](https://github.com/the-omega-institute/trureturing/issues/21649). A dependent source arena, faithful reconstruction and equivalence bridge, whole-family variation, sensitivity and observational-dependence evidence remain uncompiled. No Reg mirror or validated registration is asserted.

The consistency check is in [the experiments repository, pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/2cfc99876ed22f8f3e4e64efdfb58443745f9091/docs/reports/badica-2026-jaccard-arbitrary-lattices), file `check.py`, SHA-256 `d68ad0712f308c730d0bbb76af6ce2482776e6eba0e448f779e92ec0d147cbb9`. The command `git -C /Users/auric/trureturing-experiments show 2cfc99876ed22f8f3e4e64efdfb58443745f9091:docs/reports/badica-2026-jaccard-arbitrary-lattices/check.py | /opt/homebrew/bin/python3 -` exits 0. It checks every triple on the Boolean lattice $2^3$ for $f(S)=|S|+1$; samples 200,000 positive valuations on each of $N_5$ and $M_3$ for Theorem 4; and samples 400,000 valuations on each lattice for the log-submodular claim. Exactly 1,059 and 1,279 valuations pass the respective triangle tests, with zero failures of the necessary conditions; exactly 1,041 and 977 valuations satisfy the claim's hypotheses, with zero triangle violations. Its role is consistency and source fidelity. The Lean proof establishes the unbounded statements.

## Triage

| item | status | evidence kind and scope |
| --- | --- | --- |
| Second Section 8 question | proved | Kernel-checked `result`, with the exact `claim` telescope |
| Fourth Section 8 question | proved | Kernel-checked `resultSufficiency`, with the exact `claimSufficiency` telescope |
| Decisive mechanism: two supermodularity applications and monotonicity through $B$ | proved | Proved in prose in Route; implemented in `resultSufficiency` and its private scalar helpers |
| Arbitrary-lattice scope without complements or distributivity | proved | Kernel-checked public statements require only `Lattice L` |
| Characterization with Theorem 4 | proved | Proved in prose: the literature-attested necessity direction and kernel-checked sufficiency give equivalence for strictly positive valuations; necessity is not kernel-checked here |
| Symmetric-difference formula under submodular valuations | open | Third Section 8 question; absent from both formal claims |
| Separation and full metric structure | open | Neither public theorem asserts separation or a `MetricSpace` instance |
| Boolean, $N_5$ and $M_3$ fidelity checks | computed | Pinned experiment and exact counts in Evidence; finite samples only |
| Uniform extension of the experiment | open | No inference from the samples; the two universal triangle claims instead have kernel proofs |
| Host-resource and process-safety scope | computed | Scoped verification uses serialized Lean invocations; no host-resource retry, process signal or competing implementation seat is part of this delivery |
| Prior exposure | computed | `repo-prior-exposed`; source conventions and mathematical proof are disclosed in #20617 |
| Literature status | open | Searched-scope result in Gap; completeness `ASSUMED-UNVERIFIED` |

### What the settlement shows

**Proved, kernel-checked:** `resultSufficiency` permits arbitrary lattices and replaces log-submodularity by supermodularity of the reciprocal. `result` settles the source's original positive monotone supermodular and log-submodular formulation.

**Proved in prose:** combining the source's Theorem 4 with `resultSufficiency` characterizes the triangle inequality, for strictly positive $f$, by monotonicity and supermodularity of $f$ and $1/f$. This uses a literature-attested necessity theorem; the module proves only sufficiency. No additional theorem from the source is needed to prove either delivered result.

**Open:** the symmetric-difference question, separation, sharpness beyond the stated assumptions and further relaxations of strict positivity are not settled. The source's earlier triangle theorem gains arbitrary-lattice sufficiency; no full metric claim follows from this delivery alone.

## ASSUMED-UNVERIFIED

Literature completeness, the blocked citation-index queries and the source's necessity theorem as Lean evidence remain unverified. Model-family distinctness of producing carriers is not established. The escape registrations remain unfinished under #21649.
