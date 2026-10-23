---
slug: johnston-russo-sikora-2025-antidistinguishability-tightness
bibkey: johnstonrussosikora2025antidistinguishability
doi: 10.22331/q-2025-02-04-1622
url: https://arxiv.org/abs/2311.17047v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.result
---

# Non-tightness of the antidistinguishability overlap bound

## Problem

Johnston, Russo and Sikora, “Tight bounds for antidistinguishability and circulant sets of pure quantum states”, Quantum 9, 1622, arXiv:2311.17047v2, Section 6, asks:

> We still do not know whether or not Corollary 5.4 is tight when n ≥ 5.

Corollary 5.4 guarantees antidistinguishability when every distinct-state overlap is at most $c_n=\sqrt{(n-2)/(2(n-1))}$. Issue #15573 specifies the finite-dimensional unit-state convention and the squared-overlap margin. The settlement proves non-tightness for every $n\ge10$.

### Statement echo

| Source condition | Formal counterpart | Scope |
| --- | --- | --- |
| A set of $n$ pure states | $\psi:\operatorname{Fin}(n)\to\mathbb C^d$ | Every finite ambient dimension $d$ |
| Normalized states | $\|\psi_i\|=1$ for every $i$ | No dimension or distinctness restriction |
| POVM with zero probability for the corresponding state | `IsAntidistinguishable` | Positive semidefinite effects, identity sum, zero Born quadratic form |
| Tightness of the overlap guarantee | `IsTight` | Every positive squared-overlap margin admits a non-antidistinguishable family |
| Positive source cap | $c_n>0$ for $n\ge10$ | Squaring reparametrizes positive margins: $(c_n+\varepsilon)^2-c_n^2>0$ and $\sqrt{c_n^2+\delta}-c_n>0$ |
| Non-tightness | `claim` and `result` | Every $n\ge10$; cases $5\le n\le9$ remain open |

The positive margin $\delta_n$ is additional proved information, rather than a hypothesis strengthening the source question. The displayed finite-dimensional POVM definition is literal. The Gram construction is reused as `Matrix.gram`, and the squared Frobenius norm is reused as `RHLinalg.frobSq`.

## Motivation

`D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.result` proves the universal non-tightness claim. Its quantitative theorem gives a uniform guarantee for arbitrary unit-state ensembles, including non-circulant Gram matrices.

## Gap

The literature screen recorded in #15573 covers the source, its later restatement and citing works. It found no settlement within that scope. The revised Hillery–Andersson–Puthoor published body is ASSUMED-UNVERIFIED: its accepted manuscript is embargoed until 2026-10-17. The previously available arXiv body does not settle the arbitrary-ensemble guarantee.

## Route

The proof constructs a POVM from an incoherent positive semidefinite Gram decomposition (`AntidistinguishabilityGram.incoherent_gram_antidistinguishable`). Closedness and separation of that cone (`IncoherentCone.incoherent_closed`, `incoherent_separation`) combine with coordinate-hyperplane positivity and its reciprocal spectral budget (`LocallyPositiveSpectrum.local_psd_kernel_eq_zero`, `local_psd_negIndex`, `local_psd_reciprocal_budget`). The source spectral sufficient condition is `AntidistinguishabilitySpectrum.spectral_sufficient_antidistinguishable`.

Failure of the spectral condition constrains the fourth eigenvalue and rank-three residual (`AntidistinguishabilityOverlapNonTight.spectral_failure_fourth_bound`, `topThree_failure_distance`). Squaring the entries of the rank-three approximation gives rank at most nine (`topThree_square_rank`). A full-rank equal-overlap matrix has a positive distance from every such matrix (`OverlapLowRankDistance.low_rank_distance_lower`, `equalOverlap_low_rank_distance`). The quantitative spectral condition then follows by contradiction.

## Falsifier

A unit-state family with $n\ge10$, squared overlaps at most $c_n^2+\delta_n$, and no corresponding POVM would contradict `quantitative_antidistinguishability`. A source clause not represented by the statement echo would invalidate the claimed correspondence. A prior publication establishing this exact arbitrary-ensemble improvement would invalidate a priority claim; the bounded literature screen does not establish priority beyond its checked scope.

## Evidence

### Kernel-checked declarations

The five supporting modules and `AntidistinguishabilityOverlapNonTight` carry the formal proof. `quantitative_antidistinguishability` has the complete unit-norm and overlap hypotheses. `result` proves `claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

### Experiment

[The numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/d3fce0cdf5066a77d2084a1ab9b8ec68018f674e/docs/reports/johnston-russo-sikora-2025-antidistinguishability-overlap) is pinned to commit `d3fce0cdf5066a77d2084a1ab9b8ec68018f674e`. Command: `python3 check.py`, exit 0, final reading `bad= 0`. Script SHA-256: `96e3a911084ab29d6c727a6842e1d734be97b120845bbec1cf10ef6079830610`.

Computed scope: the Lemma A1 identity on 60 random rational spectra; the final inequality's closed form and strict sign for $10\le n\le400$; rank exactly nine for one random rank-three complex Gram matrix at $n=20$; and 747 admissible Gram matrices at $n=10,12,16$, with zero spectral-condition violations. The experiments establish those readings only; the uniform theorem is supplied by Lean.

## Triage

### What the settlement shows

**Mechanism — kernel-checked.** Write $\Delta=\|G\|_F^2-n^2/2$. Under spectral failure, `AntidistinguishabilityOverlapNonTight.topThree_failure_distance` gives $\|G-G_3\|_F\le\sqrt{(n-3)\Delta}/2$. `norm_square_frob_distance_le` gives $\||G|^2-|G_3|^2\|_F\le\sqrt{(n-3)\Delta}$, and `topThree_square_rank` gives rank at most nine for $|G_3|^2$. `OverlapLowRankDistance.equalOverlap_low_rank_distance` gives its distance lower bound from $H_0=(1-c_n^2)I+c_n^2J$. The coefficient satisfies $1-c_n^2>1/2$ by `cSq_lt_half`; this is the lower spectral bound used in the distance argument. These estimates force the spectral sufficient condition under the improved overlap cap.

**Quantitative statement — kernel-checked.** `AntidistinguishabilityGram.delta` defines

$$\delta_n=\frac{n-9}{16n(n-1)(n-3)}.$$

`OverlapLowRankDistance.delta_pos` proves positivity for $n\ge10$. `AntidistinguishabilityOverlapNonTight.quantitative_antidistinguishability` proves antidistinguishability whenever $|\langle\psi_i,\psi_j\rangle|^2\le c_n^2+\delta_n$. `result` therefore proves non-tightness for every $n\ge10$.

**Remaining finite cases — open.** The source question for $n=5,6,7,8,9$ is not settled by these declarations.

**Asymptotic threshold — proved in prose only.** Define $T_n$ as the infimum of the largest absolute overlap among non-antidistinguishable unit-state families. For any fixed $0<\varepsilon<1$, suppose all pairwise absolute overlaps are at most $1-\varepsilon$. If the family is non-antidistinguishable, the contrapositive of the spectral sufficient condition gives $\sum_k\sqrt{\lambda_k}<2\sqrt n$. Choose an integer $r\ge64/\varepsilon$. For $n>r$, put $s_k=\sqrt{\lambda_k}$ in decreasing order. Then $s_r\le(\sum_k s_k)/r$ and

$$\sum_{k\ge r}\lambda_k\le s_r\sum_{k\ge r}s_k<\frac{4n}{r}.$$

The singular-value decomposition of the state synthesis map identifies its squared singular values with the Gram eigenvalues; zero padding covers ambient dimension below $r$. Projection onto the top $r$ state-space spectral directions has total squared residual less than $4n/r$. At least half the states have squared residual at most $8/r\le\varepsilon/8$. Any two original states have Euclidean distance at least $\sqrt{2\varepsilon}$ because the real part of their inner product is at most its absolute value. Their projections therefore have distance at least $\sqrt{2\varepsilon}-2\sqrt{\varepsilon/8}=\sqrt{\varepsilon/2}$. They lie in the unit ball of $\mathbb R^{2r}$. Disjoint balls of radius $\sqrt{\varepsilon/2}/2$ centered at those projections lie in the ball with radius $1+\sqrt{\varepsilon/2}/2$; comparison of Euclidean volumes bounds their number by $(1+2\sqrt{2/\varepsilon})^{2r}$. Thus $n/2$ is bounded by this number. For larger $n$ every such family is antidistinguishable, so $T_n\ge1-\varepsilon$. Identical unit states are non-antidistinguishable and have maximum overlap one, so $T_n\le1$. Hence $T_n\to1$. This argument is a prose derivation; no Lean declaration in this delivery states the limit.

**Literature boundary — ASSUMED-UNVERIFIED.** The revised Hillery–Andersson–Puthoor body remains unchecked for the stated embargo reason. The literature scope and this boundary are recorded in #15573.

**Numerical readings — computed.** The pinned experiment entry in Evidence supplies exactly the finite scopes listed there, including `bad= 0`. Its rank-nine reading is for one sampled matrix; the universal rank-at-most-nine bound is the separate kernel-checked theorem `topThree_square_rank`.

The source's circulant necessity statement and its sharp Frobenius bound are unaffected mathematical results. The non-tightness proof supplies an improved sufficient overlap guarantee for arbitrary ensembles; it does not claim a full classification of non-antidistinguishable sets.

### Escape audit

The escape audit is unfinished under [#15730](https://github.com/the-omega-institute/trureturing/issues/15730). Dimension-dependent matrices, proof-dependent spectral maps, guarded inequalities and existential POVM decompositions still require faithful source-family reconstructions, lawful template readouts, selection coordinates, whole-family variation, slot sensitivity and observational-dependence evidence. The settling Reg mirror is a typed candidate; compilation alone does not establish a complete registration. The settling candidate decodes as `state=declared_unresolved` with `IE-C050 ClosedTruthReadout`, diagnostic `unclassified_form`, rule `source.residual_requires_open`; it has no source-bound escape certificate. The concrete gap is the exact dependent source-family reconstruction, lawful template readout, selection coordinates, whole-family variation, slot sensitivity and observational dependence evidence for the theorem family. The unfinished audit is tracked in [#15730](https://github.com/the-omega-institute/trureturing/issues/15730).

## ASSUMED-UNVERIFIED

The revised Hillery–Andersson–Puthoor published body is not checked. The asymptotic threshold derivation is proved in prose, with Lean formalization open. Escape registration evidence is incomplete as specified in #15730. No exhaustive literature-priority assertion is made.
