---
slug: tavakoli-abbott-renou-gisin-brunner-2018-multipartite-partial-tightness
bibkey: tavakoliabbottrenougisinbrunner2018sdi
doi: 10.1103/PhysRevA.98.052333
url: https://arxiv.org/abs/1805.00377v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.result
---

# Multipartite partial tightness of the entangled-measurement bound

## Problem

A. Tavakoli, A. A. Abbott, M.-O. Renou, N. Gisin and N. Brunner, *Semi-device-independent characterisation of multipartite entangled states and measurements*, arXiv:1805.00377v1 (Phys. Rev. A 98, 052333, 2018), Appendix C, “Partial tightness of Eq. (10) for two parties”, states:

> We leave it as an open question whether a similar partial tightness result holds in the more general $n$ partite case.

This quotation is from line 497 of the source file `SDI_manuscript.tex`, read from the versioned arXiv e-print. Lines 474–496 give the bipartite construction attaining Eq. (10) with $k=dm$ fully separable measurement operators for every $m=0,\ldots,d$.

In the source's game, each of $n$ parties receives independent uniform inputs $x_j,y_j\in\mathbb Z_d$, transforms its share of a state, and sends a $d$-dimensional system to a joint measurement. The winning output has $b_1=\sum_jx_j$ and $b_j=y_j-y_1$ for $j\ge2$, modulo $d$. The score is $\mathcal A_{n,d}=d^{-2n}\sum_{\mathbf x,\mathbf y}P(C(\mathbf x,\mathbf y)\mid\mathbf x,\mathbf y)$ (source lines 137–158). An operator is fully separable when it is a sum of positive product operators (line 258). Result 2, Eq. (10), states that at least $k$ fully separable operators imply $\mathcal A_{n,d}\le(d^n-k+k/d)/d^n$ (lines 265–272).

Issue [#23843](https://github.com/the-omega-institute/trureturing/issues/23843) fixes the affirmative reading: for all natural $n,d\ge2$ and $m\le d^{n-1}$, there exist a state on $(\mathbb C^d)^{\otimes n}$, local unitary encodings and a projective measurement with exactly $dm$ fully separable operators and score $(d^n-dm+m)/d^n$. This is proved.

## Motivation

Result 2 converts a measured game score into a lower bound on the number of entangled measurement operators. Attainment determines whether its upper bound can be lowered at a specified separable-outcome count. The question asks whether the bipartite examples extend to arbitrary party number while retaining both the exact count and the score. The [literature note](../Library/Observer/tavakoliabbottrenougisinbrunner2018sdi.md) records the source definitions and locators.

## Gap

Issue #23843 records the bounded literature check before any Lean:

- The orchestrator reports that arXiv lists only v1; whether the journal version retains the question is `ASSUMED-UNVERIFIED`.
- The orchestrator reports 31 INSPIRE citing records, with 29 available arXiv source packages searched for “partial tight”, “partially tight” and “tightness of”. The two hits, arXiv:2202.13131 and arXiv:2610.20725, concern other bounds; the search reports no settlement of this question.
- The search seat reports OpenCitations, Semantic Scholar, MathDB and formal-conjectures searches with no settlement.
- The orchestrator reports no prior repository issue for the arXiv identifier, Tavakoli or the semi-device-independent title terms.

`not-found-in-searched-scope`. These reports do not establish exhaustive novelty or priority.

## Route

Use zero-based party indices, as in Lean. Throughout the construction $n,d\ge2$, providing the nonzero instances used by the definitions. A sector label is $r\in(\mathbb Z_d)^n$ with $r_0=0$. Write $e(t,r)=|t+r_0,\ldots,t+r_{n-1}\rangle$ and $g(a,r)=d^{-1/2}\sum_{t\in\mathbb Z_d}\chi(at)e(t,r)$, where $\chi$ is the standard additive character. For a finite set $R$ of sector labels and an outcome $b$, put $a=b_0$ and replace its zeroth coordinate by zero to obtain $r$. Choose $v_b=e(a,r)$ when $r\in R$, and $v_b=g(a,r)$ otherwise; the operator is $p_b=|v_b\rangle\langle v_b|$.

1. **Choose the sectors.** For nonzero $n,d$, $n\ge2$ and natural $m\le d^{n-1}$, `choose_sectors` supplies a finite $R$ with $|R|=m$ and $r_0=0$ for every $r\in R$. Its counting argument identifies such labels with functions on the remaining $n-1$ party indices.
2. **Measurement and state.** For $n,d\ge2$, any finite $R$ and any outcomes $b,c$, `selected_orthonormal` gives $\langle v_b,v_c\rangle=\delta_{bc}$; `sector_measurement`, under the same dimension bounds and for any finite $R$, proves that the projectors form a complete projective measurement. For $n,d\ge2$, `ghz_density` proves that $|g(0,0)\rangle\langle g(0,0)|$ is a density matrix. For arbitrary $n$ and nonzero $d$, `encodings_unitary` proves that every local encoding $Z^xX^y$ is unitary.
3. **Exact separability.** For nonzero $n,d$, a vector $v$ satisfying $\langle v,v\rangle=1$, and a fully separable projector $|v\rangle\langle v|$, `rankOne_separable_product` expresses $v$ as a product of local vectors. For $n,d\ge2$, every $a\in\mathbb Z_d$ and every sector label $r$ with $r_0=0$, `fourier_not_product` excludes such a product expression for $g(a,r)$: the nonzero amplitudes at $e(0,r)$ and $e(1,r)$ violate the product-amplitude identity obtained by swapping their zeroth coordinates, since a swapped string lies outside the sector. For $n,d\ge2$, any finite $R$ and any $b$, `selected_separable_iff` therefore identifies full separability exactly with membership of the outcome's sector in $R$. For $n,d\ge2$ and finite $R$ whose labels all satisfy $r_0=0$, `sector_separability_count` gives exactly $d|R|$ fully separable outcomes.
4. **Score.** For $n,d\ge2$ and arbitrary input strings $x,y$, `encoded_ghz` proves that the tensor product of the encodings sends $g(0,0)$ to a scalar of squared modulus one times $g(\sum_jx_j,r)$, with $r_j=y_j-y_0$. For $n,d\ge2$, any finite $R$ and arbitrary $x,y$, `winning_probability` gives winning probability $1/d$ when this sector lies in $R$ and $1$ otherwise. For $n,d\ge2$ and finite $R$ with every label's zeroth coordinate zero, `sector_score` averages these probabilities to $(d^n-d|R|+|R|)/d^n$. Substituting $|R|=m$ gives `result : claim`.

## Falsifier

An affirmative construction must satisfy the source's winning condition, measurement normalization and full separability definition simultaneously. The module's definitions make these requirements explicit:

- `jointIndex n d` is the function space $\mathrm{Fin}(n)\to\mathbb Z_d$; `winningOutcome` is the source's sum-and-difference string with parties reindexed from zero.
- `score` is the uniform average of the real part of $\operatorname{Tr}(U\rho U^\dagger p_{C(x,y)})$, with $U$ the product matrix whose entries are products of local entries. Positivity, trace one and local unitarity are conclusions of `claim`, rather than assumptions hidden in the score definition.
- `IsFullySeparable` requires a finite sum of products of positive semidefinite local matrices. `claim` counts every outcome satisfying this predicate, including any unselected outcome that might admit a different separable decomposition; the proof excludes those decompositions as well.
- `IsProjectiveMeasurement` requires each outcome operator to be self-adjoint and idempotent and their sum to be the identity. `claim` does not require rank one, although the proof constructs rank-one operators.

The result is an attainment statement at $k=dm$. It neither proves Result 2's upper bound for arbitrary strategies nor answers attainment when $k$ is not divisible by $d$.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.lean.json`.

Declaration statements:

- `result`: `sha256:38c754e0187e0e6c8eb7a7f5675be13288da4842cfe99320478d88fb4d328d3f`;
- `claim`: `sha256:e53deee53b9b6cffbafe1a4362a011c0e6afdda5c63e8d93a9614f59e8710b00`.

## Triage

Tier 1 open question of a 2018 Phys. Rev. A paper, preregistered in issue #23843 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n,d,m$ with $n\ge2$, $d\ge2$ and $m\le d^{n-1}$, there exist a positive semidefinite matrix $\rho$ of trace one on the joint coordinates, local unitary matrices for every party and input pair, and a projective measurement indexed by all joint outcomes, with exactly $dm$ fully separable outcome operators and score $(d^n-dm+m)/d^n$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Decisive structure.* For $n,d\ge2$, relative coordinates distinguish $d^{n-1}$ sectors, while each sector retains one common coordinate with $d$ possible values. In the Route, `selected_orthonormal` and `sector_measurement` apply to every finite $R$ under these dimension bounds, and `sector_separability_count` and `sector_score` additionally require every label in $R$ to have zeroth coordinate zero. Thus the proof permits any subset of valid sectors, rather than requiring an interval or an algebraically special subset. The resulting score and separability count depend only on its cardinality. The formal existence claim includes composite $d$ as well as prime $d$.
- *Endpoints and sharpness.* Substitution in the proved score gives $1$ at $m=0$ and $1/d$ at $m=d^{n-1}$. For $m<d^{n-1}$, increasing $m$ by one changes the score by $-(d-1)/d^n$ and the separable count by $d$. The witnesses exclude any strictly smaller universal upper bound at these counts. Combined with the source's Result 2, they identify the optimal score for strategies with at least $dm$ fully separable operators; that universal upper bound is an external premise, not a theorem of this module.
- *Neighbouring question.* Attainment at counts not divisible by $d$ remains open in this settlement. For $n,d\ge2$ and $r_0=0$, the displayed vector formula gives $|\langle e(t,r),g(a,r)\rangle|^2=1/d>0$ for every $a,t$. Replacing just one Fourier vector by a computational vector while retaining another Fourier vector in the same sector therefore destroys orthogonality. This explains why the construction switches whole sectors; it does not exclude different constructions for the remaining counts.
- *Effect on the source.* Appendix C's bipartite attainment extends to all $n\ge2$ at the stated multiples of $d$. The measurement-entanglement interpretation of Result 2 therefore has attaining examples at those counts. The source presents its other results independently of this question: the settlement supplies no proof of its extractable-GHZ-fraction conjecture (lines 233–240), no biseparable-measurement extension of Result 2, and no answer to the dimension-witness, cryptographic or self-testing questions in the conclusion (lines 317–322).

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The INSPIRE citation listing, the 29-package keyword search, the search seat's database searches and the repository issue searches are reports attributed in #23843 and have not been independently reproduced. The journal text has not been read; retention of the question there is `ASSUMED-UNVERIFIED`. The verbatim question and the source formulas used here are checked against arXiv:1805.00377v1.

The statements grouped under “Argued, not formalized” are explanatory arguments, arithmetic consequences or comparisons with the source, not additional compiled claims. Result 2's universal upper bound, the source's other conjectures and certification results, and attainability for counts not divisible by $d$ are not formalized by this module. The construction uses finite-dimensional matrices and unitary encodings; it makes no experimental implementation or noise-robustness claim.
