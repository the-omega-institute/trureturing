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

A. Tavakoli, A. A. Abbott, M.-O. Renou, N. Gisin and N. Brunner, *Semi-device-independent characterisation of multipartite entangled states and measurements*, arXiv:1805.00377v1 (Phys. Rev. A 98, 052333, 2018), Appendix C, `SDI_manuscript.tex`, line 497:

> We leave it as an open question whether a similar partial tightness result holds in the more general $n$ partite case.

The source text at lines 474–496 concerns attainment of Eq. (10) for two parties with exactly $k=md$ fully separable measurement operators, for $m=0,\ldots,d$. Result 2, lines 265–272, bounds the average winning probability by $\mathcal A_{n,d}\le(d^n-k+k/d)/d^n$ whenever at least $k$ of the $d^n$ measurement operators are fully separable, for any shared state and local transformations in the source's scenario.

The game has uniformly distributed inputs $\mathbf x,\mathbf y\in(\mathbb Z_d)^n$ and winning output $C_1=\sum_jx_j$, $C_j=y_j-y_1$ for $j\ge2$, all modulo $d$; $\mathcal A_{n,d}=d^{-2n}\sum_{\mathbf x,\mathbf y}P(C(\mathbf x,\mathbf y)\mid\mathbf x,\mathbf y)$ (lines 137–159). The definitions and source locator are also in [the literature note](../Library/Observer/tavakoliabbottrenougisinbrunner2018sdi.md).

Issue [#23843](https://github.com/the-omega-institute/trureturing/issues/23843) fixes the affirmative reading: for every natural $n,d\ge2$ and $0\le m\le d^{n-1}$, there exist a density matrix on $(\mathbb C^d)^{\otimes n}$, local unitary encodings and a projective measurement with exactly $dm$ fully separable outcome operators and score $(d^n-dm+m)/d^n$. This is proved.

## Motivation

Result 2 turns an observed score into a lower bound on the number of entangled measurement operators. Attaining its upper bound with a specified separability count shows where that numerical threshold is sharp. The Appendix C question asks whether the bipartite attainment pattern extends to more parties.

## Gap

Issue #23843 records the bounded literature check:

- The arXiv v1 source contains the question; the downloaded `SDI_manuscript.tex` has MD5 `1888cb2a743d8cbcda8d1f130274799b` and confirms the quotation at line 497.
- The preregistration author reports an INSPIRE listing of 31 citing records and searches of 29 available arXiv sources for “partial tight”, “partially tight” and “tightness of”; the two reported hits, arXiv:2202.13131 and arXiv:2610.20725, concern other bounds.
- The preregistration reports no settlement in its OpenCitations, Semantic Scholar, MathDB and formal-conjectures searches, and no prior repository issue found by its paper-specific queries.

`not-found-in-searched-scope`. The citation searches and journal-version reading remain subject to the limits below.

## Route

All steps below use natural $n,d\ge2$, hence nonzero $n,d$. Write $J=(\mathbb Z_d)^n$ with party indices starting at zero, and restrict sector labels $r\in J$ to $r_0=0$. Put $e(t,r)=|t,t+r_1,\ldots,t+r_{n-1}\rangle$ and $g(a,r)=d^{-1/2}\sum_{t\in\mathbb Z_d}\chi(at)e(t,r)$, where $\chi$ is the standard additive character of $\mathbb Z_d$.

1. **Sectors and measurement.** `sector_coordinates` represents every $i\in J$ by $t=i_0$ and $r_j=i_j-i_0$; `sectorPoint_injective`, for labels $r,s$ with $r_0=s_0=0$, makes this representation unique. Given $m\le d^{n-1}$, `choose_sectors` supplies a finite set $R$ of $m$ labels, all with zeroth coordinate zero. For outcome $b$, set $a=b_0$ and let $r$ be $b$ with its zeroth coordinate replaced by zero. Choose $v_b=e(a,r)$ if $r\in R$, and $v_b=g(a,r)$ otherwise. `sector_basis`, for arbitrary $a,c\in\mathbb Z_d$ and labels $r,s$ with $r_0=s_0=0$, proves $\langle g(a,r),g(c,s)\rangle=1$ when $(a,r)=(c,s)$ and zero otherwise. For any finite $R\subseteq J$, `selected_orthonormal` proves orthonormality of the chosen vectors, and `sector_measurement` proves that $p_b=|v_b\rangle\langle v_b|$ is a projective measurement.
2. **Exact separability count.** `computational_projector_separable` makes each projector onto $e(t,r)$ fully separable, for every $t\in\mathbb Z_d$ and $r\in J$. For a vector $v$ with $\langle v,v\rangle=1$ whose rank-one projector is fully separable, `rankOne_separable_product` expresses $v(i)$ as a product of one-party amplitudes. For arbitrary $a\in\mathbb Z_d$ and $r$ with $r_0=0$, `fourier_not_product` excludes such a product representation of $g(a,r)$: exchanging the zeroth coordinates of the sector strings at $t=0$ and $t=1$ gives the product-amplitude identity a nonzero left side and a zero right side. For any finite $R\subseteq J$ and any outcome $b$, `selected_separable_iff` therefore identifies full separability exactly with membership of its sector in $R$. When every $r\in R$ satisfies $r_0=0$, `sector_separability_count` gives exactly $d|R|=dm$ fully separable operators.
3. **State, encodings and score.** `ghz_density` proves that $|g(0,0)\rangle\langle g(0,0)|$ is a density matrix, and `encodings_unitary` proves unitarity of the local clock-shift encodings $Z^{x_j}X^{y_j}$ for every party and input. For every $x,y\in J$, `encoded_ghz` identifies the encoded vector as a scalar of squared modulus one times $g(\sum_jx_j,r)$ with $r_j=y_j-y_0$. For any finite $R\subseteq J$ and every $x,y\in J$, `winning_probability` gives winning probability $1/d$ when this $r$ belongs to $R$, and $1$ otherwise. With the additional condition $r_0=0$ for every $r\in R$, `sector_score` averages these probabilities to $(d^n-d|R|+|R|)/d^n$. Substituting $|R|=m$ supplies all the witnesses in `result : claim`.

## Falsifier

The attainment would not answer the source question if the formal score, separability predicate or admissible witnesses differed from the source's. The module uses:

- `jointIndex n d = Fin n → ZMod d`, with `winningOutcome` equal to the source's sum-and-difference condition under zero-based party indexing;
- `score`, the uniform average of the real part of the trace of the locally conjugated density matrix against the winning outcome operator;
- `IsDensity`, positive semidefiniteness and trace one, and local matrices belonging to `Matrix.unitaryGroup` for every party and input;
- `IsFullySeparable`, a finite sum of tensor products of positive semidefinite local matrices, with no bound on the number of summands;
- `IsProjectiveMeasurement`, self-adjoint idempotent outcome operators summing to the identity, and an exact cardinality of fully separable outcomes.

The witnesses thus belong to the source's allowed class of local transformations and joint measurements. The formal conclusion is direct existence with a finite-sum score equality; it does not assert a supremum or formalize Result 2's universal upper bound.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.lean.json`.

Declaration statements:

- `result`: `sha256:38c754e0187e0e6c8eb7a7f5675be13288da4842cfe99320478d88fb4d328d3f`;
- `claim`: `sha256:e53deee53b9b6cffbafe1a4362a011c0e6afdda5c63e8d93a9614f59e8710b00`.

## Triage

Tier 1 open question of a 2018 paper, preregistered in issue #23843 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n,d,m$ with $n\ge2$, $d\ge2$ and $m\le d^{n-1}$, there exist a density matrix $\rho$ on $(\mathbb C^d)^{\otimes n}$, a unitary encoding for every party and pair of local inputs, and a projective measurement with exactly $dm$ fully separable outcome operators, such that `score` equals $(d^n-dm+m)/d^n$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Decisive mechanism.* For $n,d\ge2$ and a finite set $R$ of labels with $r_0=0$, `sector_measurement`, `selected_separable_iff`, `sector_separability_count` and `sector_score` permit the basis choice independently in each sector. Replacing a Fourier sector by its computational basis adds $d$ fully separable outcomes and reduces the score by $(d-1)/d^n$: subtracting the two `sector_score` expressions gives this difference whenever a previously unselected sector is added to $R$. The loss depends only on the number of selected sectors.
- *Extent and endpoints.* The range of `claim` includes every composite $d\ge2$ as well as prime $d$, with no restriction on $n\ge2$. Substitution of $m=0$ gives score $1$ with no fully separable outcomes; substitution of $m=d^{n-1}$ gives score $1/d$ with all $d^n$ outcomes fully separable. The sector construction changes the count in blocks of $d$. It supplies no necessity argument for divisibility in other constructions, and attainment at counts $k$ not divisible by $d$ remains open here.
- *Sharpness and effect on the source.* Taking the source's Result 2 as an external upper-bound theorem, substitution of $k=dm$ makes its bound equal to the score in `claim`. Any smaller uniform bound at that same count would exclude these admissible witnesses. Thus the affirmative Appendix C reading extends to every $n,d\ge2$ at these counts. The source's Result 1, Result 2 and examples do not assume an affirmative answer to Appendix C; this settlement adds attainment to the independent upper-bound result. The separate conjecture about optimal scores for arbitrary fixed states and extractable GHZ fraction (lines 226–242), and the questions about biseparable measurement operators, dimension witnessing and self-testing (lines 317–322), are not settled by this existence theorem.

## ASSUMED-UNVERIFIED

The bounded literature check in #23843 does not establish exhaustive worldwide novelty or priority. Its INSPIRE citation listing, the 29-source keyword search, the reported interpretation of the two hits, the other literature-database searches and the repository issue searches were not independently reproduced. The journal version was not read; whether it retains the v1 question is unverified. The quotation and its location were checked against the downloaded arXiv v1 TeX.

The source-to-formal identification of local unitary conjugations with allowed transformations is an interpretive bridge, not a separate Lean declaration. Result 2's upper bound for arbitrary allowed states, transformations and measurements is used as a literature result and is not formalized by this module. The deductions in “Argued, not formalized” have no separate compiled declarations; the numerical-computation group asserts no experimental results. Attainment for counts not divisible by $d$, the fixed-state extractable-GHZ-fraction conjecture and the source's other open questions remain outside this settlement.
