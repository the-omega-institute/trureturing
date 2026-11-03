---
slug: debrota-stacey-2019-luders-entropy-saturation-sic
bibkey: debrotastacey2019luders
doi: 10.1103/PhysRevA.100.062327
url: https://arxiv.org/abs/1907.10999v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.result
---

# Entropy saturation of a Lüders MIC channel forces SIC existence

## Problem

J. B. DeBrota and B. C. Stacey, *Lüders channels and the existence of symmetric-informationally-complete measurements*, Phys. Rev. A 100, 062327 (2019), arXiv:1907.10999v2, Section III, “Entropic Optimality”, Conjecture 1 (`lmc.tex`, lines 417–420):

> Equality is achievable in the statement of Theorem
> \ref{avgentropybnd} only if a SIC exists in dimension $d$.

The reference is to Theorem 2 (lines 385–390): every Lüders MIC channel has Haar-averaged pure-input output entropy at most
$B_d=\log(d+1)-\frac{2}{d+1}\log2$, with equality achievable if a SIC exists in dimension $d$.

A MIC is a family $E=(E_i)_{i=1}^{d^2}$ of positive semidefinite complex $d\times d$ matrices, linearly independent over $\mathbb C$, with $\sum_iE_i=I$. Its Lüders channel is
$\mathcal E_E(X)=\sum_i\sqrt{E_i}\,X\sqrt{E_i}$, using the positive square roots. A SIC is a rank-one equiangular MIC. These are the definitions in the source, lines 80–90 and 104–114, also recorded in [the literature note](../Library/Entropy/debrotastacey2019luders.md).

Issue [#25617](https://github.com/the-omega-institute/trureturing/issues/25617) fixes the statement for every positive natural dimension $d$: if a MIC $E$ has Haar-averaged pure-input output entropy $B_d$, then there exists a SIC in dimension $d$. This is the proposition `claim`, proved by `result`.

## Motivation

The source interprets the average output entropy as the typical sharpening of expectations associated with a Lüders measurement. Its Theorem 2 gives SIC channels an optimal value whenever SICs exist. The conjectured converse makes exact attainment of this entropic value another characterization of SIC existence, alongside the source's channel-action and entropy-exchange characterizations. It does not supply an attaining channel in an arbitrary dimension.

## Gap

Issue #25617 records the bounded literature check before any Lean:

- The arXiv v2 source retains the general conjecture; its Postscript (lines 568–587) sketches the unbiased $d=2$ case.
- The search seat reports full-text checks of DeBrota–Stacey (2019, arXiv:1912.07554v3), DeBrota–Fuchs–Stacey (2018, arXiv:1812.08762v5), DeBrota–Love (2021, arXiv:2106.09057), Fuchs–Stacey (2020, arXiv:2012.14375v1), Rastegin (2023, arXiv:2304.14038v2), Jackson (2025, arXiv:2510.13980) and Mitra (2022, arXiv:2201.02578v3) among the citing works, with no settlement of this implication found.
- The issue also records checks of Scott (2006, quant-ph/0604049); Pandey–Paulsen–Prakash–Rahaman (2018, arXiv:1805.04583v3); and Stacey (2023, arXiv:2312.11946), together with web searches for the conjecture and a proof. No general resolution was found in that searched scope.

`not-found-in-searched-scope`. The source reading confirms that the general conjecture is present; the other literature readings remain attributed to the issue's authors.

## Route

Fix $d\ge1$ and $E:\mathrm{Fin}(d^2)\to\mathrm{Mat}_d(\mathbb C)$ satisfying `IsMIC d E`. All saturation steps below also assume `typicalEntropy d E` equals $B_d$. Write $A_i=\sqrt{E_i}$, $P_u=UP_0U^\dagger$ for $U\in U(d)$ and $P_0=|0\rangle\langle0|$, $\rho_u=\mathcal E_E(P_u)$, $\sigma_u=(I+P_u)/(d+1)$ and $c_d=2/(d+1)$. Let $\mu$ be normalized Haar measure on $U(d)$.

1. **Entropy gap.** For every such positive dimension, MIC and unitary $U$, `entropy_gap` gives
   $B_d-S(\rho_u)=D(\rho_u\Vert\sigma_u)+(\operatorname{Re}\operatorname{tr}(P_u\rho_u)-c_d)\log2$.
   Here `sigma_log`, for every positive dimension and unitary, computes $\log\sigma_u=-\log(d+1)I+\log2\,P_u$. For density states $\rho,\sigma$ in positive dimension with $\sigma$ positive definite, `relative_entropy_hs_bound` gives $\frac12\operatorname{Re}\operatorname{tr}((\rho-\sigma)^\dagger(\rho-\sigma))\le D(\rho\Vert\sigma)$. Each $\sigma_u$ is positive definite, so this supplies nonnegativity and rigidity.
2. **Averaged overlap.** For a positive dimension and a MIC, `haar_second_moment` gives
   $a:=\int\operatorname{Re}\operatorname{tr}(P_u\rho_u)\,d\mu(u)=(t+d)/(d(d+1))$, where $t=\sum_i(\operatorname{Re}\operatorname{tr}A_i)^2$.
   For every positive semidefinite matrix $A$, `rank_one_forcing` states $(\operatorname{Re}\operatorname{tr}A)^2\ge\operatorname{Re}\operatorname{tr}(A^2)$. Applied to the $A_i$, this yields $t\ge d$ and $a\ge c_d$.
3. **Saturation and rank.** For a positive dimension, a MIC and exact entropy saturation, `saturation_remainders` gives $t=d$ and $D(\rho_u\Vert\sigma_u)=0$ almost everywhere. The integrated entropy gap is a sum of two nonnegative terms, so both vanish. The individual trace gaps also vanish. `rank_one_from_equality` requires a positive semidefinite, nonzero matrix $A$ and $(\operatorname{Re}\operatorname{tr}A)^2=\operatorname{Re}\operatorname{tr}(A^2)$; it produces a real scalar multiple of a Hermitian idempotent of trace one. MIC independence ensures $A_i\ne0$. Under the same positive-dimension, MIC and saturation hypotheses, `saturation_forces_rank_one` obtains this representation for every effect $E_i$.
4. **Channel rigidity.** Under those same three hypotheses, `saturation_ae_luders_eq_sigma` gives $\rho_u=\sigma_u$ almost everywhere, and `saturation_everywhere_luders_eq_sigma` gives it for every unitary. The latter uses continuity and the positive measure of nonempty open sets. `unitary_pure_ext` requires positive dimension and two complex-linear matrix maps agreeing on every $UP_0U^\dagger$; it identifies the maps. Consequently `depolarizing_identity`, for a positive dimension, MIC and exact saturation, gives $\mathcal E_E(X)=(X+\operatorname{tr}(X)I)/(d+1)$ for every complex matrix $X$.
5. **Coefficient comparison.** `sic_coefficients` requires positive dimension, `IsMIC d E`, representations $E_i=c_i p_i$ with $c_i\in\mathbb R$, $p_i^\dagger=p_i$, $p_i^2=p_i$, $\operatorname{tr}p_i=1$, and the displayed depolarizing identity for every complex matrix. It concludes `IsSIC d E`. Its coefficient comparison in the linearly independent family $E$ obtains $c_i=1/d$ and common effect trace products $1/d^2$ on the diagonal and $1/(d^2(d+1))$ off the diagonal. `route_result_from` uses the rank, depolarizing and SIC implications to choose $E$ itself as the existential witness in `claim`.

## Falsifier

A proof of a different entropy average or a weaker meaning of SIC would not settle the source question. The module uses:

- `IsMIC`: exactly $d^2$ positive semidefinite effects summing to $I$, linearly independent over $\mathbb C$.
- `IsSIC`: a MIC whose effects are real scalar multiples of Hermitian idempotents of trace one, with one common diagonal and one common off-diagonal trace product. A Hermitian idempotent has eigenvalues zero or one, so trace one specifies a rank-one orthogonal projector. Positivity and nonzero MIC effects force the real scalars to be positive.
- `typicalEntropy`: the integral of von Neumann entropy over $UP_0U^\dagger$ with `Measure.haarMeasure` of the top positive compact set of the unitary group, which has total mass one. For a MIC, `ludersState` is the positive-square-root Lüders output; its fallback definition on non-MIC families is outside the theorem's premise.

All logarithms are natural. The statement includes $d=1$ and excludes $d=0$. It requires exact equality of the Haar integral, not agreement on finitely many inputs or approximate equality. It asserts SIC existence conditional on saturation.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.lean.json`.

Declaration statements:

- `result`: `sha256:9e2e41c5e7383f2238d5ecef45766f716665322f33754f9eee23b9853e2356a9`;
- `claim`: `sha256:8d294046fbcde54789c1d08b44ea340a09f33108eb1560afb460d16cefa05c2d`.

## Triage

Tier 1 conjecture of a 2019 paper, retained in arXiv v2 with an unbiased qubit special case sketched in the Postscript, preregistered in issue #25617 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every positive natural dimension $d$ and every MIC $E$ with $d^2$ effects, equality of its Haar-averaged pure-input Lüders output entropy with $\log(d+1)-\frac{2}{d+1}\log2$ implies that there exists a rank-one equiangular MIC in dimension $d$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism.* With $d\ge1$, a MIC and exact entropy saturation, `saturation_remainders` separates a vanishing relative-entropy remainder from a vanishing sum of trace gaps. These force channel rigidity and rank-one effects through the lemmas and hypotheses in Route. The overlap remainder is nonnegative after Haar averaging; the argument does not require its pointwise sign. Thus the proof needs neither an unbiasedness assumption nor group covariance, and its dimensional scope extends beyond the Postscript's qubit case.
- *Sharpness and the source's conclusions.* For a SIC in positive dimension, the source's channel formula (lines 145–151) sends a pure projector $P$ to $(I+P)/(d+1)$. Its eigenvalues are $2/(d+1)$ once and $1/(d+1)$ with multiplicity $d-1$; their entropy is $B_d$. Combining this sufficiency argument with `result` makes attainment of Theorem 2's bound equivalent to SIC existence. The source's Theorem 1 about channel action and Theorem 3 about entropy exchange have separate proofs; this settlement supplies the missing necessity in Theorem 2 without relying on Conjecture 1 to justify either of those other theorems. Their proofs are not additional conclusions of `result`.
- *Why minimality matters to the stronger conclusion.* Starting from a SIC in positive dimension, split any effect $E_i$ into $sE_i$ and $(1-s)E_i$, where $0<s<1$. Their positive square roots contribute $sA_iXA_i+(1-s)A_iXA_i=A_iXA_i$, so the Lüders map and its entropy average are unchanged. The resulting POVM has $d^2+1$ effects and a linear dependence. This shows why an extension asserting that every saturating POVM is itself a SIC would need a minimality condition; it does not challenge the existential conclusion about the dimension.
- *Neighbouring questions.* Existence of a saturating MIC in every dimension, hence universal SIC existence, is not supplied. Quantitative control of distance to a SIC from a small entropy deficit is open here. The module addresses exact saturation and gives no quantitative distance estimate for the measurement effects.

## ASSUMED-UNVERIFIED

The bounded literature check in #25617 does not establish exhaustive worldwide novelty or priority. Its citing-work readings, the Scott and Pandey–Paulsen–Prakash–Rahaman readings, the Stacey reading and its web-search results have not been independently reproduced here. The issue records the following as unread because of paywalls or blocked access: Phys. Rev. A 104, 052227; Phys. Rev. A 111, 012430; APL Quantum, DOI 10.1063/5.0254873; and J. B. DeBrota's 2020 UMass Boston dissertation. Absence of a settlement in those sources is unverified.

The sharpness calculation, the combination with the source's sufficiency direction, the effect-splitting argument and the interpretation of consequences for the other source theorems are mathematical exposition, not additional formal conclusions of `result`. No numerical experiments are reported. The source's Postscript geometry and its entropy-exchange proof have been read as source text, not independently formalized or fully rederived. Universal SIC existence, approximate saturation and quantitative stability remain outside this settlement.
