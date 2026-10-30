---
slug: siudzinska-2020-generalized-pauli-volume-ratios
bibkey: siudzinska2020pauligeometry
doi: 10.1103/PhysRevA.101.062323
url: https://arxiv.org/abs/2002.04657v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.result
---

# Three volume ratios for generalized Pauli eigenvalue regions

## Problem

Katarzyna Siudzińska, *Geometry of generalized Pauli channels*, Phys. Rev. A 101, 062323 (2020), arXiv:2002.04657v2, states three conjectures in Section 4.2, “$N=d+1$ and $N=d$ mutually unbiased bases”. The v2 TeX source `GGPC_volume5.tex`, lines 243–246, reads:

> and conjecture that the general formula reads
> $\frac{V_{CP}(d)}{V_P(d)}=\frac{d}{(d+1)!}.$

Lines 276–279 read:

> and conjecture that the general formula reads
> $\frac{V_{G}(d)}{V_{CP}(d)}=\frac{d^2-1}{d^2}\left(\frac{d-1}{d}\right)^{d}.$

Lines 302–305 read:

> from which we conjecture that
> $\frac{V_{EB}(d)}{V_{G}(d)}=\frac{1}{d+1}.$

For a natural number $d\ge2$, put $m=d+1$ and $s(x)=\sum_{i=1}^{m}x_i$ for $x\in\mathbb R^m$. The module defines precisely these four sets:

- $P=\{x:\ -1/(d-1)\le x_i\le1\text{ for every }i\}$ (`boxRegion`).
- $C=\{x:\ -1/(d-1)\le s(x)\text{ and }s(x)\le1+dx_j\text{ for every }j\}$ (`cpRegion`).
- $G=C\cap\{x:\ x_i\ge0\text{ for every }i\}$ (`generatorRegion`).
- $E=G\cap\{x:\ s(x)\le1\}$ (`ebRegion`).

For these sets write $V_A=\operatorname{channelVolume}(d,A)=(\sqrt{d-1}/d)^m\operatorname{Leb}_m(A)$, for $A=P,C,G,E$. In Lean, `channelVolume` uses `(volume A).toReal`; the proof obtains finite positive Lebesgue measures for all four sets when $d\ge2$. Thus $V_P,V_C,V_G,V_E$ match the source's $V_P(d),V_{CP}(d),V_G(d),V_{EB}(d)$ as coordinate-region volumes. The source locates the box and its weight at lines 210–228, complete positivity at lines 359–364, nonnegative eigenvalues at lines 256–267, and the nonnegative entanglement-breaking region at lines 282–293; see also [the literature note](../Library/QuadraticForms/siudzinska2020pauligeometry.md).

Issue [#22754](https://github.com/the-omega-institute/trureturing/issues/22754) fixes the statement as the conjunction of these three identities for every natural $d\ge2$. This is proved for the specified coordinate regions.

## Motivation

The ratios measure how much of the source's eigenvalue parameter space belongs to each nested class. In the source's channel interpretation with $N=d+1$ mutually unbiased bases, they compare complete positivity with a box of necessary positivity conditions, nonnegative eigenvalues with complete positivity, and entanglement breaking with the nonnegative subclass. Closed formulas replace separate integrations in each dimension and determine the dimension dependence of these relative volumes.

## Gap

The bounded literature check recorded in #22754 reports:

- arXiv v1 and v2 retain the three conjectures; the v2 conjectures are present at the source locations quoted above;
- OpenAlex lists seven citing works, and the five distinct works returned by OpenCitations, arXiv:2003.12184, 2010.01128, 2210.17448, 2312.02004 and 2402.04415, contain no all-$d$ settlement according to `search-fq`;
- `search-fq` reports no match in MathDB or formal-conjectures, and the orchestrator reports no existing repository record in the preregistration searches.

`not-found-in-searched-scope`.

## Route

Fix a natural $d\ge2$, put $m=d+1$, let $u=(1,\ldots,1)$, and let $S=\{t\in\mathbb R^m:\ t_i\ge0\text{ for every }i,\ \sum_i t_i\le1\}$. The following helper names are local to `GeneralizedPauliVolumeRatios` unless otherwise qualified.

1. **Standard and affine simplices.** `standard_volume` states, for every natural $n$, that `simplexCoords (n + 1)` has Lebesgue measure $1/n!$; at $n=m$ this gives $\operatorname{Leb}_m(S)=1/m!$. It reuses `ConditionalSubentropyGuessingBound.simplex_volume`. For a real $c>0$ and a natural $d\ge2$, `affine_simplex_volume` gives $\operatorname{Leb}_m(T_c(S))=dc^m/m!$, where $T_c(t)=u+c(t-(\sum_jt_j)u)$ and `affineSimplex d c` is this image. Its linear matrix is $c(I-J)$, with $J$ the all-ones matrix. Factoring $J=AB$ with an $m$-by-one column and a one-by-$m$ row of ones, `Matrix.det_one_sub_mul_comm` gives $\det(I-J)=1-m=-d$; translation invariance and `Measure.addHaar_image_linearMap` give the stated measure.
2. **The complete-positivity simplex.** For a natural $d\ge2$, a real $c>0$ and any $x\in\mathbb R^m$, `affine_simplex_iff` states that $x\in T_c(S)$ exactly when $m-cd\le s(x)$ and $s(x)\le1+dx_j$ for every $j$. For the converse its coordinates are $t_i=(dx_i-s(x)+1)/(cd)$: the upper inequalities imply $t_i\ge0$, the lower one gives $\sum_i t_i=(m-s(x))/(cd)\le1$, and substitution gives $T_c(t)=x$. For every natural $d\ge2$, `cp_eq_affine` applies this at $L=d/(d-1)>0$ to identify $C=T_L(S)$, since $m-Ld=-1/(d-1)$. Hence $\operatorname{Leb}_m(C)=dL^m/m!$.
3. **The nonnegative and entanglement-breaking regions.** For every natural $d\ge2$, `generator_eq_union` gives $G=S\cup T_1(S)$ and `simplex_overlap_null` gives $\operatorname{Leb}_m(S\cap T_1(S))=0$. The overlap has coordinate sum one; the reused `ConditionalSubentropyGuessingBound.simplex_sum_boundary_null` states that the sum-$t$ hyperplane is null for every natural number of coordinates and every real $t>0$, here with $m$ coordinates and $t=1$. The measurable union calculation in `generator_volume`, for every natural $d\ge2$, gives $\operatorname{Leb}_m(G)=(d+1)/m!$. Under the same hypothesis, `eb_eq_standard` identifies $E=S$, giving $\operatorname{Leb}_m(E)=1/m!$.
4. **The box and quotients.** For every natural $d\ge2$, `box_volume` gives $\operatorname{Leb}_m(P)=L^m$ from its side length $L$. Given $d\ge2$ and the four measure equalities $\operatorname{Leb}_m(P)=L^m$, $\operatorname{Leb}_m(C)=dL^m/m!$, $\operatorname{Leb}_m(G)=(d+1)/m!$ and $\operatorname{Leb}_m(E)=1/m!$, `ratios_from_volumes` gives exactly the three conjectured ratios. Its proof establishes positivity of $d$, $d-1$, $L$, $m!$ and the common weight, converts the finite measures to real values, and cancels nonzero factors. `result` supplies those four equalities for every natural $d\ge2$.

## Falsifier

A mismatch between the source's integration regions and the four Lean sets would prevent the identities from answering the stated conjectures. The correspondence has these limits:

- For $d\ge2$, the inequalities $s(x)\le1+dx_j$ for every $j$ are equivalent to $s(x)\le1+d\min_jx_j$, the upper complete-positivity inequality in Appendix A: a minimum exists over the nonempty finite coordinate set and multiplication by $d>0$ preserves order.
- $P$ is the box of necessary positivity conditions. Siudzińska (2020, arXiv:2002.04657v2, line 213) explicitly says, “Hence, condition (\ref{def2GP}) is not sufficient.” The first denominator is the volume of this box, not the exact volume of positive maps.
- $E$ includes nonnegative coordinates. The third identity concerns entanglement breaking within $G$, rather than the entire entanglement-breaking region with arbitrary coordinate signs.
- The theorem concerns the four coordinate sets for every natural $d\ge2$. It neither constructs $d+1$ mutually unbiased bases in every dimension nor formalizes the physical interpretation of nonnegative eigenvalues as attainability by a time-local generator.

## Evidence

The canonical source is `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.lean`.

- **Proof.** It proves `result`, the conjunction of the three ratio identities for every natural $d\ge2$.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.lean.json`.

Declaration statements:

- `result`: `sha256:ce4fa811aeed695641edcd11b6913c09e90ac4291f49c1546caca7c9ed3d9f3d`.

## Triage

Tier 1: three explicit conjectures of a 2020 Phys. Rev. A paper, preregistered in issue #22754 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $d\ge2$, the `channelVolume` values of the four sets defined above satisfy $V_C/V_P=d/(d+1)!$, $V_G/V_C=((d^2-1)/d^2)((d-1)/d)^d$ and $V_E/V_G=1/(d+1)$.

**Computed, not formalized:** exact rational evaluation reproduces all twelve ratios printed by Siudzińska (2020, arXiv:2002.04657v2) for $d=2,3,4,5$.

**Argued, not formalized.**

- *Mechanism and extension.* For every natural $d\ge2$, the decisive structure is $C=T_L(S)$, $G=S\cup T_1(S)$ with null overlap, and $E=S$ (`cp_eq_affine`, `generator_eq_union`, `simplex_overlap_null`, `eb_eq_standard`, with exactly that dimension hypothesis). For $d\ge2$ and any real $c>0$, `affine_simplex_iff` and `affine_simplex_volume` describe the whole family $T_c(S)$ and its measure $dc^m/m!$; the complete-positivity region uses the particular parameter $c=L$. If the common scalar weight is replaced by any positive constant $w$, the three quotients remain the same: all relevant measures are finite and their denominators are positive, so $(w\operatorname{Leb}_m(A))/(w\operatorname{Leb}_m(B))=\operatorname{Leb}_m(A)/\operatorname{Leb}_m(B)$. This does not cover a position-dependent density or a different metric with such a density.
- *Exactness and asymptotics.* These are equalities for every natural $d\ge2$, rather than upper or lower estimates for the four specified regions. For $r(x)=(1-x^{-2})(1-x^{-1})^x$ on real $x>1$, integration of $1/(1-t)$ gives $-t/(1-t)<\log(1-t)<-t$ for $0<t<1$. Hence $-x/(x-1)<x\log(1-1/x)<-1$, which tends to $-1$; together with $\log(1-x^{-2})\to0$, this gives $r(x)\to1/e$ from below. Also $(\log r)'(x)=2/(x(x^2-1))+\log(1-1/x)+1/(x-1)>0$ by the same lower logarithm bound, so the second ratio increases with integer $d\ge2$. The first ratio tends to zero because successive terms have quotient $(d+1)/(d(d+2))<1/2$ for $d\ge2$, and the third tends to zero as $1/(d+1)$.
- *Effect on the paper.* The three all-dimension coordinate-volume formulas in Section 4.2 are established by `result`. The preceding argument supplies an unformalized justification for the source's nonzero limiting fraction: line 313 says the second ratio “approaches $1/e$ for $d\to\infty$”, whereas line 280 says “monotonically approaches $e$ from below”; the latter value is inconsistent with the formula. The source's additional identification with $N=d$ channel volumes (line 233) requires a correspondence between parameterizations that this module does not formalize. Its $N=3$ formulas and the suggestion about sufficiency of the entanglement-breaking condition at lines 328–332 are not settled by this result. The questions in the Conclusions (line 347) about arbitrary $N$, tighter positivity and entanglement-breaking regions, and other metrics remain outside the theorem.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The arXiv v1, OpenAlex, OpenCitations, five citing-paper, MathDB and formal-conjectures readings are attributed to `search-fq` in #22754 and are not independently reproduced here; the repository deduplication searches are the orchestrator's issue-reported readings. The v2 TeX source and its quoted regions and conjectures are directly checked.

The rational calculation and the deductions labelled “Argued, not formalized” have no additional Lean formalization here. In particular, the asymptotic limits, monotonicity, constant-weight extension, equivalence with the minimum-coordinate inequality, and interpretation of the source's dependent statements are prose arguments. The module does not formalize the channel construction, the availability of complete mutually unbiased bases, the time-local-generator interpretation, or the entanglement-breaking criterion as a statement about quantum states; these are source-level interpretations of the explicitly defined regions. No independent reproduction of the orchestrator's Monte Carlo check in #22754 is claimed.
