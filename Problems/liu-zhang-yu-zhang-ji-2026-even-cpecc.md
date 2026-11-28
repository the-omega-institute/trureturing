---
slug: liu-zhang-yu-zhang-ji-2026-even-cpecc
bibkey: liuzhangyuzhangji2026optimalcpecc
doi: null
url: https://arxiv.org/abs/2611.34386v1
triage: window
motivation_gids:
  - D5/S3/Combinatorics/Hamming/HammingMultipartitePartition
---

# Optimal constant-power error-correcting cooling codes for even deletion sizes

## Problem

Section 5 of arXiv:2611.34386v1 asks for constructions of optimal
((n,t,w,w-2))-CPECC codes when (t) is even and (0<t<w-3).
The question arises after the paper's optimal construction for odd (t).
Section 5 gives no length range for the even case. [Source, Section 5](https://arxiv.org/html/2611.34386v1#S5)

## Motivation

For (e=w-2), two supports of size (w) from different information
classes may share at most one point. Classifying the size of a code
therefore uses a packing of pair shadows on the coordinate set. The
related repository result on multipartite Hamming graphs also uses
clique structure to constrain a partition.

## Gap

Theorem 3.4 gives a global edge budget. Issue #35006 identifies a sharper
budget for lengths (nge k=w+t) with (nequiv2pmod{k(k-1)}).
This progression is a subrange of the source's even-deletion question.
The unrestricted even-(t) construction remains open in this dossier.
[Issue #35006](https://github.com/the-omega-institute/trureturing/issues/35006)

## Route

Set (R=(n-g)/(k-1)) and (J=n(n-g)/(k(k-1))). Select one
(k)-clique in every shadow with a clique of that order. If (b) cliques
are selected and a point belongs to (r) of them, the point has leave
degree ((g-1)+(k-1)(R-r)). A remaining shadow can use only points with
(r<R). On those points the total degree is at most
(k(k+g-2)(J-b)). Each remaining shadow uses at least (B(w,t)) edges by
Theorem 3.3, giving at most (J) classes under the threshold inequality
(k(k+g-2)le 2B(w,t)). A supplied (k)-GDD with groups of size (g)
gives one class of all (w)-subsets of every block and hence (J) classes.

## Falsifier

A family with more than (J) classes satisfying the fixed word weight,
ambient deletion condition, cross-class intersection condition, and all
parameter hypotheses would falsify the finite upper bound. A supplied
matching-parameter design whose blocks failed the stated count or whose
(w)-subsets failed the class conditions would falsify the construction.

## Evidence

The finite upper bound is
`D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound.finite_cpecc_support_upper_bound`.
The attainment theorem is
`D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.finite_cpecc_support_optimum_of_design`.
The residue-two criterion is
`D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.even_residue_optimum_iff_groupDivisibleDesign`.
It proves that \(J\) is the optimum exactly when the two-point-group
design exists. The general finite statements use (nge k=w+t), (tge1), (w>t+3),
(1le g<w), (k-1mid n-g), (k(k-1)mid n(n-g)), and the
threshold in the Route section. Attainment takes a finite design as an input.

## Triage

A partial resolution on the matching finite parameters. The case (g=2)
relates the issue's lengths to type (2^{n/2}). For (t=2s>0) and
(w=2s+4+r), (2B(w,t)-k^2=r^2+4(s+1)r+2(s+1)^2>0), so the
threshold is satisfied. Theorem 2.2 in Section 2 cites J. Liu's 2007
asymptotic existence theorem. For fixed (k) and (g=2), the progression
satisfies its two divisibility conditions, yielding eventual attainment
as a literature consequence. [J. Liu, JCTA 114 (2007), 410–420](https://doi.org/10.1016/j.jcta.2006.06.006)

## ASSUMED-UNVERIFIED

Asymptotic GDD existence is external to the Lean development. An explicit
starting length and the other length residues are outside the finite
construction established here.
