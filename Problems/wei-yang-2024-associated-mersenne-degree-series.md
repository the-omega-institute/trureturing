---
slug: wei-yang-2024-associated-mersenne-degree-series
bibkey: wei2024associatedmersenne
doi: 10.48550/arXiv.2407.08237
url: https://arxiv.org/abs/2407.08237v1
triage: theorem
motivation_gids:
  - D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.result
---

# Degree generating function of Associated Mersenne graphs

## Problem

Wei and Yang, *Associated Mersenne graphs*, arXiv:2407.08237v1,
Question 6.2: “For given n and k, how many vertices of Associated Mersenne
graph ℳₙ have degree k?” The vertices are labelled binary words for which
every circular run of ones is followed by a strictly longer run of zeros.
Adjacent vertices differ at one position. The conventions are
$\mathbf M_0=\{\lambda\}$ and $\mathbf M_1=\{0\}$.

## Motivation

The first-tier external question is preregistered in
[#14818](https://github.com/the-omega-institute/trureturing/issues/14818).
The formal resolution is Proved by
`D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.result`, with
`claim : degSeries * DEN = NUM`. The Library entry is
`Library/Words/wei2024associatedmersenne.md`.

## Gap

The preregistration records no answer in the inspected arXiv version,
citing works, MathDB results or repository. The journal full text has not
been verified. This bounds the literature claim to the inspected sources.
The circular single-run case needs a distinct flip count because both gap
endpoints meet the same run.

## Route

Positive marked runs extract ordered tuples $(r_i,s_i)$ with $r_i>0$,
$s_i\ge0$ and total length $\sum_i(2r_i+1+s_i)=n$.
`RunTupleBijection.marked_admissible_tuple` supplies extraction; the
reconstruction and `markedTupleEquiv` identify the labelled marked words
and tuples. `SingleRunDegrees.singleRun_degree` and
`MultiRunDegrees.degree_raw_multi` classify the legal flips.
`MarkedDegreeEnumeration.marked_degree_double_count` gives the refined
identity $\ell\,\#\mathrm{words}=n\,\#\mathrm{tuples}$.
`TransferTuples.trace_coefficient_tuples` enumerates the tuple weights,
and `TransferResolvent.matrixGeom_inverse` supplies the coefficientwise
finite matrix inverse. The settling theorem combines these relations.

The binding `IsOneRunStart` admits $r=0$. Positive marks use
`IsMarkedStart := ∃ r > 0, IsOneRunStart w i r`; `marked_start_iff`
connects the two notions. For $[(r,1)]$, the provisional degree is
$\min(r,2)+1$ and the tuple degree is $\min(r,2)$.
The exact correction is $x(1-y)R$ before marking and
$x\,\partial_x(x(1-y)R)$ after marking, as expressed by
`singleton_weight_correction`.

Writing $R=x^3y+x^5y^2/(1-x^2)$ and
$D=1-xy-R+x(y-1)R^2$, the transfer expression is
$F=1+x(1-y)+x^2(1-y^2)-xD_x/D+x(1-y)(R+xR_x)$.
The Lean statement clears the explicit denominator using `NUM` and `DEN`.
The constant coefficient of `DEN` is $1$, so the coefficients uniquely
specify every $N_n(k)$. Rotations are never quotiented out, including
periodic words.

## Falsifier

A mismatch between literal circular admissibility and the defining
predicate, a coefficient mismatch, or a publication already answering the
question in the preregistered literature scope invalidates the proposed
settlement. The numerical comparison has exact finite scope; it does not
replace the universal Lean theorem.

## Evidence

The eight D5 modules and their Blueprint Scribes contain the mathematical
proof. The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The settling node carries `OpenProblemResolutionClaim` with Proved.

Experiment entry: [degree-series numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/wei-yang-2024-associated-mersenne-degree-series).
At experiments commit `602ec65402d492351ebc19230b04caa93001cda8`, run
`/usr/bin/time -l python3 docs/reports/wei-yang-2024-associated-mersenne-degree-series/check.py`
from that repository root, with Python and SymPy. Exit code: 0.
`check.py` SHA-256:
`2dbc02fa28e1960a0523508203ba5ddfd1b3b72b44a0a1d351adb2dfee7132aa`.
Every length $0\le n\le18$ matches independent enumeration of words and
Hamming-distance-one neighbours. In particular:

| length | degree histogram |
| --- | --- |
| 3 | $\{1:3,3:1\}$ |
| 5 | $\{2:5,3:5,5:1\}$ |
| 8 | $\{2:8,3:16,4:4,5:8,6:8,8:1\}$ |

The four-slot escape audit is unfinished for the public theorem targets,
including the non-refutation `result` and the newly public
`split_replicates` and public shared `split_reverse_map`: [#14898](https://github.com/the-omega-institute/trureturing/issues/14898).
No `declared_validated` registration is claimed. The dependent telescopes
need exact source reconstruction and lawful readout bridges, together
with variation, sensitivity and actual observational dependence evidence.

## Triage

### What the settlement shows

**Proved — mechanism.** The marked-word/ordered-tuple correspondence,
pair-local flip classification, degree-refined marked double count and
corrected transfer expression yield the rational degree generating
function. Their kernel-checked anchors are respectively
`RunTupleBijection.marked_admissible_tuple`,
`SingleRunDegrees.singleRun_degree`, `MultiRunDegrees.degree_raw_multi`,
`MarkedDegreeEnumeration.marked_degree_double_count`,
`TransferTuples.trace_coefficient_tuples`,
`TransferResolvent.matrixGeom_inverse`, and
`DegreeGeneratingFunction.result`. The result holds for every length,
including $0,1,2$, and all degree coefficients, with labelled positions
and periodic words retained. No length cutoff or aperiodicity hypothesis
is imposed.

**Computed — histograms.** $N_3$, $N_5$ and $N_8$ have exactly the histograms
above. The cited experiment, command, exit code and SHA-256 support this
reading, and its full tested scope is $0\le n\le18$. Numerical agreement
beyond that scope is not claimed.

**Open — asymptotic distribution.** Extracting and justifying an asymptotic
degree law from the rational function is a follow-up; no limiting law is
proved or computed in this delivery.

**Open — mean and variance.** Coefficient differentiation in $y$ gives a
route to moments, but exact moment formulas and their asymptotics are
neither formalized nor computed here.

**Open — Question 6.1.** Hamiltonicity is not addressed. The degree-series
identity answers Question 6.2; it supplies no Hamilton cycle and changes
no Hamiltonicity conclusion. No dependence of the source's other results
on an answer to Question 6.2 is asserted.

## ASSUMED-UNVERIFIED

The journal version's full text was not verified; whether it retains
Question 6.2 as open is ASSUMED-UNVERIFIED. No publication-priority or
exhaustive literature-search claim is made. The linked escape audit lacks
the compiled four-slot evidence specified there.
