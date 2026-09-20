[Index](../../marked_head_profile.md) · [Missing-label comparisons](301-three-missing-source-pairs-clear-the-complete-core-comparisons.md) · [Ineffective15](300-ineffective15-clears-a-complete-source-and-two-core-branches.md)

# Ineffective leading pairs retain the complete source and core bounds

Throughout, assume the original effective9 source branch of
[301](301-three-missing-source-pairs-clear-the-complete-core-comparisons.md).
The three complete comparisons there also hold when both members of one
of {27,45}, {27,135}, {45,135} are absent or ineffective at the source
stages defined below. Their complete source bounds remain respectively
370.327597092541...,400.88931221245247...,398.7297311409643....
Both original complete core-error additions still keep them below403.
This extends the domain of those comparisons without improving their
numerical upper bounds. It supplies no later-prime continuation.

## What ineffective means

Keep the original distinct modulus labels and their chosen residues. For27
test its cylinder after the shallow pure3 labels3 and9; higher pure3
classes may equivalently be included when testing whether its remaining
mass is zero. For15 test after all pure3 and pure5 classes but before the
other alpha classes3*5^b. For45 test after those pure stages and all alpha
classes but before the other beta classes9*5^b. For135 test after the pure,
alpha and beta stages but before the other late classes3^a*5^b, a>=3.
In each mixed stage its leading class is assigned first in that stage's
union. Ineffective means zero additional Haar mass at this precise point.
Absence is allowed separately. No meaning depends on an observer's test.

For each present leading cylinder the following are exact equivalences:

| Leading modulus | Ineffective iff contained in a present original class of modulus |
| --- | --- |
|27|3 or9|
|15|3 or5|
|45|3,9,5 or15|
|135|3,9,27,5,15 or45|

Every listed blocker divides the leading modulus. Thus its cylinder either
contains the whole leading cylinder or is disjoint from it; the relevant
condition is equality of the original residue after reduction.

Containment makes the leading class ineffective immediately. Conversely
assume no listed blocker contains it. In the leading ternary cylinder,
deeper pure3 classes remove at most their complete geometric width. The
remaining ternary widths are at least

    27: 1/27-sum_(a>=4)3^-a = 1/54,
    15: 1/3-sum_(a>=2)3^-a = 1/6,
    45: 1/9-sum_(a>=3)3^-a = 1/18,
    135:1/27-sum_(a>=4)3^-a = 1/54.

In the first-five cylinder, deeper pure5, alpha and beta stages each
contribute at most sum_(b>=2)5^-b=1/20. On the fixed ternary cell of the
leading45 or135 cylinder, each preceding alpha/beta class's ternary
condition is constant. The precursor survivor therefore factors there
into the ternary pure survivor and a subset of the five cylinder. This
is a genuine product description of this source stage, not an independence
assumption between arbitrary mixed forbidden events. The positive leading
mass floors are consequently

    15: (1/6)*(1/5-1/20)   =1/40,
    45: (1/18)*(1/5-2/20)  =1/180,
    135:(1/54)*(1/5-3/20)  =1/1080.

These bounds include all higher exponents and allow independent residues
and absences. The27 floor is also strictly positive. Thus none of the
infinite tails can create a new zero-mass case beyond the listed blockers.

## Same complete parameter contractions

An ineffective leading class contributes nothing to its stage's union and
can be omitted when estimating that union. Its complete assigned raw cap
is therefore unnecessary. The original parameter bounds from301 become

    absent/ineffective27: sum deficit<=1/6,
    absent/ineffective15: sum alpha<=1/20,
    absent/ineffective45: sum beta<=1/20,
    absent/ineffective135:sum late<=7/1080.

For27 the factor9 in the deficit normalization gives
9*sum_(a>=4)3^-a=1/6. For135 the complete late sum is1/72 and removal of its
zero contribution leaves1/72-1/135=7/1080. For15 and45 only b>=2 remains
in the respective leading mixed stage, with total five-coordinate width
1/20. Nothing removes the independent test for the same modulus.

These are exactly the containing domains used by301. All signed source
terms, masses, positive denominator bounds, independent tests and complete
tails consequently retain their certified comparisons. Different source
parameters are not declared independent; their product is a containing
domain just as in301.

## Preservation by both original cores

The two core exponent boxes have3-cutoffs20 and17 and5-cutoffs20 and10.
They retain every present label in

    {3,5,9,15,27,45,135}

with its original residue. If a leading class is absent it remains absent.
If it is present and ineffective, at least one of its finite blockers is
present and contains it. That same blocker survives both restrictions,
so its effectiveness cannot be restored by removing deeper classes.
Both cores also retain the original effective9 shallow pair. This proves
preservation of the actual branch hypotheses; arbitrary numerical caps
are not asserted to persist under restriction.

The301 complete core errors therefore apply unchanged on all three pairs.
The smaller strict403 margins remain32.4518824992...,1.8901673793... and
4.0497484508... respectively. The ineffective15 branch is already the
published300 case. Consequently a source not cleared by these four
sufficient branches must have effective15 and at least two effective
labels among27,45,135. This is a boundary of the present negative-Q
source/core criterion, not a necessary-label theorem for every hypothetical
covering family without a later-prime proof.

Effectiveness supplies no universal positive overlap. Take the original
residues

    3:0, 9:4, 5:0, 15:1, 27:2, 45:7, 135:8.

On the60-point mod135 shallow survivor, the four leading deletion masks
are respectively

    27:  {2,29,56,83},
    15:  {1,16,46,61,91,106},
    45:  {7,52,97},
    135: {8}.

They are nonempty and pairwise disjoint. Thus effective leading labels
alone provide no positive overlap credit.

The all-height result follows from the complete geometric tails and finite
blocker proof above. The numerical bounds and both complete core errors
are the unchanged exact results in the
[301 certificate](../../certificates/source_norms/source-budgets/absent_source_label_comparisons.json).
Independent exact CRT checks support the blocker and normalization
calculation; finite checks do not replace its all-height proof. This is an
ordinary mathematical extension of the source domain, with no new Lean
verification, deposit or unrestricted Erdős7 conclusion.
