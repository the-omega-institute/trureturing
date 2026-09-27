# Three shared query labels strictly improve the current head envelope

The fixed actual109 source admits a strict head-query improvement without changing its original residues, its reference, or any full-height fee. The three query labels3,5,15 share their chosen residues across the six factors in their squared-load block. Maximizing those factors separately overcharges the block by

    kappa_3515(sigma) = 6983/77760 = 0.08980195473251029... .

At the unchanged head coefficient c=1084133/201247200, the complete gate improves by

    c kappa_3515(sigma) = 7570500739/15648982272000
                      = 0.00048376952618481436... .

This is a lawful improvement of the head-query estimate, unlike the hypothetical fee deletion in694. The all-one source still has a negative complete gate after the correction. No positive gate or unrestricted Erdős#7 conclusion is asserted. The abstract shared-label cluster method is reused from existing Reports27/28 and problem-details66; the new application is the exact current-source factor map and its numerical correction. No new Lean verification is asserted.

## One complete layout does not mean one common residue

For a finite resolving head period Q with15|Q, as in the current application, a complete test layout b chooses one independent residue b_d mod d for every d|Q, including the unit. Write

    I_d(x)=1_(x=b_d mod d),
    L_b=1+sum_(d|Q,d>1) I_d,
    Gamma_Q(eta)=max_b integral L_b^2 d eta.

Different b_d need not agree when one modulus divides another. They need not lie on one common p-adic path. The same b_d is nevertheless reused in every pair containing label d and at every source point. Original forbidden residues are also fixed, but they are not the freely chosen test residues b_d.

The square expands exactly as

    eta(1)+3 sum_d eta(I_d)+2 sum_(d<e) eta(I_d I_e).

For a fixed pair, CRT makes the intersection empty or one lcm(d,e) cylinder. Write q_f(eta)=max_r eta([r]_f). Report592/JM3 first bounds each ordered-pair term by q_lcm(d,e) independently. Counting exponent pairs gives

    Gamma_Q(eta)<=eta(1)+sum_(1<f|Q) c(f)q_f(eta),
    c(f)=product_(p|f)(2v_p(f)+1).

The loss of shared-label information happens at the pairwise maxima, before the coefficient grouping. Counting the pairs is exact; it does not restore the residues shared by them.

## How the current512 screens arise

RP6 then bounds the nonunit query masses on one reference source nu that dominates the actual remaining survivor eta. A screen maximizes a complete query over its central selectors and fixed outside query values. An outside value is fixed across the full central sum; no cellwise switching is allowed. Different numerical queries and different screen groups can attain their bounds at different choices.

The two central height statuses are0,1,2,3, with3 denoting all heights at least3; the other five coordinates are indexed by their queried support T. For j=32(4e3+e5)+T, the current generator uses

    W_j = a3(e3) a5(e5) product_(q in T) omega_q,
    a3=(1,3,5,8/9), a5=(1,3,5,1/8),
    omega_q=3/(q-1)+(5q-3)/[(q-2)(q-1)^2],
    W_0=0.

These are positive complete geometric height sums. The final envelope

    R(nu)=sum_j W_j S_j(nu)

also incorporates the analytic prefix normalizers. It is not a claim that all heights, selectors or pair maxima are simultaneously attained. The central low-height entries used below are exact query maxima:

    S_128(nu)=q3(nu), W_128=3;
    S_32(nu)=q5(nu), W_32=3;
    S_160(nu)=q15(nu), W_160=9.

No higher-height coefficient is changed in the following replacement.

## The correct measure-dependent replacement

For any finite positive head measure nu, define

    B(nu)=3q3(nu)+3q5(nu)+9q15(nu),

    K(nu)=max_(a mod3,b mod5,r mod15) [
        3nu([a]_3)+3nu([b]_5)+3nu([r]_15)
        +2nu([a]_3 intersect[b]_5)
        +2nu([a]_3 intersect[r]_15)
        +2nu([b]_5 intersect[r]_15)],

    kappa(nu)=B(nu)-K(nu)>=0.

The three variables a,b,r are independent choices, each reused throughout the entire block. This is exactly the contribution of the three unaries and their three unordered pairs. Its maximum includes all225 choices, including choices that sacrifice a marginal maximum or choose incompatible residues. The independent block B is not a valid equality replacement for K. The intersections with[r]_15 simplify to nu([r]_15) times the appropriate compatibility indicator; that simplification does not impose compatibility.

For every eta whose complete nonunit envelope is evaluated on itself,

    Gamma_Q(eta)<=eta(1)+R(eta)-B(eta)+K(eta).       (SQ1)

More generally, if eta<=nu on the same carrier, nonunit square factors are nonnegative. Dominate them by nu, retain the actual unit mass eta(1), and apply the block estimate there:

    Gamma_Q(eta)<=eta(1)+R(nu)-B(nu)+K(nu).         (SQ2)

SQ2 is the form needed after actual remaining-original deletion from a retained source nu=f sigma. It does not identify kappa(eta) with kappa(nu).

The accounting is literal: remove the entire3q3,3q5 and9q15 terms. The9q15 consists of the15 unary with coefficient3 and three unordered pairs with coefficients2. Every other pair involving labels3,5 or15 remains present. Those remaining pairs may still be bounded independently; relaxing their shared parameters supplies an upper bound and does not invalidate the selected block. No factor is subtracted twice.

For the current all-height screen table, replace its three contributions by

    c[3S_128(nu)+3S_32(nu)+9S_160(nu)]
       -> c K(nu).                                (SQ3)

Equivalently subtract3c,3c,9c respectively from C128,C32,C160 and add one new fee cK(nu). The pinned table has C128=C32=1084133/67082400 and C160=1084133/22360800. Thus all three become zero exactly: no original-loss fee is hidden in these entries. Every original-loss coefficient elsewhere, the four fullmode8 additions and the unit term stay as before. This gives the corrected head gate

    G_joint(f)=G_old(f)+c kappa(f sigma).          (SQ4)

It is essential to recompute the correction on f sigma. The constant kappa(sigma) is not a uniform correction for every retained f. If eta<=sigma but one wants to use R(eta), an available weaker bound is

    Gamma_Q(eta)<=eta(1)+R(eta)-B(eta)
                              +min(B(eta),K(sigma)),

because K(eta)<=K(sigma) and K(eta)<=B(eta). The expression R(eta)-kappa(sigma) is not justified.

## Exact current-source calculation

The program reconstructs the central mod9 by mod25 marginal from the actual original predicates, retaining each original's fixed phase. Each outside coordinate is counted on its q² atoms; the pair originals impose at most one root1. The higher pure deletions of681 preserve the assigned coarse central leaf masses and give its checked deep factors81/82 and1875/1876. Thus the block and complete-gate calculations refer to the same actual109 source.

For its unretained source sigma:

| Query | Maximum mass | Maximizing residue |
|---|---:|---|
|3|19938190667/71833132800|1 mod3|
|5|122669/699840|3 mod5|
|15|32413/349920|3 mod15|

The maximal mod15 cell projects to0 mod3, whereas the maximal mod3 root is1. Keeping the complete tradeoff, enumeration gives

    B(sigma)=472417771663/215499398400,
    K(sigma)=453065504443/215499398400,
    argmax K={(1 mod3,3 mod5,13 mod15)},
    B(sigma)-K(sigma)=6983/77760.

The225 independent phase triples are evaluated on the same exact marginal. A separately authored checker independently reconstructs these same225 layouts and obtains the identical unique maximizing triple and rational gap. Its result agrees with the pre-existing producer enumeration; the two implementations are within the same model family.

As a smaller control, the block using only labels3 and5 has independent bound998058579029/646498195200, joint maximum328385689183/215499398400 at(1,3), and gap6983/349920. That pair's maximum is also reconstructed by direct evaluation against all225 central residues. The pair and triangle overlap, so their gaps are alternatives and are never added.

The accompanying finite search of the declared central label list

    {3,5,9,15,25,45,75,225}

also evaluates28 two-label and56 three-label clusters on the same marginal. Ten two-label and39 three-label clusters have positive deficits. These counts concern only that finite library; different overlapping cluster deficits cannot all be added without their literal factor-capacity accounting. The selected triangle uses just one block and needs no packing assumption.

## The all-one source does not pay the complete gate

The program separately evaluates every original512 full-height screen, with the four complete fullmode8 fees and the actual109 central deep factors. It uses680's proved outside-root/deep domination for this unretained source, checking all six first7 roots in each query support that contains7. It does not optimize a retention field.

The exact old all-one gate is

    -102747178320681648015183928043
    /1862325532039825870617600000000
    =-0.055171438372614436... .

After the legal3/5/15 block replacement it becomes

    -101846241980444859105430228043
    /1862325532039825870617600000000
    =-0.05468766884642962... .

Both are below193/100000. The verified strict improvement therefore supplies a correctly connected interface, not a positive head certificate.

The remaining precise fixed-source question is whether there is one measurable0<=f<=1, possibly with additional non-overlapping or lawfully packed query blocks, such that the corrected complete gate exceeds193/100000. No such f is supplied here. Even resolving that fixed-source question would not remove the arbitrary-family phase, pure-source or network obligations of unrestricted #7.

## Reuse and remaining boundaries

The shared-factor mechanism and factor packing already appear in Reports27/28. [Problem-details66](../../../problem-details/66-shared-phase-triangles-and-common-center-obstruction.md) supplies the more specific {p,q,pq} conditional maximization and common-center obstruction. No new general cluster theorem is claimed. Report416 already gives exact independent-phase layout DP and disproves imposing a common path. Report588 is a different source's first-hinge prefix-incidence estimate and supplies no ready-made number for the present square. Reports683/684's published fee reductions concern owner primes at least37, whereas SQ3 changes the present head-query debit directly.

The strict-improvement condition for this selected block is kappa(f sigma)>0 for the particular source being evaluated. The unretained actual109 source above passes it. Pure product examples can have kappa=0, and deleting most source mass may remove the incompatible maxima; neither modulus distinctness nor positive original deletion alone forces a positive uniform correction. The all-height scope of SQ1–SQ4 follows by replacing finitely many literal factors and retaining every other coefficient, not by extrapolating the finite enumeration to higher heights.

The new fee K depends only on the retained mod15 marginal. Hence689's prefix averaging and690's outside-category pooling preserve K as well as source mass; their existing nonincrease of every remaining nonnegative screen still applies. The corrected criterion therefore retains the same finite category representation. Its225 new linear rows have one fixed(a,b,r) per row, used across all source states. If n(x) counts the three active query indicators, the row coefficient is n(x)^2+2n(x), hence one of0,3,8,15. This gives an explicit finite matrix interface without imposing a common residue on its independent label variables. Finding a paying field for that changed objective is a new optimization question; no such optimization was performed here.

The [cluster and full-gate program](../../../frontier/cover-geometry/clustered109-central-query-clusters/clustered109_central_query_clusters.py) and [exact result](../../../frontier/cover-geometry/clustered109-central-query-clusters/clustered109_central_query_clusters.json) retain the finite cluster library and complete all-one gate. It performs338 explicit checks using rational source reconstruction and bounded exact integer arrays; display decimals do not decide inequalities. Full-height screen evaluation uses rational arithmetic.

The separately authored [source reconstruction and literal triangle program](../../../frontier/cover-geometry/actual109-small-label-triangles/actual109_small_label_triangles.py) and [result](../../../frontier/cover-geometry/actual109-small-label-triangles/actual109_small_label_triangles.json) enumerate all225 layouts of{3,5,15} and135 layouts of{3,5,9}, with965 checks. The latter triangle has gap6983/349920 and unique layout(1,3,7); it shares factors with the selected triangle, so the gains cannot be added.

The [independent checker](../../../frontier/cover-geometry/actual109-small-triangle-from-verified-cell-masses/actual109_small_triangle_from_verified_cell_masses.py) and [result](../../../frontier/cover-geometry/actual109-small-triangle-from-verified-cell-masses/actual109_small_triangle_from_verified_cell_masses.json) reuse692's already verified source masses, reconstruct them by CRT, compare every225 central atom, and check all360 triangle layouts and their literal fee capacities, with779 checks. This is an independent small-cluster evaluation with a reused verified source, not an independent reconstruction of every inherited source theorem. All programs use sibling defaults and can redirect outputs. These are ordinary mathematical applications and exact finite checks, not new Lean verification.

From the repository root:

```sh
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered109-central-query-clusters/clustered109_central_query_clusters.py --output /tmp/clustered109_central_query_clusters_replay.json
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual109-small-label-triangles/actual109_small_label_triangles.py --output /tmp/actual109_small_label_triangles_replay.json
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual109-small-triangle-from-verified-cell-masses/actual109_small_triangle_from_verified_cell_masses.py --compare /tmp/actual109_small_label_triangles_replay.json --output /tmp/actual109_small_triangle_independent_replay.json
```
