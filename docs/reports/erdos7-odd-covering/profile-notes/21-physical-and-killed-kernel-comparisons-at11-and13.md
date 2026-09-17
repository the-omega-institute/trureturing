[Index](../marked_head_profile.md) · [Previous](20-genuine-current-kernels-and-positive-charge.md) · [Next](22-comparing-the-two-killed-steps.md)

<a id="physical-and-killed-kernel-comparisons-at11-and13"></a>
### Physical and killed kernel comparisons at11 and13

The weighted WT4 proof applies with any fixed admissible pure-base
threshold T, rather than only T=8. Set

    s_*=(p-2)/(p-1), delta=(T-1)/(p-2),
    C=1/(1-delta), ell=max(C^2,C/delta).

Use T=4 at11 and T=6 at13. The pairs (C/s_*) are respectively5/3 and2.
All delta lie strictly between zero and one. The actual pure survivor
bases have Haar mass at least s_*, in both full and core families.

For a source probability bounded by D_* times Haar and with every
complete square at most J_*, define for i=0,2

    z0(p)=1,       u0(p)=p/(p-1),
    z2(p)=Phi_p(0),u2(p)=Sigma_p,
    t0(p,b)=sum_(a>b)p^-a,
    t2(p,b)=sum_(a>b)p^-a Phi_p(a),
    H_i(S,b)=product_(q in S)[u_i(q)-t_i(q,b)]
                 -product_(q in S)z_i(q).

Here H_i excludes the unit old cofactor exactly once. Put J_0=1,
J_2=J_*. The error for the i-th weighted comparison is

    e_p,i = D_* T_i(S,b)
             [(C/s_*)(u_i(p)-z_i(p))
                    +(ell/s_*^2)z_i(p)/(p-1)]
           + D_* H_i(S,b)
             [(C/s_*)t_i(p,b)+(ell/s_*^2)z_i(p)t0(p,b)]
           + J_i[(C/s_*)t_i(p,b)
                    +((ell+C)/s_*^2)z_i(p)t0(p,b)].    (APC3)

The three terms respectively cover old cofactors outside the box at
all positive current depths; nonunit old cofactors inside the box at
current depth above b; and omitted pure current classes. These regions
are disjoint and exhaust all omitted current forbidden labels.

For i=2 this is exactly WT4's weighted proof with the stated thresholds.
For i=0, repeat its pointwise physical or killed kernel comparison with
weight1. A mixed query of old modulus d then has old mass at most D_*/d,
and the current Haar query mass is p^-a; the two full test axes are absent.
This replaces Phi by1, Sigma by p/(p-1), and J_* by1. The pure-base
comparison still pays both the common-region coefficient variation and
the changed region, hence the coefficient ell+C remains. L1 is not
replaced by probability total variation in APC3.

At11 use S={3,5,7},D_*=D0,J_*=G0. At13 use S={3,5,7,11},
D_*=(5/3)D0,J_*=(23/15)G0. These are unconditioned physical11 bounds
under either construction. Its killed measure is dominated by its
physical measure, so the same direct error estimates apply to killed
chains as well.

For a common physical or killed kernel of mass at most1, WT5 gives
Delta2 propagation factor1+c(Phi_p(0)-1); these are23/15 at11 and55/36
at13. Delta0 contracts with factor1. Comparing the two kernels under the
full old measure, then propagating the change of old measure through the
same core kernel, yields for both physical and killed final measures

    ew=(55/36)[(23/15)e0w+e11,2]+e13,2,
    em=e0m+e11,0+e13,0.                                (APC4)

The killed chain is mu K11^- K13^-; it retains exactly those points that
avoid the old family and both actual current masks. No intermediate
conditioning is introduced. The physical chain is normalized on every
history, including histories previously marked bad.

<a id="final-normalization-and-the-complete-original-test-tail"></a>
### Final normalization and the complete original test tail

Let eta,eta0 be the two killed13 measures, with masses q,q0>=r. Their
normalizations are nu_F and nu_b. The exact decomposition

    nu_F-nu_b=(eta-eta0)/q + ((q0-q)/q)nu_b

and |q-q0|<=em give, for every complete old test A,

    Delta2(nu_F,nu_b)<=eNw=(ew+G*em)/r,
    Delta0(nu_F,nu_b)<=eNm=2em/r.                      (APC5)

The bound G is valid for nu_b because F_b is itself an arbitrary actual
five-prime family using the identical construction. Thus the two terms
in APC5 do not mix the AO and AP probabilities. The first inequality
bounds integrals against absolute measure difference, not merely the
difference between two separately maximizing tests.

For any probability of Haar density at most D, the previously proved
full original two-test tail is

    tail_test(S,b,D)
       =D{product_(p in S)p(p+1)/(p-1)^2
                 -product_(p in S)[1+sum_(a=1..b)(2a+1)p^-a]}.

It bounds E(L_full^2-L_box^2) for every complete layout. Applying it
to nu_b and APC5 to the identical full layout gives APC1 with

    E_b=eNw+tail_test({3,5,7,11,13},b,D).              (APC6)

For the opposite direction, extend each box test to the complete
original inventory. Its extra indicators are nonnegative, so APC5 alone
bounds Gamma_box(nu_b)-Gamma_full(nu_F). No equality of maximizing
layouts is assumed.

All tests are lifted to the same period before comparison. A core
kernel depends only on retained low coordinates, so the construction
from F_b is a rational law on that finite core lifted by independent
uniform higher digits. If an original height is below b, intersect the
box with the physical inventory; uniform padding yields the same bounds.

<a id="a-completely-finite-reference-for-the1719-joint-criterion"></a>
### A completely finite reference for the17/19 joint criterion

Start with the full actual nu_F at13 and the two actual pure-base
AP17/8,AP19/8 kernels, with no intermediate conditioning. First apply
WT1--WT11 with the stronger same-law HC9 density and square bounds: keep old cofactor exponents at most20 and current
forbidden depths at most8 in both future masks, including pure depth8.
This costs the exact allowance

    e_mask=0.26221638911048406... .

At this intermediate stage the incoming probability and all tests
remain full. Now replace only the incoming probability by the actual
AP13 core law nu_20, holding the two reference kernels fixed.
For a common two-kernel continuation, the weighted variation factor is

    k17*k19=(89/64)(59/45)=5251/2880.

Each assigned charge is the expectation, under the initial probability,
of a fixed function with values in[0,1]. For the19 charge this function
already integrates the normalized reference17 kernel. Two probabilities
have difference of total mass zero, so each such expectation changes
by at most half their L1 distance. The sum of the two charge changes
is at most their L1 distance, not twice that distance. Thus changing
the incoming law costs at most

    e_incoming=(5251/2880)eNw_20+483eNm_20.             (APC7)

Finally retain only test labels with all seven exponents at most20.
The final reference physical density is at most(18/5)D. Its test-tail
cost is

    e_test=tail_test({3,5,7,11,13,17,19},20,(18/5)D)
          =8.512798422966208e-06... .

Every ordered test pair with an omitted label is included in this
positive tail. The exact complete allowance is

    e_mask+e_incoming+e_test
        =0.2624239752577702... <263/1000.             (APC8)

Consequently, it suffices to prove on this finite reference

    E_finite[L_box^2-1]+483 B_finite<=483-263/1000       (APC9)

for every complete box20 test and every retained original family
pattern. The reference is fully specified: actual incoming AP13 core20
law; actual future kernels with old-cofactor box20 and current/pure
depth8; and test box20. All are computable on a common finite period
dividing (3*5*7*11*13*17*19)^20. The surviving family pattern still
records every retained original modulus and its original residue.

If APC9 holds for a given retained pattern, APC8 gives a strict
positive slack for the full functional E_actual(L^2-1)+483B_actual<483.
As in WT10 this implies B_actual<1 and a supported complete-square
bound484 after one final conditioning. No assumption of final survival
was made to construct any of the physical kernels.

APC9 has not been proved uniformly or evaluated over all finite
patterns. The period and number of patterns are not claimed small.
Further prime continuation is also still required for unrestricted
Erdős7. The finite reduction is an ordinary mathematical result with
an exact arithmetic certificate; it is not an end-to-end Lean theorem.

The adjacent exact verifier reconstructs these bounds from the shared-cell
hinge, pure-root and weighted-kernel certificates, each pinned by SHA-256.
It checks every whole certificate field. The displayed decimals are for
reading; all acceptance comparisons use rational arithmetic.

The [AP-core verifier](../verify_ap_core_stability.py) checks the
[exact certificate](../certificates/ap_core_stability_certificate.json). Its three source
certificates are pinned by SHA-256. Default mode verifies; `--write` regenerates.

<a id="full-original-heights-can-make-both-sh26-joint-savings-vanish"></a>
## Full original heights can make both SH26 joint savings vanish

At each of p17 and p19 there is a genuine pure-base BBMST step at threshold `T=8`, starting from a uniform complete actual357 survivor law, for which one complete original test has all of the following properties:

* its zero-current-exponent old block is nonconstant;
* all positive-current-exponent old layouts are distinct from each other and from the zero block;
* the actual assigned bad mass is strictly positive;
* the entire cap-covariance correction dropped by SH26 is zero;
* the actual killed excess `integral_bad(L^2-1)` is zero.

The construction retains all original test labels through its actual highest current exponent. The cap statement refers specifically to SH26's generic pure-density envelope. The actual pure density provides a separate strictly positive cap improvement, displayed below. The test is not a current-square maximizer; this example does not decide a tradeoff restricted to maximizing tests or their common dual mixtures.

<a id="actual-old-source-and-current-pure-law"></a>
### Actual old source and current pure law

Use the following parameters:

| p | current height H | old Q | old source size | full original period |
|---|---|---|---|---|
|17|4|`945=3^3*5*7`|432|78927345|
|19|8|`2835=3^4*5*7`|1296|48148401221235|

For every original nonunit divisor d of Q, keep the forbidden class `0 mod d`. The complete actual old survivor set is `S=(Z/QZ)^*`; let nu be uniform on S. Set `x0=1`, `x1=1+Q/3`, so `x1=316` or946. Both points belong to S.

The only current pure forbidden class is `0 mod p^H`. The actual pure base m is uniform on the `n=p^H-1` other current points; its Haar mass is `lambda=1-p^-H`. Set

`delta=7/(p-2)`, `C=1/(1-delta)`.

For these heights `M=delta*n` is an integer. Its H base-p digits, from the coefficient of `p^(H-1)` downward, are

| p | M | base-p digits |
|---|---|---|
|17|38976|`(7,15,14,12)`|
|19|6993231840|`(7,15,12,5,11,3,6,13)`|

Write these digits as b1,...,bH. Decompose M into disjoint current prefix cylinders as follows. At depth1 use roots1,...,7. The remaining prefixes lie inside root8. Starting with prefix r=8, at depth e>=2 use the b_e children `r+j p^(e-1)`, `0<=j<b_e`, and then continue inside the unused child `r+b_e p^(e-1)`. A depth-e cylinder contains `p^(H-e)` current points. These cylinders are pairwise disjoint and their total size is exactly M. All avoid the excluded pure leaf0 and the clean root p-1.

<a id="original-mixed-labels-and-the-exact-threshold-row"></a>
### Original mixed labels and the exact threshold row

At depth1 assign roots1,...,7 respectively to old divisors

`(3,5,7,9,15,21,35)`,

with old residue1. All seven divide Q/3. At each depth e>=2, assign its b_e disjoint current prefixes to the first b_e nonunit divisors of Q in increasing order, also with old residue1. There are15 or19 available old nonunit labels, so every depth budget fits. Different current exponents remain different original modulus labels.

Finally add the original modulus Qp with old residue x1 and current root9. Its old cofactor was not used among the seven depth1 classes. This extra current cylinder is disjoint from all preceding cylinders. Thus original moduli remain distinct, and every actual mixed current cylinder is globally disjoint from every other one, even when the old projections overlap.

There are65 forbidden classes at17 and93 at19, including all original old classes and the one current pure class. The certificate gives every literal CRT modulus/residue pair. No original forbidden label is silently merged.

For every old row x, the actual mixed fraction is therefore the exact positive sum

`alpha(x)=n^-1 sum_(d,a,e,r) p^(H-e) 1_(x=a mod d)`.

At x0 every original prefix in the M decomposition is active and the extra Qp class is inactive. Hence `alpha(x0)=M/n=delta` exactly.

At x1 all seven original depth1 classes remain active. At a deeper exponent, only old cofactors having the maximum ternary exponent can cease to match; there are exactly four such possible old labels. Thus the total lost current mass is at most

`4 sum_(e=2)^H p^(H-e) < 4 p^(H-1)/(p-1)`.

The new root9 adds `p^(H-1)` current points. Since p-1>4, `alpha(x1)>delta`. The exact fractions are

| p | alpha(x0) | alpha(x1) | beta(x1) | assigned mass b |
|---|---|---|---|---|
|17|`7/15`|`1067/2088`|`463/5568`|`463/2405376`|
|19|`7/17`|`2612524913/5661187680`|`281447633/3330110400`|`281447633/4315823078400`|

Here `beta=(alpha-delta)_+/(1-delta)`. In fact only x1 has positive beta: without the extra Qp cylinder every row's active subset has at most M points, and that extra class is active only at x1.

Every actual bad set is contained in current roots1,...,9. In particular alpha<1 in every row. Use the genuine normalized BB density relative to m,

`k_x=a(alpha) 1_(B_x^c)+[beta(alpha)/alpha] 1_(B_x)`,

where `a(alpha)=1/(1-min(alpha,delta))` and the bad coefficient is zero at alpha=0. Its row mass is exactly1. Let P=nu k and let B be the actual mixed bad event. The old marginal remains nu and `P(B)=b>0`.

<a id="complete-independent-old-test-blocks"></a>
### Complete independent old test blocks

For the zero-current-exponent test block, use residue0 at every nonunit old divisor except Q, where the test residue is1. Its complete old load is

`A0(x)=1+1_(x=x0)` on S.

For each positive current exponent e, use old residue0 at every nonunit divisor except Q, where the residue is3e. Each of these residues is divisible by3, so every nonunit test in that block is inactive on S. Thus

`Ae(x)=1` for every x in S and every e>=1.

The layouts are nevertheless independent and distinct: their Q-label residues are `1,3,6,...,3H`. This is a concrete choice of different original layouts, not an assumption identifying the arbitrary blocks in SH26.

At every positive current exponent e and every old test divisor d, choose current prefix `p-1 mod p^e`. This specifies one literal CRT test at every original divisor `dp^e`, `d|Q`, `0<=e<=H`. There are80 tests at17 and180 at19. The full test load is exactly

`L(x,y)=A0(x)+sum_(e=1)^H 1_(y=p-1 mod p^e)`.

All positive current test prefixes lie inside the clean root p-1, whereas every actual mixed bad prefix lies on roots1 through9. Consequently L=A0 on B. Since beta(x0)=0 and A0=1 away from x0,

`integral_B(L^2-1)dP=E_nu[beta(A0^2-1)]=0`.

The zero block is nonconstant, with

`E_nu(A0-1)=1/432` at17 and `1/1296` at19.

<a id="the-complete-sh26-cap-covariance-sum"></a>
### The complete SH26 cap-covariance sum

Use precisely SH26's generic envelope

`c=(p-1)/(p-9)`,

`c_actual(x)=(p-1)/[(p-2)(1-min(alpha(x),delta))]`.

Its nonnegative discarded covariance correction, before any all-height enlargement, is

`Z=sum_((e,f)!=(0,0), 0<=e,f<=H) p^-max(e,f)`
`    * E_nu[(c-c_actual)(Ae Af-1)]`.

If both exponents are positive, Ae Af-1=0. If exactly one exponent is zero, Ae Af-1 is the indicator of x0. At x0, alpha=delta and hence c_actual=c. Every ordered-pair summand is therefore zero, so Z=0 exactly. This uses every original current depth and every original old test label. It does not truncate either inventory or take a limiting probability.

Combining the two results gives `Z=integral_B(L^2-1)dP=0` with positive b and nonconstant A0. A positive height-uniform lower bound on their sum cannot follow merely from these observations. In particular the discrete alpha gap for one current digit does not survive the full original current-height domain.

<a id="two-limits-on-the-conclusion"></a>
### Two limits on the conclusion

The actual pure mass lambda is much larger than SH26's generic lower bound `(p-2)/(p-1)`. Reading it gives the stronger actual full-Haar cap `C/lambda`, which remains strictly below c even at alpha=delta:

| p | SH26 ceiling c | actual pure-density ceiling C/lambda | difference |
|---|---|---|---|
|17|2|`83521/44544`|`5567/44544`|
|19|`9/5`|`16983563041/9990331200`|`999033119/9990331200`|

This separate pure-density saving is positive. The simultaneous-zero result does not remove it and does not rule out a stronger tradeoff that retains actual pure geometry.

The displayed full test is also not maximizing. Its original zero-layer modulus3 test is residue0, inactive on S. Changing that single test to residue1 adds the indicator of a set of old mass1/2. Since L>=1, its physical square rises by at least3/2. Thus no assertion about a common maximizing test or a dual mixture is supplied. Whether those extra optimizing constraints force a useful uniform saving remains unverified here.

<a id="exact-verification"></a>
### Exact verification

The adjacent verifier reconstructs every original forbidden and test class, checks all current-prefix intersections for disjointness, and computes every old row's exact mask count. This covers all current points by exact disjoint-cylinder cardinalities, including the entire period48148401221235 at19. It does not sample that period or normalize a truncated current law.

It checks every row's genuine kernel normalization, all distinct old block layouts and their loads, the entire ordered-exponent covariance sum, positive charge, and exact killed excess. It also reconstructs the full physical and killed test squares using the exact clean-prefix first and second count sums. Default operation compares `certificate.json`; `--write` explicitly regenerates it. Run `python3 -I -O /tmp/erdos7-0916/current-joint-tradeoff/verify.py`. This is ordinary mathematics and exact finite verification, with no new Lean declaration or canonical status claim.

The [joint-zero verifier](../verify_current_joint_zero.py) reconstructs the
[complete-label certificate](../certificates/current_joint_zero_certificate.json). Default
mode verifies every field; `--write` regenerates. It evaluates the whole
current period by exact disjoint-prefix cardinalities, without sampling.

<a id="rro53-and-the-current-prime-root-overlap-interface"></a>
## RRO53 and the current-prime root-overlap interface

[RRO53.5](https://github.com/the-omega-institute/trureturing/blob/387d32951f23706f94532f9165699764966ea655/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L22220) classifies the
complete graph of unit-pair sums, including pairs on either side of any
chosen bipartition. The finite-core current-prime interface keeps only
the overlap between forbidden roots and test roots. Its exact capacity
is different.

Let L and R be finite sets of distinct original labels at one fixed
current-prime depth, and let Omega be the alphabet of effective roots,
of size q. Given maps a:L->Omega and b:R->Omega, put an edge ij exactly
when a(i)=b(j). Labels remain distinct even when their roots coincide.
For a proposed bipartite graph G on these fixed sides, let c_+(G) count
its components containing an edge; let i_L and i_R indicate whether it
has an isolated vertex on the respective side. Then such root maps
exist if and only if

    every component containing an edge is complete bipartite
        with the specified left and right sides, and
    c_+(G)+i_L+i_R <= q.                              (CR1)

Proof. Every edge equates its two root labels, so all vertices of a
connected component containing an edge have the same root. Every
cross-side pair in that component must therefore be an edge. Two such
components cannot use the same root, since each contains both a left
and a right vertex, which would create cross-component edges. An
isolated vertex cannot use a root already used by any edge component.
If isolated vertices occur on both sides, their two sets of used roots
must be disjoint, or an edge would join an isolated left/right pair.
This proves necessity. For sufficiency, give each edge component one
distinct root; give all left isolated vertices one additional root if
needed, and all right isolated vertices another distinct additional
root if needed. This realizes exactly every edge and nonedge. Empty
sides and empty graphs are covered by the same rule.

At depth1, if the actual pure modulus-p forbidden root a0 exists, its
entire root is absent from the pure base. Keep every original label in
the inventory; mark labels with that root inactive, with zero current
contribution. Apply CR1 only to the remaining effective left/right
vertices, with q=p-1. The inactive labels are not ordinary isolated
vertices and do not consume colors in CR1. If the pure modulus-p class
is absent, the safe full alphabet has q=p. Thus the respective generic
depth1 capacities are16 or17 at17 and18 or19 at19.

For active depth1 roots with a0 removed, the signed embedding

    u_i=a(i)-a0,  v_j=-(b(j)-a0)

uses units and satisfies u_i+v_j=0 exactly on the cross edges. It does
not specify the same-side pairs. Consequently RRO53's capacity
(p-1)/2 for the complete unit-sum graph cannot be imposed on this
projection. For example, take both sides to list every nonzero residue
once. The cross graph is(p-1)K2 and is actually realized, although its
number of edge components exceeds(p-1)/2.

The shape condition in CR1 can equivalently be enforced by excluding
induced bipartite P4s: three edges of a cross rectangle force its fourth
edge, since three root equalities imply the fourth. Together with CR1's
q-capacity this is an exact feasibility cut for an oracle that relaxes
unknown same-depth root-overlap matrices. Direct enumeration of actual
roots already satisfies these relations.

The edges here record only current-root equality. Old-cofactor
compatibility, activation, same-law mass and AP weights must remain
separate data. Distinct original labels with equal current roots cannot
be merged merely because CR1 puts them in one component. At a larger
fixed depth the same lemma uses its actual effective residue alphabet.
Across different depths, additional residue-prefix compatibility is
required. Refining to a common depth turns a shallower original label
into a union of leaves; selecting one leaf would change the event.

This elementary in-text consequence of residue labeling provides
finite-core feasibility pruning. It supplies no quantitative improvement
of the current same-law square/charge bound by itself and adds no Lean
declaration.

<a id="exact-limit-of-the-joint-integer-moment-refinement-at-w483"></a>
## Exact limit of the joint integer-moment refinement at W=483

For the two fixed schedules selected in SP, the simultaneous mean,
square and H1--H17 observations improve the SH27 cost bounds by exactly

    restart:  600111216928696/4705230572550772875
               =0.00012754129849227924...;
    fourstep: 13638891293834/216227850226171875
               =0.00006307647825924308... .             (JM1)

The resulting W483 defects are respectively
242.74746814910034... and 121.19483996554176..., both positive. Exact
dual majorants and matching abstract load distributions show that no
further tightening of these SH27 costs follows from this particular
set of univariate moment constraints. The separate SH26 physical-square
term is held fixed. This conclusion is specific to two schedules and
does not determine the best schedule among all255 choices.

<a id="fixed-sources-schedules-and-relaxed-moment-problem"></a>
### Fixed sources, schedules and relaxed moment problem

The restart route uses the actual supported AP(4,6)13 source of SP,
then physical steps17/T6 and19/T8. The fourstep route uses uniform
actual357 survivors, then physical steps11/T4,13/T6,17/T6,19/T8 with
one final conditioning. Source laws, every original labelled test,
residue and missing-class branch remain as in SP. The source bounds
apply at arbitrary finite original prime heights.

For each route write M,G,Hj for its simultaneous source bounds

    E L<=M, E L^2<=G, E(L-j)_+<=Hj, 1<=j<=17,          (JM2)

where L is a complete positive integer-valued labelled load. For the
fourstep source M=3071051/584325 and G=3849/106. For restart,
M=2621130891614589/246025127976511 and
G=6471426752685569/37850019688694. All17 hinge fractions are in the
source-pinned certificate. In particular M is a complete-load mean
bound, not a renamed cylinder-sum bound.

We maximize each SH27 cost over all positive integer distributions
satisfying JM2. Such an abstract distribution need not arise from an
actual congruence family or from the physical construction. This
enlargement gives valid upper bounds for the actual source loads.

Let d=p-1-T, c=(p-1)/d, a=(3p-1)/(p-1)^2 and let f be the product of
the later factors1+ac. For a given earlier auxiliary multiplier n,
the cost as a function of the source load is

    h(p,T,n;x)=483(nx-T)_+/d
       +f*a[(p-1)/(p-1-min(nx,T))-c].                  (JM3)

Different p,n terms may concern different actual complete test
layouts. Each bound is applied separately using JM2; no common
actual layout or common maximizer is assumed.

<a id="exact-dual-bounds-for-the-only-changed-term"></a>
### Exact dual bounds for the only changed term

Only p=19,T=8,n=1 changes. Its future multiplier is1 and its cost is

    F(x)=483(x-8)_+/10
           +(14/81)[18/(18-min(x,8))-9/5].             (JM4)

Define

    QR(x)=-7/135+(7/270)(x-6)_+
                        +(6517/135)(x-8)_+;
    QF(x)=-14/135+(2/135)(x-3)_++(1/270)(x-4)_+
                     +(1/135)(x-6)_+
                        +(6517/135)(x-8)_+.           (JM5)

Both majorize F for every x>=1. Below the first knot, the constant
equals F at that knot and F is increasing. Between consecutive knots
the majorant is a chord of the convex function F on[1,8]. For QR the
knots are6,8; for QF they are3,4,6,8. At and above8 each majorant is
exactly483(x-8)/10: its value at8 is zero and its slope is483/10.
Thus the entire unbounded load tail is proved by identity. The exact
verifier checks integers1,...,8 and that affine identity, which
suffices for the positive integer moment problem.

All hinge coefficients in JM5 are nonnegative; the mean and square
coefficients are zero. Substituting the respective Hj in JM5 therefore
gives dual upper bounds valid for every distribution in JM2.

The old integer expansion of F has coefficient7/1485 at H7. All
savings come from the valid convexity constraint

    E(L-7)_+ <= [E(L-6)_+ + E(L-8)_+]/2.              (JM6)

Each old bound table has H7>(H6+H8)/2. The improvement of the
unweighted19/T8/N1 term is exactly

    (7/1485)[H7-(H6+H8)/2].                           (JM7)

Multiplying by Pr(N=1), namely77/85 for restart and2156/3315 for
fourstep, gives JM1. Using the mean, square and the other retained
hinges simultaneously yields no additional gain for these costs,
as the feasible equality witnesses below demonstrate.

<a id="matching-abstract-distributions"></a>
### Matching abstract distributions

For restart put r=(H6-H8)/2 and use the distribution

    Pr(L=13)=H8-4r,
    Pr(L=12)=r-Pr(L=13),
    Pr(L=6)=1-r.                                      (JM8)

For fourstep put q=H3-H4, v=(H4-H6)/2, r=(H6-H8)/2 and use

    Pr(L=12)=H8-3r,
    Pr(L=11)=r-Pr(L=12),
    Pr(L=6)=v-r,
    Pr(L=4)=q-v,
    Pr(L=3)=1-q.                                      (JM9)

Substitution of the certified rational Hj gives nonnegative masses
summing to1. In each route E L=M, E L^2<=G, and every one of the17
hinge inequalities in JM2 holds. These are exact finite rational
inequalities checked and retained in the certificate. The dual
hinges with positive coefficients attain their upper bounds, and
QR=F or QF=F on the corresponding support, so these laws attain JM5.

For every other retained finite auxiliary multiplier, the old SH27
bound is already attained by the same law of its route. Explicitly,
if vj=h(p,T,n;j) and e=ceil(T/n), then on positive integers

    h(p,T,n;x)=v1+(v2-v1)(x-1)
        +sum_(j=2)^e(v_(j+1)-2vj+v_(j-1))(x-j)_+.    (JM10)

The slope after e is exactly483n/d. The existing helper checks the
finite identity, the final affine slope and nonnegativity of all
moment coefficients. The new verifier substitutes JM8 or JM9 in
every such cost and verifies equality with its retained upper bound.
This establishes the maximum for each term without a numerical LP
oracle or a finite load cutoff.

<a id="complete-auxiliary-tails-and-the-precise-limitation"></a>
### Complete auxiliary tails and the precise limitation

For each earlier physical prime q with its cap cq, the comparison
factor Nq has

    Pr(Nq=1)=1-cq/q,
    Pr(Nq=v)=cq(q-1)q^(-v), v>=2,
    E Nq=1+cq/(q-1).

The auxiliary product N uses independent comparison factors; this
does not assert independence of the actual forbidden events. The
probabilities Pr(N=n) for n<T are computed exactly. The full tail
probability and first moment are obtained by subtracting that finite
part from1 and product_q(1+cq/(q-1)). For every n>=T and x>=1, JM3 is
exactly483(nx-T)/d. Thus the complete tail cost is

    (483/d)[M E(N;N>=T)-T Pr(N>=T)].                 (JM11)

JM8 and JM9 have mean exactly M, so they attain JM11 as well. Every
tail probability, full auxiliary mean, tail mean and matching tail
cost is included in the certificate. No auxiliary height or product
distribution is truncated or renormalized.

Consequently the sum of optimized SH27 costs is the exact optimum
of the listed univariate moment relaxation for each fixed schedule.
This remains true if a single abstract law is required for all its
terms, since JM8 or JM9 attains all of them simultaneously. The
statement for actual layouts is only the separate valid upper bounds.

The W483 defect uses

    G*product_p(1+ap*cp)-1-483 + sum(SH27 costs).       (JM12)

The coefficient of G in JM12 is held fixed in this calculation.
Both matching laws have square slack, so they do not certify
attainment of the entire physical-square contribution or of the
full actual defect. They also do not identify an actual covering
layout, exclude further information about joint square/bad-mask
geometry, or settle unrestricted Erdős7. The reusable conclusion
is that improving only these SH27 cost terms through JM2 is exhausted
at the positive defects reported above.

The standard-library verifier pins the SP profile and the generic
`build_step`, `feature_value`, `verify_at` helper by SHA-256. The
helper's PG1 loader is not called and its13/T5-specific improvement
does not occur; an exact check rejects any such foreign-law input.
Default mode recomputes and compares the entire certificate;
`--write` regenerates it. All mathematical checks survive `-I -O`.

The [joint-moment verifier](../verify_joint_moment_limits.py) reconstructs
the [primal/dual certificate](../certificates/joint_moment_limits_certificate.json) using
only exact rational arithmetic and the pinned SP source.

<a id="direct-killed-law-comparison-and-a-smaller-complete-finite-core"></a>
## Direct killed-law comparison and a smaller complete finite core

Use the actual supported AP(4,6)13 law of HC9 and SP4. Extend it through
actual pure-base AP17/T8 and AP19/T8, with normalized physical kernels on
every history and no intermediate conditioning. If Kp denotes a physical
kernel, its killed version Kp^- keeps just the actual mixed-good summand.
The final killed measure is

    eta=nu13 K17^- K19^-,  Q_eta(L)=integral(L^2-484)d eta.  (KC1)

The complete original test L includes its unit label, so L>=1. Strict
Q_eta(L)<0 for every complete test implies eta(1)>0, since the zero
measure would give Q=0. One final normalization then gives every complete
square below484. Final survival is a consequence, not a premise.

The following bounds concern Q, not APC's physical-square-plus-assigned-
charge functional. They approximate the same underlying AP construction.
At the previous box20/current-depth8 cutoffs, the complete Q error is
less than0.000667. There is also a complete unequal box with4,889,808 test
labels and error less than0.263. Neither statement evaluates the finite
core inequality or completes the continuation beyond19.

<a id="independent-mass-and-square-errors-for-each-omitted-mask"></a>
### Independent mass and square errors for each omitted mask

Let B=(b_q) be the vector of old original-cofactor cutoffs. The current
pure and mixed cutoff k need not equal any b_q. For i=0,2 put

    z0(p)=1, u0(p)=p/(p-1), t0(p,k)=1/[(p-1)p^k],
    z2(p)=Phi_p(0), u2(p)=Sigma_p,
    t2(p,k)=sum_(a>k)p^-a Phi_p(a),

where Phi and Sigma are the complete two-test/one-query factors in APC2.
Define

    U_i(B)=product_q u_i(q),
    V_i(B)=product_q[u_i(q)-t_i(q,b_q)],
    Z_i(B)=product_q z_i(q), R_i(B)=U_i(B)-V_i(B).

The queried-label tail R_i includes every label with any old exponent
outside B. In its weighted version the two test axes remain complete.
The complement of an unequal box can equivalently be partitioned by
its first coordinate exceeding its cutoff; the product difference is
exact and contains no finite-height restriction.

For threshold T at p set

    s_*=(p-2)/(p-1), delta=(T-1)/(p-2),
    C=1/(1-delta), ell=max(C^2,C/delta), c=C/s_*.

If the source probability has Haar density at most D_* and complete
square at most J_*, use J_0=1 and J_2=J_*. The direct physical or killed
kernel error is bounded by

    epsilon_p,i = D_* R_i(B)
       [c(u_i(p)-z_i(p))+(ell/s_*^2)z_i(p)/(p-1)]
      +D_*[V_i(B)-Z_i(B)]
       [c t_i(p,k)+(ell/s_*^2)z_i(p)t0(p,k)]
      +J_i[c t_i(p,k)+((ell+C)/s_*^2)z_i(p)t0(p,k)].   (KC2)

This is APC3 with separate old cutoffs and current cutoff. Its three
terms cover old-cofactor tails at every positive current depth, retained
nonunit cofactors at omitted current depths, and pure-current tails.
For i=0 the weight is1: old and current query masses are D_*/d and
p^-a. For i=2 the original complete test-pair weights give Phi. The
pure-base coefficient ell+C still pays both the changed region and the
common-region density change. Thus epsilon_0 is an L1 error in its own
right; it is not inferred by paying the much larger square-weighted
error as mass.

At17 use (D_*,J_*)=(D,G), where

    D=1039695426000000/18925009844347,
    G=6471426752685569/37850019688694.

At19 use (2D,(89/64)G), valid for the unconditioned physical17 measure.
The killed17 input is dominated by this physical measure, so it has the
same direct error bounds. For box20/current8, exact evaluation gives

|error|upper bound, decimal display|
|---|---:|
|epsilon17,2|0.0001293444399147029...|
|epsilon19,2|0.0002832646182242736...|
|epsilon17,0|0.000000010898327478914162...|
|epsilon19,0|0.000000014506721280970769...|

All four values use the same actual HC13 source bounds.
