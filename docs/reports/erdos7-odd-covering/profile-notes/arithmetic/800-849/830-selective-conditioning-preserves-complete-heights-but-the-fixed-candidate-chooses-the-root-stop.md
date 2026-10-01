# Selective conditioning preserves complete heights but the fixed candidate chooses the root stop

A finite stop/split dynamic program gives a complete-height hinge bound on
one actual retained source, no larger than either the whole-source stop or
the fully colour-conditioned comparison. For the unchanged Report827
phase31/C candidate, its exact 2916-box computation selects the root stop
at every integer threshold0 through28. The root stop is therefore optimal
throughout the whole real interval[0,28]. Its best continuation gate is
strictly below -7/50. Even replacing the entire nonnegative moment/tail
debit by zero leaves the best gate strictly below -9/100.

This is an obstruction for this fixed candidate, source point, inherited
mass floor and stated proof class. It does not obstruct other retained
tables, sharper source bounds or other hinge comparisons, and does not
settle unrestricted Erdős #7. The universal arguments below are ordinary
mathematics with exact rational controls, not new Lean verification.

## Reuse and the precise addition

Report790 PC9–PC11 proves the coordinatewise nested-event comparison for
arbitrary cofactor phases and complete heights. [Report828](828-colour-conditioned-root-hinges-preserve-one-retained-source.md)
uses it on each actual colour cell, preserving a common ternary mixture.
Report820 fixes the actual live/clipping cells on which its unnormalized
coordinate measures are affine in whole probability blocks. Report05 HG6
and Report06 DV6 already combine whole-cost bounds while retaining one
actual measure and normalization. Problem-details55 gives a different
adaptive-coordinate decision-tree proof: its rows build an actual source
under transcript-conditional caps. Here the source is already fixed and
the tree only partitions an integral into independently valid upper bounds.
No source is rebuilt by the choices of this tree.

The construction below combines these source and comparison interfaces
with a finite proof-class minimum. It makes no literature-priority claim.

## The same actual source on every box

Keep the actual product law lambda_w, the normalized five-leaf weights w,
and one table `0<=u_l(s)<=w_l` from Report810. The five ternary leaves are
(4,7,2,5,8), with roots {4,7} and {2,5,8}; beta_l is normalized Haar within
leaf l. The nonternary product coordinates are the same actual lambda_q,
with category probabilities pi_q(c) and uniform all-height cylinder caps
C_q/q^e. The unnormalized retained measure has density u_l(s) relative to
`beta_l tensor product_q lambda_q`, summed over l.

Fix one live/dead pattern. A partial colour box B fixes some coordinates
to one live category and leaves the others free. The all-colour source
has three categories at 5 and two at each of the other six coordinates,
so there are at most `(1+3)(1+2)^6=2916` boxes and `3*2^6=192` full boxes.
Dead-category branches are omitted. On each nonempty box put

    v_l(B)=max_(live s in B) u_l(s),
    M_B=sum_l v_l(B),
    R_B=max(v_4+v_7,v_2+v_5+v_8),
    V_B=max_l v_l(B).

Use v=0 when a box has no live assignments. The comparison measure

    nuhat_B = [sum_l v_l(B) beta_l]
               tensor product_(q fixed) (lambda_q restricted to its colour)
               tensor product_(q free) lambda_q

dominates the actual `nu_u restricted to B`, since u_l(s)<=v_l(B) at every
point in B. Also v_l(B)<=w_l. This changes only the upper comparison, not
the actual retained source, survivor U, or eventual denominator alpha_u.
Both measures here are unnormalized; no cellwise normalization is used to
replace the actual continuation law.

## An exact complete-height stop cost

Define the unnormalized ternary auxiliary measure tau_B on positive
integers by

    tau_B{1}=M_B-R_B,
    tau_B{2}=R_B-V_B,
    tau_B{n}=2 V_B 3^(2-n),              n>=3.

It is positive because `0<=V_B<=R_B<=M_B`. Its mass is M_B and its complete
mean is `M_B+R_B+(3/2)V_B`. When M_B=0 it is the zero measure.

For a free coordinate q use a positive-integer auxiliary probability
measure of mass 1 with tails `Pr(N_q>=e+1)=C_q/q^e`, e>=1.
For q fixed to a live colour c, use a measure of mass pi=pi_q(c), with tails

    mass{N_q>=2}=min(pi,C_q/q),
    mass{N_q>=e+1}=C_q/q^e,                e>=2.             (S1)

This formula requires the Report820 cell condition pi>=C_q/q^2; its actual
live cells have a strict lower bound above that value. For a general colour
outside this domain the tails must instead be min(pi,C_q/q^e) at EVERY
depth, with all additional breakpoints retained. A dead colour gives the
zero measure at all depths; it must never retain positive deep tails.

Write mu_(q,B) for these measures, and define, for h>=0,

    C_B(h)=integral (n3 product_q nq-h)+
                          d tau_B(n3) product_q d mu_(q,B)(nq).          (S2)

For every fixed query layout a, with its one phase at each numerical
label, the 790/828 labelwise replacements applied to nuhat_B give

    integral_B (N_a-h)+ dnu_u <= C_B(h).                    (S3)

At each coordinate the other variables provide nonnegative coefficients;
every original label keeps its own literal cylinder until replacement.
Only after all coordinates have been replaced does the complete exponent
box factor into the product of auxiliary runs. Distinct labels need not
have compatible CRT phases or agree on shared-coordinate projections.
Completing absent labels is monotone, and finite complete boxes converge
by monotone convergence. The geometric first moments are finite. Thus S3
is uniform over all complete queries and all finite original heights.
There is no requirement that different boxes attain their comparisons
under one query, since each inequality already bounds the SAME query.

The stop cost is exactly finite to calculate at fixed h. If Z is the
positive integer product under the unnormalized auxiliary measure, then

    C_B(h)=mean(Z)-h mass(Z)
                     +sum_(integer 1<=n<h) (h-n) mass{Z=n}.             (S4)

Its full mean and mass are products of the coordinate full means and
masses. The finite correction uses only the atoms below h. This retains
all geometric tails; no exponent truncation occurs. At h=0, it is just
the complete mean. A fixed live coordinate has mean
`pi+min(pi,C_q/q)+C_q/[q(q-1)]`; a free one has mean `1+C_q/(q-1)`.

## Backward induction and exact proof-class minimum

Set

    D_B(h)=min(C_B(h),
               min_(q free) sum_(c live) D_(B,q=c)(h)).                 (S5)

With no free coordinate the only choice is the stop. All terms are
nonnegative. For a free q, the live child boxes partition the actual
source in B up to null sets. By induction each child integral for the
same query is at most its D value, so their sum bounds the integral in B.
The stop does too by S3. Their minimum remains a valid bound. Hence

    integral (N_a-h)+ dnu_u <= D_root(h)                  for every a.  (S6)

A proof tree either stops at its root or splits one free coordinate and
attaches a proof tree to every live child. Induction on the number of
free coordinates shows that S5 equals the minimum sum of leaf stop costs
among ALL such trees. Children may choose different later axes or stopping
depths. The tree has finite depth at most seven, and the finite box state
is sufficient for memoization. This is optimality within this stated
proof class, not among all possible hinge inequalities.

At the root, v_l<=w_l makes M_B, R_B and V_B no larger than the corresponding
whole-source ternary mass, root cap and leaf cap. For any increasing
nonnegative payoff, its integral against tau is nondecreasing in each of
M,R,V by summation over tails. The nonternary root runs are unchanged.
Consequently

    D_root <= C_root <= old H_h(w).

A fully split tree gives exactly the reviewed 828 root-mixture colour
bound, so also `D_root<=H_root,828`. These two comparisons hold on the
same u,w,pi, not at independently optimized sources. No strict gain is
guaranteed. Selected original phases and their nullity constraints remain
part of the original retained-source construction and are not rephased.

If L_cap and K_cap are the unchanged valid source and fourth-moment
quantities, the sufficient continuation numerator is

    (28-h)L_cap-D_root(h)-27 T29 T1600 K_cap,       0<=h<28.             (S7)

The actual normalization is still alpha_u=nu_u(U), and the pure-29 factor
occurs once. All inherited old-source and complete-tail premises remain.

## Fixed trees preserve the vertex argument; optimized trees need a guard

Fix u,w and ONE tree throughout a Report820 live/clipping product cell.
For a fixed colour, the auxiliary atoms are

    mass{1}=pi-min(pi,C_q/q),
    mass{2}=min(pi,C_q/q)-C_q/q^2,
    mass{n}=C_q(q-1)/q^n,                          n>=3.

On one fixed shallow clipping branch every atom and the full mean is
affine in the whole local pi_q block. The free-coordinate measures are
constant. Since the live set and u are fixed, v_l(B),M_B,R_B,V_B are fixed.
Thus each stop cost, and the sum for ONE fixed tree, is separately affine
in each whole local probability block. Formula S4 proves this also with
the complete geometric tail. The corresponding gate with fixed-tree cost
is block-concave, so the existing shared-table product-vertex argument
applies on that cell.

For fixed u, the optimized D_root is a minimum of these separately affine
functions and is separately concave; its negative is separately convex.
It therefore has the WRONG general curvature for the old gate argument.
The failure occurs inside this proof class. Use one q=7 coordinate, one
ternary leaf, h=0, colours{0}/nonzero, and retained weights u=(1,5/6).
Let pi be the singleton probability in[1/7,1/6]. This interval lies within
the declared outer source cell[5/41,6/35] with fixed clipping branches.
The root cost is21/5 and the split cost is

    (7/2)[2pi+1/35+(5/6)(6/5-pi)].

At pi=1/7,13/84,1/6 the optimal costs are251/60,21/5,21/5. The midpoint
exceeds the endpoint average by1/120, so the negative optimized cost is
not concave. These are points in the declared outer cell; realization of
every interpolated point by a finite pure family is not asserted.

Therefore a whole-cell certificate must use one common tree, or provide
an additional certified partition/cover and prove the tree's validity on
each part. Choosing the best tree independently at old source vertices
and retaining the old concavity claim is not justified.

At fixed pi, tail summation writes each stop cost as

    C_B=a_B M_B+b_B R_B+c_B V_B,       a_B,b_B,c_B>=0.                   (S8)

Each v_l is a maximum of table coordinates. Hence M_B is convex, R_B is
a maximum of sums of convex functions, and V_B is a maximum of convex
functions. S8 proves convexity and positive homogeneity in u; a fixed
tree sum is convex too. The optimized cost need not be convex. Take the
actual finite pure source
obtained by deleting1mod7, so pi(0)=1/6, with one ternary leaf, h=0 and
u=(1,t). The two available costs give

    D(t)=min(21/5,19/15+(217/60)t),         0<=t<=1.

At t=0,1/2,1 the values are19/15,123/40,21/5; the midpoint exceeds the
endpoint average by41/120. Thus there is no automatic single convex or
linear program for the tree-optimized table problem. At fixed pi and
fixed tree, epigraph variables for v_l>=u_l(s), R and V do give finite
linear upper-cost constraints, since S8's coefficients are nonnegative.
The same u must still be used across every certified source vertex.

## A same-source counterexample to greedy immediate splitting

Take the actual finite pure source obtained by deleting1mod7 and1mod11,
so the singleton-zero probabilities are1/6 and1/10. Each coordinate is
Haar on its normalized complement, with a uniform infinite suffix. Its
literal depth-e cylinder cap q/(q-1)/q^e is at most the unchanged default
C_q/q^e, where C_q=(q-1)/(q-2). Use one allowed ternary leaf and the
anti-diagonal table

    u(0,0)=u(1,1)=0,       u(0,1)=u(1,0)=1.

At h=0 the complete root stop is14/3. Splitting only7 then stopping both
children costs293/54; splitting only11 then stopping costs2821/550. Both
are larger than14/3. But fully splitting costs3367/1650<14/3. All costs
include the full geometric means and the same ternary mean7/2.

Thus discarding a first split because its immediately stopped children
cost more can miss a strictly better descendant tree, on a genuine common
source with the default caps. A fixed finite query using all twelve labels
3^a7^b11^c, a=0,1,2 and b,c=0,1, phase4 except phase8 at modulus77, has mean
4/5 under this retained source; this is below the recursive upper bound.
It exercises projected phases that depend on the numerical cofactor.

## Integer thresholds control the continuum, without interpolating the optimum

For fixed source and retained table, each fixed tree integrates hinges
of integer loads. Its cost is affine in h on every unit interval[j,j+1].
The optimum D(h), being a minimum of these affine costs, is concave on
that interval. It need not be affine. With L and tail fixed, the gate

    G(h)=(28-h)L-D(h)-tail

is convex there, and hence

    G(j+t)<=(1-t)G(j)+tG(j+1)<=max(G(j),G(j+1)), 0<=t<=1.

Integer endpoints0 through28 therefore bound every permitted real0<=h<28.
Endpoint28 is excluded from the continuation range and is used only to
bound the final open interval. Negative endpoint values prove failure on
the whole range; an endpoint supremum need not itself be attained in the
open range.

An actual class-internal counterexample to linear interpolation uses the
finite pure source deleting1mod7, one ternary leaf, and u=(1,4/5). On[0,1],

    D(h)=min(21/5-h,104/25-(5/6)h).

The two trees exchange at h=6/25. Values at0,1/2,1 are104/25,37/10,16/5;
the midpoint exceeds the endpoint average by1/50. Thus optimized D must
not be linearly interpolated as though one tree remained active.

## The unchanged phase31/C candidate selects the root stop

Reuse the exact candidate in [Report827](827-retained-factorial-hinges-preserve-complete-heights-but-need-not-improve-the-gate.md)
and its source C. The 106 nonzero retained coefficients, selected original
phases, source probabilities, survivor normalization, source floor L and
complete fourth-moment/tail debit are unchanged. Report828's full-split
curve is also reproduced exactly, as a dependency check.

The old ternary weight numerator is

    w=(21173425,21173425,19217717,19217717,19217716)/10^8.

Taking componentwise maxima of the already fixed table at the root gives

    v=(21173425,21173425,19217716,19217716,19217716)/10^8.

The two differences of10^-8 come from the inherited rationalization of
that table. They slightly tighten the root comparison but are not a
substantive gain from selective conditioning. No retained coefficient or
actual source is changed by removing these unused envelope amounts.

The exact computation includes all2916 partial boxes, their192 full-colour
boxes and thresholds0 through28. At EVERY integer threshold, stopping at
the root attains the DP minimum. A deterministic rule prefers stopping on
a tie, then the smallest splitting prime; it selects the same one-node
tree throughout. This does not claim that no other tree ties the optimum.

| h | Root stop = optimal D(h) | Fully split828 cost | Complete gate |
|---:|---:|---:|---:|
|16|0.29277688095662818...|1.1950722248591517...|-0.18656449106244655...|
|24|0.14524621039557972...|0.7114653195884888...|-0.14029691413905671...|
|28|0.11423859909615815...|0.58738671025840083...|-0.15992084965846445...|

The accompanying result retains the exact rational values for all29 rows;
decimals here are displays only. The allowed integer maximum and the
closed-endpoint maximum both occur at h=24, strictly below -7/50.
At h=16 the old-comparison difference is only3.811673226759535e-9; at h=24
it is1.734624230827285e-9, entirely due to the two envelope differences.

There is also an exact all-real optimality consequence. On each[j,j+1],
D is concave, is no greater than the affine root-stop cost, and agrees
with that cost at both endpoints. Concavity gives the reverse inequality
against their common chord. Therefore D equals the root stop throughout
[0,28]. No untested fractional threshold can introduce a better split in
this fixed proof class. The negative integer gates consequently bound all
permitted real thresholds.

Even the complete tail debit is not this candidate's sole obstacle. On
the same already computed curve, add back the unchanged nonnegative tail
cost to obtain `(28-h)L-D(h)`. Its maximum is also at24 and equals
-0.09461466357675041..., strictly below -9/100. The exact fraction and
comparison are checked in the result. Thus reducing only the nonnegative
fourth-moment/tail debit—even to zero—cannot repair this fixed candidate,
source point, mass floor and best hinge in this class. This does not
exclude changing the source, retained table, mass estimate or hinge class.

## Reproduction and scope

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/selective_conditioning_hinge.py),
[certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/selective_conditioning_hinge_certificate.json)
and [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/selective_conditioning_hinge.json)
use standard-library exact rationals. The certificate binds the existing
827 candidate and result and the existing828 result by content hash; it
does not copy or independently reselect a candidate.

Default execution recomputes and compares the saved result without
rewriting it. `--write-result PATH` explicitly regenerates the result;
`--input-dir PATH` relocates the three inherited input artifacts.

```sh
python3 -I -S -B selective_conditioning_hinge.py
```

The consumer checks complete local masses and means with their analytic
tails, every partial box and threshold, the exact DP and attaining tree,
the common-source partition, root/old and full-split828 comparisons,
the all-real endpoint and root-optimality deductions, and the zero-tail
margin. Its tiny controls also reconstruct the actual finite-pure greedy
example, table nonconvexity, fixed-cell negative-cost nonconcavity,
within-unit threshold switch, literal cofactor-dependent query, zero
table and dead-colour handling. All checks remain active under Python
optimization. Normal, optimized and relocated replays each complete90038
explicit checks, and18 mutation classes are rejected. An independent
implementation agrees with all29 exact root curves, selected-tree values
and the zero-tail diagnostic. Universal quantifiers and all heights use
the ordinary proof above.

The calculation changes the proof decomposition of one fixed source, not
its table or original family. There is no new solver, source sweep,
whole-cell certificate or claim against every possible retained kernel.
The common-tree restriction remains necessary for future source-cell
transport unless a separate valid transport argument is supplied.
