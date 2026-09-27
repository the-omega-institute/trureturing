# Retained reference blocks give a five-parent same-source comparison

The paired theorem of [Report683](683-paired-responses-tighten-complete-four-parent-owner-fees.md) extends to a retained reference block when the actual source supplies joint marginal-measure domination on every support enlarged by that block. Disintegration is against the fixed reference measure, without normalizing the actual conditional law. This gives a positive comparison measure for the five parents3,5,7,11,13 while preserving each original label and its arbitrary globally fixed phase.

On the unchanged193 owner rows, the complete five-parent comparison total decreases from0.01806976791983579... to0.016649386961474392.... The new canonical bound controls192 rows; owner41 retains the larger old outside37 bound. The total is not a policy allowing five parents from37. Complete paid policies use three, four and five parents in different ranges and retain the original infinite tails.

With683's four-parent fees already in place, the five-parent starting primes remain397 for the RS policy and587 for the elementary policy; the new five-parent bound increases their reserves. These are conditional results under678's actual matching source and the inherited head, ordinary-domain and network assumptions. They do not settle unrestricted Erdős #7. The proof and rational calculations below are ordinary mathematics, not new Lean verification or a claim of research originality.

## 1. A paired comparison retaining an actual reference block

Let P1,P2,PJ be fixed probability measures, and let nu be one finite positive measure on their product space. Suppose all four joint marginal-measure inequalities hold:

    nu_(T union J) <= r_T (P_T product PJ), T subset{1,2},
    P_empty=unit, P_{1,2}=P1 product P2.                 (R1)

The empty T condition bounds the entire J marginal. Separate bounds on the pair marginal and on the J marginal would not imply(R1). All inequalities refer to the same actual nu and hold for every measurable event, hence every nonnegative measurable payoff.

Use683's decreasing depth caps u1,u2 and write

    a=u1(1), b=u2(1), p_i(k)=u_i(k)-u_i(k+1), k>=1.

Assume the three coefficients

    r_1-b r_12,
    r_2-a r_12,
    r_empty-a r_1-b r_2+ab r_12

are nonnegative. Define the positive pair measure tau by

    tau(y,z)=r_12 p_1(y)p_2(z), y,z>=1;
    tau(y,0)=(r_1-b r_12)p_1(y), y>=1;
    tau(0,z)=(r_2-a r_12)p_2(z), z>=1;
    tau(0,0)=r_empty-a r_1-b r_2+ab r_12.

For a finite set of original labels j, nonnegative weights w_j, original coordinate events I_(j,i) of reference mass at most u_i(e_(j,i)), and bounded nonnegative reference-block functions G_j, the following holds for every nonnegative increasing convex phi:

    integral phi(sum_j w_j I_(j,1) I_(j,2) G_j(v)) dnu
      <= integral phi(sum_j w_j 1_(y>=e_(j,1))
                                  1_(z>=e_(j,2)) G_j(v))
                    d(tau product PJ).                 (R2)

Exponent zero means the constant-one indicator. Each positive-depth event retains its own actual phase, including dependence on the full numerical label. No nesting of the actual events is assumed.

To prove(R2), use the full-support inequality in(R1) to write

    dnu=f(x1,x2,v) dP1 dP2 dPJ, 0<=f<=r_12 a.e.

For each v, take the unnormalized kernel with density f(.,.,v) relative to P1 product P2. Integrating f over omitted pair coordinates gives the densities of the four marginals. By(R1) and Fubini, outside one PJ-null set these four densities are bounded by their respective r_T. There are only four supports, so the exceptional sets can be united. Density domination then supplies the inequalities for all measurable events simultaneously.

Apply683 to that kernel with weights w_j G_j(v), and integrate against PJ. The ordered-chain comparison uses fixed exponents and a fixed label tie-break, so the resulting functions are measurable. At no step is the kernel divided by its actual J-marginal density. On a finite prefix quotient, the same proof divides by positive reference atom masses; actual zero reference atoms have zero mass by domination.

If PJ is itself a product of fixed coordinate laws and each G_j is a product of their original cylinder indicators, apply the usual positive ordered-chain comparison to these coordinates after(R2). Fix the pair depths and all other reference coordinates, replace one coordinate's indicators by its common nested auxiliary, and integrate. Positivity of tau permits this iteration. Thus a retained product reference block can be compared by independent auxiliary depths after the pair comparison. This does not assert independence of the actual coordinates.

## 2. The actual678 source supplies the enlarged supports

At fixed actual central input c,683's measurable-source argument supplies an unnormalized outside subkernel nu_c, relative to the fixed central product rho3 product rho5, such that

    (nu_c)_U <= H_U(c) product_(q in U)rho_q
              <= H_U(0,b) product_(q in U)rho_q.         (R3)

Here rho_q is the actual normalized pure survivor law fixed for the entire original family. The inequalities concern all measurable queried events, not only cylinder maxima. They follow from the strict conditional Shearer response and product references in678. Actual central masks, head-good restrictions and bounded retention fields only reduce the same submeasure.

All later actual normalized kernels are integrated backwards before using(R3), retaining their full-history caps. Fixing comparison auxiliaries afterwards does not condition an earlier actual kernel on later observations. This is the same order of operations used in651,655 and683.

Take pair7,11 and retain J={13}. With Q={7,11,13,17,19}, the required four constants are the matching responses on the complements of13;7,13;11,13;7,11,13. Use

    D7=5/6,
    Dq=(q-2)/(q-1)-2/[q(q-2)], q>7,
    b_pq=1/[p(p-2)(q-1)]+1/[(p-1)q(q-2)],
    H(empty)=1,
    H(V)=Dp H(V minus p)
          -sum_(q in V minus p)b_pq H(V minus{p,q}).

Exact evaluation gives

    r_empty=621424177961/986324169600,
    r_7=5990546387/7827969600,
    r_11=1199347867/1660478400,
    r_7,11=20681057/23721120.

With a=1/6 and b=1/10, the four coefficients of tau13 are

    c00=274195883147/616452606000,
    c10=2654035753/3913984800,
    c01=1437103303/2490717600,
    c11=20681057/23721120.

All are strictly positive. Apply(R2), keeping each original13 indicator, and then compare13 under its fixed rho13 reference. The actual central indicators and phases remain until the positive central comparison. Any central-mask rebate would require its own lawful split; the fees here simply use the unmasked upper bound.

The diagnostic exact source in681/682 does not inherit(R3) merely from its prefix table or support. This theorem has no automatic application to that different source. The enlarged measurable domination would have to be proved there separately.

## 3. Complete original labels before computing the hinge

For each original numerical modulus with owner prime v, retain its complete parent exponent vector e, owner height h and globally fixed phase throughout the comparisons. Distinct numerical moduli permit at most one original for each(e,h). Thus, after comparison, every nonzero parent exponent vector has total weight

    beta_e=sum_(present h)(v-1)/v^h<=1.

Complete absent nonzero exponent patterns nonnegatively. Pure owner powers are already paid by the ordinary domain, so do not insert the zero vector. The completed count is

    C=X3 X5 (1+Y)(1+Z) X13-1,

under the positive measure P3 product P5 product tau13 product P13. The X variables and Y,Z are comparison auxiliaries. Arbitrarily large finite original exponent heights are allowed; positive auxiliary tails are complete.

For a row threshold t, put s=t+1 and P=C+1. The measure and complete means are

    mass=r_empty=621424177961/986324169600,
    integral P=(32/11)(r_empty+r_7/5+r_11/9+r_7,11/45)
               =4353261014017/1695244666500,
    integral C=11680669184521/6027536592000.

The full hinge is recovered by the finite negative part:

    integral(P-s)_+=integral P-s*r_empty
                     +sum_(integer k<s)(s-k)mu(P=k).   (R4)

The subtraction uses s times the actual comparison mass. Replacing it by s would silently normalize a measure that is not normalized. Only the negative part is truncated in(R4); the mean includes every positive-tail contribution.

The old canonical five-parent measure has omitted factor zeta5=D17 D19=4138163/4744224. In the block order11,10,01,00, its coefficients minus those of tau13 are

    287/697680,
    837100549/7827969600,
    43922707/293025600,
    1032648263699/4931620848000.

All are positive. Hence tau13 is blockwise dominated by zeta5 times the independent7/11 depth law. This proves a smaller canonical hinge at every finite threshold. A separate branch comparison is still required for a universal five-parent fee.

## 4. A complete branch bound, including the early exception

Replace only the canonical set{3,5,7,11,13} by the new paired bound. Every other five-parent type retains655's product and omitted-mass bound. Taking their maximum gives a valid row fee without asserting that the improved canonical measure dominates every other branch.

There are638 padded types: choose k of the ten literal head primes,0<=k<=5, and use the ordered outside envelopes for the remaining5-k roles. For owner v only types with enough earlier outside primes are eligible. In ascending owner order the first six eligible counts are252,462,582,627,637,638. An outside envelope bounds its assigned role; it does not merge original moduli or choose new phases.

Fewer than five actual parents can be padded by unused earlier head roles in the comparison. Apply the corresponding theorem with zero weights on newly added exponent patterns, then complete nonnegatively. No actual parent, row parameter or numerical original is changed.

There is also a small analytic cover of the old noncanonical alternatives for independent checking. Protect a parent outside{3,5,7,11,13}, then use655's exchanges to insert3,5,7,11 while retaining that parent. A remaining Q parent>=17 is bounded by17 with the appropriate omitted factor. A later head is one of23,29,31; an outside role is bounded by outside37. Thus retain the five old alternatives with fifth role

    17,23,29,31,outside37,

with outside37 eligible only when an earlier outside parent exists. These alternatives preserve the first-depth exceptions; singleton17 is not asserted to dominate every later-head or outside law. The full638 census separately checks the actual finite row comparisons.

On192 of193 rows, the new canonical lower endpoint exceeds every eligible old noncanonical upper endpoint. At owner41 the old type{3,5,7,11}+outside37 is larger:

    old outside37 fee=0.0029935506266142286...,
    new canonical fee=0.0029903587471914344....

Use the former at this row. The all-row totals are

| Bound on the unchanged193 rows | Sum |
| --- | ---: |
| Old canonical five-parent envelope |0.01806976791983579...|
| New canonical alone |0.0166461950820516...|
| Valid maximum over all branches |0.016649386961474392...|

None of these all-row totals pays the head gate by itself. The actual complete policies below allow five parents only after a later cutoff.

## 5. Complete policies with the original tails

Keep666's193 rows,37<=v<1253, the same h_v, cap(v-1)/h_v, ordinary-domain debit v-2-2^(-16), all326 Euler factors, TypeI fee, complete five-parent tail and arbitrary-parent tails. The five-parent row fee is(R4) divided by h_v, or the old noncanonical maximum if larger. The finite negative-part endpoint is1080.

For cutoffs p4<=p5, use three parents below p4,683's four-parent fees from p4 to p5, and the new universal five-parent fees from p5 to1253. The original five-parent tail begins at1253. The RS and elementary arbitrary-parent switches remain2^46 and2^68 respectively. Their common target is projected reserve>1/2000000, equivalently density>1/(2000000 Qoff) under the inherited projection.

| Complete policy | Three-parent rows | Four-parent rows | Five-parent rows | Projected reserve |
| --- | --- | --- | --- | ---: |
| RS |37..131|137..389|397..1249|5.006332164496716e-7|
| Elementary |37..181|191..577|587..1249|5.002121291233308e-7|

At the same fixed four-parent starts, moving the five-parent start to the preceding prime fails this particular target: the RS389 upper reserve is4.973695859925861e-7 and the elementary577 upper reserve is4.998798357787103e-7. These are failures of these fixed schedules and bounds, not impossibility statements about other sources or row choices.

The change attributable to the new five-parent estimate must be separated from683's earlier improvement. Using683's four-parent fees and the old five-parent fees already gives starts397/587 with reserves5.003907724689467e-7 and5.001952220582724e-7. The new five-parent estimate adds2.424439807249548e-10 and1.6907065058389563e-11 respectively, without advancing those starts. The older four-and-five bounds gave419/601 at these fixed four-parent starts.

Direct three-to-five schedules, with no four-parent interval, first become positive at191 RS and227 elementary; the density target is first met at211 RS and307 elementary. The certificate checks all18915 ordered cutoff pairs for each policy and retains the complete undominated cutoff frontier. It does not optimize new h_v values or claim global optimality over other policy classes.

## 6. Verification and unresolved scope

The [producer](../../frontier/cover-geometry/paired_five_owner_fixed_rows_certificate.py) and its [result](../../frontier/cover-geometry/paired_five_owner_fixed_rows_certificate.json) rebuild the matching constants, positive pair blocks, full means and all193 canonical hinges. Directed rational intervals at scale10^90 cover every old noncanonical branch and every policy decision. Input hashes pin the inherited row schedule,657's complete continuation data and683's four-parent result. The producer reports397141 checks. Its allbranch_upper_total encloses the sum of the published row upper bounds; that field's lower endpoint is not a lower bound on the exact fee sum. Row enclosures and policy endpoints retain their ordinary directed-bound meanings.

The [independent verifier](../../frontier/cover-geometry/paired_five_owner_fixed_rows_independent.py) and its [result](../../frontier/cover-geometry/paired_five_owner_fixed_rows_independent.json) report40736 checks. It enumerates matchings independently, constructs the dependent pair-product distribution by divisor convolution, matches all193 exact paired and old-canonical fee fingerprints, and checks the five old runner alternatives using the analytic cover in section4. It checks638 type identities and eligibility, both18915-pair policy fingerprints, exact endpoints, predecessors and the complete undominated cutoff frontiers. It does not import or execute the producer or duplicate its full noncanonical interval census.

Both programs replay with byte-identical output under Python's isolated standard-library mode. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/paired_five_owner_fixed_rows_certificate.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/paired_five_owner_fixed_rows_independent.py
```

The source proof is(R1)-(R3), not an inference from successful finite calculations. Neither the finite census nor a smaller row fee removes the head phase assumptions, the common-source requirement or the remaining unrestricted covering obstruction. A replacement seventh-moment tail would need its own complete moment comparison and tail certificate; this result retains the original tail.
