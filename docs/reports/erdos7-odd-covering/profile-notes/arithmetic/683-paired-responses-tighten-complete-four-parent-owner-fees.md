# Paired responses bound arbitrary-phase owner loads on one actual source

The four simultaneous response measures of [Report678](678-native-null-geometries-admit-a-uniform-common-phase-bound.md) can be used together before the central3/5 comparison. This gives an increasing-convex upper comparison for arbitrary globally fixed phases at7 and11. The nested depths in the bound are auxiliary variables; the actual original cylinders need not be nested or share phases.

The resulting comparison measure is positive. Consequently its complete stop-loss expectation is increasing and convex in the remaining central factor. This avoids applying a signed mixed hinge coefficient term by term to a convex-order theorem. It preserves original numerical labels and all finite exponent heights.

On666's unchanged193 actual rows, the resulting universal four-parent comparison fees are strictly smaller at every row. Their total is0.00689994005222675..., compared with0.007308948765250718... before. The complete paid policies gain reserve; their first four-parent cutoffs remain unchanged. The all-four-parent total does not itself fit the head gate and is not a policy allowing four parents from37.

The theorem applies to678's actual unnormalized matching source and its later restrictions. Four scalar prefix bounds alone do not supply its hypotheses. It does not automatically apply to the different exact source of681/682. The complete row comparison below lowers the four-parent fees with the existing rows and tails; it does not remove the head or network restrictions. This is an ordinary mathematical result, not new Lean verification or a claim of research originality.

## 1. A two-coordinate theorem for arbitrary actual phases

Let P1 and P2 be fixed probability laws and nu one finite positive measure on their product space. For T subset{1,2}, assume the simultaneous marginal-measure inequalities

    nu_T <= r_T P_T,
    P_{1,2}=P1 product P2,

where the empty-coordinate inequality means nu(1)<=r_empty. The inequalities hold for every measurable event, equivalently for every nonnegative measurable function of the stated coordinates.

For coordinate i, let u_i(e), e>=1, be a decreasing sequence in[0,1] tending to zero. Put a=u_1(1), b=u_2(1), and

    p_i(k)=u_i(k)-u_i(k+1), k>=1.

Each positive-depth original event A_(j,i) has P_i mass at most u_i(e_(j,i)). Exponent zero means the constant-one indicator. Let J be any finite set of original numerical labels, with nonnegative weights w_j, and define

    F=sum_(j in J) w_j I_(j,1) I_(j,2).

Every A_(j,i) keeps its own globally fixed phase. Its phase may depend on the full label, including the other coordinate's exponent. No compatibility across different labels is assumed.

Assume

    r_1-b r_12 >=0,
    r_2-a r_12 >=0,
    r_empty-a r_1-b r_2+ab r_12 >=0.

Define a finite positive measure tau on nonnegative integer pairs by

    tau(y,z)=r_12 p_1(y)p_2(z),                    y,z>=1;
    tau(y,0)=(r_1-b r_12)p_1(y),                  y>=1;
    tau(0,z)=(r_2-a r_12)p_2(z),                  z>=1;
    tau(0,0)=r_empty-a r_1-b r_2+ab r_12.

Its mass is r_empty. Use the same original labels and weights to define

    Fsharp(y,z)=sum_(j in J) w_j
                  1_(y>=e_(j,1)) 1_(z>=e_(j,2)).

For every nonnegative increasing convex phi,

    integral phi(F) dnu <= integral phi(Fsharp) dtau.       (P1)

This is a bound on the entire load, not a product of separately optimized original-event estimates.

## 2. The first rearrangement keeps four nonnegative support pieces

Fix the actual second coordinate. Write B for the sum of labels not querying coordinate1 and write c_j>=0 for the contribution of each label querying1 once its first-coordinate indicator is removed. Order these labels by decreasing u_1(e_(j,1)), breaking ties by their fixed numerical labels.

Put

    d_j=phi(B+sum_(k<=j)c_k)-phi(B+sum_(k<j)c_k).

If only some of these events are active, convexity bounds each increment along that active subchain by its full-chain increment. Hence

    phi(F)<=phi(B)+sum_j 1_(A_(j,1)) d_j.                 (P2)

Let C be the constant load querying neither coordinate. Replace c_j by c_j0=w_j for labels querying only1 and by0 for labels querying both coordinates. Define the corresponding d_j0 at base C. For a first-coordinate-only label, the added amount is unchanged and its full-chain base is larger; for a joint label, d_j0=0. Thus

    0<=d_j0<=d_j.

The right side of(P2) decomposes into four nonnegative functions with the indicated supports:

    empty:  phi(C);
    {2}:    phi(B)-phi(C);
    {1}:    sum_j 1_(A_(j,1)) d_j0;
    {1,2}:  sum_j 1_(A_(j,1))(d_j-d_j0).

Apply the corresponding marginal-measure domination to each piece. The reference joint measure is P1 product P2, so the original first-coordinate event can then be integrated using its cap u_1(e). In the common-uniform nested family these caps are attained and the active labels form a prefix of the ordered list. Therefore the ordered-chain identity is exact after replacement.

Write Y for the resulting nested auxiliary depth, with mass1-a at0 and mass p_1(y) at each y>=1. Let F^(1) be the load with only its first-coordinate events nested, let F1(Y) retain labels whose support is contained in{1}, and let F2 be the original load with support contained in{2}. The comparison just obtained is

    integral phi(F) dnu <= Lambda(F^(1)),

where, for a load H with these support restrictions,

    Lambda(H)=r_empty phi(C)
      +r_1 E1[phi(H1)-phi(C)]
      +r_2 E2[phi(H2)-phi(C)]
      +r_12 E12[phi(H)-phi(H1)-phi(H2)+phi(C)].          (P3)

No signed component was passed through a measure inequality in deriving(P3).

## 3. The zero-depth atom makes the second rearrangement positive

At Y=0 all positive-depth first-coordinate labels vanish, so F^(1)(0,x2)=F2(x2) and F1(0)=C. Collecting the second-coordinate-dependent terms of(P3) gives

    (r_2-a r_12)[phi(F2)-phi(C)]
      +r_12 sum_(y>=1) p_1(y)
           [phi(F^(1)(y,x2))-phi(F1(y))].              (P4)

Every bracket has the form phi(D+sum_j v_j I_j)-phi(D), with v_j>=0. It is an increasing supermodular function of the active second-coordinate label set. All coefficients in(P4) are nonnegative. The same ordered-chain argument can therefore replace all actual second-coordinate events by ONE common nested auxiliary depth Z, even when the actual phases vary with the other exponent or full numerical label.

Expanding(P3) for the fully nested load gives exactly the four blocks of tau in section1. This proves(P1). The intermediate actual events and nu were never replaced by a claimed actual nested joint law; nesting occurs only in the comparison.

For finite J the load is bounded and all integrals exist. The auxiliary tails are complete, so no upper bound on original exponent heights is imposed. Subsequent nonnegative completions may use monotone convergence; positive tails are not truncated.

## 4. The actual matching source supplies the stronger measure hypothesis

For each actual central cell c in678, its unary submeasures satisfy

    xi_(q,c)<=rho_q, xi_(q,c)(1)=Z_q(c),

where rho_q is the actual normalized pure survivor law fixed for the whole original family. The final references in(P1) are rho7 and rho11. The intermediate cell-dependent laws xi_(q,c)/Z_q(c) and the auxiliary depth laws are not substitutes for these references.

At fixed c let P_c be the product of normalized unary laws, let F avoid all actual pair-edge events, and let F_out(T) avoid only edges disjoint from the queried support T. The inherited strict conditional Shearer construction gives

    P_c(F)/P_c(F_out(T)) >= S_all/S_out(T),

where S is its positive matching polynomial. For ANY measurable query A_T, product independence implies

    P_c(A_T intersect F)
      <=P_c(A_T intersect F_out(T))
      =P_c(A_T)P_c(F_out(T)).

Multiply the resulting conditional-query bound by the actual source mass (product_q Z_q)S_all and restore unary masses. Its T marginal obeys

    zeta_(c,T)<=H_T(c) product_(q in T)xi_(q,c)
              <=H_T(c) product_(q in T)rho_q.          (P5)

Thus the response bound is a marginal-measure domination for all nonnegative measurable payoffs, not merely a single-cylinder bound. Every support uses the SAME zeta_c. Pair padding, scalar thinning, actual guarded/head-good restrictions and retention fields bounded by one preserve(P5).

The disintegration is

    dSigma=d(rho3 product rho5)(central) dnu_c(outside),

with an UNNORMALIZED outside subkernel nu_c. Normalizing the final law conditional on its central coordinate would give conditional mass1 and would invalidate a bound with r_empty<1. The fixed central15 mask may remain in nu_c and only reduces its mass and marginals.

## 5. One uniform positive comparison measure

Use Q={7,11,13,17,19} and678's parameters

    r_q=1/(q-1), a_q=1/[q(q-2)],
    b_qs=a_q r_s+r_q a_s,
    Z7(0)=5/6,
    Zq=(q-2)/(q-1)-2a_q for q>7.

The all-induced strict region makes every unqueried edge derivative nonpositive and every unary-mass derivative positive. Therefore all four actual responses for T subset{7,11} satisfy

    H_T(n,b+d activation)<=H_T(n,b)<=H_T(0,b)=R_T.

Exact matching-polynomial evaluation gives

    R_empty=4772450719173523/8462661375168000;
    R_7=27737260658149/40298387500800;
    R_11=5537579678017/8548142803200;
    R_7,11=10660439701/13568480640.

With u_q(1)=1/(q-1) and u_q(e)=1/[(q-2)q^(e-1)] for e>=2, a=1/6 and b=1/10. The three nontrivial tau coefficients are

    R_7-b R_7,11=3071388758369/5037298437600>0;
    R_11-a R_7,11=1104558377353/2137035700800>0;
    R_empty-a R_7-b R_11+ab R_7,11
      =84106036967663/211566534379200>0.

These R values are the matching baseline. They are not656's linear union-polynomial values: positive two-edge matching terms contribute to the first three entries. They also upper-bound the older linear responses, but the reference source in an application must be stated.

## 6. Legal central completion and continuation boundary

First integrate all later actual normalized kernels backwards, using full-history caps at queried coordinates and normalization at unqueried ones. Fixing the resulting independent comparison auxiliaries leaves a nonnegative payoff on the actual core. It is not conditioning on actual later observations or feeding an auxiliary value into an earlier actual kernel.

Apply(P1) to the complete7/11-dependent original-label sum while retaining every actual central indicator and phase. For each fixed(y,z), compare the central rectangle indicators using the same central cap order, and integrate the inequalities against the positive tau measure. Only after these comparisons may original labels be aggregated. In particular,

    J_s(A)=integral (A(1+y)(1+z)-s)_+ dtau(y,z)

is nonnegative, increasing and convex for A>=0. Here A=(1+L3)(1+L5) is the completed auxiliary central factor, not a claimed actual pair of nested depths.

For each fixed nonzero parent exponent vector e, keep every original owner height h and its phase through the comparisons. Numerical modulus uniqueness and the full geometric height sum give

    beta_e=sum_(present h) (v-1)/v^h<=1.

Completing absent exponent patterns therefore bounds the auxiliary load by product_p(1+L_p)-1. The zero vector is not inserted because pure owner powers are already paid by the actual ordinary domain. This yields

    (completed load-t)_+ <= (product_p(1+L_p)-(t+1))_+,

and gives precisely s=t+1. No duplicate numerical label or newly chosen original phase is introduced.

If656's central-mask rebate is used, retain the mask during the noncentral comparison and perform its fixed-baseline split only afterwards. A signed mixed difference of hinges is not itself guaranteed increasing or convex and cannot be compared separately.

## 7. Keep a valid bound for every parent branch

The paired theorem first gives a fee for the canonical parent set{3,5,7,11}. Every other four-parent set retains655's existing product/omitted-mass fee. At a fixed owner threshold take the maximum of the new canonical bound and every old noncanonical bound. Each term is an upper bound for its own actual parent set on the same source, so this maximum is a valid universal row fee. No new ordering theorem for the paired comparison measures is assumed.

There are386 complete padded branch types: choose a subset of the ten literal head primes of size k<=4, and use the ordered outside envelopes for the remaining4-k roles. At owner v keep only types with at most the number of possible earlier outside primes. Thus one head-subset/outside-count type represents all actual choices at those ordered cap bounds; it does not identify different original labels or phases. The numerical certificate tests the complete finite census at each of193 actual owner thresholds, with full-height hinges.

For fewer than four parents, add unused earlier head roles only to the comparison. Keep their initially absent exponent patterns at weight zero and then complete nonnegatively. If the padded type is canonical, the paired theorem applies directly to these zero-weight labels. Otherwise the existing product comparison applies. This operation does not change the actual parent union, phases, row or Euler cap.

There is also an analytic check on the noncanonical census. Fix one noncanonical parent p. The exchanges from655 can insert3,5,7 while preserving that parent, leaving{3,5,7,p}. A selected Q or later-head p>=13 is dominated by13 using the same cap and omitted-mass comparisons. For an outside parent, use655's whole-product inequality

    Pr(X3 X13>t)>=D13 Pr(X3 X_outside37>t),

and condition on the independent common factor X5 X7. This covers the first-depth exception at the outside37 envelope; it does not assert that X13 alone dominates that envelope. Hence the old noncanonical fees are bounded by the old{3,5,7,13} fee with omitted factor D11 D17 D19. The direct census supplies a separate finite check at the adopted thresholds.

## 8. Complete-height row fees and the unchanged policies

Keep666's193 rows at primes37<=v<1253, the same integer h_v, cap c_v=(v-1)/h_v, ordinary-domain debit

    D_v*=v-2-2^(-16), t_v=D_v*-h_v,

and the actual normalized kernels. Each cap still satisfies c_v/v<1/10. The new fee for a four-parent row is

    B_v=(1/h_v) integral
           (X3 X5 (1+y)(1+z)-(t_v+1))_+
           d(P3 product P5 product tau).

The measure in this integral has mass R_empty, not one. Its complete product and count means are

    M=(8/3)(R_empty+R_7/5+R_11/9+R_7,11/45)
      =2231434375217837/1057832671896000,
    M-R_empty=4359674760856391/2820887125056000.

For s=t_v+1, compute the full hinge by

    integral (P-s)_+ dmu
      =M-s R_empty+sum_(integer k<s) (s-k) mu(P=k).       (P6)

Only the negative part is finite. Its largest required endpoint is1080. The full mean retains every positive tail, so this calculation imposes no bound on original exponent heights. In particular subtracting s instead of s R_empty would be an invalid normalization.

The certificate computes the canonical fee exactly and rounds each output outward to multiples of10^(-90). Each old noncanonical branch is enclosed by directed arithmetic at that same scale, using its complete mean. At all193 thresholds, the new canonical LOWER endpoint exceeds every eligible old noncanonical UPPER endpoint and the inherited three-parent upper endpoint. Thus the new canonical interval bounds the full maximum in section7. The old{3,5,7,13} branch is the maximizing noncanonical comparison at every adopted threshold. No claim is made about arbitrary unadopted thresholds or row choices.

Use the inherited three-parent bounds before a cutoff P and the new four-parent bounds from P to1253. Keep the five-parent tail from1253, the TypeI fee1/65536, all326 Euler factors and either complete arbitrary-parent tail. The two alternatives are the RS switch at2^46 and the elementary switch at2^68. The complete projected reserve is

    (2673/110656)[193/100000-W_finite(P)
                     -W5-1/65536-E_policy].             (P7)

All194 possible finite cutoffs, including1253, are evaluated. The first positive cutoffs remain127 for RS and149 for the elementary policy. The first cutoffs retaining density greater than1/(2000000 Q_off) remain137 and191. The immediately previous possible cutoffs have even their reserve upper endpoints below the corresponding target. Since each new four-parent lower fee still exceeds the old three-parent upper fee, later cutoffs increase the comparison reserve.

The improvements at the retained density cutoffs are:

| Complete policy and first four-parent prime | Previous projected reserve | New projected reserve | Increase |
| --- | ---: | ---: | ---: |
| RS,137 |5.337302153105605e-7|5.408201247122068e-7|7.089909401646363e-9|
| Elementary,191 |5.048516293555438e-7|5.057002681555681e-7|8.486388000243288e-10|

At common cutoff191, the RS reserve is1.1741097236603517e-6 and the elementary reserve is5.057002681555681e-7. Decisions use rational interval endpoints; these decimals are explanatory. No h, actual kernel, Euler cap, private-interface condition or tail switch is optimized anew. The ordinary and private-domain hypotheses are exactly those retained by666/678.

## 9. Portable evidence and scope

The standard-library [certificate program](../../frontier/cover-geometry/paired_owner_fixed_rows_certificate.py) and [result](../../frontier/cover-geometry/paired_owner_fixed_rows_certificate.json) perform150,486 explicit checks. They recompute all four R constants from the matching recurrence, the positive tau blocks, full means, all193 canonical row fees, the386 padded branch census, early-owner eligibility, and both complete policies at194 cutoffs. Final fee intervals are rounded outward, and no optimizer or finite positive-tail cutoff is used.

The three pinned numerical inputs are `four_parent_tail_fixed_schedule.json`, `ordinary_domain_five_parent_certificate.json` and `joint_square_pair_225_star_certificate.json`. Their hashes, inherited row identities, Euler/tail data and rational reserve endpoints are retained in the result. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/paired_owner_fixed_rows_certificate.py
```

The actual-source measure bridge, arbitrary-phase rearrangement and numerical-label completion are the ordinary proofs above. A separate ordinary review checked them against the inherited source construction. Finite arithmetic does not establish these unbounded quantifiers by enumeration, and none of this is Lean verification.

The separately authored [independent checker](../../frontier/cover-geometry/paired_owner_fixed_rows_independent.py) reads the retained data without reading or importing the producer. Its [result](../../frontier/cover-geometry/paired_owner_fixed_rows_independent.json) records8,947 explicit checks. It reconstructs all193 paired, old three/four-parent and old{3,5,7,13} runner-up fees with exact rational arithmetic, encloses them in the published intervals, and reproduces the exact-fee fingerprint and both194-cutoff fingerprints. Its global noncanonical conclusion uses the separately reviewed runner-up proof of section7; it does not claim an independent recalculation of every individual385 branch interval width. The proof reviews and both implementations are within the same model family.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/paired_owner_fixed_rows_independent.py
```

This advances the complete fee comparison while retaining the original conditional source and network hypotheses. It does not remove678's fifty root-incidence slots or the declared early-parent/private-domain restrictions. The original unrestricted phase, higher-pure and network requirements of Erdős #7 remain open.
