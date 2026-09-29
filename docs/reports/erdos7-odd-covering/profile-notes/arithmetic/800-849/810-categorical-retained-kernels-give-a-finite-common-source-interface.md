# Categorical retained kernels give a finite common-source interface

One fixed table of fractional retention, together with one five-leaf weight vector, gives a finite sufficient source certificate without requiring decreasing cores or a common safe colour. Its cylinder menus use one common queried colour assignment across all participating leaves. The complete source bound is separately concave in each whole local probability simplex, so one shared table can be checked on product vertices and optimized through a finite rational linear program.

A small exact example on the primes 3, 5 and 7 has retained mass 1693/4032, retained old-survivor mass 11/28 and full old-survivor mass 521/672. Its complete all-height inventory gives the lower bound 19499/201600 at the actual source and the uniform bound 433/8400 over all ten vertices of its declared categorical relaxation. The example includes fractional retention, an absorbed pure-25 original and unselected deep originals.

These are ordinary mathematical arguments and exact rational controls, not Lean results. The finite interface does not establish a positive solution for every actual phase family, or unrestricted Erdős #7. Finite does not imply that enumerating its general vertex product is practical.

## 1. Existing interfaces and the additional bridge

[Report530](../500-549/530-one-supported-law-controls-unused-and-deep-occupied-labels.md) and [Report794](../750-799/794-actual-prefix-orbits-make-all-height-source-search-sparse.md) already provide exact finite actual-carrier or actual-prefix-orbit source LPs, preserving numerical query labels and one actual survivor. Reports541–542 already use capped probability simplexes. Reports791–796 preserve common source roles and distinguish fixed-weight certificate failure from actual coverage. [Reports806](806-actual-ternary-leaf-cores-give-a-finite-common-source-linear-program.md)–[808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md) give fixed leaf-core source bounds, complete numerical inventories and categorical first-digit examples.

The additional bridge here is to remove the decreasing-core and common-safe-colour requirements while retaining a finite robust product-source certificate. Replacing a fixed core by a fractional retained kernel also permits the core and five source weights to vary jointly in one LP. This is an exact representation of the specified sufficient method, not a claim that the general convexity or minimax principles are new.

## 2. One categorical source, with a genuine retained submeasure

Let Q be a fixed finite set of odd nonternary head primes, disjoint from 29. The actual old family is finite, has pairwise numerically distinct odd moduli greater than one, and has support contained in {3} union Q. Every actual pure-3 or pure-9 original is respectively the usual 0 mod 3 or 1 mod 9, or is already null under the chosen five-leaf source. Every actual pure-q original, q in Q, is absorbed into the one normalized actual law lambda_q. All other pure ternary heights, including every 3^h with h >= 3, remain in the residual charge. These conditions identify the family to which the lower bound applies; they do not allow arbitrary extra pure originals to be silently discarded. Use the normalized ternary leaves(4,7,2,5,8), with roots A={0,1}, B={2,3,4}. Above ternary depth2 the source is Haar. Let lambda_q be the one actual normalized pure-q survivor law, satisfying for all positivee and literal phasesa

    lambda_q(a modq^e)<=C_q/q^e,

with fixed rational constants satisfying 1 <= C_q <= q. Throughout the concrete controls the inherited constants are C_q=(q-1)/(q-2), q >= 5. Alternate constants require both the displayed range and the actual cylinder inequalities at every height. The upper bound C_q <= q makes the query comparator below a probability law; the lower bound is also required by all-height cylinder normalization.

For eachq choose a fixed partition of Z/q into nonempty colour classes

    P_(q,c), c in C_q^colour.

Colour classes at one prime are mutually exclusive. They are not independent Boolean events. Let

    pi_(q,c)=lambda_q(x modq belongs to P_(q,c)).

The actual vector belongs to the rational capped simplex

    P_q={pi>=0: sum_c pi_c=1,
         pi_c<=min(1, |P_(q,c)| C_q/q)}.                         (K1)

Known additional rational linear restrictions may shrink P_q, provided the actual law satisfies them. Different primes remain independent under the full source. For a full colour pattern s, writepi(s)=product_q pi_(q,s_q).

Choose one vectorw_l>=0 withsum_l w_l=1. The full law is

    lambda_w=lambda3,w tensor product_q lambda_q.

Instead of choosing Boolean cores first, choose a retained-kernel table

    0<=u_l(s)<=w_l for everyleafl and every literal colour patterns. (K2)

Define nu_u using coefficientu_l(s) in place ofw_l on the leaf/colour cell, with the same actual lambda_q distributions within cells and the same ternary Haar suffixes. Equivalently its mass on such a cell is

    u_l(s) product_q pi_(q,s_q).

This defines one genuine positive submeasure satisfyingnu_u<=lambda_w. There is no division by a zero weight and no cellwise probability renormalization. Every query and every deletion uses this same tableu and the same actual lambda_q laws. Its exact initial mass is

    M(pi,u)=sum_s pi(s) sum_l u_l(s).                           (K3)

A fixed arbitrary Boolean leaf coreG_l is the special linear face

    u_l(s)=w_l 1_(G_l)(s).

No decreasingness is required. Allowing all ofK2 is a relaxation to actual fractional retention, not a relaxation to unrealizable joint colour allocations. Each feasibleu is a concrete submeasure on the same full carrier.

## 3. Every numerical cylinder has one common colour assignment

For supportD subsetQ and one colour assignmentkappa onD define

    A_(l,D,kappa)(pi,u)
      =sum_(s outsideD) [product_(q outsideD)pi_(q,s_q)]
                        u_l(kappa,s).                         (K4)

An actual n-cylinder withsupp(n)=D fixes one literal first digit at everyq inD, hence one commonkappa. Because the kernel sees only first digits, independence of the underlying product source gives

    nu_u(actual_n on leafl)
       =lambda_D(actual_n) A_(l,D,kappa)
       <=(C_D/n) A_(l,D,kappa),
    C_D=product_(q inD)C_q.                                   (K5)

The cylinder may have arbitrary finite exponents. Every positive exponent fixes its prime's first colour; exponent0 does not. Every tuple of nonempty colour classes onD has literal representatives whose CRT combination is a possible phase for such a numerical label. Source-null possibilities may be retained in the upper-bound menu; doing so only overestimates the loss.

The complete common-phase envelopes are

    F_(D,0)=max_kappa sum_l A_(l,D,kappa),
    F_(D,1)=max_(R in{A,B},kappa) sum_(l inR)A_(l,D,kappa),
    F_(D,2)=max_(l,kappa) A_(l,D,kappa).                         (K6)

The same kappa is used within each displayed sum. Replacing the first expression bysum_l max_kappa A_l is a possibly strict looser bound, not an exact reduction. In the second expression the colour choice is common across the leaves of the selected root. The third expression has only one selected leaf, so its joint maximum has no within-sum compatibility issue.

Thus an actual original3^h n has intersection mass at most(C_D/n)F_(D,h) for h=0,1,2, and at most

    (C_D/n)3^(2-h)F_(D,2) for h>=3.                            (K7)

These are upper bounds for a fixed actual original and its globally fixed phase. The maxima are not new source choices. Initial positive mass always comes fromK3, never from a query-colour maximum.

## 4. Selected-null constraints and complete residual inventories

Keep the usual finite selected setS of distinct shallow mixed numerical labels3^h n withh<=2,n>1. At h=0 require at least two nonternary support primes. Each present selected original has one actual phasea_m and consequently one fixedkappa_m onD.

A uniform pointwise sufficient nullity condition is

    u_l(kappa_m,s_outsideD)=0
      for every compatible retained ternary leafl
      and every outside colour completion.                    (K8)

These are linear zero constraints on the sameu table. They use actual selected phases; no independent rephasing by label, leaf or vertex is allowed. A selected cylinder proved null under the actual pure survivor may be exempted, but that exemption is extra certified source information. First-digit observations alone need not decide it.

Withbeta_D=product_(q inD)C_q/(q-1), beta_empty=1, subtract the selected numerical contributions from their appropriate complete inventories exactly as in801/806:

    R_(D,h)=beta_D-sum_(3^h n inS, supp(n)=D)C_D/n,

on the usual allowed shallow support/types, and zero otherwise. AllR are nonnegative. Phases do not multiply the inventory: each numerical label contributes once, with its ONE actual phase. All higher ternary powers are retained by sum_(h>=3)3^(2-h)=1/2, including empty nonternary support D=empty. This charge includes actual pure ternary powers of every height h>=3.

ForU the complete actual old survivor, K5–K8 and the union bound give

    lambda_w(U)>=nu_u(U)>=L(pi,u),
    L=M(pi,u)-sum_D R_(D,0)F_(D,0)
             -sum_D R_(D,1)F_(D,1)
             -sum_D [R_(D,2)+beta_D/2]F_(D,2).                 (K9)

This is the complete numerical inventory with arbitrary finite actual exponents. It is not the smaller inventory seen in a finite experiment. A selected absent label is free; subtracting it removes no actual remaining class.

## 5. Why product-polytope vertices suffice without monotonicity

Fixu and all probability vectors exceptpi_q. EachA inK4 is affine in the whole vectorpi_q whenq is outsideD, and constant whenq is inD. EveryF is a maximum of affine functions and is convex in that block. M is affine. The loss coefficients inK9 are nonnegative, soL is concave in each entire local probability blockpi_q.

Eachpi_q inP_q is a convex combination of its finite vertices. Repeated separate concavity proves

    L(pi,u)>=min_(v in product_q Vert(P_q))L(v,u).              (K10)

No monotone partial order, safe representative, simultaneous maximum across leaves, or independence of colours at one prime is needed. The vertex tuples need not be realized by actual finite pure families. This is a robust sufficient relaxation over the declared product polytope.

Theu table is held fixed in this argument. Choosing a new retention or new source weight at every vertex would change the required quantifiers.

## 6. Joint retention/weight optimization is a finite LP

Use global variablesw,u,alpha,r,v, and separate epigraph variablesz_(vertex,D,h) at every product vertex and each required support/type. Impose K2, normalization of w, selected-zero constraints K8, and any source-nullity restrictions from section 2. In particular, if a nonstandard actual pure-3 or pure-9 phase is null only because its compatible leaf weights vanish, impose w_l=0 on those leaves throughout optimization. An actual pure-cylinder nullity used to exempt a selected label must remain valid for the same chosen weights and laws; a weight-dependent exemption is not carried across the LP without its zero constraints. Also impose

    0<=alpha<=1,
    0<=v<=r<=1,
    r>=w0+w1, r>=w2+w3+w4,
    v>=w_l for everyleaf.

At a fixed product vertex, eachA inK4 is LINEAR in the retained tableu. For h=0 add the epigraph row

    z_(vertex,D,0)>=sum_l A_(l,D,kappa)(vertex,u)
      for EVERYcommonkappa.

For h=1 add one row for every joint(root,kappa), and for h=2 one row for every joint(leaf,kappa). Take0<=z<=1. Add at every vertex

    alpha<=M(vertex,u)-sum_D R_(D,0)z_(vertex,D,0)
              -sum_D R_(D,1)z_(vertex,D,1)
              -sum_D [R_(D,2)+beta_D/2]z_(vertex,D,2).          (K11)

These are finite rational linear constraints. From any feasible point, the epigraphs dominateK6 andK10 giveslambda_w(U)>=alpha for the one commonw,u. Conversely any retained-kernel certificate with uniform lower boundalpha is represented by taking each epigraph at its exact finite maximum. The conversion is exact for the stated residual-inventory method, not for all possible supported probability laws.

Whenalpha>0, use the ONE full-source restriction

    mu=lambda_w|U/lambda_w(U).

The retained kernel proves its denominator is large enough; it is not renormalized separately for each query. The full productlambda_w supplies the same complete query and fourth-moment comparisons as806. For a fixed integer threshold0<=h<28,

    H_h(r,v)=H0_h+Hr_h r+Hv_h v,

with nonnegative rational coefficients calculated from the full mean and finite subthreshold correction. To see both affine dependence and the coefficient signs, let J_q be independent auxiliary variables with tails

    P(J_q >= e)=C_q/q^e, e>=1,
    P(J_3 >= 1)=r,
    P(J_3 >= e)=v/3^(e-2), e>=2.

The cap range and 0<=v<=r<=1 make these genuine probability laws. Put N=product_q(1+J_q), and for a fixed value N let f(y)=(Ny-h)_+. Summation by tails gives

    E f(1+J_3)
      =E f(1)
       +r E[f(2)-f(1)]
       +v sum_(e>=2)3^(2-e) E[f(e+1)-f(e)].

Every displayed increment is nonnegative. Integrability follows from the finite mean, and the identity proves H0_h,Hr_h,Hv_h>=0. The nonternary mean is product_q[1+C_q/(q-1)]. For integer h, the identity

    E[(Z-h)_+]=E[Z]-h+sum_(1<=n<h)(h-n)P(Z=n)

computes each coefficient using only finitely many subthreshold atoms and the exact full mean. No truncated query inventory replaces that mean. Define A4(q)=sum_(e>=1)((e+1)^4-e^4)/q^e, a rational convergent series. With the actual pure-29 survivor factor, put

    Kq=product_q[1+C_q A4(q)] [1+(28/27)A4(29)].

Under the complete 29-admission and fourth-moment continuation of Report806, for any nonnegative certified source-independent full-tail coefficient T, maximize

    epsilon=(28-h)alpha-H0_h-Hr_h r-Hv_h v
                          -27Kq(1+15r+216v)T.                 (K12)

It is linear. Reducingr,v to their true maxima forw cannot reduce its value. A positive objective proves a final common distorted mass at leastepsilon/(27alpha). It uses the full lambda_w comparator throughout, despite the possibly correlated retained submeasure nu_u.

Fixed Boolean cores are the linear restrictionsu_l(s)=w_l 1_G_l(s), so their earlier LPs are special cases. Allowing arbitrary K2 is beyond [Report809](809-two-colour-core-obstructs-every-fixed-weight-full-box-certificate.md)'s fixed-core hypothesis. That observation alone does not supply a positive continuation certificate. A positive point certificate or restricted actual-family construction must still be checked on its declared source domain; no uniform positive solution for all actual families follows from this interface.

## 7. A nonmonotone core invalidates forced-miss replacement

UseQ={5}, the usual pure ternary anchors, Haar at5, and

    w=(2/5,2/5,1/15,1/15,1/15).

On the short root let the core ACCEPT precisely the5-hitx5=0; on the long root let it accept precisely a5-miss. There is no single5 assignment that pointwise enlarges both core types.

The actual mixed original10 mod15 has root1 and5-digit0. Its intersection with the core has mass

    (4/5)(1/5)=4/25.

Forcing the zero-hit INDICATOR to0, that is replacing its literal digit by a nonzero digit, leaves only the long-root response1/5. Applying the inheritedC5/5=4/15 would falsely bound that actual intersection by

    (4/15)(1/5)=4/75<4/25.

The common-colour maximum inK6 instead givesF_(D,1)=4/5 and the valid bound16/75. This is a direct actual-cylinder counterexample to the old forced-miss step, not a counterexample to the new maximum formula.

The common no-ternary colour maximum for these same leaf responses is4/5, whereas summing five separately optimized leaf responses gives1. Thus replacingmax_kappa sum_l bysum_l max_kappa can lose information even though it remains an upper bound. The discrepancy also occurs for an actual no-ternary label35 after adjoining a free7 coordinate: the core need not depend on that coordinate.

## 8. Finite first-digit information still cannot detect every deep nullity

The two actual pure25 originals1 mod25 and6 mod25 give normalized pure survivor laws with exactly the SAME entire first-digit distribution

    (5/24,1/6,5/24,5/24,5/24)

on digits0,...,4. With the same uniform five-leaf ternary law, the fixed mixed original1 mod75 has source mass0 in the first case and1/60 in the second. The selected label, its first digit and every first-digit colour probability agree.

Thus even the full categorical first-digit vector does not decide whether this higher-prefix cylinder is already null under a pure survivor law. K8 is a sufficient pointwise first-digit certificate; it is not a complete test of all actual deep nullities or exact selected-union leakage. A deeper prefix partition or an independently certified nullity fact is needed for those tasks. Report794 already gives an actual-prefix route when the full finite family is specified.

The complete inventory sums do handle arbitrary heights as upper bounds. That fact must not be confused with complete observation of the actual high-prefix arrangement. If a core itself depends on deeper digits, a query below the retained depth need not fix one colour; its correct menu and unnormalized cylinder intersections must be refined accordingly. The present proof deliberately concerns fixed first-digit colour partitions and the existing ternary depth2 source.

## 9. Finite does not imply inexpensive or uniformly successful

For the5 partition{0},{1},{2,3,4}, K1 has five vertices:

    (0,1/5,4/5), (0,4/15,11/15),
    (1/5,0,4/5), (4/15,0,11/15), (4/15,4/15,7/15).

This additionally retains the cap on the other-digit category. It is a subset of808's valid rectangular relaxation; it does not remove that report's all-upper corner.

With EVERY first digit kept separately atq and the universalC_q, each local simplex vertex hasq-2 coordinates atC_q/q, one at1/q and one at0. There areq(q-1) local vertices. For the seven primes5,7,11,13,17,19,23, the raw product therefore has678487883673600 vertices. This is an exact combinatorial count, not a runtime claim or a proposal to enumerate them.

Sparse core predicates, coarser valid partitions, symmetry, separation of violated constraints, or stronger source-specific restrictions would be needed for a usable broad search. The present note establishes the finite faithful sufficient interface and its limits. It has not proved that any such strategy closes the quantitative gap, that every actual phase family has a positive robust LP point, or that first-digit information is universally sufficient.

## 10. Small exact controls and reproducible scope

The [consumer](../../../frontier/cover-geometry/refined-capped-source/categorical_retained_kernel.py), [certificate](../../../frontier/cover-geometry/refined-capped-source/categorical_retained_kernel_certificate.json) and [result](../../../frontier/cover-geometry/refined-capped-source/categorical_retained_kernel.json) give a standalone exact implementation of the finite menus and a literal common-source example. Only standard-library rational arithmetic is used; no LP optimizer or large vertex product is run.

The example uses Q=(5,7), the partitions {0},{1},{2,3,4} and {0},{1,2,3,4,5,6}, and weights (1/4,1/4,1/6,1/6,1/6). The actual old originals are

    0 mod3, 1 mod9, 6 mod25,
    10 mod15, 11 mod45, 0 mod35,
    1 mod105, 4 mod27, 1 mod175.

The selected numerical labels are 15,45,35. The pure-5 law is uniform on residues modulo 25 other than 6; the 7-law is Haar. On the period 4725, the consumer constructs both the full source and the genuinely fractional retained submeasure. The exact values are

    retained initial mass       = 1693/4032,
    retained old-survivor mass  = 11/28,
    full old-survivor mass      = 521/672,
    complete inventory lower   = 19499/201600,
    minimum over 10 vertices   = 433/8400.

The inventory lower bound includes all permitted numerical labels and ternary heights, rather than merely the nine originals in this example. The literal finite calculation is a separate check of the bound, not a replacement for the general inventory argument.

There are 24,452 explicit checks: these include 9,920 arbitrary-phase cylinder inequalities on the resolved finite carrier, 1,240 exact leaf/nonternary cylinder factorizations, all ten product vertices, 25 whole-block midpoint concavity controls and all 28 full-query hinge thresholds. The consumer also checks the exact counterexamples and vertex counts in sections 7–9. The comparison with the retained result is an additional replay check. Fractional entries are checked against their shared source weights; selected-null constraints are checked on every compatible leaf and outside colour completion.

Normal, optimized and relocated optimized replays pass. Critical forged inputs are rejected for an oversized retained coefficient, selected-null violation, wrong normalization, invalid partition, invalid cap, duplicated numerical label, an unabsorbed pure original, a false counterexample mass, a forged result and a duplicated JSON key. Optimized execution preserves all checks because none uses Python assert.

The unbounded statements in sections 2–6 are supplied by the ordinary proofs above. These finite controls neither constitute a Lean proof nor assert success for an arbitrary actual covering family.
