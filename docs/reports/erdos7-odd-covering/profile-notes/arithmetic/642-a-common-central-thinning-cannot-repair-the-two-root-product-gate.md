# A common central thinning cannot repair the two-root product gate

For the product-source interface of [Report640](640-global-root-exclusions-close-the-complete-core-inventory.md), root budget

    d=(2,1,1,1,1), Q=(7,11,13,17,19)

does not admit a positive certificate through ANY ONE common central thinning theta. This statement covers all120 central cell weights0<=theta(l,m)<=1, jointly tested against every11400 pure-source comparison corner. It is stronger than a failure at theta=1 or a negative numerical optimization result.

The exact robust optimum is ZERO. The proof uses a symmetry reduction that preserves the entire query interface, followed by an exact two-corner dual certificate. It retains640's complete512 coefficients, c, W, full inventory and arbitrary-height prefix caps. This is a boundary of the declared product source and query envelope; it does not assert that the actual survivor is empty, that no different common source works, or that the comparison corners are all physically attained by pure inventories. These are ordinary mathematics and exact arithmetic, not new Lean verification.

## 1. The fixed source and the optimization question

At each q let d_q actual live roots be excluded from the same root-balanced pure source. Define

    A_q=1−d_q/(q−1),
    h_T=product_(q notinT) A_q, T subset Q.

For d=(2,1,1,1,1), all A_q are positive and h_empty=187/384. Keep the central15 mask

    M(l,m)=0 if l<3 and m<5, and1 otherwise.

An allowed common thinning is any fixed array theta in[0,1]^(6*20), used for every source comparison and every query. Its response is

    H_T(l,m)=h_T M(l,m)theta(l,m).                         (T1)

Let C_j be exactly640's full512 coefficients, INCLUDING its arbitrary central45/75/225 charges, and let g=200163067/201247200. No anchor-release fees are added here. For a source corner v=(z,w,z',w'), use the same central selector menus as640 and put

    G_v(theta)=g sum_(l,m)w_l v_m H_empty(l,m)
                    −sum_(j=0)^511 C_j S_(j,v)(H).         (T2)

The question is the precisely bounded optimization

    max_(theta in[0,1]^120) min_(v in all11400 corners) G_v(theta). (T3)

Zero theta is admissible and has value0. The result below proves the matching upper bound0. It does not prove that a nonzero useful source can attain a positive margin, nor that the physical family has a zero survivor.

## 2. A lawful symmetry reduces120 values to three

Use these finite permutations of central reference leaves:

- arbitrary permutations of the three ternary children inside EACH of its two first roots;
- arbitrary permutations of the five quinary children inside EACH of its four first roots;
- arbitrary permutations of the three nonmasked quinary first roots, transporting their entire child blocks.

The distinguished ternary first root and the distinguished quinary first root defining M remain fixed. This group preserves M and the first-root partitions used by the selector menus. It also preserves the complete domain of source corners: null and weak leaf identities are permuted, their weights remain respectively0/1/2 in ternary units1/9 and0/3/4 in quinary units1/75.

The depth-two leaf selectors and arbitrary-deeper selectors are transported with their leaves. In particular delta_l and(4/5)delta_m keep their coefficients; the condition that a selected leaf has positive source weight is transported as well. No extra leaf probability is inserted into a deep selector. Total and first-root menus are respectively unchanged or permuted. The512 coefficients depend on exponent modes and outside supports, not leaf identities, so all costs remain unchanged.

For such a permutation gamma, acting on theta and source corners, therefore

    G_(gamma v)(gamma theta)=G_v(theta).                    (T4)

This is an identity of the complete comparison problem. It is not permission to change an actual original's phase separately in different cells or queries. The outside source factors h_T are constant across central cells; a fixed phase-activation field from another star construction would need its own invariance proof.

Each G_v is concave in theta: mass is linear, each screen is a maximum of linear forms, and all C_j are nonnegative. Thus J(theta)=min_v G_v(theta) is concave. If theta_bar is the finite group average, then

    G_v(theta_bar)>=average_gamma G_v(gamma theta)
                  =average_gamma G_(gamma^(-1)v)(theta)
                  >=J(theta).

Taking the minimum over v proves J(theta_bar)>=J(theta). Hence group averaging cannot lower the robust gate.

The nonmasked cell orbits are exactly

    A: l<3, m>=5                 (45 cells),
    B: l>=3, m<5                 (15 cells),
    C: l>=3, m>=5                (45 cells).

Masked cells never contribute and may be set to zero. Consequently the robust optimum over ALL120 theta values equals the optimum over just three common numbers(t_A,t_B,t_C) in[0,1]^3. This is a proved reduction, not a search over an assumed convenient shape.

## 3. Exact source menus and complete fee folding

Because h_T is constant in central cells, define16 complete coefficients

    f_mode=sum_(T subset Q) C_(32*mode+T) h_T.               (T5)

No coefficient or query is omitted. For a block-constant theta, a central selector has an integer coefficient triple k, and its value is(k_A t_A+k_B t_B+k_C t_C)/675.

Every source corner has

    u=9 times mass of ternary root0 in{3,4,5,6},
    v=75 times mass of quinary root0 in{15,16,19,20}.

The ternary selector pairs (contributions from root0,root1) are

| Mode | Pairs |
|---|---|
|0|(u,9−u)|
|1|(u,0),(0,9−u)|
|2|(2,0),(0,2)|
|3|(9,0),(0,9)|

The quinary selector pairs (contributions from root0,all other roots) are

| Mode | Pairs |
|---|---|
|0|(v,75−v)|
|1|(v,0),(0,20)|
|2|(4,0),(0,4)|
|3|(60,0),(0,60)|

Within each ternary first root, at least one leaf retains the top numerator2. Within each quinary first root, at least one leaf retains4. Of the three nonmasked quinary first roots, at least one is untouched by the single null and single weak leaf, and its total numerator is20. These facts justify the maxima in the tables; smaller dominated options can be removed for nonnegative t.

For any chosen pair(x0,x1) and(y0,y1), the three block coefficients are

    k=(x0*y1, x1*y0, x1*y1).                              (T6)

Thus all11400 corners give exactly16 menu shapes(u,v). The exact checker enumerates all literal corners, checks the required axis maxima, and compares each of the16 shapes against directly constructed literal selectors. Arbitrary deeper query heights are already represented by the unchanged deep modes and the full coefficients in T5.

## 4. Two corners and an exact dual upper bound

Only these two corners are needed for an upper bound:

    v0=(3,4,0,1), giving(u,v)=(6,15),
    v1=(3,4,5,6), giving(u,v)=(6,20).

They are members of the complete comparison domain. Select the following legal integer triples from their mode menus:

| Mode | At v0 | At v1 |
|---:|---|---|
|0|(360,45,180)|(330,60,165)|
|1|(120,0,60)|(120,0,60)|
|2|(24,0,12)|(24,0,12)|
|3|(360,0,180)|(360,0,180)|
|4|(360,0,0)|(330,0,0)|
|5|(120,0,0)|(120,0,0)|
|6|(24,0,0)|(24,0,0)|
|7|(360,0,0)|(360,0,0)|
|8|(0,30,120)|(0,40,110)|
|9|(40,0,0)|convex combination of(40,0,0),(0,40,0),(0,0,40)|
|10|(0,8,0)|(0,8,0)|
|11|(120,0,0)|(120,0,0)|
|12|(0,135,540)|(0,180,495)|
|13|(0,0,180)|(0,0,180)|
|14|(36,0,0)|(36,0,0)|
|15|(0,540,0)|(540,0,0)|

Call these triples k0_m and k1_m, with the one mode9 mixture omitted temporarily. Define vectors

    U=g h_empty k0_0/675 −sum_m f_m k0_m/675,
    V=g h_empty k1_0/675 −sum_(m!=9) f_m k1_m/675,
    K=40 f_9/675.

Let s(U),s(V) be their sums of three coordinates and set

    lambda=(K−s(V))/(s(U)−s(V)+K),
    pi_j=[lambda U_j+(1−lambda)V_j]/[(1−lambda)K].          (T7)

The actual exact coefficient evaluation gives

    lambda=203208177531255678309923/
               301561670020142150028512,

strictly between0 and1. Every pi_j is strictly positive and their sum is exactly1. Their approximate values, for readability only, are

    (0.48500822362537344,
     0.21918720615734155,
     0.295804570217285).

The certificate data retains the exact three rational values. Use them as the weights of the three legal mode9 selectors at v1.

Every screen maximum is at least a selected legal form and at least any convex combination of legal forms. Since fees f_m are nonnegative, these replacements give AFFINE UPPER bounds on the gates:

    G_v0(t)<=U dot t,
    G_v1(t)<=(V−K pi) dot t.

By T7, each coordinate of

    lambda U+(1−lambda)(V−K pi)

is EXACTLY zero. Therefore, for every nonnegative three-block t,

    min_v G_v(t)
       <=lambda G_v0(t)+(1−lambda)G_v1(t)
       <=0.                                                (T8)

Together with the group-average reduction and theta=0, this proves that T3 equals exactly0. The argument does not rely on a floating optimizer's stopping criterion, small numerical residual or rounded sign.

For comparison, theta=1 has minimum

    −203208177531255678309923/
          20428636029505837056000000,

at shape(6,20). T8 proves that a different ONE common theta cannot restore a positive gate in this interface; it does not merely repeat the theta=1 diagnostic.

## 5. Verification and remaining alternatives

The [standard-library program](../../frontier/cover-geometry/two_root_common_theta_exact_dual.py) reads the unchanged640 certificate and produces the [exact dual data](../../frontier/cover-geometry/two_root_common_theta_exact_dual.json). It reconstructs every32 outside factor and folds all512 costs, verifies all11400 source-corner axis conditions and16 literal menu shapes, checks every selected form, both convex weight conditions, and all three exact zero residuals. The program records11,724 exact checks. No numerical optimizer is needed to replay the certificate. The ordinary group-action argument in section2 supplies the reduction from arbitrary120cell theta.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_root_common_theta_exact_dual.py

An independent reconstruction, without importing the candidate producer, passes460 checks. It builds the two literal selector menus from the prior independently reconstructed640 costs, verifies all convex weights and three exact zero coefficients, and checks the axis maxima over all30 ternary and380 quinary null/weak pairs. The independent ordinary review also verifies the full mask-stabilizer averaging argument.

The same obstruction is upward closed in root budgets, with the fee envelope held fixed. For positive A_q, division by h_empty gives

    G_v(theta)/h_empty
      =g times central_mass_v(theta)
       −sum_j C_j s_(j,v)(theta)/product_(q in T_j)A_q.

All s and C are nonnegative. Decreasing any A_q cannot increase this normalized gate. Thus every componentwise larger budget d'>=(2,1,1,1,1), with positive residual factors, also fails the same common-theta robust certificate. A zero residual factor makes source mass zero and leaves nonnegative query fees, so it cannot give a positive gate either. This is a direct comparison of the same complete envelope, not a new optimization or a claim about actual survivor mass.

The excluded route is precisely a common central thinning of the fixed two-root product source, certified by the stated complete512 envelope at all comparison corners. It does not exclude:

- a different actual common source retaining useful correlations;
- improved SAME-source query or original-loss bounds;
- a valid source-dependent construction with its own comparison proof;
- direct control of actual pure-source weights when the comparison envelope is too large.

In particular the exact dual is a reason to change one of those relations, rather than continue optimizing theta inside T1–T3. A genuine empty fibre and a nonpositive sufficient gate remain different conclusions.
