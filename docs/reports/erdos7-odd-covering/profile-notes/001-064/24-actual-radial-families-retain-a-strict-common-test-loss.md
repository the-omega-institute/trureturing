[Index](../../marked_head_profile.md) · [Previous](23-actual-maximizing-tests-constrain-the-killed-pair-matrix.md) · [Next](25-eliminating-current-heights-with-a-common-old-test-distance-profile.md)

<a id="actual-radial-families-retain-a-strict-common-test-loss"></a>
### Actual radial families retain a strict common-test loss

For the two previously pinned actual AP13 fixtures, the complete killed-square maxima are exactly

| current prime | complete killed-square maximum |
|---|---:|
| 17 | 5109223159/246343680 |
| 19 | 127329253189/6281763840 |

These are the earlier literal spur lower bounds, now also upper bounds over every original complete test. Each zero and positive block retains all144 independently selected old labels. The intermediate ternary optimization retains two independently selected labels at each depth; it does not restrict all depths to a single nested chain.

More generally, a positive separation between independently maximizing the killed baseline and positive-current frontier holds for the explicit radial actual families at every ternary height H>=2 and every prime p>max(13,H+1), with threshold T=H. The quantitative statement below does not assert an exact general maximum or a uniform inequality for arbitrary AP13 sources.

<a id="an-actual-family-at-arbitrary-finite-height"></a>
#### An actual family at arbitrary finite height

Take Q_H=3^H*5*7*11*13, and forbid0 modulo every divisor d>1 of Q_H. The actual uniform357 source and the prescribed pure-base AP11/T4 and AP13/T6 steps, followed by one final conditioning, give exactly uniform measure mu on the units of Q_H: all mixed classes are inactive, and the pure classes remove only zero roots.

At the current prime p, forbid pure root0 and, for j=1,...,H, one class modulo3^j p whose old residue is1 and current residue is j. These are distinct original moduli; root p-1 is clean on every row. The full original current height is1. No higher original test labels exist or are discarded.

Let R be the number of nested old cylinders E_j={x=1 mod3^j} containing x. Its probabilities under the ternary unit law are

    P_0=1/2,
    P_j=3^-j for1<=j<H,
    P_H=1/(2*3^(H-1)).

Choose delta=(H-1)/(p-2), the threshold-H parameter. The physical assigned bad mass is positive only at R=H:

    beta_H=1/(p-1),  beta_j=0 for j<H,
    b=P_H/(p-1).

Here b is also the full actual charge because the other four coordinates are independent. Put q_j=1-beta_j and let t_j be the probability of the common clean current root:

    t_j=1/(p-1-j) for0<=j<H,
    t_H=(p-2)/[(p-1)(p-H-1)].

All t_j are strictly increasing when H>=2. The source's other four prime axes contribute the exact square factor

    S=product_(r=5,7,11,13)(1+3/(r-1))=273/64.

The previously established clean-root and independent-axis arguments apply unchanged: replacing current residues by the common clean root maximizes every positive-current pair, and aligning the independent other-prime roots maximizes their pair masses. Grouping by their original other-prime divisor and applying Cauchy-Schwarz then gives an exact factor S, while preserving every original label.

Thus the full killed maximum is S times

    K=sup_(A0,A1) E[q A0^2+t(2A0 A1+A1^2)],

where each A_i=1+sum_(d=1..H)1_(x=a_(i,d) mod3^d) and every a_(i,d) is independently chosen.

For any nonnegative radial weight w write Gamma_3(w)=sup_A E[w A^2], and put

    G3=E(1+R)^2,   Jt=E[t_R(1+R)^2].

Uniform ternary pair caps and the common opposite root2 give

    Gamma_3(q)=G3-b.

The constant label contributes E q=1-b; every positive-depth pair avoids E_H and attains its unweighted cylinder cap when centered at2. Monotonicity of t shows that all weighted t-pair caps are attained by centering every label at1, so Gamma_3(t)=Jt. Consequently

    Gamma_full(q)=S(G3-b),
    Xi_p^-=3S Jt.

The factor S multiplies b in the first formula. Writing Gamma_full(1)-b would be incorrect for this complete old domain.

<a id="a-general-strictly-positive-common-test-loss"></a>
#### A general strictly positive common-test loss

For depth a>=1 define

    m_a=1/(2*3^(a-1)),
    Delta_a=sum_(j=a..H)P_j(t_j-t_(a-1))>0.

The maximal q-prefix mass is m_a, the maximal t-prefix mass is m_a t_(a-1)+Delta_a. A nonspine depth-a prefix has R<=a-1 constant; among these, R=a-1 maximizes its q+t mass. The spine prefix contains the whole charged leaf. Therefore its exact maximal q+t prefix mass is

    max{m_a(1+t_(a-1)),
        m_a(1+t_(a-1))+Delta_a-b}.

The difference between the sum of the separate q and t prefix maxima and their joint prefix maximum is exactly min(b,Delta_a).

There are2a+1 ordered old-label pairs of maximum exponent a. Gamma_3(q) and Gamma_3(t) attain all their respective pair caps simultaneously. Gamma_3(q+t) is at most the sum of its pair caps; this upper bound does not assume that those caps can be simultaneously realized. Since2A0 A1<=A0^2+A1^2,

    K<=Gamma_3(q+t)+2Gamma_3(t).

It follows that

    Gamma_full(q)+Xi_p^- - sup_L integral L^2 d(mu K_p^-)
      >= S sum_(a=1..H)(2a+1)min(b,Delta_a)>0.       (RS1)

In particular the depth1 contribution alone is3S min(b,Delta_1)>0. This is a general same-family inequality for the explicit actual radial construction. It proves that independently sharp baseline and positive-frontier estimates need not be jointly sharp. It does not supply a numerical bound for all actual KC layouts.

For H=8,p=17 or19, the right side of RS1 is exactly the difference between the independently optimized baseline-plus-Xi and the previously published ZB killed upper bound. The exact optimization below improves that separation further.

<a id="first-exit-normal-form-preserves-all-independent-labels"></a>
#### First-exit normal form preserves all independent labels

A label selecting residue0 modulo3 has zero mass on the source. Moving that label to a unit cylinder cannot decrease the objective, whose expanded pair coefficients are nonnegative. Hence restrict to unit residues.

For a depth-d label, either its cylinder is the spine E_d, denoted r=0, or it first differs from the spine at a unique depth r in{1,...,d}. Its representative can be chosen as

    a(d,0)=1,
    a(d,r)=1+3^(r-1) for1<=r<=d.

For r=1 the other unit root is2. For r>=2 the two off-spine children have identical uniform measures and the same radial q and t values. All labels with the same first-exit depth r can be moved to this one representative path. Their individual weighted cylinder masses are preserved and all pair intersections within this group become maximal. Intersections with a spine label depend only on whether that spine's depth is less than r, and are therefore preserved. Labels with different nonzero first-exit depths lie in disjoint branches, and remain disjoint.

Thus this simultaneous replacement never decreases any expanded nonnegative pair contribution. Conversely every resulting collection is an actual legal complete test. This proves an exact reduction to independent choices

    r_(i,d) in{0,...,d}, i=0,1, d=1,...,H.

Different depths may choose different offshoots. No globally nested-chain claim is used; such a claim is false for general radial weights.

For a radial w, the mass of the representative cylinder is

    C_w(d,0)=sum_(j=d..H)P_j w_j,
    C_w(d,r)=w_(r-1)/(2*3^(d-1)) for r>0.

Two representative cylinders meet precisely when their explicit residues agree modulo3^min(d,e). If compatible, their intersection is the deeper representative cylinder; otherwise it is empty. These are the exact table entries used below.

<a id="exact-integer-optimization-and-exhaustive-branch-coverage"></a>
#### Exact integer optimization and exhaustive branch coverage

For H=8 there are16 independently selected positive-depth labels, with total domain

    [product_(d=1..8)(d+1)]^2=(9!)^2=131681894400.

The two depth0 labels are constant1. Expanding the ternary objective gives a constant E(q+3t), one unary term per label, and one term per unordered pair. For a zero-block label the unary weight is3q+2t; for a positive-block label it is5t. A pair of zero-block labels has weight2q; every other pair has weight2t. The representative-cylinder formulas therefore determine a finite quadratic table exactly.

The verifier multiplies all nonconstant rational coefficients by their common denominator. The integer scales are25219434240 at17 and53591297760 at19. It supplies the literal spur candidate

    r_(i,d)=0 for d<=7,  r_(i,8)=8, for both i.

The integer objective values excluding the constant term are respectively92418259287 and191714857884.

The branch-bound calculation is exact over an arbitrary finite unary/pair table. At a partially assigned node, `current` is the exact contribution already assigned; `adj_i(r)` is the original unary plus interactions with assigned labels. If U is the remaining label set, then every completion is at most

    current+sum_(i in U)max_r adj_i(r)
           +sum_(unordered i,j in U)max_(r,s)V_ij(r,s).

Conditioning on one candidate i=r gives the stronger valid bound

    current+adj_i(r)
      +sum_(j in U\{i})max_s[adj_j(s)+V_ij(r,s)]
      +sum_(unordered j,k in U\{i})max_(s,t)V_jk(s,t).

Every termwise maximum bounds the corresponding term in every completion. If all choices of any selected variable are bounded by the incumbent, the whole node closes. Otherwise every still-viable choice is recursively visited. Every excluded choice and every terminal node contributes its exact product of remaining domain sizes to a disjoint coverage count. The final count is131681894400 for each prime.

The deterministic replay visits9 nodes per prime, computes all screening bounds as integers and reaches no assignment exceeding the literal spur candidate. The [certificate](../../certificates/actual_radial_maximum_certificate.json) includes trace-event counts, a SHA-256 of the recomputed exact bound trace, and the full domain-coverage count. The trace hash identifies the replay; soundness follows from the inequalities and exhaustive branch partition, not from trusting the hash. No external optimization solver is part of this certificate.

<a id="exact-separation-and-its-two-contributions"></a>
#### Exact separation and its two contributions

At the maximizing spur test the killed baseline and Xi losses are both positive:

| p | baseline loss from its own supremum | Xi loss from its own supremum | total split-sup loss |
|---|---:|---:|---:|
| 17 | 637/165888 | 10829/35831808 | 148421/35831808 |
| 19 | 637/186624 | 10829/61585920 | 221039/61585920 |

The old unweighted square is G=S G3=795613/46656. On the charged leaf, the spur's ternary old load is8, so its deleted old square is64S b=273b. Its baseline loss is therefore(273-S)b. Switching the last test cylinder from E8 to one off-spine child of E7 changes E[t A^2] by17 P8(t8-t7); hence the Xi loss is3S*17P8(t8-t7). These exact formulas add to the displayed gaps.

The baseline alone is maximized by moving all positive-depth ternary labels to root2. Xi alone is maximized by centering both old blocks on the spine. The common killed maximizer uses the different spur arrangement. The calculation retains one actual source, one kernel and one globally legal complete test at every stage.

For the pinned explicit normalized17 history in the19 construction, the independent extra17 coordinate multiplies the complete-square maximum and split-sup loss by19/16. It has576 original test labels and zero17 mixed charge. This is a valid same-chain extension of the19 fixture, not a license to add the separate positive-charge17 fixture to it.

<a id="correlation-is-not-the-only-discarded-information"></a>
#### Correlation is not the only discarded information

The same globally maximizing spur test also has strict losses when a signed old term is replaced by its positive part. Its old source hinge at81 is64423/14580: moving the full centered test to the spur preserves its distribution under the uniform unit source. This is a value of this specific test, without asserting that it maximizes every convex cost.

Write A for this full old load and beta for the actual row charge. The two additional nonnegative terms are

    D=E_mu[beta(A^2-81)_+],
    N=E_mu[(1-beta)(81-A^2)_+].

Their exact values on the same killed-maximizing test are

| p | D | N |
|---|---:|---:|
| 17 | 4283/1492992 | 510347321/7464960 |
| 19 | 4283/1679616 | 574140853/8398080 |

To compute them, let B be the other-prime old-load factor. Then E B^2=S and Pr(B=1)=33/64. On the charged leaf A=8B, so E(64B^2-81)_+=12849/64 and E(81-64B^2)_+=561/64. Thus D=(12849/64)b and N=H81-G+81-(561/64)b. All values are exact under the same source and kernel.

These terms are distinct from the split-sup mismatch. In particular the positive-part step already loses information even if a later bound manages the baseline/Xi correlation perfectly. The general multi-prime signed telescope must also retain its killing, transport and mass terms; this finite example does not identify any one loss as the only remaining obstruction.

The [radial maximum verifier](../../verify_actual_radial_maximum.py) hash-pins the already published actual-family certificate and verifier, reconstructs the full finite table, recomputes every integer bound and domain count, checks all new maxima against the literal pinned lower witnesses, and checks the displayed separations and hinge losses. These are ordinary mathematical and exact finite computational results, not a Lean declaration or an unrestricted Erdős #7 endpoint.

<a id="positive-radial-weights-do-not-justify-a-nested-chain-restriction"></a>
### Positive radial weights do not justify a nested-chain restriction

The first-exit reduction above retains different offshoots for different original depth labels. Positivity and radiality alone cannot justify replacing these independent choices by a single nested chain.

On Z/9Z give residues0 through8 the positive weights

    (28,48,28,28,1,28,28,1,28)/218.

This probability is radial about1, with shell weights28 outside1 mod3,1 inside1 mod3 but outside1 mod9, and48 at1 mod9. Select one cylinder at each original depth0,1,2:

    A_(a,b)=1+1_(x=a mod3)+1_(x=b mod9),
    a in{0,1,2}, b in{0,...,8}.

There are27 original layouts, of which9 are nested. Write w_b for the unnormalized point weight and W_a for the mod3 cylinder weight. Then W0=W2=84, W1=50, and direct expansion gives

    218 E A_(a,b)^2
      =218+3W_a+(3+2*1_(b=a mod3))w_b.              (RC1)

For a=0 or2, the best nonnested numerator is218+3*84+3*48=614, at b=1; the best nested numerator is218+3*84+5*28=610. For a=1 the largest numerator is218+3*50+5*48=608, at b=1. Hence

    max_(a,b) E A_(a,b)^2=307/109,
    max_(b=a mod3) E A_(a,b)^2=305/109.             (RC2)

The only global maximizers are(a,b)=(0,1),(2,1), both nonnested. The [27-layout verifier](../../elementary-checks/verify_radial_chain_counterexample.py) independently compares the direct pointwise loads with RC1 and reproduces the [full table](../../certificates/radial_chain_counterexample_certificate.json).

The restriction also fails for two independently chosen blocks. For every epsilon>0, Cauchy-Schwarz and RC2 give

    max_(A0,A1) E[A0^2+epsilon*(2A0*A1+A1^2)]
      =(1+3epsilon)*307/109,                       (RC3)

attained when both blocks equal a nonnested maximizer. Restricting both blocks to chains gives exactly(1+3epsilon)*305/109 by the same argument. Thus neither independent block choices nor positive coefficients repair the restriction.

The shell sequence28,1,48 is not monotone. This does not contradict the common-center maximum for a nonnegative combination of nested spine restrictions used for Gamma_3(t). It refutes an extension to arbitrary positive radial coefficients, the situation for which the first-exit optimizer must retain independent offshoot choices. This probability is not asserted to arise from the actual AP13 construction; the result is a counterexample to a proposed optimization reduction, not a covering system or an unrestricted noncoverage theorem.

<a id="sparse-prefix-certificates-and-the-actual-weighted-objective"></a>
### Sparse prefix certificates and the actual weighted objective

[RRO Section58 at dev11036b0baf](https://github.com/the-omega-institute/trureturing/blob/11036b0baf142c8e6535e61f29d2cae83ecf7bba/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#58-二进制估值标签下的精度跳跃构造可核验证书与展开输出障碍) constructs sparse ordinary integer witnesses for a complete unit-sum valuation array. Its finite split forest has fewer than n events for n original vertices; binary-encoded jump depths replace traversal through every intermediate digit. Successful witnesses and induced obstructions remain bound to every original input label. The section's polynomial bit bound concerns constructing or checking one complete array, not optimizing over all arrays. This dev increment adds theory and digestion inputs, with no corresponding D5, Blueprint or frozen-state change.

There is an explicit bridge from odd-prime congruence centers to its input language. For each integer center a_i take the two units

    z_i^+=1+p*a_i,  z_i^-=-(1+p*a_i).

Every same-sign sum has valuation0, while

    v_p(z_i^++z_j^-)=1+v_p(a_i-a_j),               (SC1)

with infinity for equal centers. Thus the complete difference-prefix geometry can be expressed using a common unit-sum array. Reconstructing some integer tuple realizing this array does not, by itself, reconstruct the fixed original residues or the actual AP probability.

For the #7 objective, a valid compression must retain all named forbidden and test cylinders, their original depths and identities, and their shared centers across stages. Jump lengths affect mass: a unit cylinder at depth d has uniform unit mass1/[(p-1)*p^(d-1)]. The same unlabelled tree with a different jump depth can therefore have different weighted integrals. Replacing an expanded integer by a sparse digit table neither deletes that factor nor makes its fully expanded rational denominator short.

One sufficient transport contract is a product of measure-preserving prime-coordinate tree isomorphisms that maps every named cylinder to its counterpart and commutes with the stage projections. The physical AP kernels must be transported by those same maps: their row masks, row normalizations and assigned deletion weights then have identical values at corresponding rows. Induction over the stages preserves the complete actual law and the final killed integrals, including every CT loss term. A tree for the test centers alone, or independently chosen witnesses for separate subarrays, does not meet this contract. No such uniform reduction of the full KC optimization is established here.

The sign issue belongs to the objective rather than the sparse syntax. The integer branch-bound inequalities above remain valid for an exact finite unary/pair table with signed entries, because each term is bounded by its own maximum. In contrast, the first-exit consolidation argument uses nonnegative pair coefficients; an intersection-increasing replacement does not justify moving the negative CT correction in the same direction. One must either preserve the full joint integral exactly or supply a valid lower bound for the correction on every branch under consideration.

Equivalently, the direct same-law objective is

    Q_eta(L)=sum_(i,j) integral I_i*I_j d eta-484*eta(1). (SC2)

Its pair entries are nonnegative, but eta is the complete actual killed law. General eta need not have the radial symmetry used by RS1 and the finite first-exit optimization. Sparse realizability certificates do not provide that symmetry or a numerical upper bound on SC2.

Consequently the applicable search improvement is event-based checking of complete prefix candidates and rejection by obstructions whose entire induced input is fixed. Unspecified entries in a partial candidate remain unspecified; Section58 does not authorize filling them independently or applying its small complete-array obstruction claim to arbitrary partial input. The remaining numerical obligation is still the same-test weighted bound, including conditional low-load deletion in CT5 or a complete upper-bound certificate for all KC layouts. Neither the299.398 criterion nor the ASB scalar obstruction is settled by this representation change.

<a id="the-actual-positive-current-frontier-can-approach-its-weighted-cap-bound"></a>
### The actual positive-current frontier can approach its weighted cap bound

Fix p in{17,19}, delta=7/(p-2), and a finite current height H>=2. There is a genuine actual AP13 input and current forbidden family, with positive assigned charge, such that the global maximum over every original complete test satisfies

    Xi_(p,H)^-=a_(p,H) J_(g,H)/lambda_(p,H),
    Xi_(p,H)^-/(a_p J_p)
      =(a_(p,H)/a_p)(p-2)/(p-2+p^-H) -> 1.          (CSH1)

Here a_(p,H)=sum_(e=1..H)(2e+1)p^-e and a_p=(3p-1)/(p-1)^2. The argument uses one actual probability for each finite family and retains all its original labels. It concerns the positive-current objective Xi, not the full killed square or the signed KC objective.

<a id="actual-labels-and-probability"></a>
#### Actual labels and probability

Set Q=3^8. The only old forbidden class is0 modulo Q, so sigma is uniform on the6560 nonzero residues of Z/QZ. There are no5,7,11 or13 labels. The AP11 and AP13 steps are identities at their original height0, and final conditioning changes nothing. For the direct19 family, the absent17 step is likewise an identity. These are legitimate missing-class branches of the actual AP construction.

Use one actual pure forbidden class at each current exponent e=1,...,H. Its least-significant-first digits are0 at e=1 and

    (9, 1,...,1, 0)

at e>=2, with e-2 middle ones. Equivalently its residue is9+sum_(j=1..e-2)p^j. The pure cylinders are disjoint: different positive depths first differ where the shorter prefix ends in0 and the longer one has1. They avoid current roots1,...,8 and p-1. The exact pure-survivor Haar mass is

    lambda_(p,H)=1-sum_(e=1..H)p^-e
                =(p-2+p^-H)/(p-1).                (CSH2)

For each i=1,...,8 add one actual mixed class of modulus3^i p, with old residue1 and current root i. CRT gives an integer residue for each class. All H+9 actual moduli are distinct; their least common multiple is3^8 p^H. Every divisor3^j p^e, 0<=j<=8 and0<=e<=H, is an independent complete-test label, including those absent from the forbidden inventory. There are9(H+1) such labels.

Let k(x) be the largest j<=8 with x=1 modulo3^j. Its exact multiplicities on sigma are

    (n0,...,n8)=(4373,1458,486,162,54,18,6,2,1).

The actual mixed union in row k is precisely the k whole current roots1,...,k. Under the normalized pure-survivor base m_H its mass is

    alpha_H(k)=k/(p lambda_(p,H)).

This is an equality for the actual union, not a union bound. Set

    g_H(k)=1/(1-min(alpha_H(k),delta)),
    beta_H(k)=(alpha_H(k)-delta)_+/(1-delta).

For k<=7, alpha_H(k)<delta. For k=8 it exceeds delta: lambda_(p,H)<=(p-1)/p and8/(p-1)>7/(p-2) because p>9. The normalized physical row law has good density g_H relative to m_H and bad total mass beta_H. Its killed restriction keeps the good density and deletes the bad side. Thus the global assigned bad mass is

    b_H=beta_H(8)/6560>0,
    b_H -> (p-8)/[6560 p(p-9)]>0.                 (CSH3)

The limits are9/892160 at17 and11/1246400 at19.

<a id="the-old-weighted-maximum-and-the-complete-current-maximum"></a>
#### The old weighted maximum and the complete current maximum

Write A=1+sum_(j=1..8)1_(x=a_j mod3^j), with all original old residues independent. For depth m>=1, the spine cylinder D_m={x=1 mod3^m} has exactly3^(8-m) old survivors, each with k>=m. Every other depth-m cylinder has k=t<m constant and at most the same number of survivors. The cylinder containing0 has one fewer survivor. Since g_H is nondecreasing, D_m maximizes the g_H-weighted mass among all depth-m cylinders.

Any pair of old test cylinders is disjoint or intersects in one cylinder of their maximum depth. Their weighted mass is consequently bounded by the corresponding D_m mass. All these maxima are simultaneously attained by the coherent old test A_*=1+k. Therefore

    J_(g,H)=sup_A E_sigma[g_H A^2]
           =(1/6560)sum_(k=0..8)n_k g_H(k)(k+1)^2.  (CSH4)

The current KC coefficient is exactly kappa_p(alpha)=((p-1)/(p-2))g(alpha), so on this same actual family

    J_p=((p-1)/(p-2))J_(g,H).                      (CSH5)

For an arbitrary full complete test, let A_e be its independently selected old block at current exponent e. Every positive current pair at depths e,f has pure-base intersection mass at most p^-max(e,f)/lambda_(p,H). Killing can only reduce it. Summing the original old-label pairs and using weighted Cauchy-Schwarz bounds its total by

    [p^-max(e,f)/lambda_(p,H)] E_sigma[g_H A_e A_f]
      <=[p^-max(e,f)/lambda_(p,H)]J_(g,H).

There are2t+1 ordered current-exponent pairs with maximum t>0. Summing gives Xi_(p,H)^-<=a_(p,H)J_(g,H)/lambda_(p,H).

For equality, choose A_e=A_* for every current exponent, including0, and choose the literal nested current prefixes p-1 modulo p^e for all positive original labels. The entire root p-1 avoids both actual pure and mixed classes. Each relevant intersection therefore has exactly its Haar mass p^-max(e,f), divided by the same lambda_(p,H), and survives killing. The old weighted Cauchy-Schwarz inequalities are equalities as well. This is one globally legal complete test attaining every bound; no independence restriction has been imposed on the optimization domain. It proves the first equality in CSH1.

<a id="exact-limiting-boundary-and-its-scope"></a>
#### Exact limiting boundary and its scope

The complete coefficient tail is

    a_p-a_(p,H)
      =p^-H[(2H+3)p-(2H+1)]/(p-1)^2.

Combining this with CSH2 and CSH5 proves the ratio formula in CSH1. Also J_p<=81(p-1)/(p-9), uniformly in H, because A_*<=9 and g_H<=(p-2)/(p-9). Consequently

    a_p J_p-Xi_(p,H)^- ->0,
    (a_p J_p-Xi_(p,H)^-)/b_H ->0.                  (CSH6)

Thus no fixed positive epsilon, absolute rebate c, or charge coefficient c can make any of the following valid for all these actual finite families:

    Xi_p^-<=(1-epsilon)a_p J_p,
    Xi_p^-<=a_p J_p-c,
    Xi_p^-<=a_p J_p-c b_p.

The examples already satisfy common-prefix feasibility, have an actual mixed union of original labels, have strictly positive charge, and attain the global Xi maximum with every positive-current pair disjoint from the bad union. A uniformly positive saving from only these hypotheses is therefore impossible.

This uses the existing clean-prefix cap-attainment mechanism and adds the old global maximization and limiting comparison with the stated J_p bound. It differs from the earlier nonmaximizing joint-zero tests and from the height-one ZB/RS examples, whose actual pure mass stays separated from the generic all-height lower bound.

The conclusion does not rule out savings conditional on large J_p, larger charge, specific old geometry or actual joint-energy observations. It also does not remove the killed-baseline and transport terms in CT. At the maximizing test above, A_*=9 on the charged row, so its deleted old square is81 b_H and its total killed excess above the unit floor is80 b_H. Only its positive-current overlap is zero. No assertion about the299.398 joint target or an unrestricted covering-system endpoint follows.

<a id="mask-energy-localization-requires-a-valid-actual-tail-bound"></a>
### Mask-energy localization requires a valid actual tail bound

An event decomposition can retain some old-side mask-energy information. On one actual input law sigma, write

    G=sup_A E A^2, T(tau)=sup_A E(A^2-tau)_+,
    pi_p(r)=Pr_sigma(alpha_p>r),
    kappa_p(z)=((p-1)/(p-2))/(1-min(z,delta)),
    c_p=((p-1)/(p-2))/(1-delta).

For0<=r<delta and tau>=0, monotonicity of kappa and splitting at the actual event E={alpha_p>r} give

    J_p<=kappa_p(r)G
       +(c_p-kappa_p(r))*min{G,tau*pi_p(r)+T(tau)}. (MT1)

Indeed kappa_p(alpha)<=kappa_p(r)+(c_p-kappa_p(r))*1_E, and for every original A, E[A^2 1_E] is bounded both by G and by tau*pi_p(r)+T(tau). Taking the supremum proves MT1. This is a direct application of the existing event and hinge bounds, not a new Lean declaration. It only improves the estimate after its actual tail premise is supplied.

The proposed universal premise pi_p(1/4)<=1/20 is false, including on a single actual17-to19 chain. Reuse the complete315 unit family above: eleven old forbidden classes0 modulo each nonunit divisor of315 give the uniform law nu on144 units. At each of p=17,19, add pure0 modulo p and, for the increasing list d_1,...,d_11 of nonunit divisors of315, the original CRT class

    x=1 mod d_i, y_p=i mod p, at modulus d_i*p.

These35 forbidden moduli are distinct, with period315*17*19=101745. All48 divisor test labels of that period remain present; the missing17*19 mixed exclusions are not fabricated. There are no11 or13 exclusions, so nu is the actual AP13 law. Each current pure base is uniform on its nonzero roots. For the original forbidden load

    C=(1+I3+I9)(1+I5)(1+I7),
    I_d=1_(x=1 mod d),

the exact current union mass is alpha_p=(C-1)/(p-1), since its active mixed labels use different current roots.

For both primes the event alpha_p>1/4 is exactly C>=6. Among the six ternary units the factor1+I3+I9 has values1,2,3 with counts3,2,1. The factors1+I5 and1+I7 have counts(3,1) and(5,1) at values(1,2). Thus C=6,8,12 have respectively8,2,1 original unit rows, and

    nu(alpha17>1/4)=11/144>1/20.                  (MT2)

The normalized physical K17 preserves the old315 marginal row by row. The19 forbidden masks have no17 coordinate, hence their alpha19 is the same function of x after this actual17 step. Consequently

    mu17(alpha19>1/4)=11/144,
    b17=53/18432>0, b19=61/25920>0.                (MT3)

This uses one explicitly combined original family and its normalized physical17 law. It does not transfer the assertion to the differently conditioned17 law or to the final killed measure. The charge values follow from the same row1 formulas already established for the315 family; K17's preserved old marginal also preserves the19 charge integral.

For this threshold, kappa17(1/4)=64/45,c17=2 and kappa19(1/4)=24/17,c19=9/5. These constants make MT1 a valid conditional estimate, but MT2--MT3 exclude the1/20 premise on the whole allowed class. Conditional estimates restricted by additional actual geometry or energy remain possible. Existing AP3--AP4 hinge comparisons for upper tails are still valid; they do not supply new joint statistics merely by being substituted into MT1, and the fixed scalar ASB obstruction remains in force.

<a id="source-only-energy-conditions-do-not-force-a-positive-current-rebate"></a>
### Source-only energy conditions do not force a positive-current rebate

Fix p in{17,19}, threshold T=8, and one actual incoming probability mu on its full old period Q, with p not dividing Q. Assume Q has at least eight distinct divisors greater than1. This can be the prescribed supported AP13 law for p=17, or an already fixed normalized physical mu17 for p=19. All earlier actual exclusions, heights and kernels remain fixed.

For this very source there is a sequence of legitimate finite current-prime completions with positive assigned charge and complete current height H such that

    Xi_(p,H)^-/(a_p J_(p,H)) ->1,
    a_p J_(p,H)-Xi_(p,H)^- ->0,
    [a_p J_(p,H)-Xi_(p,H)^-]/b_H ->0.              (SPF1)

The source law mu, its complete original old-test domain, G_mu=sup_A E_mu A^2, and the distribution of every individually specified old test are exactly unchanged with H. Thus a positive uniform Xi rebate cannot be forced by imposing only conditions on this source or its old energy profile, whenever the proposed class contains such an actual source. This is conditional on the existence of a source satisfying the proposed restrictions; it does not assert that an arbitrary numerical high-energy class is nonempty.

<a id="an-actual-completion-preserving-the-full-old-period"></a>
#### An actual completion preserving the full old period

Choose eight distinct nonunit divisors d_1,...,d_8 of Q and a point x0 with mu(x0)>0. Include Q itself among the d_i if the earlier actual exclusions do not already have old least common multiple Q. This ensures that the new complete family's old part is exactly Q even when its original heights had been set by later-prime padding. No old label is lost through a smaller least common multiple.

Add the eight mixed classes of original moduli d_i p, with old residue x0 modulo d_i and current root i. For every H>=2 add the pure p-classes0 modulo p and, at exponent e=2,...,H, the least-significant-first prefix(9,1,...,1,0). Their residues are9+sum_(j=1..e-2)p^j. These pure cylinders are pairwise disjoint, avoid roots1,...,8, and leave the whole root p-1 clean. All original moduli are distinct and the full new period is Q p^H.

The actual pure-survivor Haar mass and old row count are

    lambda_H=(p-2+p^-H)/(p-1),
    k(x)=sum_(i=1..8)1_(x=x0 mod d_i).

The current mixed union consists of exactly k(x) distinct whole roots, so its conditional pure-base mass is alpha_H(x)=k(x)/(p lambda_H). Put

    delta=7/(p-2),
    g_H=1/(1-min(alpha_H,delta)),
    beta_H=(alpha_H-delta)_+/(1-delta),
    r_p=(p-1)/(p-2),
    J_(p,H)=sup_A E_mu[r_p g_H A^2].

These are the prescribed actual normalized physical and killed kernel quantities. For k<=7 one has alpha_H<delta, whereas k=8 implies alpha_H>delta. If

    C={x:x=x0 mod lcm(d_1,...,d_8)},

then the assigned bad mass is exactly

    b_H=mu(C)*[8/(p lambda_H)-delta]/(1-delta)
      ->mu(C)*(p-8)/[p(p-9)]>0.                   (SPF2)

The event C has positive mass since it contains x0. If Q was included among the d_i, then C is the single residue x0 modulo Q. The current step is normalized row by row; mu itself is the same incoming law for every H.

<a id="global-xi-equality-needs-no-coherent-old-maximizer"></a>
#### Global Xi equality needs no coherent old maximizer

There is one complete old block A_e for every current exponent e=0,...,H, and every divisor label of Q remains independently selected within every block. For arbitrary current residues, the killed intersection of a pair of labels of current exponents e,f has pure-base mass at most

    p^-max(e,f)/lambda_H

when max(e,f)>0. Expanding every original old-label pair and then applying weighted Cauchy-Schwarz gives

    positive pair-block(e,f)
       <=[p^-max(e,f)/lambda_H]E_mu[g_H A_e A_f]
       <=[p^-max(e,f)/lambda_H]sup_A E_mu[g_H A^2].

Set a_(p,H)=sum_(t=1..H)(2t+1)p^-t. Summing all ordered current-exponent pairs gives the corresponding upper bound a_(p,H) sup_A E_mu[g_H A^2]/lambda_H.

The old domain is finite, so let A_H be any actual complete old test attaining sup_A E_mu[g_H A^2]. It need not be nested, centered, radial, or equal to the forbidden layout. Select this very old test in every current block, and put every positive current test prefix at p-1 modulo p^e. All those prefixes are nested within the globally clean root. Each positive pair then attains its exact pure-base cap and survives killing; the weighted Cauchy-Schwarz inequalities are equalities because the old blocks coincide with A_H. Hence

    Xi_(p,H)^-=a_(p,H) sup_A E_mu[g_H A^2]/lambda_H,
    Xi_(p,H)^-/(a_p J_(p,H))
      =(a_(p,H)/a_p)*(p-2)/(p-2+p^-H),             (SPF3)

where a_p=(3p-1)/(p-1)^2. This is a global maximum over the full independent original test domain. Selecting repeated old blocks proves attainment, rather than restricting the optimization domain in advance.

<a id="exact-consequences-for-conditional-energy-strategies"></a>
#### Exact consequences for conditional energy strategies

The coefficient tail is

    a_p-a_(p,H)=p^-H[(2H+3)p-(2H+1)]/(p-1)^2.

The ratio in SPF3 therefore tends to1, independently of mu or the shape of its maximizing old tests. Moreover

    r_p G_mu<=J_(p,H)<=c_p G_mu,
    c_p=(p-1)/(p-9),

so J_(p,H) is bounded by one fixed finite constant. This proves the additive limit in SPF1. SPF2 proves its charge-normalized limit. The quantitative pure-height convergence is O(H p^-H), with a bound proportional to the fixed G_mu.

In particular, even allowing the proposed rebate constant to depend on this source, no strictly positive epsilon(mu), c(mu), or d(mu) can make respectively

    Xi_p^-<=(1-epsilon(mu))a_p J_p,
    Xi_p^-<=a_p J_p-c(mu),
    Xi_p^-<=a_p J_p-d(mu)b_p

hold for every legitimate current completion of this source. Restricting G_mu, a source-only hinge profile, or the high-load probability of an identified old test cannot change this counterexample construction: each of those observations is exactly preserved. If G_mu>64, the required eight nonunit old divisors follow automatically, since a period with at most eight divisors has A<=8 for every complete old test and hence G_mu<=64.

A condition on J_p itself is different, because the mask weights vary with H. Precisely,

    J_(p,H) -> J_infinity
      =r_p sup_A E_mu[g_infinity A^2],
    g_infinity(x)
      =1/(1-min(k(x)(p-1)/[p(p-2)],delta)),
    J_infinity>=r_p G_mu.

The convergence follows uniformly on the finite old carrier and test domain. A strict condition J_p>J0 is preserved eventually if J_infinity>J0; it is not claimed for every arbitrary high-J threshold. In particular G_mu>J0/r_p is a sufficient condition for this completion to remain above J0. Conditions involving the actual relation between a maximizing test and the weighted mask, or the joint old/new objective, contain information beyond the preserved source alone.

<a id="the19-input-and-the-remaining-common-test-loss"></a>
#### The19 input and the remaining common-test loss

For p=19, start with one already specified normalized physical mu17 from its actual AP13-to17 construction, including all original17 heights. The new d_i may contain17 factors; choosing Q among them preserves those exact heights in the full family. The19 source is then exactly that same mu17. No conditioning is inserted and no independently chosen17 family is substituted. This establishes a source-preserving19 statement without asserting that the17 and19 Xi maxima can be attained by one final common test.

Finally, the optimizing A_H can have substantial energy on the charged event C. The deleted old-square term E_mu[beta_H A_H^2] is retained in the full killed objective and need not tend to0. The CT terms, their shared-label correlations, and the gap between separately maximizing the stages are not bounded by SPF1. Thus the useful remaining conditional target is a bound on the full same-test killed or signed objective, rather than a positive standalone Xi rebate inferred only from high old-source energy. No general KC numerical bound or unrestricted Erdős #7 endpoint is claimed.

<a id="a-positive-unit-load-event-can-be-completely-deleted"></a>
### A positive unit-load event can be completely deleted

Source density and positive low-load mass do not, by themselves, give a positive conditional survival fraction in CT5. Fix H>=16 and reuse the actual ternary family from CT6: the forbidden class at3^n is3^(n-1)-1, while the inherited test at3^n is2*3^(n-1)-1, for1<=n<=H. Include the unit test. There are no5,7,11 or13 exclusions, so the actual AP13 law nu is uniform on the complete old survivor set S_H. Its Haar mass is(1+3^-H)/2 and its density is strictly below2.

On that source the complete old test A takes values1 and2. Its unit-load event is precisely E={-1 mod3^H}, with

    nu(E)=2/(3^H+1)>0.                            (CB1)

Add pure0 modulo17 and, for n=1,...,16, the original mixed class of modulus3^n*17 with CRT residues

    x=-1 mod3^n,  y=n mod17.

All H+17 actual moduli are distinct. Their period is3^H*17, and every one of its2(H+1) complete test labels remains available. At H16 every nonunit divisor has its actual forbidden class. For larger H the additional mixed exclusions are absent, but their test labels are retained. An explicit full test extends the inherited A by choosing its old residues in each positive17 label and current root16.

On every old point of E, all16 mixed masks are active. They cover all16 nonzero roots of the actual pure17 base, giving alpha17=1. The prescribed threshold delta=7/15 therefore gives

    beta17=(alpha17-delta)_+/(1-delta)=1,
    K17^-1=0 on E,
    nu(1_E beta17)=nu(E),  eta(E)=0.               (CB2)

Here the19 factor is absent, so its step is identity. In particular no universal estimate nu(1_E beta17)<=theta*nu(E) with theta<1 follows even with the source density below2 and nu(E)>0. The family does not cover all integers: on the positive source cylinder1 mod3 none of these mixed masks is active, so every nonzero17 root survives there.

The example concerns E={A=1}. The wider band A<=2 is the entire source, and CB2 does not exclude a useful conditional estimate for such broader bands or a tradeoff with the same test's positive-current energy. It specifies the extra deletion information required by CT5, without replacing that obligation by a source-density bound.

<a id="conditional-deletion-controlled-by-the-same315-head-cells"></a>
### Conditional deletion controlled by the same315 head cells

There is a positive conditional estimate when the current mixed forbidden classes use only old cofactors dividing315. At p=17 or19 assume every actual mixed forbidden modulus is d*p^e, where d>1 divides315 and e>=1. All residues, finite current heights, missing classes and pure p-power exclusions remain arbitrary. At17 this hypothesis excludes old11/13 factors; at19 it also excludes17 factors. It is a restriction on forbidden classes, not on the complete test inventory, which retains all original divisor labels and their cross factors.

Let sigma be the normalized actual incoming probability on the old coordinates, padding unused315 digits uniformly if needed. For any old event E set

    w_E(u)=sigma(E intersect {x=u mod315}).

Then the AP/T8 assigned bad mass satisfies

    integral_E beta_p d sigma <=4/(p-9)*max_u w_E(u). (HBD1)

Indeed the actual pure-survivor Haar mass lambda is at least(p-2)/(p-1). At current depth e let B_e(u) count the active original nonunit315 cofactor cylinders. There are at most11, each with its own fixed residue. With t_e=(p-1)p^-e and all absent depths assigned B_e=0, the actual mixed union obeys

    alpha_p(u)<=(1/(p-2))*sum_e t_e B_e(u),
    beta_p(u)<=(1/(p-9))*sum_e t_e(B_e(u)-7)_+.

The second inequality uses delta=7/(p-2) and convexity of the positive part; sum_e t_e=1 includes the entire current tail. Complete each 1+B_e upward to a315 comparison load C_e. The existing endpoint identity(2), extended homogeneously to every nonnegative head measure w, gives

    sum_u w(u)(C_e(u)-8)_+<=4 max_u w(u).

Applying this to the one measure w_E proves HBD1. No source probability or test residue is reselected by depth. The comparison loads C_e bound the original masks; they do not identify the masks with the inherited test defining E. If the largest current height is H, the right side can additionally be multiplied by1-p^-H.

<a id="joint-deletion-and-the-two-largest-event-cells"></a>
#### Joint deletion and the two largest event cells

Under this cofactor restriction beta17 and beta19 are functions of the same315 head alone. For the normalized physical mu17=nu13 K17, the old marginal remains nu13. Consequently the final killed measure satisfies the exact identity

    eta(E)=sum_u w_E(u)(1-beta17(u))(1-beta19(u)).

Let w1>=w2 be the two largest entries of w_E. The argument for HBD1 applied to counting measure, rather than the probability sigma, gives

    sum_u beta17(u)<=1/2,  sum_u beta19(u)<=2/5.

These bounds imply

    nu13(E)-eta(E)
      <=max{(7/10)w1,(1/2)w1+(2/5)w2}
      <=(9/10)w1.                                 (HBD2)

To check the first inequality, maximize sum_u w_E(u)(b_u+c_u-b_uc_u) on the two nonnegative simplices sum b<=1/2 and sum c<=2/5. The objective is affine in either variable with the other fixed, so a maximizing pair of simplex vertices exists. Vertices on the same cell give at most(7/10)w1; vertices on different cells give at most(1/2)w1+(2/5)w2. Zero vertices give no larger value. This upper optimization does not assert that all its vertices are actual masks. It retains the two deletion events on one actual head and accounts for their overlap.

Now assume the actual357 period divides315. Its full original survivor set S in this head has N>=74 points by the existing315 counting result. Start with the uniform law on S, apply the actual physical11/T4 and13/T6 kernels, and condition once, with retained mass rho>=r=18925009844347/38266567762500. Each physical kernel preserves the incoming head marginal; restriction and division by rho therefore give

    max_u w_E(u)<=1/(N rho)<=1/(74r).               (HBD3)

This uses the full actual source, not a replacement by the canonically pruned law or another supported probability. Source11/13 masks may have arbitrary permitted old cofactors, residues and finite heights.

For every inherited complete test A, the same-law mean bound M=2621130891614589/246025127976511 and integer A>=1 imply nu13(A<=10)>=(11-M)/10. Write m=nu13(E) and c0=1/(74r). Since w1<=c0 and w1+w2<=m, HBD2 gives

    eta(E)>=min{m-(7/10)c0,(3/5)m-(1/10)c0}.

Both expressions increase with m. At m=(11-M)/10 the first is smaller, so

    eta(A<=10)>=704627631753217/45514648675654535>0,
    Delta_121(L)>=21 eta(A<=10)
      >=14797180266817557/45514648675654535
       =0.3251080849215137... .                    (HBD4)

The bound holds for the inherited block of every complete final test in this restricted actual family, with no assumption of positive final mass. For the ASB candidate marginal with nu13(A=1)=7/100, the same conditional calculation gives Delta_121>=120*(7/100-9/(740r))>5.4489577146. If its positive terms also obey the stated ASB upper functional, this exceeds that functional's defect3.96663236768. It does not exclude the source marginal by itself or assert an unrestricted improvement of the299.398 target.

An exact actual-family check uses the existing86-survivor315 family, eleven mixed11 classes, seven mixed13 classes involving11, and three current heights at both17 and19. Its103 distinct forbidden moduli have period1517938437015 and768 complete test labels. Direct physical AP(4,6) integration gives rho=819/860. Exact prefix unions, independently counted as finite bitsets, give positive charges at both current primes; the same inherited tests satisfy HBD1--HBD4 on all checked bands. The universal statement rests on the proof above, not this single instance.

The existing DV1 construction supplies a different supported law with a stronger315-source square bound. It cannot replace the particular actual AP(4,6) probability used here. The useful addition is the event-conditioned head observation and its CT consumer, not a new noncoverage endpoint for this subfamily. Extending HBD1 to arbitrary old cofactors requires another estimate: the excluded old exponents and11/13/17 factors cannot be omitted as an unpaid tail.

<a id="highest-digit-crt-contrasts-give-signed-common-test-cuts"></a>
### Highest-digit CRT contrasts give signed common-test cuts

Fix the actual source nu on Z/QZ, Q>1, and project the complete killed17/19 output eta to this old coordinate. Define the actual deleted and surviving point masses

    u(x)=nu(x)[beta17+K17^- beta19](x),
    v(x)=eta({x}),  u(x)+v(x)=nu(x).

For a complete inherited test A and integer s>=2, the first two CT3 losses are

    D_s(A)=sum_x u(x)(A(x)^2-s^2)_+,
    N_s(A)=sum_x v(x)(s^2-A(x)^2)_+.

These retain the same original source and the same test. Original modulus uniqueness supplies an additional discrete constraint on their sum.

Write Q=product_i p_i^h_i with r>=1 distinct primes, and let a be the residue selected by the original full-modulus test label Q. In each coordinate choose one alternative to a_i that agrees modulo p_i^(h_i-1) but differs modulo p_i^h_i. The2^r CRT corners x_epsilon independently choose the original or alternative coordinate. Then

    sum_epsilon (-1)^|epsilon| A(x_epsilon)=1.      (CCD1)

Every proper-divisor indicator is constant in at least one cube direction, so cancels from the alternating sum, irrespective of its independently chosen residue. The unique Q indicator contributes1 at the all-original corner and0 elsewhere. This proves CCD1 without aligning any proper-divisor labels.

Let C+ and C- be the even and odd corners. They have equal cardinality. CCD1 forces at least one even corner with A>=s+1 or one odd corner with A<=s-1: otherwise the alternating sum is at most0. Hence

    D_s(A)+N_s(A)
      >=min({(2s+1)u(x):x in C+}
               union {(2s-1)v(x):x in C-}).         (CCD2)

Strict positivity requires deleted mass at every even corner and surviving mass at every odd corner. Positive total charge alone does not suffice. For s=9 the coefficients are19 and17.

Several cubes for the same assigned Q residue can be combined. Choose nonnegative rational lambda_C satisfying the separate point capacities

    sum_(C:x in C+)lambda_C<=(2s+1)u(x),
    sum_(C:x in C-)lambda_C<=(2s-1)v(x).

Each cube has a qualifying high or low corner. Weight these clauses and use the capacities to obtain

    sum_C lambda_C<=D_s(A)+N_s(A)<=Delta_(s^2)(L).   (CCD3)

Thus overlapping cubes have a finite fractional-packing certificate that does not charge any point beyond its own actual mass. Once the literal Q label is assigned, the certificate holds uniformly over every remaining independent original test label. A global optimization must cover every Q residue or justify its branch exclusions using the full objective; Xi-only optimality conditions do not authorize exclusions here.

For an actual nonempty branch, take Q=3^9 and forbid0 modulo3^j for1<=j<=9. The old source is uniform on its13122 units. At17 add pure0 and eight classes3^j*17 with old residue1 and current root j,1<=j<=8. Other source-prime steps and19 have height0. The full family has18 distinct forbidden moduli and20 complete test labels. On E8={x=1 mod3^8}, alpha17=1/2 and beta17=1/16; outside E8 the assigned charge vanishes.

Assign the original Q test residue a=1. Its two highest-digit corners1 and6562 lie in E8 and have

    u(1)=1/209952,  v(6562)=15/209952.

The one-cube certificate at s=9 gives Delta81(L)>=19/209952 for every complete test in this branch. Centering every old label at1 gives A(1)=10,A(6562)=9 and attains this restricted two-corner cost; it need not minimize the full CT loss. This is a usable branch constraint, not a uniform bound across all source geometries or full-modulus residues. Cube weights can vanish in other branches and become arbitrarily small with growing periods.

The endpoint identity(2), existing AP comparison, and CT decomposition are reused directly in these conditional arguments. The CRT cut follows from cancellation of the original proper-divisor indicators and finite point capacities. These are ordinary proofs with exact arithmetic checks; they add no Lean declaration, frozen status or unrestricted Erdős #7 conclusion.
