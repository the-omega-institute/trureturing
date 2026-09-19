[Index](../../marked_head_profile.md) · [Original complete scans](225-two-original-tests-share-the-complete-retained-bridge.md) · [Independent survival tests](226-the-joint135125-records-strengthen-two-complete-survival-bounds.md) · [Complete joint-row transport](230-the-complete-retained-duals-share-one-raw-source-support.md)

# Explicit pruning errors preserve all four face ceilings near the source

For every nonnegative hinge vector a=(a_1,...,a_8), the formulas below give finite, explicitly evaluable errors e_2(d,R,G), e_4(d,R,G), e_6(d,R,G). Every original head and every original retained-seven projection is included. The full-hinge deletion D_H of218, all original selected-prefix omissions, complete infinite tails, and one actual seven-coordinate defect budget remain.

This is an ordinary proof using the source and measure inequalities of125,195,208,218,227,228. It is not Lean verification and does not by itself supply the complete52-cost consumer or close the global complement. The [evaluator](../../frontier/transport/uniform_pruning_candidate_transport.py) checks the finite coefficient identities and evaluates the displayed formulas; those computations do not replace the measure arguments here.

## 1. Parameters, exact candidate meaning and the result

Use one actual source with sigma<=d, actual residual rho<=R, in either established195/208 source domain (or any smaller rectangle). G>0 is a proved common wrong-slot gap. In particular the following outer rectangles and gaps are available:

    d<=1/20, R<=1/1000, G=1/60;
    d<=1/12, R<=1/3000, G=53/2700.

Keep the canonical first-beta cell2, ROOT=(0,0,1,1,1), and slots(P,A,B,Q,H). Put

    H(v)=sum_t a_t*(v-t)_+,
    A=sum_t a_t, H6=H(6), k_t=min(t-1,4),
    M_a=sum_t a_t*(6+k_t-t)_+,
    A_i=sum_(k_t>=i) a_t, 1<=i<=4.

For j=2,4,6, V_j^face(b) denotes the actual normalized pruning expression used in225/226 for a fixed original head and j-projection tuple b. It includes218's full D_H, not only a_1 times the old mean credit. In terms of201/204 it is

    raw head LP + selected-cylinder increments - D_H + complete assigned tail.

Every actual original objective on branch b obeys

    objective_actual(b) <= V_j^face(b)+e_j(d,R,G).       (P1)

The three functions below are uniform in b. The complete bound on the three pruned classes is

    Bpruned=max(A2+e2,A4+max(e2,e4),A6+max(e2,e4,e6)).

Indeed min_l(F_l+e_l)<=min_l F_l+max_l e_l. A4 and A6 remain maxima of the accepted minima, so their transport uses the displayed maximum of errors. Each of225/226's four canonical scan certificates binds its own coefficients, maxima and exhaustive branch counts. The checker reads these directly and verifies the full62,500,000-leaf partition for each original test.

The expanded leaves additionally require their own complete bounds. Although all four scans have prefix_bounded=0, a prefix alternative can still enter an expanded leaf's accepted minimum. Absence of a prefix-pruned class alone does not show that a joint dual preserves the recorded face ceiling. This note proves only the displayed three-class bound; it does not discard an expanded prefix alternative to infer a face or neighborhood ceiling.

## 2. The finite raw and selected tables

Let g_j(t,v;m,l) be the existing exact complete unit-seven increment:

    j=2 or4:
      g=(1/[5*7^max(t-v-m,0)])+(6/35)*max(m-max(t-v,0),0),
      0<=m<=j, l=0;

    j=6: q=max(t-v,0), f=1+m, s=1+l,
      g=(6/35)*max(f-q,0)
        +(6/245)*max(s-max(q-f,0),0)
        +1/[5*7^(2+max(q-f-s,0))],
      0<=m<=4, 0<=l<=2.

These are the functions in `k_face_common_seven_hinges.seven_increment` and `second_depth_seven_comparison.seven_increment`. Their geometric term retains the entire unit-seven continuation.

Define the following finite maxima, without searching the original layouts:

    G_j=max_(v=1..6,m,l) sum_t a_t*g_j(t,v;m,l),
    D_ij=max_(v=1..6,k=0..i-1,m,l)
             sum_(k_t>=i) a_t*[g_j(t,v+k+1;m,l)-g_j(t,v+k;m,l)].

The allowed (m,l) are the ranges just displayed. All these forward increments are nonnegative. The actual seven projections need not realize the coordinatewise containing maxima.

Set

    U=d/(1-d),
    v0=min(1/20,U/4+10R),
    v1=min(1/10,U/4+5R/(1/3-d/18)),
    wbar=1+d/5+R/G.

The raw head coefficient is at most wbar*H6+G_j. The ith selected forward coefficient is at most wbar*A_i+D_ij.

The complete sum of enlarged node capacities and group-budget increments is

    DeltaC=2d/45+v0/6+v1/3,
    DeltaB=(9+d)*U/72+d/36.                           (P2)

These come directly from195/208: four nonexcluded cell0 increments d/90, Q increments v0/18,v0/9,v1/9,v1/9,v1/9, and group increments ((3+d)U/72,d/36,U/12). No group increment is omitted.

The exact face raw-cap sums are

    sum r*=97/360, sum_(c!=0)r*=41/180,
    sum_H r*=1/10, sum_(root1,H)r*=1/15.              (P3)

The four face selected-operator norms, in order25,27,75,81, and their enlargement bounds are

    p=(1/50,1/36,1/75,1/108),
    dp=(d/450,max(v0,v1)/27,d/450,max(v0,v1)/81).

The mixed-intersection correction constants may be bounded uniformly by

    z=(0,1/675,1/675,2/2025),
    Qsel=sum_i A_i*(p_i+z_i).                        (P4)

For the fourth selected step the factor2 bounds the existing maximum of 2*(mid-low) and high-low. The other fourth-step option needs only1/2025 and is also covered. All raw CRT caps themselves remain unchanged by product Haar domination.

The deterministic source prices from the finite head and selected operators are

    Chead_j=(DeltaC+DeltaB)*(wbar*H6+G_j)+41d*H6/900,
    Csel_j=sum_i dp_i*(wbar*A_i+D_ij)+(d/5)*Qsel.      (P5)

The remaining wrong-slot prices, before using defects, are

    Q5=H6/10+Qsel, Q15=H6/15+Qsel,
    Q5*q5+Q15*q15.                                  (P6)

Proof of(P5): clip an enlarged raw LP vector first to the old node caps, then within each disjoint group to its old budget. The total removed mass is at most DeltaC+DeltaB and its coefficient is bounded by wbar*H6+G_j. The remaining vector is face-feasible. Its coefficient change is Dw_i*H(B_i), where

    Dw_i=(d/5)*I_(c!=0)+q5*I_H+q15*I_(root1,H).

Apply(P3). For a selected operator, split its change as dp times the enlarged coefficient plus the old profile times the coefficient change. The latter is bounded by A_i*Dw. Apply the operator norms and(P4). A mixed correction's change is at most its stated z_i*A_i*max Dw: only the coefficient of w changes, and differences of hinge forward increments lie between0 andA_i.

For a minimum of selected alternatives, hold the face-minimizing alternative fixed, or use min(F_l+e_l)<=min F_l+max e_l. This proves the uniform difference without asserting convexity of a minimum or of an LP with moving constraints.

## 3. The whole-hinge deletion error

For each fixed head let H_cs=H(B_cs), m_s=min(H_0s,H_1s), l_s=(H_1s-H_0s)_+, and h_c=min_s H_cs. Thus m_s+l_s=H_1s<=H6. The loss of218's exact face credit is bounded by

    D_H(face)-integral H(B)d(E3+E5)
      <=sum_s m_s*(q*_s/90-e3_0s-e3_1s)
        +sum_s l_s*(q*_s/135-e3_1s)
        +sum_c h_c*(eta*_c*(1+ROOT(c))/100-sum_s e5_cs). (P7)

This is a pointwise lower-marginal inequality. It drops only nonnegative pure3 contributions outside root0; it does not assume those actual contributions vanish.

Apply228's signed E3 row estimate with alpha_s=-m_s, beta_s=l_s, gamma_cs=0; apply227's signed E5 estimate with row-total price -h_c and every other E5 price zero. Their deterministic source contribution is at most

    Cdel=H6*[d/(120*(3-2d))+19d/3600].                (P8)

Indeed k_s=alpha_s/90-beta_s/135 lies in[-H6/90,0]. The first source gain max(k_Q,0) is zero and the other source gains are at mostH6/90, so the full availability source charge is at most 3d*H6/[360*(3-2d)]. The remaining E3 source charge is at most d*H6/240. The E5 source price is at most d*H6/900. Their sum is(P8).

Write

    kappa=(6-d)/(3-2d),
    tbar=2*(1+d)/(1-4d),
    Cbar=(3/4+d/4)/(1/5-3d/8).

On d<=1/12, Cbar>=1+tbar. The corresponding seven-coordinate deletion prices are bounded by

    (H6/9, 0, H6*Cbar, H6*(1+tbar), H6, kappa*H6, 0), (P9)

in the order(E5,E15,E27,Ege4,E5d,E15d,omega). This follows from xi,chi,bad0,bad1,later<=H6 in228. The E3 H-slot price is at most10*(H6/90)=H6/9. In227 the negative E5-total prices give deep-five charges H6 and kappa*H6; no positive total price or fixed-H price is present.

The E3 inequalities explicitly retain bad-carrier and root1-spill contributions through Cbar and tbar. They are not replaced by a support-zero assumption. Passing from shifted shallow defects to full E5,E15 can only increase this nonnegative upper.

The survivor old-hinge integral additionally pays at most M_a*omega, since selected prefixes have k_t<=4. This same W appears in the full tails below. It is not charged against the raw seven increment and no second D_H is subtracted.

## 4. Complete tails with one fixed finite support

Choose an integer N>=4 before maximizing the whole source rectangle. For each threshold t, use exactly125's omissions O_l(t):

| Family l | prime p_l | first depth s_l | O_l(t) |
| --- | ---: | ---: | --- |
| pure3 |3|3|3 if k_t>=2;4 if k_t>=4|
| pure5 |5|2|2 if k_t>=1|
| root-five |5|2|2 if k_t>=3|
| cell-five |5|2|empty|

Define finite numbers

    n_l(t)=N-s_l+1-|O_l(t)|,
    r_l(t)=p_l^(1-s_l)/(p_l-1)-sum_(n in O_l(t))p_l^-n,
    P_l=sum_t a_t*n_l(t), R_l=sum_t a_t*r_l(t).

All omitted depths are<=N. The complete geometric tail beyond N is exactly p_l^-N/(p_l-1). For each family excess epsilon_l,

    sum_(n>=s_l,n notin O_l(t)) min(epsilon_l,H_l*p_l^-n)
      <=n_l(t)*epsilon_l+H_l*p_l^-N/(p_l-1).         (P10)

Thus(P10) retains, rather than truncates, every exponent. Here195 extends the125 reference envelopes through d<=1/12:

    delta c=(d/4,13d/90,d/15,d/45),
    Hbar=(1/20+21d/20-d^2/5,
          1/10+(19d+2d^2)/90,
          1/15+d/9,
          1/45+d/30-d^2/360).

The family excesses can be bounded on the same actual source by

    epsilon3=E5+E5d+kappa*(E15+E15d)+omega,
    epsilon5=E27+Ege4+d/240+omega,
    epsilon15=omega, epsilon45=omega.

The root0 branch in125(OT6) is dominated by the source reference on these domains: the general source inequalities give c1-h0>=(3/5)*(1/3-d/18)-(1/6+d/18)=1/30-4d/45>=7/270>0 for d<=1/12. Thus the branch is not silently omitted beyond an old radius restriction.

The assigned positive-seven tails retain all unselected labels. Their source increments are zeta_j*d, with

    zeta2=3/280, zeta4=1/168, zeta6=23/5880.

Their face constants are779/12600,13/360,2669/88200. For six projections, remove exactly the original147 and245 assigned terms (6/245)*N3 and (6/245)*(h/5) from208's complete four-projection series. The remaining series is

    Z6=N3/245+N9/35+Dsrc/90+53h/4900
                              +11h1/700+em/20+1/360.

Here N3 is the largest source root mass, N9 the largest cell mass, Dsrc=max_l d_l, h is pure3 source mass, h1 its root1 mass, and em=max_l eta_l, as in158/208. Every displayed coefficient is positive. Substitution of195's six-loss source envelopes gives face2669/88200 and the exact loss-price vector

    (1/2940,23/5880,1/8820,29/44100,0,0).

Its largest price is23/5880; the second-largest is at most(1-d)*23/5880 for d<=1/12. The exposed-price inequality156 therefore gives Z6<=2669/88200+23d/5880. The checker separately reconstructs the assigned removals, face constants and six-loss prices for all three projection counts. No face cap is subtracted from an unrelated off-face upper.

The resulting deterministic complete-tail price is

    Ctail_j=sum_l delta_c_l*R_l
          +A*sum_l Hbar_l*p_l^-N/(p_l-1)
          +(d/240)*P5+A*zeta_j*d.                  (P11)

The1/72 deep-mixed zero-seven series is unchanged and cancels in the face difference. The remaining primitive prices are

    (P3,kappa*P3,P5,P5,P3,kappa*P3,P3+P5+P15+P45).

In particular, no constant finite slope in R is asserted for the whole infinite series at zero.

## 5. One actual residual maximum

Use the unshifted actual defect vector

    E=(E5,E15,E27,Ege4,E5d,E15d,omega)>=0, sum E<=rho<=R.

The proved wrong-slot gaps give G*q5<=E5 and G*q15<=E15. Add(P6), (P9), the old-hinge W price and all tail prices before optimizing this one vector. The seven final prices are

    L=(P3+H6/9+Q5/G,
       kappa*P3+Q15/G,
       P5+H6*Cbar,
       P5+H6*(1+tbar),
       P3+H6,
       kappa*(P3+H6),
       P3+P5+P15+P45+M_a).

An explicit answer to(P1) is

    e_j=Chead_j+Csel_j+Cdel+Ctail_j+R*max L.         (P12)

Every original row/family contribution has been assigned before the maximum. The endpoint cap envelopes v0,v1 are containing geometric bounds on the actual source; their use does not claim independent realizability of separate maximizing allocations. No additional copy of the residual is introduced.

For consumers that transport the raw head and selected profiles jointly, `deletion_tail_data(a,j,d,R,N)` exposes the same full deletion and complete-tail terms before the coarse residual maximum. In its `shifted_primitive_prices`, E5 and E15 denote E5-G*q5 and E15-G*q15. The consumer adds G*P3*q5+G*kappa*P3*q15 to restore the tail's unshifted shallow defects. The deletion H6/9 coefficient already multiplies the shifted E5 defect, so it incurs no additional G*H6*q5/9 term. The omega price already contains M_a once. This API excludes Chead, Csel and the selected q prices of(P6); those belong to the consumer's joint raw/profile support. At the exact face its deterministic source contribution is zero. `evaluate(a,j,d,R,G,N)` gives the full coarse candidate error(P12).

For an explicitly vanishing modulus choose, for d+R>0,

    N=min{n>=4:3^-n<=d+R},

and define e_j(0,0,G)=0. For G bounded below by a positive fixed gap, N=O(log(1/(d+R))), P_l=O(N), the complete geometric remainder isO(d+R), and all other source increments areO(d+R). Therefore(P12) tends to zero and isO((d+R)*log(1/(d+R))). The cut is selected once from the rectangle endpoints and then held fixed for every actual source in that rectangle.

## 6. Exact evaluations and scope

The evaluator reads the four original hinge vectors, complete pruning maxima, branch counts and decision digests directly from the canonical225/226 certificates through the logical certificate reader. It pins these inputs and their complete inherited source bindings; it has no temporary snapshot dependency. It checks(P3), all four exact selected norms, both endpoint face remainders163/1800 and19/648, nonnegative finite raw increments, and the exact zero-radius specialization. All arithmetic is Fraction arithmetic and every check survives `python3 -I -O`.

At(d,R,G)=(10^-8,10^-11,1/60), N=17. The complete all-layout errors are:

| Objective | e2 | e4 | e6 |
| --- | ---: | ---: | ---: |
|heavy0|2.63193768536e-7|3.17879852184e-7|3.24966620957e-7|
|heavy16|2.10257838634e-7|2.54006183458e-7|2.59675598476e-7|
|AP13|1.13848935176e-8|1.24648935267e-8|1.26055738001e-8|
|AP11-B0|9.06119095962e-9|1.01414862184e-8|1.02821664918e-8|

These displayed decimals are rounded presentations of exact rational output. All three pruning classes of all four tests remain below their existing face ceilings on this small rectangle; the evaluator compares A2+e2,A4+max(e2,e4),A6+max(e2,e4,e6) with the recorded faceM.

The same formulas give valid but coarse wide-domain errors; for heavy0 they are(1.93745...,2.33409...,2.38697...) on(1/20,1/1000). They are not a claim of a useful whole-domain403 comparison. A complete neighborhood result still requires the joint-dual plus tail values and all52 original consumer costs, actual signed mass, independent survival blocks and count tails. The global complementary branch remains a separate obligation.


```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/uniform_pruning_candidate_transport.py --check
```

The [certificate](../../certificates/source_norms/retained-transport/uniform_pruning_candidate_transport.json) retains the exact source prices, finite table maxima, all four original scan partitions, six evaluated domains, complete geometric coefficients, seven combined prices and all twelve small-rectangle inequalities. It does not rerun the original branch scans.
