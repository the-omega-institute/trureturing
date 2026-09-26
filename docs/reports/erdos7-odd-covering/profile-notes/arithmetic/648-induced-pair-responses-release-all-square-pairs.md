# Induced pair responses release all square pairs on one actual source

All twenty originals q²s and qs², q<s in Q={7,11,13,17,19}, may have arbitrary globally fixed full residues, together with all fifteen arbitrary square-star phases admitted by [Report646](646-all-square-star-phases-admit-the-complete-network.md). The complete declared Report625 network remains supported by the stronger owner rows of [Report647](647-order-matched-moments-strengthen-complete-networks.md).

This jointly releases35 root-incidence conditions. Forty linear-star and twenty pair conditions remain. The complete head gate is at least

    gamma20=203129722400814193208791597
                 /20692505911553620784640000000.

Using Report647's order-four network gives full survivor density strictly greater than

    1/(23600 Q_off).

Its order-three network gives the alternative bound1/(36700 Q_off). Both use the same literal head, central conventions, finite original inventory rules and declared network interfaces below. These are ordinary mathematical results and exact rational certificates, not new Lean verification or unrestricted Erdős #7.

The head construction performs one actual joint pair deletion and one scalar thinning at each central cell. Every query retains the deletion budget of its unqueried induced subgraph. The complete thirty-two responses are then used for all512 original and query charges.

## 1. One joint thinning supports every induced query response

Let V be a finite coordinate set and P=product_(i in V)P_i one product probability law. Let E_e be finitely many actual events, each depending only on its declared nonempty scope e⊆V. Give simultaneous bounds

    P(E_e)<=p_e, p_e>=0, sum_e p_e<1.

For U⊆V define

    d_U=sum_(e⊆U)p_e, lambda_U=1-d_U,
    s_U=P(avoid every E_e with e⊆U).

The union bound gives s_U>=lambda_U>0. Define ONE submeasure

    nu=(lambda_V/s_V) P restricted outside union_e E_e.     (I1)

It has mass exactly lambda_V, is dominated by P, and avoids all actual events. For every query A_T depending only on coordinates T⊆V,

    nu(A_T)<=lambda_(V\T) P(A_T).                          (I2)

To prove this, put U=V\T and d_inc=d_V-d_U. Excluding the additional events whose scopes meet T loses at most d_inc, so

    s_V>=s_U-d_inc.

Using s_U>=lambda_U gives

    s_V/s_U>=1-d_inc/s_U
              >=1-d_inc/lambda_U=lambda_V/lambda_U.

Hence(lambda_V/s_V)s_U<=lambda_U. Dropping exclusion factors whose scopes meet T leaves an avoidance event depending only on U. Product factorization across T and U now yields

    nu(A_T)<=(lambda_V/s_V)P(A_T)s_U
             <=lambda_U P(A_T).

For T empty, I1 gives exact mass. No independence between the E_e is assumed. Every event, overlap and phase belongs to the same actual product source. The hypothesis sum p_e<1 is a sufficient construction condition; its failure would not prove that the actual survivor is empty.

For coordinate submeasures xi_i of positive masses Z_i, apply I1 to P_i=xi_i/Z_i. If an actual event union on an edge{q,s} has unnormalized product-mass bound beta_qs, use

    p_qs=beta_qs/(Z_q Z_s).

After restoring the coordinate masses and applying the original cylinder caps at queried coordinates, the simultaneous response is

    H_T=product_(q notin T)Z_q
        -sum_({q,s}⊆V\T)beta_qs
             product_(u notin T and u!=q,s)Z_u.             (I3)

An edge union may contain several distinct original labels. Its bound is a union estimate; it neither identifies their phases nor counts them as a new numerical modulus.

## 2. Exact phase scope and the remaining sixty incidences

Retain646's literal head

    P={3,5,7,11,13,17,19,23,29,31},
    Q={7,11,13,17,19}.

Each numerical modulus is greater than one and odd, occurs at most once, and has one full residue fixed globally. Keep the first pure3 phase2mod3, first pure5 phase4mod5 and central15 phase0mod15, with the same auxiliary-deletion convention for missing labels. Higher pure phases and finite heights are arbitrary. All previously admitted head numerical labels and their complete remaining-original budgets remain present.

Use one cell-dependent live-root table t_q(c), fixed for the actual family before all numerical corner comparisons and queries. It must satisfy:

- Each active linear star3q,5q,15q,9q,25q,45q,75q,225q has outside first root t_q(c). These are forty original conditions.
- Each active original qs or9qs has at least one endpoint equal to its corresponding t-root. These are twenty original conditions over the ten unordered pairs in Q.

The endpoint used to certify a retained pair may depend on the original and cell. The original endpoint values themselves never change. Missing originals impose no incidence condition.

There is no root-incidence condition on any of the following thirty-five originals:

    3q²,5q²,9q², q in Q;                         fifteen stars;
    q²s,qs², q<s in Q.                           twenty pairs.

Their central parts, when present, and all outside components have arbitrary globally fixed phases. These freedoms hold simultaneously in one actual family. The remaining sixty incidences, central conventions and outside-network restrictions are substantive hypotheses.

## 3. The actual five-coordinate pair block

At each central reference cell c=(l,m), start with646's actual outside submeasures xi_(q,c). They are dominated by the actual normalized pure-q survivor laws, with first- and second-prefix caps

    r_q=1/(q-1), a_q=1/[q(q-2)].

For q>7 their exact mass is

    Z_q=D_q=(q-2)/(q-1)-2/[q(q-2)].

If at most two square stars are active, their actual cylinders are deleted. If all three are active, the construction deletes3q² and5q² and leaves the guarded portion of9q² for its existing later payment. In either case it thins the actual remainder to D_q.

At7 all three active square-star cylinders are deleted. Its exact mass is

    Z_7(c)=5/6-n(c)/35,
    n(c)=1_(floor(l/3)=R)+1_(floor(m/5)=C)+1_(l=ell),

where(R,C,ell) ranges over the same2*4*6=48 globally padded layouts. Padding is fixed once and does not change any actual original phase. In particular

    Z_7(c)>=157/210>0.

For every edge{q,s} in Q, let E_qs be the union of the TWO actual original events q²s and qs². Its unnormalized product-source cap is

    beta_qs=a_q r_s+r_q a_s.                              (I4)

This estimate permits arbitrary endpoint roots, arbitrary square lifts, absent labels and any overlap. Normalize all five xi_(q,c), and put

    lambda_Q(c)=1-sum_(q<s in Q) beta_qs/[Z_q(c)Z_s(c)].

The bound is positive uniformly. Substituting Z_7>=157/210 and the exact D_q at all other coordinates gives

    lambda_Q(c)>=328686693796069/337134711943765>0.        (I5)

Let s_Q(c) be the actual surviving fraction after deleting all ten edge unions. It can depend on the original phases and the cell. Apply I1 with the single thinning lambda_Q(c)/s_Q(c), then restore the coordinate masses and central15 mask M(c). This defines one actual submeasure eta, dominated by646's source and therefore by the same normalized pure product.

All twenty released pair originals are now null. The forty linear stars and twenty retained pairs were already null under the shared root table. The exact empty response and all thirty-one nonempty upper responses are

    H'_T(c)=M(c)[ product_(q notin T)Z_q(c)
          -sum_({q,s}⊆Q\T)beta_qs
              product_(u notin T and u!=q,s)Z_u(c) ].     (I6)

They belong to the same eta for all T⊆Q. A query touching one coordinate does not discard the valid avoidance budget on the remaining induced graph. Conversely, every edge meeting the query support is removed from that particular upper response, exactly as I2 requires. All queried full-height cylinder caps remain unchanged.

The construction depends on the central cell, not on deeper central digits. It therefore preserves the existing central deep-selector estimates. No numerical comparison corner is substituted for the already constructed actual source.

## 4. The complete512 gate and the four guarded residuals

The four possible guarded9q² residuals, q=11,13,17,19, are treated exactly as in646. Restrict eta outside their actual union. All queries decrease, and the same four coefficients g a_q at central mode(2,1), support{q}, pay their one-time loss. These are restricted portions of the original9q² events. They are not new45q² labels; each independently existing45q² retains its own phase and already-paid coefficient.

Consequently the complete512 coefficient array C is exactly646's array. It retains every previous original, the complete higher-height tails, all nonunit query fees and the actual retained unit contribution. The twenty newly avoided pairs receive no additional deletion charge: their cost and induced query improvement have both been included in I6.

Set

    g=200163067/201247200, alpha=2673/110656.

For the actual central probabilities w_l,v_m, the sufficient gate is

    G=g sum_(l,m)w_l v_m H'_empty(l,m)
       -sum_(j=0)^511 C_j S_j(H').                       (I7)

There are16 central modes and32 outside supports, with j=32*mode+support. Every S_j maximizes its complete declared central selector menu applied to the same H'_T. The ternary menu levels are the whole w, a root restriction, a leaf mass w_l delta_l, and the deep selector delta_l. The corresponding quinary deep selector is(4/5)delta_m. Deep selectors are not multiplied by the current leaf probabilities. Deep selectors range only over live leaves. The existing zero selectors and all height coefficients are retained.

Fix each actual null leaf throughout its convex decomposition; on that face every other leaf has positive mass by the stated caps and total mass one, so the live deep-selector menu is fixed. For fixed H', the gate is concave separately in w and v on those faces: its mass is bilinear, and each nonnegative debit coefficient multiplies a maximum of forms affine in either weight vector when the other is fixed. The actual central pure laws satisfy the same one-null-leaf capacity conditions as624/646. At3 each comparison corner has one zero, one weak1/9 and four strong2/9 entries. At5 it has one zero, one weak3/75 and eighteen strong4/75 entries. There are

    (6*5)*(20*19)=11400

literal corner pairs. Successive convex decomposition of the actual weights transfers a lower bound on all those corners to every actual admitted central source. This argument compares weights algebraically; it does not assume that each numerical corner can be realized by the actual higher-digit source.

## 5. Exact affine responses and complete corner coverage

The twenty-pair response remains affine in n(c), but it does not share the simple multiplicative7-factor of the twelve-pair special case. Let B=Q\{7}, and for U⊆B define

    Phi(U)=product_(q in U)D_q
       -sum_({q,s}⊆U)beta_qs product_(u in U\{q,s})D_u,
    Psi(U)=sum_(s in U)beta_7s product_(u in U\{s})D_u.

If7 is queried, I6 is simply M(c)Phi(Q\T). If7 is unqueried and U=B\T, it is

    H'_T(c)=M(c)[Z_7(c)Phi(U)-Psi(U)]
            =M(c)[(5/6)Phi(U)-Psi(U)-n(c)Phi(U)/35].     (I8)

In particular the Psi term must not be multiplied by1-6n/175. Every selector maximum is evaluated on the complete affine response, retaining the relationship between its constant and n terms.

The [portable producer](../../frontier/cover-geometry/induced_square_pair_boundary_certificate.py) and [exact data](../../frontier/cover-geometry/induced_square_pair_boundary_certificate.json) retain the complete coefficient array and both pair scopes. The independent [full twenty-pair orbit certificate](../../frontier/cover-geometry/induced_pair_full20_orbit_certificate.py) and [its data](../../frontier/cover-geometry/induced_pair_full20_orbit_certificate.json) reconstruct the twenty-pair responses and every512 reading without importing the producer or its data.

The corner comparison has20 orbits under simultaneous central-leaf permutations preserving the masked first-root rectangle. Representatives for(null,weak) are

    THREE=((0,1),(0,3),(3,4),(3,0)),
    FIVE=((0,1),(0,5),(5,6),(5,0),(5,10)).

Their twenty multiplicities sum to11400. Transporting the corner also transports the whole(R,C,ell) layout and every selector; the forty-eight layouts are retained in every case. The independent computation therefore evaluates

    20*48*512=491520 complete selector readings,

covering all48*11400=547200 literal layout/corner addresses. Literal address coverage is not a claim of547200 separate arithmetic gate evaluations.

The exact minimum is

    gamma20=203129722400814193208791597
                 /20692505911553620784640000000.         (I9)

One minimizing comparison corner is(z3,w3,z5,w5)=(3,4,5,6), with layout(R,C,ell)=(1,2,5). It is a numerical comparison witness, not an assertion that this corner law is an actual source realization. The exact conditional source construction and the separate-concavity argument give the arbitrary-phase and arbitrary-height theorem; finite address coverage certifies the coefficient gate.

## 6. Stronger complete networks make the twenty-pair gate sufficient

Rebuild the normalized23/29/31 continuation from this actual restricted source. Domination by the normalized pure product and reverse integration give exactly the simultaneous625 head joint caps. These are joint bounds on one law, not products of separately bounded singleton marginals.

Report647 then supplies either of two actual network constructions. Below971 it uses an order-matched row threshold1-1/r and D>=5r, so the conditional cap remains below v/5. From971 to2^115 it keeps the complete cubical rows. At and above2^115 it uses the declared arbitrary-parent rows with the finite Euler correction belonging to that same selected row table.

Write

    E115=19740202146111572828188083
               /495176015714152109959649689600.

Including the complete owner-prime tail, the ordinary Type I fee and the arbitrary-parent tail, the two source-unit network bounds are

    W_net^(3)<8631/1000000+1/65536+E115,
    W_net^(4)<397/50000+1/65536+(8/3)E115.                 (I10)

The order-four construction uses its own larger large-owner bound: its finite Euler correction is below.008, whereas order three has a correction below.003. Both use the same threshold2^115. One cannot combine the order-four owner fee with the order-three tail without another proof.

The exact rational comparisons are

    alpha[gamma20-397/50000-1/65536-(8/3)E115]
      =2743939009142154673482700111324202982905740495717
        /64724509349361084582831211196283176201622650880000000
      >1/23600,                                         (I11)

and

    alpha[gamma20-8631/1000000-1/65536-E115]
      =14139629098284561357011327894223077923624675090991
        /517796074794888676662649689570265409612981207040000000
      >1/36700.                                         (I12)

The [joint budget calculation](../../frontier/cover-geometry/order_matched_phase_release_comparison.py) and [exact comparisons](../../frontier/cover-geometry/order_matched_phase_release_comparison.json) retain these gate, owner, tail and projection calculations.

All the original625 network restrictions remain:

- At each37<=v<2^115, one fixed union of at most three smaller head or declared network parents.
- At eachv>=2^115, one arbitrary fixed finite union of smaller head or declared network parents.
- Exactly the declared ordinary extension domains, Type I blockers and disjoint private interiors, with each original assigned once. Undeclared private-interior coordinates cannot be used as parents.

Rows are normalized at every complete prior history, including dead fibres. The good joint mass is therefore at least gamma20 minus the matching same-law network budget. Simultaneous private filling and CRT give the full densities in the opening statement, with arbitrary finite network size, width, depth and resolving heights. The factor Q_off is the product of the actual outside resolving prime powers.

The remaining head boundary is forty linear-star and twenty qs/9qs incidences, in addition to the stated central and network conventions. The theorem neither transports the literal head to arbitrary primes nor combines any other optional phase-release family.

## Appendix: the twelve-pair special case

If the eight square-pair labels incident to7 retain their old root incidences, one may apply I1 only to the block B={11,13,17,19}. The twelve originals q²s,qs² inside B are then free, together with all fifteen square stars, while forty linear-star and twenty-eight pair incidences remain.

Its constant normalized retention floor is

    lambda_B=27737181643229/27915613090885>0,

and its stronger complete head gate is

    gamma12=26988940112492901117737957
                  /1881136901050329162240000000.

The source responses have the same I6 formula with the edge sum restricted to B. With the former646 network bound1411/100000+1/65536+E115 this already gives density greater than1/(230000 Q_off). The larger head reserve can also be paired with any separately proved compatible network budget.

This is an optional narrower head scope. The main result above permits all twenty square-pair phases, including the eight incident to7, and uses the complete order-matched network costs of647.
