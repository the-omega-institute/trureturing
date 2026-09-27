# Coherent star phases improve mode0 but do not pay the complete gate

For the native central null geometry(3,5), keeping the forty linear-star phases globally coherent gives a uniform mode0 lower bound of64121/3125000=0.02051872. It allows arbitrary central phases, outside roots and root-pair endpoints within the declared comparison. One corner-independent retention field realizes this bound on one actual source, with every retained matching response strictly positive.

The same field does not pay the complete response-envelope gate. On the existing clustered phase81 fixture, its corrected512-term gate is-0.1257123184425597.... Already mode1 exceeds the proposed uniform budget for all remaining modes. Thus the mode0 theorem is a valid partial result, while the proposed remaining-debit inequality for this field is refuted.

This is an ordinary mathematical result with exact finite arithmetic. It is not Lean verification, an all-field impossibility theorem, or a covering counterexample. A negative gate computed from conservative query upper bounds does not imply that the actual surviving source is empty or that its exact query responses fail. No incidence restriction is removed from an existing complete noncoverage theorem by this partial result.

## 1. Actual numerical labels and a conservative common source

Use Q={7,11,13,17,19}, and the forty distinct numerical labels dq with

    d in D={3,5,15,9,25,45,75,225}.

Each present original retains its one globally fixed phase a_(q,d). At a live central cell c define

    n_q(c)=sum_(d in D)1_(c=a_(q,d) mod d).

An absent original contributes zero. Counts deliberately include repeated outside roots; root collisions can make this comparison conservative. No phase depends on the cell, corner or subsequent query.

Begin with the inherited actual normalized root-balanced pure laws rho_q, with root caps r_q=1/(q-1), square caps a_q=1/[q(q-2)] and all full-height caps. Fix one auxiliary live root at each q for the whole family. Delete it and the actual square-star cylinders paid by

    B7=1-r7-3a7=157/210,
    Bq=1-rq-2aq for q>7.

At7 the three square stars3q²,5q²,9q² are paid; at the other coordinates3q² and5q² are paid. Then delete all root cylinders of active dq originals. On the same actual unary measure the remaining mass V_q(c) is at least Bq-rq*n_q(c). Set

    Z_q(c)=max(0,Bq-rq*n_q(c)).

Where Z_q>0, scale the actual remaining submeasure by Z_q/V_q. Its mass is exactly Z_q and every inherited cylinder upper bound is preserved. Zero-mass cells are discarded by the field below. This is thinning, not renormalization of the actual prefix caps.

For every pair{p,q}, impose the union of the actual pq,p²q,pq²,9pq events. The universal unnormalized activity bound is

    beta_pq=a_p*r_q+r_p*a_q+2*r_p*r_q.

One root-root term pays arbitrary pq endpoints; the other pays9pq at every cell. The corresponding probability under the normalized unary product is at most beta_pq/(Z_p Z_q). Events on disjoint edges depend on disjoint coordinates. All actual phases and higher-pure survivor laws remain fixed.

## 2. Matching responses, strictness and query transport

For T subset Q let H_T(n) be the signed matching sum on V=Q minus T:

    H_T=product_(q in V)Z_q
       -sum_(edges e in V)beta_e product_(q in V minus e)Z_q
       +sum_(unordered disjoint edge pairs{e,f} in V)
          beta_e beta_f product_(q in V minus(e union f))Z_q.

Each unordered pair is counted once. The complete graph on five vertices has26 matchings. Equivalently, H(empty)=1 and

    H(V)=Z_p H(V minus p)
          -sum_(q in V minus p)beta_pq H(V minus{p,q}).

With640's base mode0 coefficients C_(0,T) and g=200163067/201247200, define

    F(n)=g H_empty(n)-sum_T C_(0,T)H_T(n),
    chi(c)=1_(F(n(c))>0).

Of59049 count vectors in{0,...,8}^5,15894 satisfy F>0. For every such vector all32 vertex-induced responses are positive. The minimum is

    28028831665337/8462661375168000.

These32 tests also imply the required positivity for every induced event subset. The derivative with respect to an edge activity is minus the matching polynomial on at most three remaining vertices. That smaller polynomial is linear in its edge activities; decreasing any of them raises it above its positive complete-graph value. Consequently every matching polynomial decreases with each edge activity throughout the box from zero to beta. Deleting edges raises it. Hence all1024 subsets of the ten pair events, and all smaller actual activity vectors, lie in the strict region. This is the ordinary argument connecting the32 numerical tests to the conditional Shearer hypotheses.

At a retained cell let nu_c be the product of the normalized thinned unary measures, A_c the actual pair-avoidance event and P_c=product_q Z_q. The inherited strict conditional ratio theorem gives

    nu_c(A_c)>=H_empty/P_c.

The single submeasure

    zeta_c=H_empty nu_c(. | A_c)

is therefore dominated by the actual unnormalized unary product and has mass H_empty. For a query on support T, retaining only edges disjoint from T and applying the conditional ratio bound gives

    zeta_c(query)<=H_T product_(q in T)cap_q(query_q).

This holds for every finite-height query on the same source. The Z_q denominators cancel; thirty-two separately optimized laws are never introduced.

The field chi and the attached zeta_c are independent of the numerical weak corner. Thus645's two weak-marker priority conditions hold with equality, and its actual central mixture construction applies. The95 corner laws are comparison objects; they are not assumed to be95 independently available actual pure sources.

## 3. Global phase coherence gives the mode0 lower bound

Exact finite evaluation gives the affine minorant

    F_+(n)>=(140440-35110*n7-17555*n11-10551*n13
                    -4824*n17-4138*n19)/1000000.       (C1)

Equality occurs at(0,8,0,0,0) and(4,0,0,0,0). The constant-three vector gives

    F(3,3,3,3,3)
      =8482754828806680432735281/3678667717609532583936000000.

Write the eighty live cells as(l,m), with

    l in{0,1,2,4,5}, m in{0,...,19} minus{5},
    exclude(l<3 and m<5).

Their physical residues are3*(l mod3)+floor(l/3) modulo9 and5*(m mod5)+floor(m/5) modulo25. At corner(i,j), the weight is

    mu_ij(l,m)=(2-1_(l=i))(4-1_(m=j))/675.

Put D_ij=sum_c mu_ij(c) and

    S_ij=sum_(d in D)max_(a mod d)sum_(c=a mod d)mu_ij(c).

For each q, its eight fixed phases satisfy

    sum_c mu_ij(c)n_q(c)<=S_ij.                          (C2)

This follows by interchanging the sum over cells with the sum over original dq labels, and then bounding each one fixed residue class by its largest class mass. It does not choose a different phase for each cell.

The sum of the five slopes in(C1) is36089/500000. Therefore

    sum_c mu_ij(c)F_+(n(c))
      >=(3511/25000)D_ij-(36089/500000)S_ij
      >=64121/3125000                                  (C3)

at every one of95 corners. For example, at(4,6), D=37/45 and S=296/225; its eight class maxima, in the displayed D order, are

    22/45,4/15,8/45,2/9,4/75,8/135,8/225,8/675.

Thus global coherence prevents the pessimistic constant-three-count box from obstructing the mode0 sum. It does not supply an upper bound on the remaining fifteen modes. The calculation covers this native null geometry, not automatically the other native geometries already considered in677/678 under their own hypotheses.

## 4. A coherent regression refutes the proposed remaining-debit claim

The candidate claim was that the same chi would pay every remaining mode from the difference between(C3) and gamma=193/100000, namely

    proposed remaining budget=232359/12500000=0.01858872.

Retain640's entire512 coefficient table. Because the new source does not establish the old9q² guards for q>7, add the full charges

    C_(8,{q}) += g/[q(q-2)], q=11,13,17,19.

Mode8 is ternary leaf times the whole quinary coordinate. Substituting guarded mode9 would require an additional actual deletion argument absent from this construction.

Use the existing [clustered global-phase fixture](../../frontier/cover-geometry/clustered_global_phase_fixture.json). Its forty original dq labels all have central phase81 modulo d. Keep their actual full phases. At corner(4,10), the common field retains74 cells. Evaluating all559 literal central selector candidates across sixteen menus, with the maximum taken after the whole cell sum, gives

    mode0=31840305005954603376439854827/206925059115536207846400000000,
    remaining debit=231413335724929518222451571471/827700236462144831385600000000,
    complete gate=-34684038567037034905564050721/275900078820714943795200000000
                 =-0.1257123184425597... .

Already mode1 alone costs

    41957988958888040447123383/1724375492629468398720000000
      =0.02433228095518052...,

strictly more than the proposed TOTAL remaining budget. Thus that uniform remaining-debit inequality is false for the specified chi. The full response-envelope gate also fails on this fixture even after using its larger actual mode0 value, not merely the uniform lower bound(C3).

The selector normalization uses denominator1350, ordinary ternary numerators2*(2-delta), deep ternary numerator18, ordinary quinary numerators4-delta and deep quinary numerator60. The equivalent denominator675 implementation halves only the ternary numerators. Generic deep caps are retained; no uniform weak-leaf improvement or missing higher-pure phase is assumed.

This regression concerns the declared count-based response envelope. It overcounts repeated roots, and its H_T are simultaneous upper bounds, not necessarily attainable query values. A sharper actual response or a different field may work. There is no dual certificate here excluding every field, and the fixture is not an arithmetic covering.

## 5. Verification and the remaining mathematical target

The [producer](../../frontier/cover-geometry/coherent_star_mode0_certificate.py) and [result](../../frontier/cover-geometry/coherent_star_mode0_certificate.json) use an integer matching recurrence and the root-major CRT coordinates, with568318 checks. The [independent verifier](../../frontier/cover-geometry/coherent_star_mode0_independent.py) and [result](../../frontier/cover-geometry/coherent_star_mode0_independent.json) enumerate matchings directly and reconstruct cells from physical residues with a225-entry CRT table, with568038 checks. Both check all59049 count vectors, all95 corners and the coherent fixture's sixteen exact mode fees with fullmode8 charges. Their pinned inputs are640's coefficient result and the101-original fixture. Neither program uses a floating-point comparison or a linear-program optimizer.

The producer evaluates17887 nonzero-coefficient selector/support candidates; the independent implementation evaluates17888 including the single zero-coefficient mode0/empty-support case. Both include all559 selector candidates and every charged term. The exact source mass, all corner summaries and all sixteen fee blocks agree. Both canonical outputs replay byte for byte:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/coherent_star_mode0_certificate.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/coherent_star_mode0_independent.py
```

The mode0 bound and the failed complete-gate regression are separate conclusions. Further work must control all selector modes jointly or use a sharper actual source/response. An affine phase-support bound for a fixed complete selector tuple can be valid, but testing only generated tuples does not prove a statement for every tuple without a certified separation or global coverage argument.

Actual higher-pure holes also prevent assuming uniform depth-two tails without a support-preserving averaging theorem. The source constructed here retains the actual higher-pure laws at all heights. Neither the successful mode0 computation nor the negative regression changes the unrestricted quantifiers of Erdős #7.
