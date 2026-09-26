# A finite field library covers every binary leaf layout

Each of the ten originals9qs, q<s in Q={7,11,13,17,19}, may independently have central residue4mod9 or7mod9, with arbitrary globally fixed outside endpoints. All2^10=1024 joint assignments admit the complete declared three-parent ordinary/private networks, with full survivor density strictly greater than

    1/(420000 Q_off).

The first/square pure phases remain2mod3,1mod9,4mod5,1mod25; the central15 phase is0. Arbitrary finite higher pure3 and pure5 originals retain [Report661](661-priority-fields-restore-arbitrary-higher-central-pure-phases.md)'s scope. The three square7 central roles remain1mod3,2mod5,7mod9. All twenty q²s/qs² outside phases remain arbitrary. Forty linear-star and tenqs incidences remain, including every225q incidence. The same original inventory, actual-source conditions and ordinary/private interfaces apply. These restrictions are not relaxed by the field selection.

The proof uses a library of FOUR jointly compatible95-field families. Every actual central layout selects one entire family, used for all its numerical corners and all its queries. No one family is claimed to work for every layout. This realizes the layout-dependent quantifier needed after [Report662](662-the-complete-gate-budget-requires-layout-adapted-leaf-pair-fields.md)'s obstruction to paying both endpoint layouts with a common field family.

The exact uniform complete head gate is at least

    gamma*=1864487415907319442048626989
              /931162766019912935308800000000
           =0.0020023217035156316... >1/500.             (B1)

This is ordinary mathematics and exact rational computation, not new Lean verification. It proves the complete two-leaf branch, not all5^10 live-leaf layouts or unrestricted Erdős #7.

## 1. Layouts form one joint partition of the original labels

Keep root-major central leaf indices

    x3(l)=l//3+3(l mod3) mod9,
    x5(m)=m//5+5(m mod5) mod25.

Thus leaf4 is residue4mod9 and leaf5 is residue7mod9. The null leaves arel=3,m=5; the central15 mask excludesl<3,m<5. Let I={0,1,2,4,5}, J={0,...,19}\{5}.

Order the ten numerical edges{q,s} lexicographically. A subsetA of these edges records the9qs originals with centralleaf4. Its complement records those with centralleaf5. An integer mask in0,...,1023 encodesA, bit zero corresponding to{7,11}. Each edge has one fixed original central role throughout the construction. The subsets used on different central rows are complementary parts of ONE layout, not independently optimized row assignments. Missing9qs may use one fixed auxiliary padding role4 or5; existing original phases are not changed.

At each cellc=(l,m) use the same coordinate source construction as661/662. In particular

    r_q=1/(q-1), a_q=1/[q(q-2)],
    Z7(c)=5/6-[1_(l//3=1)+1_(m//5=2)+1_(l=5)]/35,
    Zq=(q-2)/(q-1)-2a_q, q>7.

The square7 depth-two role remainsleaf5, independently ofA. For e={q,s}, put

    b_e=a_q r_s+r_q a_s, d_e=r_q r_s,
    beta_e^A(c)=b_e+d_e[1_(e in A)1_(l=4)
                            +1_(e notin A)1_(l=5)].      (B2)

Every released q²s,qs²,9qs original is included once in its actual edge event union. The first two components contribute b_e; the last contributes its specified active-leaf term. Arbitrary outside endpoint phases and overlaps are allowed by the same joint union bound. The fifty retained root incidences still delete the linear stars andqs.

The componentwise bounds beta_e^A<=b_e+d_e andZ7>=157/210 imply

    1-sum_e beta_e^A/(Zq Zs)
      >=754111121894423/876550251053789>0               (B3)

for every cell and all1024 layouts. Consequently the conditional matching construction gives one actual outside submeasurezeta_(A,c), dominated by the actual coordinate product, with exact mass and simultaneous full-height responses

    H_T^A(c)=sum_(matchings F in Q\T)(-1)^|F|
                product_(e in F)beta_e^A(c)
                product_(q notin T union vertices(F))Zq(c). (B4)

The same zeta_(A,c) is used for every weak-marker corner and every query. It may depend on the actual original family and cell. It need not be invariant under numerical comparison symmetries.

## 2. A finite local-response decomposition

For arbitrary live-leaf assignments, writeA_l for the set of edges whose9qs role isleafl. The setsA_l partition the ten original edges. At a cell inleafl, the response depends on the assignment only throughA_l. Hence there are1024 possible local edge-subset activations, independently of how other edges are distributed among the other rows. This is a response lookup reduction; it does not authorize recombining incompatible local subsets.

For the present binary branch,A_4=A,A_5=A^c andA_0=A_1=A_2=empty. Let H_T(n,B) be the matching polynomial usingZ7=5/6−n/35 and beta_e=b_e+d_e1_(e in B). The six central response profiles, in order, are

    regular leaves, column other than2: H_T(0,empty);
    regular leaves, column2:            H_T(1,empty);
    leaf4, column other than2:           H_T(1,A);
    leaf4, column2:                     H_T(2,A);
    leaf5, column other than2:           H_T(2,A^c);
    leaf5, column2:                     H_T(3,A^c).       (B5)

Here regular meansl in{0,1,2}. Masked cells contribute zero separately. The certificate precomputes H_T(n,B) for every n in{0,1,2,3}, everyB⊆E and everyT⊆Q.

The matching polynomial has degree at most two in the edge activations becauseK5 has no three-edge matching. Therefore

    H_T(n,B)=h0_(n,T)+sum_(e in B)u_(n,T,e)
                       +sum_(e<f in B, disjoint)v_(n,T,e,f). (B6)

Each unordered pair of disjoint edges is counted once, using the fixed numerical edge order. All coefficients are rational and computed from the displayed masses. Interactions occur only on disjoint original edges, the Petersen graph on the ten edge labels. FormulaB6 retains the numerical prime weights; no prime or edge is permuted. It supplies an exact finite table rather than a lower relaxation of the response.

## 3. Select one complete priority family for each layout

For each numerical weak-marker pair(i,j) use the fixed-null corner vectors

    w^i_l=(2-1_(i=l))/9 onI, zero onleaf3;
    v^j_m=(4-1_(j=m))/75 onJ, zero onleaf5.

Every library item s is an entire familyTheta_s=(theta_s^ij(c)) satisfying

    0<=theta_s^ij(c)<=1,
    theta_s^lj(l,m)>=theta_s^ij(l,m),
    theta_s^im(l,m)>=theta_s^ij(l,m),                    (B7)

and vanishing on both null leaves and the common central15 mask. These are645's two priority conditions. They couple all95 corner fields. A selected item is not an independent choice of an optimal field for each corner.

The library uses180 orbit coordinates per family under the same finite group as662: S3 acts on regular ternary leaves0,1,2, and independent permutations act within the live leaves of each quinary column. Leaves4 and5 and all outside edge labels stay fixed. This group preserves EVERY binary layout's responseB4, all masks, every complete selector menu and its coefficient. The same12 corner representatives

    (i,j) in{0,4,5}×{0,6,10,15}                         (B8)

therefore cover all95 corners for each invariant field family. Whole, root/column, leaf and deep selectors all transform together; the deep constants1 and4/5 are unchanged. This is comparison symmetry, not symmetry of the actual probability source.

The exact data gives four field tables and a total selection function

    s:{0,...,1023}->{0,1,2,3}.

Family0 is661's table with exact common denominator180. Family1 is662's dyadic table. Families2 and3 have denominator2^20 as well. Thus the original rational levels8/9,11/12,19/20 are not approximated by a dyadic value. The selection uses family0 on405 layouts, family1 on38, family2 on21 and family3 on560. These counts describe one supplied certificate, not optimality or uniqueness.

For every one of the1024 layouts, the certificate proves

    min_(i,j) G_(A,i,j)(theta_(s(A))^ij)>=gamma*.       (B9)

In particular

    min_A max_s min_(i,j) G_(A,i,j)(theta_s^ij)>=gamma*.

The order is essential: one indexs(A) is fixed before any corner or query is evaluated. Replacing this by a separate field choice within each corner or selector would not establish the same-source result.

## 4. Complete selectors and exact checking

The complete512 coefficients are the same pinned640 array with the four guarded9q² additions g a_q at central mode(2,1), outside support{q}, forq=11,13,17,19. Hereg=200163067/201247200. The original inventory, unit term, full-height sums and all query fees are unchanged.

For each corner and field, evaluate all16 central modes and32 outside supports. The ternary selector levels are wholew, root restrictions, leaf masses anddelta_l; the quinary levels are wholev, column restrictions, leaf masses and(4/5)delta_m. Deep selectors retain their density-cap normalization.

FormulaB5 allows each literal selector, after multiplying its actual field values, to be aggregated into a nonnegative six-entry coefficient vector. Its dot product with the six H_T profiles equals the original120cell sum. Identical coefficient vectors may be merged. A vectoru may also be discarded if another vectorv in the SAME menu satisfiesu<=v entrywise: every H_T profile is positive, so the dot product foru never exceeds that forv. The producer checks a retained dominating vector for every original selector. It keeps the maximum over all remaining vectors; it does not freeze an anchor selector or ignore selector switching.

The resulting rational calculation checks all

    1024×12×512=6291456

complete screen maxima. Its minimum is exactlyB1, attained at the all-leaf5 layoutA=empty, family0 and weak pair(4,6). The other weak pairs in that corner's orbit are represented by the same value. Every inequality inB9 is checked with exact integers and fractions.

The producer also checks both priority inequalities on all4×95×80 live field entries. The12-corner reduction affects only gate evaluation; priority is not assumed from representative corners. All local subset matching responses are checked positive, and the uniform strict regionB3 supports the actual conditional source for the entire branch.

## 5. One actual source for each original family

Fix any admitted actual family and its single globally fixed binary layoutA. Choose its certified library indexs(A). Construct actual central probability lawsrho3<=2H3 andrho5<=(4/3)H5 by624/661 after deleting the fixed first/square pure classes and all actual higher pure originals. The complete pure tails1/18 and1/100 guarantee the required positive fixed-null capacities. Decompose their numerical leaf massesw,v as

    w=sum_i alpha_i w^i, v=sum_j beta_j v^j.

No comparison corner is required to be an actual probability law on that family's deep survivor. Use the one actual source already constructed and define

    lambda_c=sum_(i,j)alpha_i beta_j w^i_l v^j_m
                                     theta_(s(A))^ij(c),
    theta_eff(c)=lambda_c/(w_l v_m)

on positive cells, zero on nulls or the mask. Attach the SAME actualzeta_(A,c) fromB4. The chosen field index is fixed for the family; it does not change across alpha,beta, observed queries or continuation branches.

Report645 applies toB7. It preserves the exact average source mass and bounds every finite-depth single or paired central cylinder by the averaged corner fields. Multiplying by the same simultaneous H_T responses and maximizing the complete labelled selectors yields

    G_actual(theta_eff)
      >=sum_(i,j)alpha_i beta_j G_(A,i,j)(theta_(s(A))^ij)
      >=gamma*.                                           (B10)

This is the all-height proof. The finite1024-layout table certifies the complete coefficient inequalities; it does not replace the actual-source or density argument. There is no clipping debit, and no averaging of probability laws belonging to different original families.

## 6. Complete networks and remaining boundary

The source inB10 is dominated by the same actual pure product and fixed unary submeasures as661/662. Its omitted-coordinate caps, rebuilt23/29/31 continuation and simultaneous network bounds therefore use the unchanged657/658 recipes. Actual normalized rows are constructed from this new source; probability kernels from another source are not copied.

Retain all193 finite row bounds, the complete owner tail, the ordinary Type I fee1/65536 and either full arbitrary-parent tail. At most three earlier declared parents are allowed at each37<=v<2^46 in theRS policy, or below2^68 in the elementary policy; arbitrary fixed finite parent unions are allowed from the respective switch onward. All ordinary domains, private interiors and one-time original assignments remain required.

With projection factor2673/110656, the exact uniform gateB1 gives projected reserves

    RS46:         0.000003076056256528969...,
    elementary68:0.000002407646801024185...,

both strictly greater than1/420000. Simultaneous private filling and CRT give the density in the opening statement for arbitrary finite network size, width, depth and resolving heights within these declared interfaces.

The new conclusion covers every independent assignment of the ten9qs roles to leaves4 and5. It does not permit central leaves0,1,2, change the fixed nulls or square7 roles, release any of the fifty retained incidences, combine the225q phase release, transport the literal head to other primes, or remove the ordinary/private network restrictions. For all five live leaves the local subsetsA_l must still form one partition, and a paying field family must be selected for that whole partition.

## 7. A verified transport rule for further layout branches

The binary certificate above evaluates each actual layout's comparison table directly. A second lawful route can group larger classes of layouts under one virtual upper table. This is an application of [Scott--Sokal, Proposition2.26(b), equation(2.74)](../../../../../Library/Arith/scottsokal2003repulsive.md), whose strict-region hypotheses are essential. It does not assert that such an upper table has a paying gate.

At a fixed cell keep the SAME positive massesZq and let edge caps satisfy `0<=beta_e<=beta_e^+`. Suppose every induced independent-set polynomial of `L(K5)` at `x_e^+=beta_e^+/(Zq Zs)` is strictly positive. For `x_e=beta_e/(Zq Zs)` writep for that graph's alternating independent-set polynomial, andlambda_T for the indicator of edges disjoint fromT. The cited theorem gives

    p(lambda_T x)/p(x)<=p(lambda_T x^+)/p(x^+).

UsingB4's unnormalized masses, define

    r(c)=H_empty^+(c)/H_empty(c).

Strict positivity and downward monotonicity give `0<r<=1`, and the SAME coordinate masses cancel to give

    r H_empty=H_empty^+,
    r H_T<=H_T^+ for everyT.                         (B11)

For a virtual-table priority familyvarphi^ij, set `theta^ij(c)=r(c)varphi^ij(c)`. This uses one factor independent ofi,j, so both priority inequalities are preserved. On the actual source, its mass equals the virtual comparison mass and all simultaneous nonnegative query expressions are no larger. Consequently, for every numerical corner and including the true maxima in all512 menus,

    G_actual_layout(theta)>=G_virtual(varphi).       (B12)

The factor r restricts the actual conditional law once, through theta=r varphi; it is not applied a second time. No imaginary globally phased family replaces that law. The same all-depth645 transport then applies. Neither B11 nor B12 supplies positivity of the virtual gate.

For the support masks used here there is a finite proof of the ratio theorem. On any finite hard-core graph putq_A for the induced alternating polynomial. Its deletion recurrence is

    q_A(x)=q_(A\{v})(x)-x_v q_(A\N_A[v])(x).

Assume everyq_A(y)>0 and0<=x<=y. Strong induction on|A| proves both positivity atx and

    q_A(x)/q_(A\{v})(x)>=q_A(y)/q_(A\{v})(y)>0.

Indeed deleting the neighbours ofv successively insideA\{v} expresses `q_(A\{v})/q_(A\N_A[v])` as a product of ratios for strictly smaller induced graphs. That product atx is at least its positive value aty. Dividing the recurrence byq_(A\{v}) then yields the displayed inequality. Telescoping over any set of deleted vertices and taking reciprocals proves the required ratio monotonicity. The same induction proves downward positivity; full-polynomial positivity alone cannot replace the all-induced assumption. This is an elementary verification of the cited specialization, not a new general ratio theorem.

For a branch of global phase layouts, fix some edge roles and put all remaining marker increments on in every permitted cell as a virtual upper bound. This preserves the numerical labels; each actual layout remains fixed within the branch. The upper caps are bounded by `b_e+d_e`, soB3 proves the strict region for every such branch table. A successful compatible virtual field would then cover every layout in that branch byB11--B12. To obtain a new global theorem one must still certify a paying gate on EVERY branch of an explicit exhaustive cover. This obligation is not discharged by the binary1024-layout certificate.

## 8. A single supported ternary row cannot have a positive complete head gate

A possible reduction would choose a row carrying at most two of the ten edge activations and use fields supported only on that row. It would suffice to certify all5×(1+10+45)=280 labelled sparse-row cases. However, none of these required row-supported positive95-field certificates exists under the current complete coefficient envelope. This follows from four already present selector-mode families; no LP or layout scan is needed.

This is an ordinary proof plus a minimal exact rational coefficient certificate. It concerns the specified gate, not actual survivor mass. It does not exclude general fields supported on several rows, layout-adapted fields, different query bounds, or a different complete-charge method. No Lean verification is claimed.

### 8.1. Every queried-support response is at least the empty response

For U subset Q, write its matching polynomial as

    H(U)=sum_(matchings F in U)(-1)^|F|
                  product_(e in F)beta_e
                  product_(q in U\vertices(F))Zq.

Assume0<Zq<=1, beta_e>=0, and H(U)>0 for all U. These hypotheses hold on every unmasked cell of the current uniformly strict response box, for any of the live-leaf layouts and any subset of active9qs labels.

Partition matchings according to the status of vertex v in U. Either v is unmatched or matched to exactly one u. This gives the exact recurrence

    H(U)=Z_v H(U-v)-sum_(u in U-v) beta_{vu} H(U\{v,u}).

Every subtracted term is nonnegative, so

    0<H(U)<=Z_v H(U-v)<=H(U-v).

Delete the physical query-support vertices one at a time. Since `H_T=H(Q\T)` and `H_empty=H(Q)`,

    H_T(c)>=H_empty(c)>0 for every T.                 (SR1)

On the common null/mask cells both field contributions are zero, and no division is needed. This is a physical-vertex matching recurrence; it does not require numerical prime permutations or a fractional hard-core theorem.

### 8.2. The weak corner of the supported row forces four query charges

Fix a live ternary row l and ANY nonnegative field theta supported there. Take a numerical corner `(i,j)` with i=l; j may be any of the19 live quinary weak markers. Its row mass is `w_l^i=1/9`. Define the field's source mass

    M=(1/9) sum_m v_m^j theta(l,m) H_empty(l,m)>=0.

For each outside query support T, use quinary mode b=0, the whole v vector. The ternary modes a=0,1,2,3 have legal choices: whole w, the first-root block containing l, leaf l, and deep delta_l. Because the field vanishes off l, their selected query values are respectively

    (1/9) sum_m v_m theta H_T,
    (1/9) sum_m v_m theta H_T,
    (1/9) sum_m v_m theta H_T,
            sum_m v_m theta H_T.

By(SR1) the corresponding COMPLETE menu maxima are at least

    M, M, M, 9M.                                     (SR2)

These are only legal lower bounds on the maxima; they do not assume an active selector or freeze selector switching. The factor9 comes from the genuine deep selector delta_l, which has no extra source-leaf probability.

No priority assumption is needed for this single-corner inequality. It holds for arbitrary field values and any active edge subset on that row.

### 8.3. The exact current coefficients make every such gate nonpositive

Write `C_(a,b,T)` for the current complete nonnegative512 coefficients, with flattened mode `4a+b` and support indexT. The mass coefficient is

    g=200163067/201247200.

Keep only the four mode families `(a,b)=(0,0),(1,0),(2,0),(3,0)`, flattened modes0,4,8,12. All remaining fees are nonnegative and can be dropped when obtaining an UPPER bound on the gate. By(SR2),

    G(theta)<= [g-K]M,
    K=sum_(T subset Q)[C_(0,0,T)+C_(1,0,T)
                            +C_(2,0,T)+9 C_(3,0,T)].    (SR3)

Exact arithmetic on the pinned640 coefficient JSON gives

    K=5410561403800247066694067
          /4539696895445741568000000
      =1.1918331836709546...,

    delta=K-g=895320178864953734214067
                   /4539696895445741568000000
          =0.19722025489480272... >0.

The four guarded9q² additions used by661--664 are at mode `(2,1)`, flattened mode9. They are outside the selected four families and are nonnegative. Thus the value of K is unchanged and the upper bound is valid for the FULL current array, not just the old base.

Therefore

    G_(i=l,j)(theta)<=-delta M<=0.                    (SR4)

It is strictly negative for a positive source mass. A zero field gives zero gate.

### 8.4. Exact quantified consequence for the sparse-row proposal

Let a whole95-field family be supported on ONE fixed row l. At each of its19 corners with weak ternary index i=l, its field obeys(SR4). Hence

    min_(i,j) G_(i,j)(theta^ij)<=0.

Taking the supremum over all such families, even allowing arbitrary compatible or incompatible choices of fields across corners, cannot make this uniform minimum positive. The all-zero compatible family is feasible and has all gates zero. Thus the best uniform HEAD gate among row-supported compatible families is exactly zero.

This statement is uniform in the row, original layout, active subset S and quinary weak marker. In particular it excludes every one of the proposed `5×(1+10+45)=280` paying row-supported cases, before subtracting any positive complete network fee. Sparse occupancy of pair activations does not compensate for concentrating the entire source on a weak ternary leaf, because the deep-query debit loses the1/9 mass factor.

The pigeonhole fact that some row contains at most two of the ten edge activations remains true. The conditional implication "if each sparse row has a paying whole95 family, then all layouts are covered" remains true. What fails is its proposed sufficient premise under the literal current envelope. Escalating from19 row variables to the full1805 row-supported variables, or repairing priorities while keeping that support, cannot fix(SR4).

This does not exclude a certificate choosing a different support ROW within each numerical field if the ENTIRE resulting family satisfies the actual coupled priorities. Such a family is outside the fixed-row premise and may need several rows after actual-source transport. It also does not exclude discarding unattainable corners in a different source-specific argument; the current result concerns the full95-corner criterion.

The [coefficient certificate](../../frontier/cover-geometry/sparse_row_complete_gate_obstruction.py) and [exact result](../../frontier/cover-geometry/sparse_row_complete_gate_obstruction.json) pin the original640 coefficient array, reconstruct the four nonnegative guarded additions and verify the displayed charge and strict gap. All14 explicit checks pass with assertions disabled. A separate local coefficient sum reproduced K and delta; the portable program's retained output was reproduced byte for byte. The recurrence and selector inequalities above supply the all-fields/all-layouts statement. Reproduce with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/sparse_row_complete_gate_obstruction.py
```

## Exact evidence

The portable [producer](../../frontier/cover-geometry/binary_leaf_pair_library_certificate.py) and [exact data](../../frontier/cover-geometry/binary_leaf_pair_library_certificate.json) use only Python's standard library and the pinned640 and658 sibling JSON. The field library and1024-entry selection function are literal certificate data; no optimizer or exploratory helper is required. It passes231,778 explicit checks with assertions disabled:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/binary_leaf_pair_library_certificate.py
```

It accepts `--directory` and `--output`. The exact result includes allfour field tables, the selection for every layout and each layout's12 complete corner gates. Finite predicates certify the supplied witness; sections1--6 supply its stated source, symmetry, all-height and continuation quantifiers. The independent [verifier](../../frontier/cover-geometry/binary_leaf_pair_library_independent.py) and its [result](../../frontier/cover-geometry/binary_leaf_pair_library_independent.json) reconstruct the edge caps and matching sums directly from the three pinned input JSON files, without reading the producer. It checks all 6,291,456 complete selector maxima, all 1024×12 corner gates, the actual permutation generators, both priorities on all 95 corners, and both full network margins. Its 612,877 explicit checks pass with assertions disabled. The exact minimum agrees with B1. A separate literal menu loop cross-checks the integer aggregation. Both programs were rerun locally, and each retained result was reproduced byte for byte. None of these checks is a new Lean proof.

The independent command, also accepting `--directory`, `--witness` and `--output`, is:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/binary_leaf_pair_library_independent.py
```
