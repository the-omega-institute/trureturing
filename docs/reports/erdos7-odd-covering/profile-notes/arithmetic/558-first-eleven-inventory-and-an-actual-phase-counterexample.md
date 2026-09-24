# First-eleven inventory saving and an actual phase counterexample

For any finite actual two-copy family on Q={5,7,11,13,17,19}, at most one original at the numerical modulus 11 is enough for the unchanged PA law to satisfy

    R_Q <= 2733779746141627138211/542935350932041267200
         =5.0351846522... <257/51.

All old 5/7 geometry, higher pure-11 classes, mixed first-11 classes, and later 13/17/19 classes may be arbitrary. The proof retains the actual pure-11 inventory in the first-row loss bound. It does not require the prescribed old48 source or old-slot rectangles of [report554](554-old-slot-rectangles-control-arbitrary-first-eleven-residues.md).

When both modulus-11 originals are present, a fixed finite family with 200 actual first-11 originals refutes the simplified uniform saving criterion

    S11+(F13-sup_L integral(L-2)_+ d lambda11)/4 >= kreq.

A 124-cylinder query already witnesses its failure. This counterexample does not refute the PA construction: retaining the old-prefix credits repairs this particular finite-query score, and a separately specified actual row13 completion has zero mass loss and gives a full-query bound below the target. The finite-query calculation and the full-query conclusion use distinct arguments.

These are ordinary mathematical deductions and exact arithmetic checks, not Lean results. No unrestricted two-copy closure or Erdős #7 conclusion follows.

[Report559](559-pure-union-savings-control-all-four-later-rows.md) extends
the pure-union inequality to all four PA rows simultaneously. It also
allows a single root13 occurrence, or simultaneous single root17 and
root19 occurrences, with arbitrary remaining original geometry.

## 1. One actual source and the inventory-sensitive first-row inequality

Use the actual PA kernels of [report348 CP/PA](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md), with no intermediate normalization. All original residues are globally fixed, the family is finite, every modulus is nonunit and Q-smooth, and every full numerical modulus has at most two original occurrences. Let lambda0 be Haar restricted to the complete actual old 5/7 survivor. Let x,y be the actual pure-5 and pure-7 survivor masses. Then

    x>=1/2, y>=2/3,
    lambda0 <= (H5 restricted to S5) times (H7 restricted to S7),
    F11=x/42+y/20+59/840 >=97/840.                        (I1)

The last expression is the complete, unnormalized old-query comparison hinge from PA2--PA3. In particular every legal finite old query L, with its unit included, satisfies

    integral(L-2)_+ d lambda0 <= F11.                    (I2)

Complete missing labels by arbitrary globally fixed phases and then apply the same source comparison. Completion adds nonnegative terms; it does not change any original.

For each exponent e, assign actual originals of numerical modulus d*11^e once to slots j=1,2, with at most one occurrence of each old numerical cofactor d in each slot. The assignment is independent of the sampled point and any later query. Write i=(e,j) and

    beta_i=5/11^e, sum_i beta_i=1.

Let p_i indicate the presence of the pure cofactor-one original in slot i. Define the weighted pure inventory p and the actual pure-union parameter rho by

    p=sum_i beta_i*p_i <=1,
    rho=5*H11(actual pure-11 forbidden union) <=p.         (I3)

The complete pure union is independent of the old point. Overlapping pure cylinders are counted once in rho. The sums use the entire geometric inventory, including absent slots; no finite truncation is renormalized.

At an old point z let n_i(z) count active NONUNIT old cofactors in slot i. Put

    G(z)=sum_i beta_i*(n_i(z)-1)_+,
    b(z)=sum_i beta_i*1_(n_i(z)>0) <=1.

If r(z) is the actual forbidden11 fraction in the fibre, the union bound on this same fibre gives

    5r(z) <= rho+G(z)+b(z).

For the actual PA cap5/3, the fibre mass and loss are

    s(z)=min(1,(5/3)*(1-r(z))),
    ell(z)=1-s(z)=(5r(z)-2)_+/3 in[0,1].

These formulas include a completely forbidden fibre. On E={ell>0},

    3ell <= G-(1-rho).

Since ell<=1 and rho<=1,

    G >=3ell+(1-rho) >=(4-rho)ell.

Off E the same inequality follows from G>=0. Thus

    (4-rho)ell <=G.                                    (I4)

For each fixed slot, 1+n_i is a legal finite old query: it has at most one globally fixed cylinder for every nonunit old numerical cofactor. Equation I2 gives

    integral(n_i-1)_+ d lambda0 <=F11,
    Gamma:=integral G d lambda0 <=F11.

Consequently the actual row loss Delta11 and its PA saving S11 obey

    Delta11=lambda0(1)-lambda11(1) <=F11/(4-rho),
    S11=F11/3-Delta11
       >=F11*(1-rho)/(3*(4-rho))
       >=F11*(1-p)/(3*(4-p)).                          (I5)

The second inequality uses rho<=p and the decreasing function (1-r)/(3*(4-r)). A complementary form retains both the comparison-query deficit and the inactive-slot deficit:

    S11 >=[F11-Gamma
              +integral_E(2-rho-b) d lambda0]/3.        (I6)

Every term on the right is nonnegative. Near equality therefore constrains the beta-weighted activation and average query deficit; it does not force each individual high-exponent slot to be active or extremal.

## 2. A root11 scarcity theorem for arbitrary old geometry

If the full numerical modulus11 has at most one original, all deeper pure11 slots may still be present, but

    rho<=p<=5/11+2*sum_(e>=2)5/11^e=6/11.

Using I1 and I5,

    S11>=5F11/114>=97/19152.                            (I7)

This conclusion is independent of the fixed old48 source used below. Mixed first11 moduli such as55 or77 need not be absent. It is also different from the condition in [report544](544-missing-original-slots-restore-a-common-law-debit.md), which uses missing slots at two of55,77,385.

For the same actual PA construction set

    T=257/51,
    c0=6168733163201163811/542935350932041267200,
    kreq=c0/(T-2)
        =6168733163201163811/1650097635185615616000.

Let m be the actual mixed5/7 forbidden mass inside the actual pure survivor, d5=x-1/2 and d7=y-2/3. Let Sq=aq Fq-Deltaq be each actual later-row saving, with a11=1/3,a13=a17=1/4,a19=1/5. All Sq, d5,d7 and1/12-m are nonnegative. The exact mass identity and report348 NC4 give

    (T-2)*lambda_final(1)-Phi
      =-c0+A5*d5+A7*d7+A57*d5*d7
           +(T-2)*(1/12-m+sum_q Sq).

The positive coefficients A5,A7,A57 are those of NC4; Phi is its complete final-query hinge on the same actual pure-source parameters. Equation I7 alone yields the uniform positive margin

    Delta=(T-2)*(97/19152-kreq)
         =2188590908071012189/542935350932041267200>0.

For every finite complete query L,

    lambda_final(L-1)<=2lambda_final(1)+Phi.

The PA mass is positive and at most one. Normalize this one actual law once, maximize each numerical label within a finite inventory, and exhaust the labels. Therefore

    R_Q<=T-Delta/lambda_final(1)<=T-Delta
       =2733779746141627138211/542935350932041267200<T.    (I8)

Thus a strict all-supported-laws lower witness above T must contain two original classes at the numerical modulus11. This is a necessary condition on such a witness, not a construction of one. Original higher exponents and all query heights remain unrestricted.

## 3. A fully fixed finite counterexample with both root11 copies

The counterexample uses exactly the following48 old originals. For p=5,7 and e=1,...,4 include the two residues

    p^(e-1), 2*p^(e-1) modulo p^e.

For every1<=a,b<=4 include the two CRT residues

    (3*5^(a-1),3*7^(b-1)),
    (3*5^(a-1),4*7^(b-1))

modulo5^a7^b. Their old period is625*2401=1500625. Direct enumeration of the literal old congruences gives

    |S5|=313, |S7|=1601, mixed deletion count=124800,
    old survivor count=376313,
    x=313/625, y=1601/2401,
    lambda0(1)=53759/214375.

For current11 exponent c=1,...,4 and color g=0,...,9 define

    q_c(g)=11^(c-1)-1+g*11^(c-1).

The four cylinders q_c(g) modulo11^c form a comb of Haar mass

    beta=1464/14641.

Different colors give disjoint combs. Each of the following25 rows specifies two fixed slots (r5,r7,g). For every row, slot and c=1,...,4 include the original with those CRT components modulo5^a7^b11^c. An exponent zero imposes no condition on that coordinate.

| (a,b) | Slot0: (r5,r7,g) | Slot1: (r5,r7,g) |
| --- | --- | --- |
| (0,0) | (0,0,6) | (0,0,3) |
| (0,1) | (0,5,1) | (0,5,5) |
| (0,2) | (0,47,4) | (0,33,4) |
| (0,3) | (0,166,4) | (0,19,4) |
| (0,4) | (0,635,7) | (0,215,4) |
| (1,0) | (4,0,2) | (4,0,8) |
| (1,1) | (4,3,4) | (4,3,1) |
| (1,2) | (3,19,7) | (4,31,5) |
| (1,3) | (4,235,1) | (3,145,7) |
| (1,4) | (3,306,0) | (4,637,4) |
| (2,0) | (4,0,0) | (24,0,7) |
| (2,1) | (19,3,7) | (9,5,0) |
| (2,2) | (19,26,4) | (15,47,0) |
| (2,3) | (19,94,5) | (9,81,1) |
| (2,4) | (18,768,7) | (19,1825,7) |
| (3,0) | (24,0,0) | (79,0,7) |
| (3,1) | (34,3,0) | (9,3,0) |
| (3,2) | (124,21,4) | (99,42,5) |
| (3,3) | (43,313,8) | (94,73,5) |
| (3,4) | (95,565,2) | (104,511,5) |
| (4,0) | (249,0,0) | (224,0,0) |
| (4,1) | (299,5,0) | (279,4,5) |
| (4,2) | (129,18,5) | (198,19,2) |
| (4,3) | (84,304,5) | (265,341,8) |
| (4,4) | (53,187,8) | (59,1123,5) |

This gives200 actual first11 originals, exactly two at each of100 numerical labels. None uses color9. All old projections and all current phases are fixed jointly; no pointwise optimization is used.

## 4. The finite query and exact first11 response

For exponents a,b=1,...,4 put

    T5=(4,14,14,14), D5=(3,3,3,3),
    T7=(5,19,19,19), D7=(6,6,6,6).

Use one query cylinder at each nonunit label5^a7^b11^c, 0<=a,b,c<=4. At c=0, pure5 queries use T5, pure7 queries use D7, and mixed queries use D5,D7. At c>=1 the11-phase is9 modulo11^c; pure5 cofactors use T5, pure7 cofactors use D7, and positive mixed5/7 cofactors use D5,T7. This is one fixed124-cylinder finite query, with the unit added once.

At an old point let t5,d5,t7,d7 count the matching depth1,...,4 query cylinders just defined; these lower-case counts are local to this paragraph and are not the NC4 pure deficits. Write

    L0=1+t5+d7+d5*d7,
    M=1+t5+d7+d5*t7,
    L=L0+M*sum_(c=1)^4 1_(z11=9 modulo11^c).

Let K be the number of distinct active original colors at the old point. Then the actual first11 allowed fraction and capped density are

    g_K=1-K*beta,
    h_K=min(5/3,1/g_K),
    s_K=h_K*g_K.

The old survivor counts at each K are

| K | Old residue count |
| --- | ---: |
| 2 | 111704 |
| 4 | 106709 |
| 5 | 55852 |
| 6 | 38052 |
| 7 | 44578 |
| 8 | 17316 |
| 9 | 2102 |

Aggregation by the color mask and four query counts gives186 profiles. At each profile, the verifier enumerates every one of the14641 eleven-words. It independently compares the literal hinge sum to the identity

    integral(L-2)_+*1_allowed dH11
       =(L0-2)_+*g_K+M*beta-1_(L0=1)/11.

The identity holds because the whole color9 root, and hence every query9 prefix, survives every original. It is not a claim that the original and query combs have the same nested structure.

The exact masses and PA saving are

    F11=4159811/36015000,
    lambda11(1)=1272755929/5991995625,
    Delta11=45972376/1198399125,
    S11=20023321/143807895000.

The finite query hinge and next comparison hinge are

    H*=integral(L-2)_+ d lambda11
      =112300666826237333/616568590178165625,
    F13=93139019/475398000,
    F13-H*=407818078583196991/29595292328551950000.

Consequently

    S11+(F13-H*)/4
      =141433689662930477/39460389771402600000
      =0.003584193934278599...,

whereas kreq=0.003738404947478915... . The exact failure is

    kreq-[S11+(F13-H*)/4]
      =319301851933315644672522473
         /2070551546915463116202297600000>0.             (C1)

Any complete query extending this finite query has at least its hinge. In particular H*<=sup_L integral(L-2)_+ d lambda11. Subtracting the supremum can only decrease the score in C1. Hence C1 refutes the simplified UNIFORM saving criterion, not just its application to an unfortunate choice of query.

## 5. What the old-prefix credit repairs, and a separate full-query repair

For this exact old source the pure and mixed deficits are

    d5=1/1250, d7=1/7203,
    1/12-m=121/720300.

Convert the NC4 pure credit to mass-saving units and include the actual mixed deficit:

    credit=(A5*d5+A7*d7+A57*d5*d7)/(T-2)+(1/12-m)
      =18036721551129456405721/27793832042657713032000000.

Then

    credit+S11+(F13-H*)/4-kreq
      =33476345951531543898470383
         /67665083232531474385696000000>0.               (C2)

Equation C2 repairs THIS FINITE QUERY score. It does not upper-bound the complete-query supremum, so by itself it does not establish the all-query criterion after credit.

A separate actual completion does establish the full PA bound for a concrete family. For each of the124 query cylinders at old numerical label d, add one actual original at numerical modulus13d with the same old phase and current13-phase0. Do not add17 or19 originals. The total family now has372 originals at248 numerical labels and still obeys the two-copy rule.

At every actual pre13 point, the forbidden13 fibre is either empty or the root0 modulo13. Its allowed mass is respectively1 or12/13, so the capped PA density with cap3/2 has fibre mass one. The actual13 loss is zero. The17 and19 losses are also zero. Thus

    lambda_final(1)=lambda11(1).

Retain the SAME full geometric final hinge Phi from PA2--PA4 and this exact final mass. Direct exact evaluation gives

    (T-2)*lambda_final(1)-Phi
      =61419637658642798267/190913010845356800000>0,
    R_Q<=2+Phi/lambda_final(1)
       =47643057811780066071/13517236531508602880<T.       (C3)

This is a complete-query conclusion: the PA hinge applies to every finite query and its full labelwise exhaustion, not only to the124 query that supplied the counterexample. C3 uses actual later-row losses and the full comparison numerator. It does not infer a supremum bound from C2.

## Verification and scope

The [standalone verifier](../../frontier/cover-geometry/first11_inventory_counterexample.py) and [exact data](../../frontier/cover-geometry/first11_inventory_counterexample.json) expand the fixed table into all200 actual first11 CRT originals, all48 old originals, the124 query cylinders and the124 optional actual row13 originals. They check every CRT component, normalized residue and full-label multiplicity; enumerate the actual old survivor and each11-word in all186 profiles; compare the direct and analytic hinge formulas; reconstruct PA/NC4 from complete geometric auxiliary laws; and verify the actual inventory bounds, fixed-family repair and general root11 scarcity constants.

All94 named checks pass with Python optimizations enabled. The data SHA256 is `6c52b898d9f97e440bbfad050d0a433e1569a961eaa5a0f2b5c49cdf03801d17`. Checks use explicit failures rather than removable Python assertions. The default output path is beside the program, and no old producer or external package is imported.

A separately written verification scans the3026 individual5/7 coordinate
values, combines1330 signature pairs and reconstructs all186 profiles.
It evaluates the11-response from five nested query bins, independently
of the retained verifier's word enumeration, and reproduces the stated
counterexample and repair constants. A copied script at a path containing
spaces, executed from another working directory, produces identical JSON
bytes on the tested macOS host. Other operating systems were not tested.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/first11_inventory_counterexample.py
```

The general inequalities I4--I8 are established by the displayed source-preserving arguments, not inferred from the finite enumeration. The counterexample is outside report554's prescribed old-slot projections and does not contradict that result. It refutes one proposed simplified PA saving criterion for unrestricted first11 old projections; it does not refute full NC4, all supported-law methods, or the surviving Erdős #7 problem. The actual-pure-union form in I5 also records the benefit of pure-cylinder overlap without requiring additional absent slots.
