[Index](../../marked_head_profile.md) · [Actual source](339-irredundant-source-seven-labels-bound-the-actual-surplus.md)

# 339f. A fixed plain source at arbitrary test heights

The [plain-source Schur certificate](339d-the-complete-plain-source-square-at-every-height.md) compares the actual F_N source with complete tests at the same height N. Here the source is held fixed while the complete test inventory is enlarged. This distinction is needed when later original moduli use higher powers of an earlier prime.

## Fixed source, enlarged test rectangle

Fix N>=12. Retain exactly the N²+5N original classes of the actual family F_N from[339](339-irredundant-source-seven-labels-bound-the-actual-surplus.md):

| Original modulus | Actual CRT residues |
|---|---|
|3^a|2 at a=1;6 at a=2;3^(a−1) at a>=3|
|5^b|5^(b−1)|
|3^a5^b|three residue1 at a=1,2, and7+3^(a−1) at a>=3; five residue2·5^(b−1) at a=1 and3·5^(b−1) otherwise|
|7^e|6 at e=1;1+7^(e−1) at e>=2|
|3·7^e|three residue0; seven residue1 at e=1 and2+7^(e−1) otherwise|
|9·7^e|three residue3; seven residue2 at e=1 and3·7^(e−1) otherwise|

Every indicated positive exponent ranges through N. No further original class is added. Let R_N be the source survivor set in Z/105^N Z. Choose arbitrary finite integers A,B,E>=N and put

    Q=3^A5^B7^E,
    m=1_{x mod105^N in R_N} Haar_Q,
    Z=m(1)>0, nu=m/Z.                                  (FH1)

Thus the additional digits are Haar extensions of the same source. The complete auxiliary test domain contains one chosen residue at every numerical divisor3^a5^b7^e,0<=a<=A,0<=b<=B,0<=e<=E. Its unit occurs exactly once. Write

    L_c(x)=sum_(d|Q)1_{x=c mod d},
    Gamma_Q(m)=max_layout integral L² dm.

**Theorem.** For this fixed source and every such rectangle,

    Gamma_Q(m)=integral L_4² dm.                       (FH2)

Moreover every maximizing raw layout is coherent at a center c satisfying

    c=4 mod9, c=4 mod5, c mod7 in{3,4,5}.              (FH3)

Every higher digit is unrestricted, and every center in(FH3) supplies a maximizer. This is an ordinary mathematical consequence of the existing infinite-index Schur bound and the explicit correction below. It concerns the plain F_N law; it is not a uniform theorem for all near-J sources or for a source multiplied by a later deletion mask.

## Actual lifted coefficients and compression

Hold the source parameters fixed:

    t=(1−3^(2−N))/18, q=(1−5^(−N))/4,
    u=(5+7^(−N))/6.

For rows j=(0,3,1,4,7) modulo9 define

    eta=(1/9−t,1/9,1/9,1/9,1/9),
    n=((1−q)(1/9−t),(1−q)/9,(1−3q)/9,
       (1−2q)/9,(1−2q)/9−tq),
    g=(u−1/7,u−2/7,u,u,u), Z=sum_j n_j g_j.           (FH4)

These are source quantities. In particular q is not replaced by the longer test-stack sum through B, and u is not replaced by a source with E original seven classes.

For a canonical cylinder of test depths(a,b,e), project each depth to its minimum with N, use the actual source-cylinder mass at that projection, and multiply by

    3^(-(a−N)_+)5^(-(b−N)_+)7^(-(e−N)_+).              (FH5)

This is exactly Haar extension. Consequently the centered and root0 upper moments of339d remain valid for every test depth:

    d(a,b,e)=3^-a5^-b7^-e,

    p(1,b,e)=5^-b7^-e sum_(j in{1,4,7})
                         (b=0?n_j:eta_j)(e=0?g_j:1),
    ucap(1,b,e)=5^-b7^-e sum_(j in{0,3})
                         (b=0?n_j:eta_j)(e=0?g_j:1).

For a>=2,

    p(a,b,e)=d(a,b,e)(b=0?1−2q:1)(e=0?u:1),
    ucap(a,b,e)=d(a,b,e)(b=0?1−q:1)
                    (e>0?1:(a=2?u−2/7:u−1/7)).       (FH6)

The same simultaneous compression is pairwise monotone on the enlarged inventory. First move every positive7 test to its nested4 path: an original intersection is empty or a prefix of maximum depth, its allowed width is at most its Haar width, and root4 has no seven-original exclusion. Pairs with zero7 exponents are unchanged. Next do the same for positive5 tests; root4 misses every pure5 and mixed35 exclusion.

Keep the two root0 mod9 rows separate. At deeper ternary depths, map row0 prefixes to18 and row3 prefixes to3. Map root1 prefixes to4. These paths have full pure3-surviving width. At zero5 depth, row4's remaining five density dominates rows1 and7; the root0 rows have no mixed35 exclusions. The seven mask is constant within each mod9 row and identical throughout root1. At positive5/7 depths the clean widths are exact. Compatible pairs remain ancestor-compatible, while originally incompatible pairs had zero mass. Thus every ordered-pair integral can only increase.

The argument holds beyond N because no added source exclusion cuts the clean subtrees. It leaves two choices at ternary depth1, three at depth2, and three deeper choices18,3,4. It does not move an original forbidden class or merge numerical test labels. At maximum depth2 row3 gives the root0 envelope in(FH6); at deeper maxima path18 gives it. Their distinct pair maxima are only upper bounds, not jointly attained choices.

## The actual rectangular H coefficients

Let I contain every test index with a>=1. Let P_i be its centered indicator, Y the full zero-three test load, and L_*=Y+sum_iP_i. Put

    K_ij=p(i vee j)+ucap(i vee j),
    H_i=integral L_*P_i dm
                   −sum_(j:a_j=0)ucap(i vee j).       (FH7)

The componentwise maximum is denoted by vee. All sums are over the complete A-by-B-by-E rectangle, including its unit. For a compressed competitor, let x_i indicate replacement of its centered choice by a root0 choice. The exact same-source expansion in339d gives

    integral(L²−L_*²)dm <= x^T Kx−2sum_iH_i x_i.       (FH8)

The diagonal of K is present. To compare H with the existing infinite kernel, define

    r5=sum_(j=1..B)5^-j−q >=0,
    r7=sum_(j=1..E)7^-j−(1−u) >=0,
    h3=a+1+sum_(j=1..A−a)3^-j,
    h5=b+1+sum_(j=1..B−b)5^-j,
    h7=e+1+sum_(j=1..E−e)7^-j.                        (FH9)

These are test-stack quantities; t,q,u still belong to the fixed source.

### The four cases with a>=2

Set gamma=1 when e>0, gamma=5/7 when a=2,e=0, and gamma=6/7 when a>=3,e=0. Define

    Hbase_i/d_i=
       [b=0?(1−q)h3−gamma:h5(h3−gamma)]
       ·[e=0?1:h7].                                  (FH10)

The exact correction is

| Target flags |(H_i−Hbase_i)/d_i|
|---|---|
|b=0,e=0|r5(h3−gamma)+r7((1−q)h3−1)+r5r7(h3−1)|
|b>0,e=0|h5(h3−1)r7|
|b=0,e>0|h7(h3−1)r5|
|b>0,e>0|0|

For example the first actual row is

    H_i/d_i=h3(1−q+r5)(1+r7)−(1+r5)(gamma+r7),

which expands into(FH10) and the first correction. All four corrections are nonnegative: h3>=3,1−q>=3/4 and gamma<=1.

### The four cases with a=1

Put

    T3=sum_(j=2..A)3^-j,
    U=2/9−t,
    R=(3−4q)/9−tq,
    R0=11/63−6t/7.

Here R is the raw root1 source mass plus q/3; the added term already accounts for the baseline positive-five stack. Set

    Hbase_i/d_i=
       3[2(b=0?R:1/3)−(e=0?R0:U)
                       +T3(b=0?1−q:1)]
       ·[b=0?1:h5]·[e=0?1:h7].                       (FH11)

The exact correction is

| Target flags |(H_i−Hbase_i)/d_i|
|---|---|
|b=0,e=0|3[r5(2/3+T3−R0)+r7(2R+T3(1−q)−U)+r5r7(2/3+T3−U)]|
|b>0,e=0|3h5r7(2/3+T3−U)|
|b=0,e>0|3h7r5(2/3+T3−U)|
|b>0,e>0|0|

These follow by summing the two shallow ternary partner exponents and the entire deep stack T3. Each correction is nonnegative, using R>=5/24,U<=2/9,R0<=11/63 and T3>=0. Therefore

    H_i>=Hbase_i>0.                                   (FH12)

## Reusing the infinite-index Schur certificate

The reusable statement of339d is quantified over every target a>=1,b,e>=0 and every fixed source triple in

    [t12,1/18] × [q12,1/4] × [5/6,u12].               (FH13)

With its positive weights w_i and lower coefficient hlow_i, it proves

    sum_(all secondary indices j) K_ij w_j
                    <=(49/25)d_i hlow_i w_i.          (FH14)

The secondary sum is infinite and nonnegative. This is the mathematical statement established by339d's finite source-box and exponent-tail reduction, not merely its N12 grid evaluation. The fixed(t,q,u) lies in(FH13), and the enlarged finite rectangle is a subsum of(FH14).

Every test height is at least12. Hence each h3,h5,h7 dominates the corresponding lower stack used in339d, T3 dominates its depth12 deep stack, and the same source-box bounds apply. In particular(FH10)--(FH11) give

    Hbase_i>=d_i hlow_i.

Together with the nonnegative corrections,

    (K_rectangle w)_i
       <=(K_infinite w)_i
       <=(49/25)Hbase_i w_i
       <=(49/25)H_i w_i.                              (FH15)

For symmetric nonnegative K and positive w, the elementary weighted square inequality gives

    x^T Kx<=sum_i[(Kw)_i/w_i]x_i².

Since each x_i is0 or1, applying(FH15) in(FH8) yields

    integral(L²−L_*²)dm<=−(1/25)sum_iH_i x_i.          (FH16)

Every nonempty change loses strictly. Thus L_* uniquely maximizes the compressed class, and pairwise-monotone compression proves(FH2) over all original auxiliary layouts. This proof does not identify arbitrary killed measures with the unmodified source.

## Why every raw maximizer is coherent

The following finite observation makes the full optimizer family explicit. Suppose pairwise-monotone compression of a Haar restriction has a unique compressed coherent optimum. Apply compression to a raw maximizing layout. Its nonnegative ordered-pair increments sum to zero, so every increment is zero.

The top label Q is a singleton{c}. Its diagonal must equal the centered diagonal1/Q, so c survives. For each d|Q, the centered ordered pair(Q,d) has mass1/Q. Equality before compression therefore implies c belongs to the original d-test cylinder. Hence every chosen residue is c mod d: the entire raw layout is coherent.

In the present source, the pure9 diagonal has its unique maximum at row4, as in339b. Equality of this diagonal forces c=4 mod9. The pure5 diagonal is maximized only at root4: root1 is pure5-forbidden; root0 loses a positive pure25 cylinder; root2 loses a positive3·5 cylinder; root3 loses a positive9·5 cylinder. Each loss has a positive surviving carrier in the other coordinates, whereas root4 is clean.

For7, exactly roots3,4,5 are globally clean. Root6 is pure7-forbidden; root1 loses a pure49 or3·7 cylinder; root2 loses9·7; root0 loses a positive9·49 cylinder. The diagonal equalities therefore force(FH3). Haar extension preserves all these strict comparisons.

Conversely every center in(FH3) has exactly the canonical masses(FH6): all deeper ternary cylinders lie in the clean row4 subtree, and every positive5/7 cylinder lies in a globally clean root. Higher digits do not affect source membership. Every ordered coherent pair then has its canonical mass, proving attainment. The raw optimum is consequently a family of coherent layouts, not a unique residue assignment.

## Exact rectangular value and fixed-source supremum

Define test sums separately from the fixed source parameters:

    J3(A)=sum_(a=0..A)(2a+1)3^-a,
    J5(B)=sum_(b=0..B)(2b+1)5^-b,
    J7(E)=sum_(e=0..E)(2e+1)7^-e,
    V5=J5(B)−1, V7=J7(E)−1,
    R_j=(n_j+V5 eta_j)(g_j+V7).

Then the exact normalized maximum is

    Gamma_Q(nu)=
       [sum_jR_j+3(R_1+R_4+R_7)
        +(J3(A)−2)(1−2q+V5)(u+V7)]/Z.               (FH17)

The subscripts of R are literal mod9 rows. Exactly(2a+1)(2b+1)(2e+1) ordered centered pairs have maximum exponents(a,b,e). Summing their actual lifted masses proves(FH17), retaining the unit and every ordered cross term.

Increasing only A,B,E adds nonnegative test indicators. Their exact geometric sums converge toJ_p(infinity)=p(p+1)/(p−1)². With source parameters fixed at F12, this gives

    sup_(A,B,E>=12) Gamma_Q(m)
       =39102661327827027195665233/8620110364906219921875000,

    sup_(A,B,E>=12) Gamma_Q(nu)
       =195513306639135135978326165/7696556594173900372773312
       =25.40269849859011....                         (FH18)

This supremum varies only finite test heights. It is different from1829/72, the limit where the actual source originals and test inventory both grow with N. It does not identify an infinite carrier with one finite optimizer.

## Exact verification and boundary

The[fixed-height checker](../../frontier/source-budgets/source_fixed_height.py) verifies Haar projection(FH5), compares every lifted p/ucap coefficient with the fixed-parameter formulas, directly sums complete rectangular H rows, and checks(FH17)--(FH18) in exact fractions:

| Fixed source N | Test heights(A,B,E) | Complete labels | Lifted moment checks | Complete H rows |
|---|---|---:|---:|---:|
|12|(12,13,14)|2730|5040|36|
|12|(14,12,13)|2730|5096|54|
|13|(15,14,13)|3360|6300|54|

The checked rows include test depths beyond the fixed source height. Each row retains its entire rectangular partner inventory and all zero-three terms. The universal quantifiers follow from(FH5)--(FH16), while the finite arithmetic independently checks their interfaces. The inherited source-box and infinite-index Schur obligations remain those of339d.

This result supplies all old test heights for one fixed plain source family. It does not supply compression after a mixed deletion mask, the analogous weighted fixed-source extension, a uniform bound on all sources sharing coarse guards, or an unrestricted later-prime continuation. Those require separate same-source inequalities.

The [retained exact certificate](../../certificates/source_norms/source-budgets/source_fixed_height.json)
records every checked H row and the complete rectangular values. From the
repository root:

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_fixed_height.py --check
```
