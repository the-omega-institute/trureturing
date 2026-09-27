# 339d. The complete plain-source square at every height N≥12

This continues the [actual-source and complete F12 results](339b-the-actual-near-j-source-and-the-unit-refund.md) for the source family constructed in [report339](339-irredundant-source-seven-labels-bound-the-actual-surplus.md).

## Scope and theorem

Fix an integer N≥12 and the actual irredundant source F_N of report339, with period Q_N=105^N and all original exclusions through N. In CRT coordinates these are:

- Pure3^a: residue2 at a1,6 at a2, and3^(a−1) at a≥3.
- Pure5^b: residue5^(b−1).
- Mixed3^a5^b: ternary residue1 for a1,2 and7+3^(a−1) for a≥3; five residue2·5^(b−1) for a1 and3·5^(b−1) otherwise.
- Pure7^e: residue6 at e1 and1+7^(e−1) otherwise.
- 3·7^e: ternary residue0; seven residue1 at e1 and2+7^(e−1) otherwise.
- 9·7^e: ternary residue3; seven residue2 at e1 and3·7^(e−1) otherwise.

Each index ranges from1 throughN, and every numerical original modulus is retained. Let R_N be the surviving CRT set, m_N=1_{R_N}H_N the raw restriction of normalized Haar probability, Z_N=m_N(1)>0, and ν_N=m_N/Z_N. Positivity follows, for example, from the surviving point(4,4,4).

A complete auxiliary layout has one chosen residue for each numerical divisor3^a5^b7^e with0≤a,b,e≤N. Its load is the sum of the corresponding indicators, with the unit included exactly once. Define Γ_{Q_N}(ν_N)=max_L ∫L²dν_N.

**Theorem.** For every integer N≥12, the complete common-center layout L_* whose every auxiliary residue is4 modulo its numerical modulus attains Γ_{Q_N}(ν_N). Within the published compressed ternary class, it is the unique maximizing layout. The full common-vertex, pair-marginal LP over that compressed class also has the unique integral common-center optimum.

The proof below is an ordinary exact mathematical certificate. It uses report339's simultaneous source-preserving compression and actual-cylinder coefficient formula. It is not a new Lean theorem, a statement about arbitrary sources, a weighted-source theorem, or a resolution of unrestricted Erdős #7. The original-source exclusions are never moved.

## Actual-source coefficients and the comparison kernel

Put

    t=(1−3^(2−N))/18,   q=(1−5^(−N))/4,   u=(5+7^(−N))/6.

Index rows in the order(0,3,1,4,7) modulo9. Their raw35 and pure3 masses are

    η=(1/9−t,1/9,1/9,1/9,1/9),
    n=((1−q)(1/9−t),(1−q)/9,(1−3q)/9,
       (1−2q)/9,(1−2q)/9−tq),
    g=(u−1/7,u−2/7,u,u,u),    Z=Σ_j n_j g_j.

The published compression simultaneously moves every positive5 and7 test to its clean nested4 path. It then retains two choices at ternary depth1(roots0/1), three at depth2(rows0/3/4), and three at larger depth(paths18/3/4). It increases every ordered-pair integral. Thus it suffices to optimize this compressed class. Every noncentered surviving choice is in ternary root0, while the centered choice is in root1.

For a≥1 and b,e≥0 let d(a,b,e)=3^(−a)5^(−b)7^(−e). Define the centered moment p(a,b,e) and a root0 upper moment ucap(a,b,e) as follows. At a1,

    p(1,b,e)=5^(−b)7^(−e) Σ_{j∈{1,4,7}}
                (b=0 ? n_j : η_j)(e=0 ? g_j :1),
    ucap(1,b,e)=5^(−b)7^(−e) Σ_{j∈{0,3}}
                (b=0 ? n_j : η_j)(e=0 ? g_j :1).

At a≥2,

    p(a,b,e)=d(a,b,e)(b=0 ?1−2q:1)(e=0 ?u:1),
    ucap(a,b,e)=d(a,b,e)(b=0 ?1−q:1)
                     (e>0 ?1:(a=2 ?u−2/7:u−1/7)).

Thus the upper choice is row3 at maximum depth2 and path18 at maximum depth≥3. Row3 dominates row0 at depth2 on the source box below; at deeper depth the two bad paths share their five factor and g0≥g3. At maximum depth1, the whole root0 is the actual bad cylinder. Incompatible actual intersections are zero. These coefficients bound every actual bad/bad intersection, but their separate maxima are not claimed jointly attainable.

Let I={(a,b,e):1≤a≤N,0≤b,e≤N}. Write i∨j for componentwise maximum. Let P_i be the actual centered indicator, and let

    Y=Σ_{0≤b,e≤N} I_{(0,b,e)},    L_*=Y+Σ_{i∈I}P_i,
    p_ij=p(i∨j)=∫P_iP_jdm,
    u_ij=ucap(i∨j),
    H_i=∫L_*P_i dm−Σ_{j:a_j=0}u_ij,
    K_ij=p_ij+u_ij,       i,j∈I.

The diagonal of K is present. The finite sums defining H retain every a0 label and all its cross terms, including the unit.

For a competing compressed layout, let x_i indicate which labels move to root0, and let A_i be that label's actual root0 indicator. Put V=Σx_iA_i and W=Σx_iP_i. Since V and W have disjoint supports and L_*=Y on root0,

    ∫(L²−L_*²)dm=∫(2YV+V²−2L_*W+W²)dm
                 ≤xᵀKx−2Σ_i H_ix_i.                 (A)

This charges the removal of exactly the same labels whose positive contributions are bounded. No sum of separately optimal pair values is identified with Γ.

## Exact loss coefficients and uniform positive lower bounds

Let

    h_{p,N}(k)=k+1+Σ_{j=1}^{N−k}p^(−j).

For a≥2 set γ=5/7 if a2,e0, γ=6/7 if a≥3,e0, and γ=1 if e>0. Summing the complete finite stacks gives

    H_(a,b,e)/d(a,b,e)
      =[ b=0 ? (1−q)h_{3,N}(a)−γ
               :h_{5,N}(b)(h_{3,N}(a)−γ) ]
       ×[ e=0 ?1:h_{7,N}(e) ].                       (B)

For a1 put T_N=Σ_{j=2}^N3^(−j),

    R1=(b=0 ? (3−4q)/9−tq :1/3),
    R0=(e=0 ?11/63−6t/7 :2/9−t).

Then

    H_(1,b,e)/d(1,b,e)
      =3[2R1−R0+T_N(b=0 ?1−q:1)]
        ×[b=0 ?1:h_{5,N}(b)]
        ×[e=0 ?1:h_{7,N}(e)].                        (C)

These are actual same-source identities. Among their cancellations are

    u+Σ_{j=1}^N7^(−j)=1,
    (u−1/7)+Σ7^(−j)=6/7,
    (u−2/7)+Σ7^(−j)=5/7,
    (1−2q)+Σ_{j=1}^N5^(−j)=1−q,
    (1−q)+Σ_{j=1}^N5^(−j)=1.

Define v_p(k)=k+1+Σ_{j=1}^{max(0,12−k)}p^(−j). For every actual k≤N with N≥12, h_{p,N}(k)≥v_p(k). Define h(a,b,e) from(B) by replacing h_{p,N} with v_p and1−q with3/4. At a1 use the same v5,v7 multipliers and replace the leading factor in(C) by

| flags | leading factor |
|---|---:|
| b0,e0 |881515/708588|
| b0,e>0 |797159/708588|
| b>0,e0 |375382/177147|
| b>0,e>0 |354293/177147|

For(C), first use T_N≥T_12, whose coefficient is positive, then minimize the separately affine expression over the four(t,q) corners below. This gives exactly the four displayed constants. In all cases

    H_i≥d_i h(i)>0.                                  (D)

The uniform source box is

    [t_12,1/18]×[q_12,1/4]×[5/6,u_12].               (E)

It contains every actual source triple N≥12. All p/ucap coefficients are separately affine in t,q,u, including any mixed products. Checking an inequality at its eight vertices therefore checks it on the entire box. The box is a coefficient comparison; it does not replace an actual source law by a vertex law.

## Twelve explicit weights and an executable geometric formula

Let λ=11/10 and σ=101/100. The constants c(a,b,e), by class, are

|flags|a1|a2|a≥3|
|---|---:|---:|---:|
|b0,e0|20|27|30|
|b0,e>0|33|50|47|
|b>0,e0|14|20|22|
|b>0,e>0|21|34|33|

Set w_(a,b,e)=c(a,b,e)λ^aσ^(b+e)>0. For the comparison only, extend the nonnegative coefficient kernel K to secondary indices a′≥1,b′,e′≥0 with t,q,u fixed. This extends the upper sum, not the actual layout or the original source.

The following formula evaluates

    G(a,b,e;t,q,u)=
      [Σ_{a′≥1,b′,e′≥0} K_((a,b,e),(a′,b′,e′))w_(a′,b′,e′)]
       /[d(a,b,e)λ^aσ^(b+e)].                        (F)

For any secondary class C define

    Φ(p,r;k,C)=Σ_{j∈C} p^(k−max(k,j))r^(j−k).

For a singleton j this is its one displayed monomial. For the tail C={j≥m},

    Φ(p,r;k,j≥m)
       =r^(−k)Σ_{j=m}^k r^j+r/(p−r),                 k≥m,
       =p^k r^(−k)(r/p)^m/(1−r/p),                   k<m.   (G)

The finite geometric sum is(r^m−r^(k+1))/(1−r). All sums converge because1<λ<3 and1<σ<5,7.

Write κ(A,β,ε) for(p+ucap)/d at ternary class A∈{1,2,3} and positive flags β,ε. It is obtained explicitly from the moments above: multiply their a1 formulas by3, use the a2 formulas when A2, and the deep formula when A3. Thus the required twelve-term formula is

    G=Σ_{A′∈{1,2,≥3}, B′∈{0,≥1}, E′∈{0,≥1}}
        c(A′,B′,E′)
        κ(max(min(a,3),class(A′)), b>0 or B′≥1, e>0 or E′≥1)
        Φ(3,λ;a,A′)Φ(5,σ;b,B′)Φ(7,σ;e,E′).           (H)

Here class(≥3)=3. The c-value uses the same class/flag table. Formula(H), including all endpoint and zero cases, is implemented using exact fractions in `source_plain_schur.py`.

## Why finite exact checks cover every exponent

It is enough to prove

    G(a,b,e;t,q,u)≤(49/25)c(a,b,e)h(a,b,e)             (I)

on(E) for all a≥1,b,e≥0. This implies the finite actual row bound

    (Kw)_i≤(49/25)H_iw_i.                             (J)

For1≤a≤12 and0≤b,e≤12, the8 source vertices give16224 exact rational checks. Every check passes. The exact maximum of G/(2ch) is

    14980406372658004079678077933975956045126998016
    /15350952520756367392769130825192909307865234375
    =0.975861683657913764... <49/50,

at(a,b,e)=(3,0,12) and(t,q,u)=(t12,q12,5/6).

On any positive/deep target-coordinate class, formula(G) makes G=A+C r^(−k) with the other coordinates fixed. Here r is λ or σ, and A≥0 because it is the limit of a nonnegative comparison sum. For k≥12, the relevant factor of h is positive times(k+s). For the b,e coordinates s=1. For the a coordinate,

    γ=(e=0 ?6/7:1),   d=(b=0 ?3/4:1),   s=1−γ/d.    (K)

In particular s=−1/7 for b=e=0 and s=−1/3 for b0,e>0. This is division by d, obtained by factoring d(a+1)−γ; multiplication would give the wrong denominator.

The forward-difference numerator of G(k)/(k+s) is

    (k+s+1)G(k)−(k+s)G(k+1)
       =A+C r^(−k)[1+(k+s)(1−r^(−1))].               (L)

For k≥12, k+s>0. The exponential bracket in(L) is positive and strictly decreases with k. If C≥0 the numerator is nonnegative because A≥0. If C<0 its least value occurs at k12. Thus one endpoint first-difference test establishes monotonicity throughout the tail.

For these endpoint tests, the dependence on each other positive/deep coordinate is separately affine in its inverse power. It is enough to use a∈{1,2,3,∞}, b,e∈{0,1,∞}. These are actual small indices or limits of the coefficient formula, not an infinite source height or invented labels. At infinity each fixed-j Φ tends to zero and each tail Φ tends to r/(r−1)+r/(p−r).

There are72 a-tail checks(3·3·8),96 b-tail checks(4·3·8), and96 e-tail checks(4·3·8):264 in total. All pass strictly. Their least raw difference is

    24166047412258860810455648580882485
    /516810321021989547903667836685719 >0.

Consequently any coordinate larger than12 can be lowered to12 without decreasing G/h. Apply this successively to all large coordinates, then use the finite grid. This proves(I) on the whole infinite target-index range and the entire containing source box. Each actual source uses only its finite labels, so(J) holds for every N≥12.

The same exact verifier also checks the64 cap comparisons(depth2 and deep,4 flags,8 vertices) and the four depth1 corner minima used in(D).

## Strict Schur comparison and the original maximum

For positive w and any real z, the elementary square inequality gives

    2z_iz_j≤(w_j/w_i)z_i²+(w_i/w_j)z_j².

Since K is symmetric and nonnegative, including its diagonal,

    zᵀKz≤Σ_i[(Kw)_i/w_i]z_i².

Use(J), x_i²=x_i, and(A):

    ∫(L²−L_*²)dm≤−(1/25)Σ_iH_ix_i.                  (M)

By(D), every nonempty change loses a strictly positive amount. This proves uniqueness inside the compressed class. The published simultaneous compression maps every original complete layout into that class without decreasing its objective, so the centered layout is a global maximizer over all original auxiliary residues. This does not assert uniqueness before compression: different original residues may agree on the surviving support.

More explicitly, with δ_i=2H_i−(Kw)_i/w_i≥H_i/25,

    2Σ_iH_ix_i−xᵀKx
      =Σ_iδ_ix_i
       +Σ_{i<j}K_ij[(w_j/w_i)x_i+(w_i/w_j)x_j−2x_ix_j].  (N)

Every term is nonnegative. Formula(N) is a joint certificate that charges shared choices of labels.

For feasible categorical site and pair marginals, let x̄_i be the probability of root0 and x̄_ij the probability that both labels choose root0; put x̄_ii=x̄_i. Pair consistency suffices to average the elementary binary inequality at each edge. The same comparison gives

    F_LP−F(L_*)≤−(1/25)Σ_iH_ix̄_i.                    (O)

No global joint law over all labels is assumed. Every optimal LP solution therefore has x̄_i=0 for every i. Each label has just one compressed root1 option, so all site marginals and consequently all pair marginals are the unique centered integral ones.

## Closed value and limit

Define

    J_p(N)=Σ_{k=0}^N(2k+1)p^(−k),
    B=J_5(N)−1,   E=J_7(N)−1,
    R_j=(n_j+Bη_j)(g_j+E).

The theorem's exact value is

    Γ_{Q_N}(ν_N)
      =[Σ_jR_j+3(R_1+R_4+R_7)
         +(J_3(N)−2)(1−2q+B)(u+E)]/Z.                (P)

To derive it, exactly(2a+1)(2b+1)(2e+1) ordered centered pairs have maximum exponents(a,b,e). Summing the actual nested-cylinder moments gives the a0 contributionΣR_j; a1 contributes3 times the root1 rows; all a≥2 use the clean row4 coefficient and have total ternary multiplicity J3−2. This counts the unit once in the load and retains all its ordered cross terms.

At N12,

    Γ_{105^12}(ν_12)
      =2036574313467845778288943/80172464522644795549722
      =25.4024162234979474335....

At N24, formula(P) is

    1828716454870908884078061103973706637506656447162
    /71988838029841937181983634214065550432830039081.

Both values are independently equal, in exact fractions, to the complete ordered-pair maximum-exponent histogram from the independent actual-source API.

As N tends to infinity, (t,q,u) tends to(1/18,1/4,5/6) and

    J_p(N)→p(p+1)/(p−1)².

The denominator Z tends to5/28>0, so substitution in(P) yields

    lim_{N→∞}Γ_{Q_N}(ν_N)=1829/72.

This exact substitution is checked by `source_plain_schur.py`.

## Evidence and remaining boundaries

The [exact standard-library verifier](../../frontier/source-budgets/source_plain_schur.py) reconstructs4056 p/ucap entries at N12 from the existing actual-cylinder API, compares20 complete rows with the H identities and the infinite geometric upper sum, and checks all16224 grid inequalities. It also verifies64 root0 cap comparisons, four depth1 corner minima,264 strict tail endpoint inequalities, the exact centered values at N12 and N24, and the limit1829/72. Its complete standalone invocation is

    python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_plain_schur.py --check

The existing sharpness producer invokes the same verifier and retains the small exact result in `plain_uniform_source_square`. Validation uses explicit exceptions, so `-O` does not disable it. The source API is the same one audited against the literal original AP partitions by the complete-square checker in339b. Grid checks and finite source samples alone do not imply the uniform theorem: the exact formulas, source box and tail reduction above supply its unbounded quantifiers. The strict loss1/25 in(M) is relative to each actual H_i; it is not an N-independent absolute gap between distinct layouts.

The theorem preserves one particular family of actual source laws. It does not permit replacing a guarded or killed law by this law, does not supply a uniform bound for arbitrary original inventories, and does not address later primes. The displayed comparison kernel is too coarse to prove the analogous weighted all-height result. Its failure would be a failure of this sufficient comparison, not a weighted-layout counterexample. No claim about unrestricted Erdős #7 follows without additional source/process bridges.

The separate [uniform transport certificate](339e-uniform-transport-for-both-actual-source-squares.md) establishes both actual-layout maxima and compressed uniqueness for N>=4. The plain pair-LP conclusion for N>=12 above remains a further conclusion of this Schur certificate; it is not extended to weighted laws or smaller N by that transport proof.
