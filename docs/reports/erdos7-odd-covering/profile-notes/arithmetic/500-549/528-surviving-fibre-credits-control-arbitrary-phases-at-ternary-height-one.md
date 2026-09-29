# Surviving-fibre credits give common query laws at ternary height one

A [large-prime continuation](#eleven-small-support-primes-allow-an-unrestricted-large-prime-tail) permits arbitrarily many additional primes greater than100000: if at most eleven support primes are at most100000, only originals entirely on those small primes need v3(m)<=1. Every tail-touching original may have arbitrary finite exponents, including deeper powers of3. The complete family remains finite and noncovering.

Every finite family of pairwise distinct odd numerical moduli greater than1, with at most eleven actual support primes and v3(m)<=1 for every original, leaves integer survivor density greater than1/700. The [eleven-prime construction](#actual-pure-outside-conditioning-closes-the-eleven-prime-branch) below permits arbitrary original residues and arbitrary finite nonternary heights. It is an ordinary proof with exact rational checks, not new Lean verification.

Let P={3,5,7,11,13,17,19}. For every finite family of pairwise distinct odd numerical moduli greater than1 supported on P, with arbitrary original residues and v3(m)<=1, there is one probability mu on its actual survivor set such that

    R_P(mu)=sum_(d>1,P-smooth) max_a mu(a mod d)<39/4,
    mu<(10240/561)H_P<19H_P.                            (FC1)

The query sum includes every prime-power depth, although the original ternary depth is restricted. All original heights at5,7,11,13,17,19 are arbitrary. The same law serves every query. Adding any finite original family supported on P union{23,29} and touching23 or29, with arbitrary old and outside residues and arbitrary finite heights, leaves full Haar survivor mass greater than

    13821/2293760>3/500.                                (FC2)

The condition v3<=1 applies only to the P-only originals. In particular, later originals involving23 or29 may have unrestricted ternary depth. No claim that arbitrary P-only originals meet the condition is made, and unrestricted Erdős#7 remains unresolved.

These are ordinary mathematical deductions. The actual-family deletion inequality below retains which coordinates of a surviving fibre an original can still remove. The query step applies the standard ordered-increment comparison, in the form of Lemma4.1 of the [pinned Schroeder source](../../../../../../Library/Arith/schroeder2026nine.md), and the stop-loss interface of [report461](../450-499/461-query-stop-loss-gives-a-common-law-six-core-completion-margin.md). No source completion, geometry certificate or new Lean verification is used. The analytic fibre estimate and its combination with that query interface are the result here; no claim of literature priority is made.

## An actual-family inequality retaining arbitrary ternary prefixes

First allow arbitrary finite original ternary heights. Put Q=P minus{3}. Work on the product of the p-adic coordinates, with normalized Haar H_p; all original events depend on a finite CRT period. For each q in Q let S_q avoid all actual original pure q-power classes, and set

    lambda_q=H_q(. intersect S_q)/H_q(S_q),
    c_q=(q-1)/(q-2),    b_q=1/(q-2).

Distinct numerical labels and the finite union bound give

    H_q(S_q)>=1-sum_(e>=1)q^-e=(q-2)/(q-1),
    lambda_q(a mod q^e)<=c_q q^-e,
    sum_(e>=1)c_q q^-e=b_q.                            (FC3)

Choose any probability lambda_3 avoiding the actual pure3-power originals, and use the one product law lambda=lambda_3 tensor product_q lambda_q before mixed deletions. Such a lambda_3 exists, for example normalized Haar on the pure3-power avoid-set, whose Haar mass is at least1/2.

For an actual ternary point t let B_q(t) be the union of q-projections of all original moduli3^i q^e, i,e>=1, whose actual ternary condition is satisfied at t. Define

    beta_q(t)=lambda_q(B_q(t)),
    G_D(t)=product_(q in Q minus D)(1-beta_q(t)).

For a remaining original m, let D(m)={q in Q:q divides m}. Its ternary cylinder is I_m; set I_m to the whole ternary carrier when3 does not divide m. Retain its actual full residue in I_m and all other projections. Put

    w_m=product_(q in D(m)) c_q q^(-v_q(m)).

If U is the complete actual original survivor set, then

    lambda(U)>=integral G_empty d lambda_3
       -sum_(original m, |D(m)|>=2)
            w_m integral_(I_m) G_D(m) d lambda_3.       (FC4)

Indeed after avoiding the original classes on{3,q}, the surviving fibre over t has exactly the fraction G_empty(t) of the nonternary product carrier. A remaining original m still has to avoid B_q(t) on every coordinate q outside D(m). These unchanged coordinates contribute exactly G_D(m)(t). On coordinates in D(m), bound the original cylinders by(FC3), dropping any further beneficial avoidance. Summing the resulting deletion bounds inside this one surviving carrier proves(FC4).

The factor G_D(m) depends on the actual numerical support of m, and its integral is over m's own actual ternary prefix. Neither may be replaced by a separately optimized scalar. Equation(FC4) itself has no bound on the original ternary height.

## The two-root budget when v3(m)<=1

Now impose v3(m)<=1 on every old-only original. If modulus3 is missing, append one class at that unused numerical label. Prove the bound for the enlarged family; its survivors also avoid the given family. If modulus3 is present, keep its actual residue. Let lambda_3 be Haar conditioned on the two remaining roots. Call them r=1,2 as names only; no original residue is translated.

Every B_q(t) is constant on each of these roots. Write beta_qr for its lambda_q mass. For each exponent e there is at most one original modulus3q^e, and it targets at most one retained ternary root. Consequently

    beta_q1+beta_q2<=b_q.                              (FC5)

Put g_r(D)=product_(q not in D)(1-beta_qr) and b_D=product_(q in D)b_q. For each fixed D of size at least two, the remaining original numerical labels are d or3d with that Q-support. Summing their outside exponent choices by(FC3), while keeping one actual residue for each full label, gives

    lambda(U)>=F(beta),
    F(beta)=(g_1(empty)+g_2(empty))/2
       -(1/2)sum_(|D|>=2) b_D
          [g_1(D)+g_2(D)+max(g_1(D),g_2(D))].           (FC6)

The first two terms in the brackets pay the3-free label d; the maximum pays the one actual root chosen by label3d. An original targeting the excluded root has zero mass. There are no additional3^i d labels in this step because of the declared ternary-height hypothesis.

## An analytic lower bound for all phase allocations

For this lower-bound comparison one may enlarge B_q on each retained root until beta_q1+beta_q2=b_q. The measures lambda_q are nonatomic, so the enlargement exists. It only shrinks the carrier before the remaining actual deletions; the same union-bound argument still gives lambda(U)>=F for the enlarged parameters. This does not replace an original class or assert that F is coordinatewise decreasing.

With every other q fixed, F is concave in(beta_q1,beta_q2): its product terms are affine in that pair and the negative of a maximum of two affine terms is concave. Its minimum on the segment with sum b_q is therefore attained at an endpoint. Iterating leaves a partition Q=A disjoint union B, placing beta_q1=b_q for q in A and beta_q2=b_q for q in B, with the opposite entries zero. This optimizes comparison parameters; it does not change the actual law later obtained by restricting lambda to U.

For u,v in[0,1], max(u,v)<=u+v-uv. Thus at a partition endpoint,

    F>=G=(g_1(empty)+g_2(empty))/2
        -sum_(|D|>=2)b_D[g_1(D)+g_2(D)]
        +(1/2)sum_(|D|>=2)b_D g_1(D)g_2(D).             (FC7)

Let e_k be the elementary symmetric polynomials in

    (b_q)=(1/3,1/5,1/9,1/11,1/15,1/17).

Write s=e_1, let C=sum_(i in A,j in B)b_i b_j, and let T be the sum of the cubic monomials meeting both A and B. Expansion of(FC7) gives the lower bound

    G>=1-s/2-e_2-C/2-(e_3-T)/2-2e_4-2e_5-3e_6.        (FC8)

The coefficients can be checked without enumerating partitions. A degree-k monomial wholly in one part, k>=2, has coefficient

    (1-k/2)(-1)^k-1.

One with r>=1 indices in A and s'>=1 indices in B, k=r+s', has coefficient

    1_(r=1)(-1)^s' + 1_(s'=1)(-1)^r
       +((k-1)/2)(-1)^k.

The quadratic coefficients are therefore-1 within a part and-3/2 across parts; cubic coefficients are-1/2 within and0 across. Degrees4,5,6 have coefficients at least-2,-2,-3, respectively. These facts imply(FC8).

Each cross triple contains two cross pairs. Since the two largest distinct b_i sum to8/15,

    T=(1/2)sum_(i in A,j in B)b_i b_j(s-b_i-b_j)
       >=(s-8/15)C/2,
    C=(sum_(i in A)b_i)(sum_(j in B)b_j)<=s^2/4.

With kappa=1/2-(s-8/15)/4=7037/16830>0, equation(FC8) consequently gives

    G>=1-s/2-e_2-e_3/2-kappa*s^2/4-2e_4-2e_5-3e_6.

The six exact symmetric values are

    (e_1,...,e_6)=(7244/8415,3937/14025,40/891,
                   19/5049,4/25245,1/378675).

Substitution yields, for every partition and hence every actual phase allocation,

    alpha=lambda(U)>=107917593011/595884873375>9/50.    (FC9)

The exact surplus over9/50 is1316631607/1191769746750. The cross-pair and cross-triple terms are linked through the same partition; optimizing them as if independent would not justify this bound.

## One all-depth query law from the retained mass

Use the original product lambda, and define mu=lambda|U/alpha. Its support lies in the actual original survivor set. It is fixed independently of all query layouts and has Haar tails beyond one period resolving the actual originals. The product cylinder caps are

    C_3=3/2,    C_q=(q-1)/(q-2), q in Q.

For any finite complete query L=sum_(d|N)1_(x=a_d mod d), including the unit label, ordered-increment comparison along the product coordinates gives

    E_lambda h(L)<=E h(M),
    M=product_(p in P)(1+J_p),
    Pr(J_p>=e)=C_p p^-e, e>=1,                         (FC10)

for increasing convex h and independent auxiliary J_p. Original and query phases remain separately labelled. The comparison events at equal depth may be nested together; this is a convex upper comparison, not an assumption that actual independent query phases coincide. It is the standard source lemma cited above, applied to this explicitly constructed product lambda.

Restriction to U and L-1<=3+(L-4)_+ give, under the same mu,

    E_mu(L-1)<=3+E(M-4)_+/alpha.                       (FC11)

Here the exact moment and the three small atoms suffice. Put u_p=1-C_p/p and v_p=C_p(p-1)/p^2. Then

    EM=product_p(1+C_p/(p-1))=3584/935<23/6,
    Pr(M=1)=product_p u_p=4929320269/22260788550<2/9,
    Pr(M=2)=(product_p u_p)sum_p v_p/u_p
       =17219034431580221/53980687022637375<8/25,
    Pr(M=3)=(product_p u_p)sum_p v_p/(p u_p)
       =19024867518738549950467/261797965053302759956875<3/40.

Since M is a positive integer,

    E(M-4)_+=EM-4+3Pr(M=1)+2Pr(M=2)+Pr(M=3)
       <23/6-4+2/3+16/25+3/40=243/200.

For reference its exact value is

    632556580988687681445089/523595930106605519913750.

Combining with(FC9) proves E_mu(L-1)<3+(243/200)/(9/50)=39/4. At any finite query period choose a maximizing phase separately for each numerical divisor. The law remains the same. Every such sum is bounded by the single constant3+E(M-4)_+/alpha<39/4; monotone exhaustion of prime-power depths therefore proves the all-depth statement in(FC1), with strictness preserved. No independently selected finite laws or unsupported uniform lifts are used.

The very same measure has

    mu<[(3/2)product_(q in Q)(q-1)/(q-2)]/(9/50) H_P
       =(10240/561)H_P<19H_P.                         (FC12)

## Arbitrary later23/29 originals

Let the additional original family be supported on P union{23,29}, with every added modulus divisible by23 or29. Take mu tensor H23 tensor H29, chosen once before any later query. Each later numerical modulus has a unique expression d23^j29^k with d P-smooth and j+k>0. At each fixed exponent pair there is at most one original for each numerical d. Its original phases are arbitrary, and the d=1 term remains included. Thus the mass of the one complete later forbidden union is less than

    [sum_(j+k>0)23^-j29^-k](1+39/4)
       =(51/616)(43/4)=2193/2464.

After deleting that union, the source probability mass is greater than271/2464. By(FC12), the full actual survivor Haar mass is greater than

    (271/2464)(561/10240)=13821/2293760>3/500.

All original families are finite. Positive Haar mass consequently gives an uncovered residue on the full actual LCM period and hence an uncovered integer. Only the old-only ternary-height premise was used; no restriction was placed on any exponent or phase of a later23/29 original.

## Why the height-one argument does not close unrestricted prefixes

The arbitrary-height inequality(FC4) remains valid. The two-root pooled budget(FC5) does not extend by erasing deeper ternary prefixes. For example take the actual family

    (3,0),(5,0),(15,1),(45,2).

Under the pure5 survivor law, nonzero first digits each have mass1/4. The15-class exposes digit1 over ternary root1, while the45-class exposes digit2 only on the depth-two cylinder2mod9 inside root2. Collapsing that latter cylinder to its first root makes the pooled projected cost1/2, exceeding b_5=1/3. Keeping it at its actual depth instead changes which integrals in(FC4) are charged. The labels15 and45 are distinct numerical moduli and cannot be assigned one common3*5 inventory budget.

The unresolved estimate is therefore on the jointly sampled original-prefix expression in(FC4), or on a new supported law retaining that expression. Neither the height-one condition nor a phase-count condition can be assumed for an unrestricted family. The result is a conditional seven-prime source and nine-prime extension, not a solution of unrestricted Erdős#7.

The seven-prime constants above follow from finite rational products, symmetric polynomial coefficients and nonnegative geometric sums. That part is analytic, with independent ordinary review; it uses no configuration enumeration, new consumer, cached source geometry or Lean build. The following eight-prime extension keeps a finite partition comparison explicitly.

## Eight old primes and arbitrary29/31 originals

Put P8=P union{23} and Q8=P8 minus{3}. For any finite distinct original family supported on P8, with arbitrary original residues and nonternary heights but v3(m)<=1, the same fibre construction gives one probability mu8 supported on its actual survivors with

    R_P8(mu8)<105/8,
    mu8<(3072/119)H_P8<26H_P8.                         (FC13)

Consequently any finite additional original family supported on P8 union{29,31}, every added modulus divisible by29 or31, may have arbitrary old and outside phases and heights. The complete first-ten-prime survivor Haar mass is greater than

    901/2949120>1/3300.                                (FC14)

The old-only ternary-height condition now includes originals involving23; the later29/31 originals have no such height restriction. This is a different sufficient family from(FC2), whose later23 originals could already have unrestricted ternary depth.

The proof through(FC6), including artificial carrier enlargement and coordinatewise concavity, applies unchanged with Q8. At a partition A disjoint union B=Q8, retain the exact maximum in F. Define

    n_q=q-2,    D0=product_(q in Q8)n_q=7952175,
    I_A(E)=product_(q in A minus E)(n_q-1)
             *product_(q in B minus E)n_q.

Then clearing denominators in the actual F formula gives

    2D0 F(A)=I_A(empty)+I_B(empty)
       -sum_(E subset Q8, |E|>=2)
          [I_A(E)+I_B(E)+max(I_A(E),I_B(E))].            (FC15)

All terms are integers. Complementing A exchanges I_A and I_B without changing the numerator, so it suffices to check the64 partitions containing5. The [exact partition consumer](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_partition.py), with its [input](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_partition_input.json), evaluates every term of(FC15). Its [result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_partition.json) retains all64 integer numerators. Their minimum is2142533, attained at A={5}; among all128 partitions the complementary partition has the same value. Thus

    min_A F(A)=2142533/15904350
       >2120580/15904350=2/15.                         (FC16)

The exact numerator surplus is21953. This is an exhaustive finite comparison after the proved reduction of all continuous budgets to partitions. It does not enumerate original congruence families or truncate their prime-power heights. No analytic exchange rule claiming that A={5} must be extremal is assumed.

Use lambda8 formed from the actual pure-coordinate survivors and the two ternary roots, and let alpha8=lambda8(U8). Concavity, the same-label deletion bound and(FC16) imply alpha8>2/15 for every admitted actual old family. Normalize the one restriction mu8=lambda8|U8/alpha8 before all queries. The independent auxiliary product M8 in(FC10) now includes23, with C23=22/21. The same three-small-atom identity gives exactly

    E(M8-4)_+
       =180301179496850337824724227641
          /133782425313748456576602521250
       <27/20.

Every complete query therefore has, under that single mu8,

    E_mu8(L-1)<3+(27/20)/(2/15)=105/8.

As above, maximizing each numerical label and then exhausting all query depths preserves the strict common bound. The product predeletion Haar cap is2048/595. Hence the very same normalized law has cap below(2048/595)/(2/15)=3072/119, proving(FC13).

For the admitted additional29/31 originals, the complete outside reciprocal inventory is59/840, with the old unit cofactor included. Under mu8 tensor H29 tensor H31, deletion of their one actual forbidden union leaves mass greater than

    1-(59/840)(1+105/8)=53/6720.

The full Haar survivor mass is consequently greater than

    (53/6720)(119/3072)=901/2949120>1/3300,

which proves(FC14). The source period resolves the original finite family; mu8 has actual Haar tails on that product, so arbitrary later old-coordinate query depths use this same law. No residue is changed between branches or tests.

The retained program also checks the exact auxiliary moment, its27/20 bound, the density conversion and the complete later deletion margin. Run:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_partition.py
```

Default execution compares the retained result. `--input-dir` selects a directory holding the input and retained result; `--output PATH` writes a newly computed result after all inequalities pass. Checks remain active under optimization, and the program imports no source geometry helper. Its mathematical role is the finite numerical premise(FC16) and the displayed rational constants; the preceding actual-family reduction, source support and arbitrary-height query argument remain ordinary proofs. No Lean certification or unrestricted Erdős#7 conclusion is claimed.

## A depth-two comparison that no leaf reweighting repairs

Return to the seven old primes P. The following is a boundary of the fibre-mass and product-query-cap comparison, not a counterexample to an actual survivor law or to Erdős#7. It excludes every reweighting and every real query threshold for one specified comparison point. No realization of that point by an actual finite original family is asserted.

At ternary height two, the pure3 and pure9 originals leave at least five depth-two cylinders; if necessary restrict this carrier further to five cylinders in two roots, with leaf groups R0={0,1} and R1={2,3,4}. These are interface names, not changes of original residues. Moduli3q^e and9q^e have separate inventories. For each q, their projected masses have respective pooled budgets b_q across the two roots and b_q across the five leaves. On a leaf, the union of its root and leaf blockers has mass at most the sum of those two masses. Artificially enlarging the blocked sets to that sum gives a smaller comparison carrier, since2b_q<1.

Consider the comparison vertex assigning each full root budget to r_q and each full leaf budget to s_q:

| q | 5 | 7 | 11 | 13 | 17 | 19 |
| --- | --- | --- | --- | --- | --- | --- |
| r_q | 1 | 0 | 0 | 0 | 0 | 0 |
| s_q | 3 | 1 | 0 | 1 | 1 | 0 |

Put beta_ql=b_q(1_(l in R_rq)+1_(l=s_q)) and G_l(D)=product_(q not in D)(1-beta_ql). For arbitrary leaf probabilities w_l>=0 with sum w_l=1, the same supported-deletion argument gives the comparison mass expression

    F2(w)=sum_l w_l G_l(empty)
       -sum_(|D|>=2)b_D [sum_l w_l G_l(D)
           +max_r sum_(l in R_r)w_l G_l(D)
           +max_l w_l G_l(D)].                         (DT1)

The three charges retain the distinct numerical labels d,3d,9d. With actual projected masses, this construction supplies a lower bound on the surviving mass; the saturated vertex above is an enlarged comparison input. A universal estimate over these budgets must handle it. Uniform weights give F2=6074/210375; the argument below does not assume that uniform weights are optimal, or that this vertex minimizes F2.

The predeletion ternary law with weights w and Haar tails has cylinder caps

    r=max(w0+w1,w2+w3+w4),    v=max_l w_l,
    Pr(J3>=1)=r,
    Pr(J3>=e)=v*3^(-(e-2)), e>=2.                      (DT2)

Together with the six independent auxiliary Q-runs of(FC10), define h_t(r,v)=E[(M-t)_+], M=(1+J3)product_q(1+Jq). These are complete tails, not finite-depth query truncations. Changing w must also change r and v. The pointwise inequality L-1<=t-1+(L-t)_+ holds for every real t. If F2(w)>0, the mass/cap interface would bound the nonunit query sum by

    t-1+h_t(r,v)/F2(w),    t real.

To reach the23/29 continuation target565/51, it would need

    (T-t)F2(w)-h_t(r,v)>0,    T=616/51.                (DT3)

For this comparison vertex,(DT3) fails for every w and every real t for which F2(w)>0. The proof uses one fixed affine bound, followed by one scalar maximization.

Fix the reference vector w*=(1/4,1/4,1/4,0,1/4). For each D choose the root maximizing sum_(l in R_r)w*_l G_l(D), taking root1 on a tie. For the leaf maximum, average uniformly over all maximizing leaves at w*. These choices lower-bound the corresponding maxima at every w, even though they were selected at w*. Substitution into(DT1) gives

    F2(w)<=sum_l A_l w_l,
    A=(309137/1514700,179237/1514700,-2611/504900,
       -5363/34425,-2611/504900).                      (DT4)

The coefficients are finite rational sums over the57 supports D of size at least two. In particular A0>A1>0 and A2,A3,A4<0. At w* the bound is attained and equals118177/1514700. The bound is an upper bound on this comparison expression, not an upper bound on the actual surviving mass.

For every real t, write h_t(r,v)=h0(t)+hr(t)r+hv(t)v. All three coefficients are nonnegative. Indeed h0=E[(N-t)_+] for N=product_q(1+Jq); the other coefficients are sums of nonnegative increments of the increasing function u ->(Nu-t)_+, using the tails in(DT2). This also proves the identity and nonnegativity without a threshold grid.

Use the valid inequalities r>=w0+w1 and v>=(w0+w1+w2+w4)/4. For t<T, equations(DT3)--(DT4) bound the score above by a convex combination of five coefficients. The first coefficient is

    g(t)=(T-t)A0-h_t(1,1/4),                          (DT5)

and the second is at most g(t). The other three coefficients are respectively

    (T-t)A2-h0-hv/4,
    (T-t)A3-h0,
    (T-t)A4-h0-hv/4,

which are strictly negative. The pair(1,1/4) in(DT5) defines a valid auxiliary distribution; it need not arise as the two actual maxima of one w.

For that scalar law, EM=4864/935. Its integer support and exact small atoms give

    Pr(M>=9)<A0<Pr(M>=8),
    h_8(1,1/4)=6406291706177849483788577
                  /7068545056439174518835625.

The function g is concave and affine between consecutive integers. Its left and right slopes at8 are Pr(M>=8)-A0>0 and Pr(M>=9)-A0<0. Thus8 is its unique global maximizing threshold and

    sup_t g(t)=g(8)
       =-522631923325787723138477/7068545056439174518835625
       <-7/100.                                      (DT6)

All five coefficients are therefore negative on t<T, proving failure of(DT3). The scalar margin7/100 is not asserted as a common margin for all five coefficients. For t>=T and F2(w)>0, the baseline t-1 already reaches565/51, so that range cannot meet the strict query target either. If F2(w)<=0, this mass lower bound cannot be used as a positive normalization denominator; no score claim for those weights at t>=T is needed.

The [exact verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_obstruction.py) reconstructs(DT4) from the stated argmax rule and computes only the auxiliary product atoms below9, together with the untruncated first moment, to verify both slopes and(DT6). Its [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_obstruction.json) retains the coefficients and rational values. Run:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_obstruction.py
```

Default execution checks the retained result; `--output PATH` writes the recomputed result. No optimizer, source geometry helper or Lean build is used. The obstruction is to proving the target from this enlarged two-tier budget and these predeletion query caps. Stronger actual-prefix incidence, overlap credits, or a different jointly supported source law remain possible routes; their sufficiency for unrestricted originals is unresolved.

[Report529](529-an-irredundant-comb-separates-fibre-credits-from-supported-query-laws.md) supplies a separate obstruction with actual distinct original labels at unbounded ternary heights. Every original has a private integer, and positive exact-single-class fibre certification forces excessive query concentration for every ternary reweighting of the specified pure-q sources. The same family admits both an overlap mass repair and a different supported product law meeting the query target.

## Finite height profiles do not extend this fibre comparison to eleven primes

The simultaneous [height bounds of Report385, HC5--HC9](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#16-retained-pure-powers-turn-private-point-demand-into-height-bounds) for a globally extremal whole cover give a finite original exponent profile when the whole ternary height is one. The present comparison still does not cross zero at the first eleven odd primes. This is a limitation of the displayed lower bound, not a covering construction and not an upper bound on the actual survivor mass.

First fix any finite odd-prime support `{3} union Q`, impose `v3(m)<=1`, and let `h_q>=1` bound **every original exponent** at each `q in Q`. All residues remain those of one actual family. Put

    d_q=(q-2)q^h_q+1,    n_q=q^h_q-1,
    c_q=(q-1)q^h_q/d_q,  b_q=n_q/d_q.

If `S_q` avoids the actual pure q-power originals, then

    H_q(S_q)>=1-sum_(e=1)^h_q q^-e=1/c_q,
    lambda_q(a mod q^e)<=c_q q^-e,
    sum_(e=1)^h_q c_q q^-e=b_q.

Here `H_q` denotes normalized Haar measure. The finite-height replacement changes both the source density cap and the complete original-label inventory. It is not a substitution of a smaller inventory into an unchanged source estimate.

The proof of (FC4) and (FC6) now applies with these `c_q,b_q`. For each nonternary support `D`, the inventory of remaining labels `d` and `3d` is bounded using the same full exponent profile. In particular, the one actual `3d` label still chooses at most one retained ternary root, so its charge is a maximum of the two fibre responses. The pooled two-root budget is still `beta_q1+beta_q2<=b_q`.

Enlarge the forbidden sets on the two roots to saturate this budget, shrinking the comparison carrier, and then apply the same coordinatewise concavity argument. This derives a new lower comparison from the actual family. It does **not** assume that the old function `F` is monotone in `b_q`. For a partition `Q=A disjoint union B`, define

    I_A(E)=product_(q not in E)(d_q-n_q*1_(q in A)),
    J(E)=product_(q in E)n_q,    D0=product_q d_q.

The exact partition value is

    2D0 F_h(A)=I_A(empty)+I_B(empty)
      -sum_(E subset Q, |E|>=2)
         J(E)[I_A(E)+I_B(E)+max(I_A(E),I_B(E))].

Every term is an integer. Setting `n_q=1,d_q=q-2` recovers the arbitrary-height comparison (FC15), including its eight-prime calibration. Complementing the partition exchanges `I_A,I_B`, so checking every partition containing 5 covers all cases.

For the globally extremal branch, combine the retained-pure and disjoint-bucket height bounds

    H5,H7<=5,    Hp<=4 for p>=11,
    Hp<=2+floor((5s-9)/(p-2)), p>3,

where `s` is the total support size. On the first eleven odd primes this gives the nonternary height profile

    primes:  5,7,11,13,17,19,23,29,31,37,
    heights: 5,5, 4, 4, 4, 4, 4, 3, 3, 3.

On the first twelve, append prime41 with height3. These are shared upper bounds for the one actual family, rather than separately optimized branch realizations.

The complete exact partition comparisons give:

| Total support | Complementary partition pairs | Arbitrary-height minimum | Finite-height minimum |
| --- | ---: | ---: | ---: |
| 11, through37 | 512 | `-11713394479/435858711750` | `-3235686764662888756400388469505835122247281/121558280938063242531355231984302827769665424` |
| 12, through41 | 1024 | `-134490454633/1888721084250` | `-193174336278412841396513204086750351078296803651/2722824454158657923874002959627060473488659053984` |

In all four comparisons, the unique minimizing representative containing5 is `A={5}`. The finite-height minima are approximately `-0.026618398514` and `-0.070946305768`; the first improves the arbitrary-height value by only about `0.000255894`. The existing eight-prime calibration remains `2142533/15904350`.

Even optimizing the two surviving ternary-root weights does not repair the eleven-prime comparison at this partition point. Put `lambda3(root1)=w` and `lambda3(root2)=1-w`, with Haar conditional tails inside each root and `0<=w<=1`. The actual-family argument gives

    F_h(A,w)=w*g1(empty)+(1-w)*g2(empty)
       -sum_(|D|>=2)b_D[
          w*g1(D)+(1-w)*g2(D)
          +max(w*g1(D),(1-w)*g2(D))].

The first two deletion terms charge the one 3-free label on both roots. Its companion `3d` targets only one actual root, so the maximum includes the root weights. This remains a common-source estimate; the two root weights do not select different original residues.

For `A={5}` and the eleven-prime finite-height profile, this function is concave and piecewise affine in `w`: it is affine minus a positive combination of maxima of affine functions. The breakpoint where the two terms for `D={5,7}` agree is

    w*=418707776472463050778264010198585
        /1104431572940608845135925740120209
      =0.3791160871629475... .

Exact rational evaluation over all1013 deletion supports gives

    F'_-(w*)=
      24981612669186739085078294065269191503567
      /467756732806400163660818593494190775448448 >0,

    F'_+(w*)=
      -28370469388546560668735906293460733917015
      /526226324407200184118420917680964622379504 <0.

Concavity therefore certifies the strict global maximum over every real `w in[0,1]`, not merely a tested grid. Its value is

    max_w F_h({5},w)=-0.007489481907568035...<-7/1000.

Only `D={5,7}` is tied at `w*`. Thus no change of the two root probabilities makes **this relaxed comparison point** positive. This does not assert that an actual family realizes the point, or exclude other source constructions or stronger estimates.

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_height_partition.py) evaluates the same integer formula for the arbitrary and bounded profiles. Its [exact JSON result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_height_partition.json) includes every partition numerator, the common denominator, all minimizers, the source caps, the inventories and the eight-prime calibration. It also derives `w*` from the `{5,7}` breakpoint and records the exact rational maximum and both supporting derivatives. It writes JSON to stdout by default or to a specified `--output` path. A separately written integer implementation reproduces both bounded-profile minima; an independent rational reconstruction verifies the reweighting certificate.

These calculations do not show that any actual family attains the comparison vertex. They show that the height restrictions alone, fed into this unchanged union-bound and fibre-credit comparison, do not establish a positive uniform comparison at the first eleven or twelve odd primes. The existing (FC14) exclusion through the first ten odd primes remains valid. A further exclusion needs stronger joint restrictions or a stronger estimate; unrestricted support is not closed by obtaining finite heights at each fixed support. These are ordinary deductions and exact integer checks, not new Lean verification.

Run from the repository root with Python3.10+ (the consumer uses `int.bit_count`):

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_height_partition.py
```

All checks remain active under `-O`; normal and optimized execution produce
identical output. The consumer reads no external input and invokes no geometry
producer or Lean checker.

## Fixed label capacities preserve the partition reduction

[Report529's ternary-height-one construction](529-an-irredundant-comb-separates-fibre-credits-from-supported-query-laws.md#actual-ternary-height-one-families-realize-the-single-class-fibre-charges)
realizes the partition budgets and all exact individual deletion charges
of the finite-height functional, for each fixed root weight. In particular
the negative eleven-prime subtraction is realized by an actual finite
irredundant noncover. That construction does not satisfy the additional
global-extremality premise, and it does not make the actual survivor
mass negative. The missing information can be the intersections of
different original deletions or additional whole-cover constraints.

The latter have a concrete inventory interface.
[Report385, PI1--PI3, JP1--JP4 and CR0--CR9](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#18-retained-mixed-originals-couple-both-ternary-roots)
bounds the numbers of original multiples of3pq and3q^2 in one globally
extremal whole cover with H3=1. Those formulas retain the actual prime
labels and the entire original family; they impose no bound on its
support size. No corresponding restriction is asserted for arbitrary
irredundant noncovers.

Its shared four-label repair also couples two different actual phases:
within a retained ternary root, two3pq phases sharing a p-root or
q-root have at most three original occupants together. Since each
phase has at most two, double-occupied cells form a matching. The new
CR1--CR8 parent movement uses an actual retained mixed original to
couple the two ternary roots: either the oldpq phase is unguarded and
its deletion removes one more allowed cell, or it is guarded and a
complete repair yields the stronger cross-root capacity. In the same
whole-cover model these give the beta-independent bounds

    # {d original:3pq|d}<=2(p-1)(q-1)-|p-q|-2,
    # {d original:3pq|d, a_d mod3=r}
        <=(p-1)(q-1)+min(p-1,q-1)-1.

For105 these are44 originals in total and at most27 on either actual
ternary root, strengthening the earlier45/27 joint bound and75/46
independent-phase bound. They are simultaneous necessary restrictions, not separately
attainable maxima. They retain all original numerical identities and
do not require identifying artificial partition membership with an
original phase. Finer row/column constraints themselves require those
physical phase labels to be kept explicitly.

CR9 also excludes a candidate numerical label if its own forced
3pq-divisor inventory exceeds CR8, strengthening JP4's earlier ceiling. This exclusion depends on the
original label and its heights, not on beta, so it may be applied
before the fixed-inventory optimization. For instance, an actual
original containing3,5,7 can have at most seven distinct nonternary
prime factors; this is not a bound on the family's complete support.

The square inventories must be imposed as well. If x_(d,r) indicates
an original3d with at least two nonternary support primes, and z_(q,e,r)
indicates an original3q^e, Report385 PI3 gives the simultaneous cuts

    sum_(d:q^2|d,r) x_(d,r) + sum_(e>=2,r) z_(q,e,r)
        <=4q^2-6q-3,
    sum_(d:q^2|d) x_(d,r) + sum_(e>=2) z_(q,e,r)
        <=2q(q-1)-2, for each r.                     (FC26)

These use the same original labels as the pair constraints. If a
selected3d has q-depth h, divisor closure forces all3q^e with1<=e<=h;
in particular h-1 star labels consume the total square capacity.
A height *upper bound* alone does not force these labels. Their actual
roots must also be retained when using the root-specific cut. These
constraints are independent of the artificial beta parameters.

Fix the finite exponent inventory, beta parameters and root weight w.
An original label3d assigned to root r has nonnegative deletion charge

    a_(d,r)(beta)=w_r*g_r(D)*product_(q in D)c_q*q^(-v_q(d)),
    D=supp(d), w_1=w, w_2=1-w.

If a set of numerical labels has at most K originals, its total charge
is bounded by the sum of the K largest allowed labelled charges,
maximizing over each label's allowed single-root choice. This is an
upper comparison: it does not claim the maximizing labels and phases
can coexist. Disjoint bins can be paid separately. For overlapping
capacity sets, keep the joint restrictions in one optimization or use
a proved relaxation; the same saving cannot be subtracted twice.

There is still an exact partition reduction for every fixed feasible
selection set independent of beta. Hold all prime blocks except q
fixed. For each numerical-label/root choice, `a_(d,r)` is affine in
`(beta_q1,beta_q2)`: it is constant when q belongs to D, and otherwise
has one factor `1-beta_qr`. Therefore the maximum total charge over
any fixed finite set of admissible selections is a maximum of affine
functions, hence convex in this block. This includes top-count bins,
joint pair capacities and uniform root-specific capacities.

The initial carrier mass and the unrestricted3-free charges are
affine in the same block. Their difference from the maximal allowed
3-divisible charge is consequently concave. Artificially enlarging
the blocked sets still shrinks the same comparison carrier, and
these numerical inventory constraints remain true for the actual
labels independently of that enlargement. Successive blockwise
extreme-point choices therefore reduce a global minimum to the same
two-root partition vertices. The minimizing partition can change;
the old minimizer alone is not a uniform certificate for the new
functional.

The beta-independent feasible-set condition is essential. A partition
obtained by enlargement and concavity does not reveal the actual
root of original3p or3q. It cannot be used to select a stronger
same-root or opposite-root phase capacity without preserving those
physical root labels and proving the additional relation. The
uniform inventory bounds in Report385 avoid that inference.

This gives a legal way to bring whole-cover phase restrictions into
the joint numerical inventory. The finite obstruction below shows
that these numerical constraints do not by themselves make this
comparison positive. No unrestricted-support conclusion or new Lean
result is claimed.

## Joint pair, square and divisor constraints still leave a negative comparison

Fix the twelve-prime height-one branch through41, with

    Q=(5,7,11,13,17,19,23,29,31,37,41),
    h=(5,5,4,4,4,4,4,3,3,3,3),
    b_q=(q^h_q-1)/((q-2)q^h_q+1),
    c_q=(q-1)q^h_q/((q-2)q^h_q+1).

These are the simultaneous finite height bounds above. At the
comparison partition A={5}, put beta_q1=b_q only for q=5, and
beta_q2=b_q for q!=5. The opposite entries are zero. Keep
g_r(D)=product_(q notin D)(1-beta_qr) and
u_d=product_(q|d)c_q/q^v_q(d).

For root r define the carrier and full3-free debit

    C_r=g_r(empty),
    B_r=sum_(D subset Q, |D|>=2) product_(q in D)b_q*g_r(D).

The3-free debit is still the complete bounded numerical inventory.
It is not asserted to be the debit of one actual original family.
Let Omega consist of numerical/root selections satisfying all the
total and root-specific pair capacities, CR9, mixed divisor closure,
and FC26 with the forced star labels. Original numerical identities
remain distinct. No nonternary residue assignment is part of Omega.
The strengthened comparison is

    F_Omega(w)=w(C_1-B_1)+(1-w)(C_2-B_2)
       -max_(S in Omega) [w sum_(d assigned1 in S)g_1(D(d))*u_d
                      +(1-w)sum_(d assigned2 in S)g_2(D(d))*u_d].

It is a lower-bound comparison after the indicated relaxations,
not an actual survivor mass. One fixed feasible selection S gives
an affine *upper bound on this comparison*:

    F_Omega(w)<=w L_1+(1-w)L_2,
    L_r=C_r-B_r-sum_(d assigned r in S)g_r(D(d))*u_d.  (FC27)

Thus two negative endpoints certify failure for every real root
weight, without computing the maximum or sampling a weight grid.

The [explicit finite witness](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_inventory_witness_input.json)
has2206 mixed labels3d, assigned197 to root1 and2009 to root2.
It includes42 star labels3q^e: all1<=e<=h_q, with the5-stars on
root1 and every other star on root2. Direct factorization and exact
arithmetic verify simultaneously:

- all55 overlapping pair capacities and110 root-specific pair capacities;
- all11 uniform square capacities and22 uniform root-specific square
  capacities of FC26,
  including the stars rather than paying their slots twice;
- all7550 label-pair CR9 restrictions and every finite height bound;
- all6375 immediate mixed-divisor edges, hence every mixed proper
  divisor required by a selected label.

The numerical palette obtained by adjoining3, bothq^e and3q^e for
all42 star positions, and bothd and3d for each selected mixedd has
4497 distinct odd nonunit labels and is divisor-closed. This is a
numerical completion only; no residues making it an extremal cover
are supplied. Its3-free part is smaller than the unrestricted debit
B_r used in FC27.

The most restrictive square counts include:

| Square divisor | Mixed counts on roots1/2 | Star counts on roots1/2 | Full root counts | Total cap | Each-root cap |
| --- | ---: | ---: | ---: | ---: | ---: |
|3*5^2|34 / 2|4 / 0|38 / 2|67|38|
|3*7^2|7 / 78|0 / 4|7 / 82|151|82|
|3*11^2|10 / 215|0 / 3|10 / 218|415|218|

For this same selection the exact rational endpoint checks give

    L_2=-0.037407841838047365...<-1/100,
    L_1=-0.030920050975640826...<-1/100.

The full fractions, all capacities, source caps and debit components
are in the [exact result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_inventory_witness.json).
Equation FC27 therefore gives F_Omega(w)<-1/100 for every w in[0,1]
at this single comparison partition. This rules out a positive
uniform bound from this particular relaxed functional, even if a
different root weight is chosen for each partition. It does not
rule out using additional actual phase relations, constraining the
3-free debit jointly, or constructing a different source law.

### Why numerical divisor closure alone cannot recover the missing saving

There is a general reason to keep phase information separate from
numerical closure in this optimization. Fix the beta parameters,
nonternary heights, and an explicit star inventory. Suppose a selected
mixedd has an absent proper divisore of at least two-prime support.
Replace3d by3e on the same root. Every pair/square total or root
occupancy is unchanged or decreases, height bounds and CR9 persist,
and no new star is forced. The number of selected mixed labels is
unchanged and their numerical sum decreases strictly.

The unweighted assigned-root charge also increases. Removing one
factorq when v_q(d)>1 multiplies the charge byq. Removing the last
factorq, while retaining at least two support primes, multiplies it by

    q*(1-beta_qr)/c_q
      >=q*(1-b_q)/c_q
      =q*((q-3)+2q^(-h_q))/(q-1)>1, q>=5.            (FC28)

For an arbitrary absent proper divisor, apply the same ratio along
the removed prime factors. Iterating missing-divisor replacements
terminates because the positive integer sum of numerical labels
strictly decreases. The result is a mixed divisor ideal, with no
smaller charge on either root. Consequently, for this numerical
capacity problem, an optimum can already be chosen divisor-closed.
Adding just that closure cannot decrease the maximizing debit.

This compression statement concerns the numerical optimization.
Replacing a real original by a divisor at the same ternary root
need not preserve its nonternary phase, private region or joint
replacement liability. FC28 does not license such a replacement in
an actual cover.

The [standalone checker](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_inventory_witness.py)
reads only its explicitly named JSON input, factors every label and
checks all displayed constraints. It computes the full3-free debit
independently as

    B_r=product_q(1-beta_qr+b_q)-C_r
        -sum_q b_q*g_r({q}),

and performs both endpoint comparisons over exact rationals. A
separate reconstruction sums over all support subsets. These are
finite computational checks and ordinary deductions, not newly
compiled Lean results or an Erdős#7 counterexample.

Normal execution and optimized execution from a relocated directory
with spaces give identical output. No personal shell configuration,
directory scan or external package is used.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_inventory_witness.py --input docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_inventory_witness_input.json
```

### Actual star roots impose a stronger constraint than FC26

[Report385 SQ1--SQ8](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#19-actual-star-roots-and-a-guarded-square-parent-repair)
sharpen the uniform square total to4q^2-6q-5. More decisively, if y_t
indicates the actual3q root and z_t the actual3q^2 root, then

    mixed_square_count_t + square_star_count_t
      +2(q-1)y_t+z_t<=2q(q-1)-2.                    (FC29)

Every indicator and counted original belongs to the same hypothetical
globally extremal family with H3=1. These actual root variables can be
retained in a beta-independent feasible set; the artificial partition
A does not supply their values.

The2206-label witness explicitly specifies the stars. Its complete
square counts on the root containing both3q and3q^2 are38,82,218 at
q5,7,11, while FC29 allows at most29,69,197. Its displayed root
assignment therefore fails the strengthened model. The earlier
FC26--FC28 obstruction remains valid for its declared uniform-capacity
contract. No positive comparison for the stronger model, or exclusion
of all other root assignments, is established by rejecting one witness.

## Whole-family height one permits a smaller common query interface

The all-depth query in(FC13) permits later originals with arbitrary ternary
height. If instead **every** original in the whole family has v3(m)<=1,
then every old cofactor of every later original has ternary exponent0 or1.
The same actual law can therefore be tested on the smaller interface

    R_<=1(mu)=sum_(d>1,P8-smooth,v3(d)<=1) max_a mu(a mod d).

Keep the actual product source lambda8, actual avoid-set U8 and one law
mu8=lambda8|U8/alpha8 from(FC13)--(FC16). Before any query is chosen,
alpha8>=alpha_*=2142533/15904350. For a finite complete restricted query,
use all labels d=3^e product_q q^i_q with e in{0,1} and bounded nonternary
depths, including d=1. Call its load L. Ordered increments in(FC10) apply
only at the depths present in this query. Thus the ternary auxiliary run
is B~Bernoulli(1/2), while the other runs retain their full tails:

    M=(1+B)product_(q in Q8)(1+J_q),
    Pr(J_q>=e)=((q-1)/(q-2))q^-e, e>=1.

The auxiliary runs are independent; actual query indicators and the
coordinates of the restricted law mu8 need not be. For every t>=1,

    E_mu8(L-1)<=t-1+E_lambda8(L-t)_+/alpha8
              <=t-1+E(M-t)_+/alpha_*=U(t).             (FC17)

Here L>=1, the hinge is nonnegative, and the comparison is on the original
product source before restriction. Maximizing the phases of each finite
query and exhausting only the nonternary depths proves R_<=1(mu8)<=U(t).
Every query uses this same mu8; no new law is selected for an exponent
slice. This does not improve the unrestricted all-depth R in(FC13).

For outside primes T={29,31,37}, fix an outside exponent tuple and factor
each original numerical label uniquely as d times its outside part.
Distinctness allows at most one original per old d within this tuple.
The old unit label must be included. Under mu8 times outside Haar measure,
the full later union consequently has mass at most

    C_T[1+R_<=1(mu8)],
    C_T=product_(r in T)r/(r-1)-1=3023/30240.          (FC18)

The whole-family height-one condition is needed here, since it puts all
these d in the restricted query interface. It is stronger than the
old-only premise of(FC14). The bound includes every outside exponent and
keeps one actual residue for each original label.

Exact arithmetic gives EM=2048/595 and

    U(6)=25585241677563810650651525265027348808464564
         /2768452210966647080721479752700688323091875
        =9.241713321332838...,
    1-C_T[1+U(6)]=-0.023832651137207977... .

The required query bound for a positive expression in(FC18) is strictly
below27217/3023. The displayed negative lower expression supplies no
positive survivor certificate; it is not a negative actual probability.

## Coupling finite source heights and query heights on the same law

For old nonternary height bounds h_q>=1 use the finite-profile source
already defined above, with

    D_q=(q-2)q^h_q+1,
    c_q=(q-1)q^h_q/D_q,    b_q=(q^h_q-1)/D_q.

Let alpha_h>0 be the lower comparison furnished by its complete partition
functional. Restrict this actual product source lambda_h to its actual
survivors U, obtaining mu_h=lambda_h|U/lambda_h(U). Define R_h by summing
the nonunit old query labels with ternary exponent0/1 and other exponents
0..h_q. Ordered increments now use

    M_h=(1+B)product_q(1+J_q),  B~Bernoulli(1/2),
    Pr(J_q>=e)=c_q q^-e for1<=e<=h_q, and0 thereafter.

In particular, the exact coordinate atoms and complete mean are

    Pr(1+J_q=1)=1-c_q/q,
    Pr(1+J_q=m)=c_q(q-1)/q^m, 2<=m<=h_q,
    Pr(1+J_q=h_q+1)=c_q/q^h_q,
    E(1+J_q)=1+b_q=c_q.

The final atom includes the entire remaining tail. The source bound and
query numerator now use the same c_q,b_q and the same actual lambda_h:

    R_h(mu_h)<=U_h(t)=t-1+E(M_h-t)_+/alpha_h,
    mu_h<=((3/2)product_q c_q)/alpha_h * H_P8.         (FC19)

The denominator is recomputed from this source; one cannot combine a
new query numerator with an unrelated independently optimized source.
For whole-family outside height bounds k_r, the same deletion argument
replaces C_T by product_(r in T)(sum_(j=0)^k_r r^-j)-1. It requires all
later old cofactors to satisfy the stated old height profile as well.

In the globally extremal whole-cover branch on the first eleven odd
primes, **both HC7 and HC9 of Report385** give the simultaneous bounds

    old q:       5,7,11,13,17,19,23,
    h_q:         5,5, 4, 4, 4, 4, 4,
    outside r:  29,31,37, with k_r=3.

The existing finite-profile partition formula has64 complementary cases
on this eight-prime core. Its unique minimizing representative containing5
is A={5}, giving

    alpha_h=7869166022025963372126998610755
            /58313734905966118372203626202336,
    EM_h=29587293691123932440386084375
          /8597041855516160750730300192,
    E(M_h-6)_+=33298700700065977060036535627593
               /58313734905966118372203626202336,
    C_T=99431594269/994678024931.

Consequently

    U_h(6)=72644530810195793920671528681368
            /7869166022025963372126998610755
           =9.23154125950097...,
    1-C_T[1+U_h(6)]
      =-5752216770187904734900111181430100674522
        /252493113440094170651284888859573040475255
      =-0.022781677851790836... .                       (FC20)

This improves the restricted query bound but does not exclude this
eleven-prime branch. A positive bound would imply an uncovered residue
on the actual finite LCM period; a nonpositive comparison gives no
covering example and does not show the true survivor mass is zero.

For both profiles,6 is the unique optimum over **all real thresholds**,
not only a scanned finite list. The function U_h is convex. Since M_h
is integer-valued, its left and right slopes at6 are respectively
1-Pr(M_h>=6)/alpha_h and1-Pr(M_h>6)/alpha_h. The exact finite-profile tails
are

    Pr(M_h>=6)=269620927993579193251848591286
                /1822304215811441199131363318823,
    Pr(M_h>6)=202740140808017619581010471770
               /1822304215811441199131363318823.

They strictly straddle alpha_h, so the slopes have opposite strict signs.
The arbitrary-nonternary-height profile has the same strict crossing
with alpha_*. Convexity proves uniqueness in both cases. Changing only
the real threshold in these fixed comparisons cannot repair their gaps.
This does not exclude better estimates using the same law, stronger
source mass bounds or additional original-label relations.

The [truncated-query consumer](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_truncated_query.py)
and [exact result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_truncated_query.json)
retain both profiles, their complete means, product atoms through6,
hinges, exact slopes and margins. The consumer checks the hashes of the
existing source certificate and finite-profile program, reuses that
partition formula and evaluates all64 cases of the new core profile.
Atoms through6 and the complete mean determine the displayed hinges
without omitting any tail. Independent arithmetic using integer
coordinate numerators and multiplicative factorizations through6 agrees
with the finite query, tails and outside ledger; it reuses alpha_h and
does not independently certify the partition reduction. Normal,
optimized and different-working-directory runs agree byte for byte.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_truncated_query.py
```

Checks remain active under `-O`; the default dependency paths are relative
to the program. These are ordinary proofs with exact finite arithmetic,
not new Lean results, a geometry enumeration or an unrestricted#7 result.

## Actual pure-outside conditioning closes the eleven-prime branch

For any finite family of pairwise distinct odd numerical moduli greater
than1, supported on at most eleven actual primes, assume every original
satisfies v3(m)<=1. Then its periodic integer survivor set has natural
density greater than1/700. All actual residues and all finite nonternary
heights are arbitrary. Global extremality, divisor closure and the
optional HC7/HC9 height bounds are unnecessary for this statement.

First work on the first eleven odd primes. Keep exactly the old law mu8
in(FC17), with its arbitrary-nonternary-height query bound

    R=25585241677563810650651525265027348808464564
       /2768452210966647080721479752700688323091875,
    mu8<=D_old H_P8,
    D_old=(2048/595)/(2142533/15904350).

Use the existing actual pure-outside continuation of
[Report463, PE3--PE4](../450-499/463-two-actual-prime-extensions-preserve-a-common-core-law.md#a-fixed-product-law-and-the-original-modulus-labels)
and [Report464, FQ2--FQ4](../450-499/464-smaller-common-law-cores-give-ten-prime-noncoverage.md#finite-prime-extension-with-actual-pure-survival).
Their counting argument requires old query control only for cofactors
appearing in later originals. Here every such cofactor belongs to the
restricted interface in(FC17), by the whole-family ternary-height premise.
This is a reuse of that continuation, with a stronger task-specific seed.

For each r in T={29,31,37}, let S_r avoid all actual original pure r-power
classes and set rho_r=H_r(.|S_r). Numerical distinctness gives

    H_r(S_r)>=(r-2)/(r-1),
    rho_r<=c_r H_r, c_r=(r-1)/(r-2),
    b_r=sum_(e>=1)c_r r^-e=1/(r-2).

The single probability nu=mu8 tensor rho29 tensor rho31 tensor rho37
already avoids all old-only originals and all pure outside originals.
Each mask uses the actual family's residues; absent pure classes are
not inserted. The masks depend on disjoint coordinates, so their product
is legitimate. Independence of the remaining forbidden events is not
assumed, and mu8 is neither replaced nor reconditioned at this step.

At each nonzero outside exponent tuple, distinct full numerical labels
leave at most one original per old cofactor d. Summing d>1 costs at most
R under the same mu8. An original with d=1 and singleton outside support
is already excluded by its own pure mask. Unit old cofactors with two or
three outside primes must still be paid. Thus, with Q=product_r(1+b_r)-1,

    nu(remaining forbidden union)<=R Q+Q-sum_r b_r,
    nu(full survivor)>=delta=1-R Q-Q+sum_r b_r.        (FC21)

These quantities all use the same law and complete geometric tails.
The charge also equals R sum b_r+(R+1)(sum_pairs b_r b_s+product b_r),
so conservative caps remain valid if some pure slots are missing.

Here Q=3/29 and Q-sum b_r=92/27405. Exact substitution gives

    delta=88016430921103672032820067404610465617466941
           /2167698081186884664204918646364638956980938125
          =0.04060363926368927...,
    nu<=D_full H, D_full=1751777280/62133457.

Consequently the actual full survivor U satisfies

    H(U)>=delta/D_full
      =88016430921103672032820067404610465617466941
        /61115611972512329206704300212201763057254400000
      >1/700.                                         (FC22)

The exact numerator surplus over1/700 at this denominator is
708413817514630308956781387179375535674941. All originals resolve on
one finite CRT period, so Haar measure equals natural integer density.
The negative outside-Haar expressions(FC18),(FC20) remain correct for
that choice of law; they do not obstruct this pure-conditioned law.

### Transport to arbitrary actual primes while preserving3

If3 occurs in the support, pad it to eleven coordinates with unused odd
primes and order them as q1=3<q2<...<q11. Write p_i for the first eleven
odd primes. Then q_i>=p_i. Apply the existing finite digitwise shifted
prefix injections from
[Report460](../450-499/460-joint-five-prime-moments-give-a-parent-seventeen-completion-margin.md#transport-to-any-five-actual-odd-primes),
using the identity at3 and resolving every actual original height.
For each injection F, an original cylinder pulls back to either an empty
set or one source cylinder with the same exponent vector. After empty
preimages are discarded, numerical labels remain distinct and v3<=1.

The preceding construction on this pullback family gives a live
submeasure xi_F with mass at least delta and xi_F<=D_full H_source.
Average the unnormalized pushforwards. Their common support avoids all
actual originals, their average mass is at least delta, and

    E_F F_*xi_F<=D_full E_F F_*H_source=D_full H_actual.

At every nonternary coordinate, each fixed source word has uniform target
image under its finite random shifts. Integrating source Haar on the
unchanged3 coordinate preserves ternary Haar. Domination is applied
before averaging even though xi_F depends on F. Projection
away from unused padding coordinates preserves the actual avoidance
and the same Haar bound. Hence(FC22) holds for every support containing3
of size at most eleven. No infinite choice of incompatible laws is used.

If3 is absent, apply the same existing pure-outside continuation with
empty old core, R=0 and initial density cap1. All original pure powers
are removed by the coordinate masks. The remaining support-size-at-least2
inventory gives

    H(U)>=[2+sum b_p-product(1+b_p)]/product(1+b_p).

This expression decreases in each b_p=1/(p-2), as in Report464 FQ5.
The first eleven nonternary primes5,7,11,13,17,19,23,29,31,37,41 therefore
give the smallest comparison for any at-most-eleven nonternary support:

    product(1+b_p)=1048576/403767,
    2+sum b_p-product(1+b_p)=29127751/66621555,
    H(U)>=29127751/173015040>1/700.

This handles absent3 without adding a twelfth coordinate or transferring
another prime's height restriction to3.

The optional whole-family finite profiles in(FC19) sharpen the literal
first-eleven-prime value. Finite old heights and arbitrary outside heights
give H(U)>=0.001480220499343449...; imposing outside heights at most3
gives

    H(U)>=3647238554156052072191496549233497994846917
          /2462011359564062528038650437146933392655778125
         =0.0014814060625625435... .

The [pure-extension consumer](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_pure_extension.py)
and [exact data](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_pure_extension.json)
consume the pinned common source/query certificate and evaluate the
continuation in both product and support-expansion forms. They also
recover the existing two-prime threshold566/49 and verify the empty-core
case. Independent rational evaluation agrees with the displayed bounds;
normal, optimized and different-working-directory outputs agree exactly.
No original geometry or prior partition computation is repeated.

These are ordinary proofs with exact arithmetic, not new Lean
verification. The result does not impose or justify height one for
arbitrary hypothetical covers, and does not settle unrestricted support.

## Eleven small support primes allow an unrestricted large-prime tail

Let R be all actual support primes at most100000. If |R|<=11 and every
original supported entirely on R has v3(m)<=1, the full finite family
cannot cover the integers. Original moduli touching a prime greater
than100000 may have arbitrary finite exponents at every coordinate,
including arbitrary powers of3. There is no bound on the number of
large support primes, or on how many of them occur in a single modulus.
Distinct odd nonunit numerical moduli and their actual residues are kept.

This is a direct use of the joint-moment tail interface in
[Chapter33, SH6 and SH11--SH13](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md#4-uniform-continuation-over-every-large-prime).
Its head premise is a supported submeasure with positive mass and a
joint Haar-density bound. It does not require an all-depth query norm.

Apply(FC22) and the no3 case to the head-only originals, obtaining their
actual survivor set U with H_R(U)>1/700. Resolve head heights large enough
for the entire original family, including the head parts of later
moduli. Uniform lifting to those heights preserves H_R(U). Use

    eta=H_R restricted to U,
    eta(1)>1/700, eta<=H_R.                            (FC23)

This is an actual Haar restriction, so the tail argument has m=1/700
and D=1. No claim that eta retains the previous source's query bound is
needed. For any at-most-eleven odd head primes, the joint second moment
of Chapter33 SH6 is at most

    M2(R)=product_(p in R) p(p+1)/(p-1)^2
           <=61036374269/1970749440.                   (FC24)

Each factor decreases with p; the first eleven odd primes majorize all
such heads. Finite heights only lower this complete geometric moment.
Domination eta<=H_R supplies the same bound despite correlations in eta.

Take B=100000, ell=10 and c_ell=201/199. The inherited analytic
prime-product premise SH11 applies since B>=286, ell>=4 and
3^ell=59049<=B. Its complete tail allowance is

    tau7=(c_ell^7/B)(B/(B-3))^2
          sum_(j=0)^7 7!/((7-j)!ell^j),
    sum_(j=0)^7 7!/((7-j)!ell^j)=305593/125000,
    M2 tau7=313147209759498591392330831
             /385594576415774972001458278400.

Thus the final supported mass is strictly greater than

    1/700-M2 tau7
      =1663915295841259580268266967
        /2699162034910424804010207948800
      >1/2000>0.                                      (FC25)

The tail theorem charges each original at its last large-prime
coordinate. At every depth it retains all earlier exponents and the
original numerical label; pure tail classes include the unit earlier
cofactor. Its normalized kernels preserve the entire preceding measure,
so all bad-set charges can be subtracted once from one final law. The
complete prime-product majorant permits any finite number of tail
primes. Positive supported mass gives an actual CRT survivor and hence
an uncovered integer.

The height-one premise is needed only to construct U. Subsequent
queries at deeper ternary exponents use eta's joint Haar domination
and the full second moment(FC24), rather than the restricted query
interface(FC17). It is therefore unnecessary to impose height one on
tail-touching originals. The number in(FC25) is mass under the final
distorted measure, not a natural-density lower bound of that size for
the complete family.

The [large-tail consumer](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_large_tail.py)
and [exact result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_large_tail.json)
consume the pinned head certificate and compute only the finite moment
product and the SH12 rational allowance. Independent evaluation using
the original SH6 factors and a recurrence for the positive polynomial
agrees exactly. Normal, optimized and different-working-directory runs
also agree. The program does not rerun the source, partition or query
calculations and does not prove the analytic prime-product estimate.
The latter retains Chapter33's Rosser--Schoenfeld/source attribution and
verification boundary. This application adds no Lean certification.

Unrestricted#7 still permits twelve or more small support primes and
head-only originals of greater ternary height. Neither is excluded by
these results.

## The depth-two comparison still fails after query truncation

The fixed comparison vertex in(DT1) remains an obstruction even when
the whole-family height-two premise permits truncating J3 at2 and the
outside23/29 law is pure-conditioned. This is a new exact certificate
for that strengthened comparison. The old(DT6) certificate concerned
the lower outside-Haar target and does not establish this variant.
No actual family is asserted to realize the relaxed vertex.

Keep its five leaf weights w, root maximum r and leaf maximum v. The
truncated ternary factor has probabilities(1-r,r-v,v) at1,2,3. Let N
be the product of the six complete nonternary factors in(FC10), with
EN=2048/935. For H_j(t)=E(jN-t)_+, the complete hinge is

    h_t=h0(t)+hr(t)r+hv(t)v,
    h0=H_1, hr=H_2-H_1, hv=H_3-H_2.

All three coefficients are nonnegative. The improved pure-conditioned
query target is566/49, so put T=615/49. A successful normalized bound
at weights with F2(w)>0 would require (T-t)F2(w)-h_t>0.

For the57 supports D of size at least two in(DT1), set

    c_l=G_l(empty)-sum_D b_D G_l(D),
    u_D=max_r sum_(l in R_r)G_l(D)w_l,
    z_D=max_l G_l(D)w_l.

Then F2(w)=sum_l c_l w_l-sum_D b_D(u_D+z_D). For each integer
t=1,...,12 maximize

    (T-t)[sum_l c_l w_l-sum_D b_D(u_D+z_D)]
      -hr*r-hv*v-h0.                                  (DT7)

Use nonnegative variables, sum_l w_l=1, and the epigraph inequalities
u_D>=sum_(l in R_r)G_l(D)w_l for both roots, z_D>=G_l(D)w_l for all
leaves, r>=sum_(l in R_r)w_l and v>=w_l. Add x_k<=1 for every variable;
the exact maxima satisfy these caps. Since T-t>0 and hr,hv>=0,
choosing the exact epigraph minima never worsens the objective. This
linear program covers every w, including the F2<=0 region that cannot
be used as a normalization denominator. It has121 variables,
527 inequalities and one equality.

For Ax<=b, ex=1, x>=0 and objective c.x-h0, exact dual certificates
y>=0 and A^T y+lambda e>=c give the upper bound b.y+lambda-h0.
The twelve supplied rational certificates verify every one of the
1452 column inequalities. All twelve integer upper bounds are below
-7/40. The largest certified integer upper, at t8, is

    -25220616066818896528630411/143948498727033000000000000.

The feasible vector w* in(DT4) has t8 score approximately-0.175205829126,
below this upper approximately-0.175205829098. Exact optimality or
uniqueness is unnecessary and is not asserted.

For fixed w with0<F2(w)<=1, the score is affine between consecutive
integer thresholds. For t<=1 it equals T F2-EM+t(1-F2), so t1 dominates.
For t>=T the score cannot be positive. On[12,T], affinity extends to13,
whose score is nonpositive because13>T. Hence any positive score at a
real threshold would force a positive score at an integer1,...,12.
The exact duals exclude this. The integer margin-7/40 is not claimed
as a uniform margin over every real threshold.

The [standard-library verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_truncated.py),
[exact duals](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_truncated_duals.json)
and [compact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_truncated.json)
reconstruct(DT7), its small product atoms through12 and its complete mean.
Floating solver proposals were rationalized and column deficits repaired
using the explicit unit-cap rows; all repair costs are included in the
verified objective. Verification uses only exact arithmetic and rejects
missing thresholds or certificates that fail the stated strict bound.
Default replay also compares the retained compact result; a stale result
is rejected. Explicit output mode regenerates it from the checked duals.
Independent reconstruction of the rows and multiplicative atom types
agrees with every dual column. Normal, optimized and different-directory
execution agree; no solver is needed to replay the certificate.

This excludes changing only leaf weights and the real threshold within
this fixed comparison. Additional actual incidence, mixed-overlap credit
or another source remain possible. It is an ordinary proof with exact
finite certificates, not new Lean verification or a covering example.
