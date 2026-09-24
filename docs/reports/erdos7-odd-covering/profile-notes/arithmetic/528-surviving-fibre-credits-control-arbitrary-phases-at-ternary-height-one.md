# Surviving-fibre credits give common query laws at ternary height one

Let P={3,5,7,11,13,17,19}. For every finite family of pairwise distinct odd numerical moduli greater than1 supported on P, with arbitrary original residues and v3(m)<=1, there is one probability mu on its actual survivor set such that

    R_P(mu)=sum_(d>1,P-smooth) max_a mu(a mod d)<39/4,
    mu<(10240/561)H_P<19H_P.                            (FC1)

The query sum includes every prime-power depth, although the original ternary depth is restricted. All original heights at5,7,11,13,17,19 are arbitrary. The same law serves every query. Adding any finite original family supported on P union{23,29} and touching23 or29, with arbitrary old and outside residues and arbitrary finite heights, leaves full Haar survivor mass greater than

    13821/2293760>3/500.                                (FC2)

The condition v3<=1 applies only to the P-only originals. In particular, later originals involving23 or29 may have unrestricted ternary depth. No claim that arbitrary P-only originals meet the condition is made, and unrestricted Erdős#7 remains unresolved.

These are ordinary mathematical deductions. The actual-family deletion inequality below retains which coordinates of a surviving fibre an original can still remove. The query step applies the standard ordered-increment comparison, in the form of Lemma4.1 of the [pinned Schroeder source](../../../../../Library/Arith/schroeder2026nine.md), and the stop-loss interface of [report461](461-query-stop-loss-gives-a-common-law-six-core-completion-margin.md). No source completion, geometry certificate or new Lean verification is used. The analytic fibre estimate and its combination with that query interface are the result here; no claim of literature priority is made.

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

All terms are integers. Complementing A exchanges I_A and I_B without changing the numerator, so it suffices to check the64 partitions containing5. The [exact partition consumer](../../frontier/cover-geometry/fibre_credit_partition.py), with its [input](../../frontier/cover-geometry/fibre_credit_partition_input.json), evaluates every term of(FC15). Its [result](../../frontier/cover-geometry/fibre_credit_partition.json) retains all64 integer numerators. Their minimum is2142533, attained at A={5}; among all128 partitions the complementary partition has the same value. Thus

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
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre_credit_partition.py
```

Default execution compares the retained result. `--input-dir` selects a directory holding the input and retained result; `--output PATH` writes a newly computed result after all inequalities pass. Checks remain active under optimization, and the program imports no source geometry helper. Its mathematical role is the finite numerical premise(FC16) and the displayed rational constants; the preceding actual-family reduction, source support and arbitrary-height query argument remain ordinary proofs. No Lean certification or unrestricted Erdős#7 conclusion is claimed.
