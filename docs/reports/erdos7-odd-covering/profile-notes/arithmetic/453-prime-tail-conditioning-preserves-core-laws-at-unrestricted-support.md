[Index](../../marked_head_profile.md) · [Coordinate assignment](452-exponent-assignment-controls-arbitrary-two-prime-tail-graphs.md) · [Original completion](378-saturated-prime-fibres-and-mixed-tail-incidence.md)

# Prime-tail conditioning preserves core laws at unrestricted support

This ordinary proof uses Chapter07's full-history capped kernels and original-label second-moment expansion. It retains all ternary depths and original head labels, conditions survivors separately at each actual core point, and bounds the remaining weighted completion under one probability law. It supplies no new Lean declaration or claim of public mathematical priority.

## Exact statement

Let K be a positive odd integer coprime to 3, let Q be a positive divisor of K, and put D=tau(Q)>=1. Let P be any finite set of primes coprime to 3K, with finite coordinate heights J_p>=1. Fix a finite ternary height H>=1. The original family has at most one residue alpha_d for each numerical modulus d>1. It consists of arbitrary core labels dividing 3^H K and tail labels

    d=3^e a product_(p in T) p^(f_p),
    a|Q, 0<=e<=H, nonempty T subset P, 1<=f_p<=J_p.

Missing labels and arbitrary independent original residues are allowed. There is no restriction on outside support size, co-occurrence graph, exponent heights, or total number of outside primes. Q describes the tail head-divisor inventory; it need not equal K.

Let S subset Z/K avoid every original 3-free core class, and let mu be any given probability supported on S. For each tail original d, let C_d be its literal cofactor cylinder modulo d/3^e, retaining alpha_d. Set

    B_* = 3^256 D^4.

If every outside prime is at least an integer B>=B_*, there is ONE probability nu on Z/K times product_p Z/p^J_p such that

1. its entire K-marginal is exactly mu;
2. it is supported on the actual residual R_3 avoiding every original 3-free core and tail class;
3. its original weighted completion load satisfies

       L_tail(nu)=sum_(tail originals d, e>=1)3^(1-e)nu(C_d)
                  <=324D/B<3^(-250).                         (UT1)

The same construction has a uniform, pointwise-in-core preconditioning failure bound

    epsilon<=108D^2(1+ln B)^2/B<3^(-240).                    (UT2)

In particular, increasing B makes (UT1) smaller than any prescribed positive core margin for families whose outside primes meet that larger cutoff. The cutoff depends on D, which can grow with the original core heights. This is not a bound uniform in those heights, nor does it settle the regime where outside primes are merely at least 43.

## 1. Original early depths and full-history kernels

For an outside prime p put

    E_p=min(H,floor(log_3 p)).

Call an original tail label early when e<=E_p, with p its largest outside prime, and assign it once to p. This includes EVERY e=0 tail label.

Fix an actual core point x in S. Process the outside primes increasingly. At p and a complete preceding history, let F_p be the actual union of p-adic cylinders from matching early originals assigned to p. The matching tests retain the fixed original residue on the core and all preceding outside coordinates. Write alpha_p=H_p(F_p), with H_p normalized Haar on Z/p^J_p.

Use the existing threshold-1/2 capped density relative to H_p:

    alpha_p<=1/2: 0 on F_p, 1/(1-alpha_p) on F_p^c;
    alpha_p> 1/2: (2alpha_p-1)/alpha_p on F_p, 2 on F_p^c.

This kernel is normalized at every history, including alpha_p=0 and 1, and has density at most 2. Let sigma_x be the resulting finite sequential probability. For V_p={sampled p-coordinate lies in F_p},

    Pr_sigma_x(V_p)=E_sigma_x[2(alpha_p-1/2)_+]
                   <=E_sigma_x alpha_p^2.                    (UT3)

Later normalized kernels preserve each complete prefix marginal. Chapter07 DG2's selected-coordinate bound therefore applies under the SAME sigma_x to any prescribed j outside cylinders:

    sigma_x(C)<=2^j product p^(-f_p).                       (UT4)

No independence is asserted. Only queried coordinates incur a factor 2; unqueried intermediate coordinates are integrated out.

## 2. Full-support second moment with original multiplicity

Write a_q=1/(q-1) and b_q=a_q+2a_q^2. For fixed largest p, exponent f_p, and a preceding outside exponent tuple, there are at most

    M_p=D(E_p+1)

early original labels, one for each numerical pair (e,a). Original labels remain separate even when their cofactor moduli or cylinder sets coincide.

Bound alpha_p by the raw sum of active original p-cylinder masses and expand its square. Current-coordinate exponents contribute a_p^2. At each pair of preceding exponent tuples there are at most M_p^2 original-label pairs. Incompatible residues contribute zero. A prime occurring in both tuples contributes one cylinder of depth max(f,g), hence one factor 2 from (UT4), not 4. The positive exponent-pair sum is

    sum_(f,g>=1) q^(-max(f,g))
      =sum_(h>=1)(2h-1)q^-h=b_q.

The untruncated Chapter07 RK1--RK2 expansion consequently gives

    E_sigma_x alpha_p^2
      <=M_p^2 a_p^2 product_(q in P,q<p)(1+4a_q+2b_q)
       =M_p^2 a_p^2 product_(q in P,q<p)(1+6a_q+4a_q^2). (UT5)

The head factor D is already paid in M_p; there is no additional D^2 multiplier. Completing prime sets and exponent ranges only enlarges this nonnegative upper bound. The argument is uniform at every actual core point, regardless of which head labels match it.

## 3. Prime-product and summation estimates

Use the elementary pi(t)<=7t/ln t for t>=2, with the self-contained binomial-coefficient proof in [report452](452-exponent-assignment-controls-arbitrary-two-prime-tail-graphs.md), (EA5). Put b=ln B and t_p=1+ln p. Partial summation gives, for p>=B,

    sum_(B<=q<=p,q prime)1/q
      =pi(p)/p-pi(B-)/B+integral_B^p pi(u)/u^2 du
      <=7/ln p+7 ln(ln p/b)
      <=7/b+7 ln(ln p/b).                              (UT6)

Here pi(B-) counts primes strictly below B, so the identity includes a prime endpoint B correctly. Since q>=3,

    6a_q+4a_q^2<=8a_q<=16/q,    2a_q<=4/q.

As b>=256 ln3>256, exponentiating (UT6) yields

    product_(B<=q<p)(1+6a_q+4a_q^2)
      <=exp(112/b)(ln p/b)^112<3(ln p/b)^112,
    product_(B<=q<p)(1+2a_q)
      <=exp(28/b)(ln p/b)^28<3(ln p/b)^28.              (UT7)

For an integer m>=0 and c>=0, put ell=c+ln B. If ell>=max(1,2m), the summand (c+ln n)^m/n^2 decreases for n>=B. Repeated integration by parts gives

    integral_B^infinity(c+ln u)^m/u^2 du
      =B^-1 sum_(j=0,...,m)[m!/(m-j)!]ell^(m-j)
      <=2ell^m/B.

Add the first summand to obtain

    sum_(n>=B)(c+ln n)^m/n^2<=3ell^m/B.                (UT8)

This overcounts primes with integers only AFTER the prime product has been bounded by a power of a logarithm.

Since ln3>1, M_p<=Dt_p and a_p<=2/p. Combining (UT5) and (UT7),

    E_sigma_x alpha_p^2<=12D^2 t_p^114/(b^112 p^2).

Apply (UT8) with c=1,m=114; here 1+b>228. With Good_x=intersection_p V_p^c, the union bound gives

    sigma_x(Good_x)>=1-epsilon,
    epsilon<=36D^2(1+b)^114/(b^112 B)
            <=108D^2(1+b)^2/B,                         (UT9)

using (1+1/b)^112<=exp(112/b)<3.

At B_*=3^256D^4, we have

    1+ln B_*=1+256ln3+4ln D<=513+4ln D<=513D.

Therefore epsilon<=108*513^2/3^256<3^(-240), since 108*513^2<3^16. The function (1+ln B)^2/B decreases on B>=B_*, so this bound remains valid for every admitted B. No core point in the support of mu is discarded.

## 4. Fibrewise conditioning and one preserved core law

Define

    rho_x=sigma_x(. | Good_x),    nu(x,y)=mu(x)rho_x(y).

By (UT9), every rho_x exists and has total mass one. Thus nu preserves mu exactly. Good_x avoids every early original cofactor event, including all e=0 tail classes. Together with mu's core support, this proves that nu is supported on the full actual R_3.

For every j prescribed outside cylinders, this SAME rho_x satisfies

    rho_x(C)<=sigma_x(C)/(1-epsilon)
             <=[2^j/(1-epsilon)] product p^(-f_p)
             <=2^(j+1) product p^(-f_p).               (UT10)

This is a joint-cylinder bound. The old caps conditional on an arbitrary prefix need not survive this final conditioning. Conditioning the global mixture mu(x)sigma_x(y) instead would reweight core points when their survival probabilities differ; the fibrewise construction above is essential.

## 5. All original late depths under the same nu

Early cofactor events have zero nu mass. If H<=floor(log_3 p), every depth with largest outside prime p is early and that p contributes zero completion load. Otherwise E_p=floor(log_3 p), and

    sum_(e>E_p)3^(1-e)<=(3/2)3^(-E_p)<=9/(2p).

For a late label with j preceding outside primes, (UT10) contributes 2^(j+2) times the reciprocal of all original outside prime powers. Sum over original head divisors, all exponents and ALL preceding prime subsets. The full contribution with largest outside prime p is at most

    L_p<=D*[9/(2p)]*4a_p product_(q in P,q<p)(1+2a_q)
        <=36D/p^2 product_(B<=q<p)(1+2a_q)
        <=108D(ln p)^28/(b^28p^2).                    (UT11)

Every queried mass belongs to the one nu; no phase is selected again to optimize a summand. Apply (UT8) with c=0,m=28 to conclude

    L_tail(nu)<=324D/B
               <=324/(3^256D^3)<3^(-250),             (UT12)

because 324<3^6. This proves (UT1)--(UT2), uniformly in all finite outside heights, support sizes, and prime counts, at the stated D-dependent cutoff.

## Reuse boundary and the core consumer

[Chapter07](../../problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md), DG1--DG4/RK1--RK2, supplies the capped kernels, selected-cylinder bounds and original-label square expansion. Its RK6--RK8 section, “The support restriction is needed only below a finite largest prime,” already proves unrestricted continuation for named heads. Those existing noncoverage conclusions dominate any claim that merely removing the support bound is new. The bridge here is the prescribed-full-core-marginal, all-original-depth WEIGHTED COMPLETION conclusion, using uniform survival at every actual core point. It is a synthesis of existing interfaces and elementary estimates, not a new foundational kernel theorem. No Lean certification of this complete argument is claimed.

Report452 retains a different feature: its ownership construction produces a product of coordinate laws conditional on the core. The sequential laws here, particularly after Good_x conditioning, need not have that factorization. Thus (UT12) does not replace every structural output of that report.

All original core cofactor masses are unchanged. Here L_core is the original3-bearing core completion load, excluding pure powers of3. If a separate result supplies L_core(mu)<=B_H-eta for some eta>0, where B_H=(3+3^(1-H))/2, choose an admitted B with 324D/B<eta. Then (UT12) and the existing whole-cover necessity certify noncoverage of the admitted complete family. This theorem does not supply eta. Absorbing smaller primes or their heights into Q changes D and can change the core margin; the displayed cutoff therefore gives no cost-free or guaranteed terminating reduction of arbitrary Erdős #7 families.

Exact finite controls: [program](../../frontier/cover-geometry/unrestricted_tail_completion.py) and [results](../../frontier/cover-geometry/unrestricted_tail_completion.controls.json).

The three-prime fixture has42 distinct original moduli, outside primes5,7,11 at height1, ternary height2, core modulus13, and a prescribed three-point law(1/2,1/3,1/6). Its chosen early cuts(0,1,1) exercise both nontrivial capped-kernel branches and a completely forbidden intermediate fibre. Actual fibre survival is(82/231,27/28,27/28); this measured survival, not the large-cutoff theorem, normalizes the fixture. The resulting314-atom common law avoids all14 original3-free classes. At core point0, the early triples exclude sigma_0-mass5/231 whose points satisfy every nontriple early constraint. Both late triple events have positive mass. The actual weighted load662227/697410 is at most its measured joint-cylinder bound465395/219186; these small primes are not claimed to satisfy(UT1).

A separate24-original fixture on43,47 has survivor probabilities2020/2021 and1. Conditioning the entire mixture would change a core mass1/2 to2020/4041; conditioning separately preserves1/2. After conditioning, one prefix leaf has probability1/23>2/47, refuting automatic reuse of the old full-history cap. All5947 selected-cylinder queries across the two fixtures satisfy the appropriate joint bounds. The controls also check original-label second moments, later-prefix preservation, actual cofactor support, and the scalar constants in(UT9)--(UT12). They do not replace the all-support proof.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/unrestricted_tail_completion.py
```
