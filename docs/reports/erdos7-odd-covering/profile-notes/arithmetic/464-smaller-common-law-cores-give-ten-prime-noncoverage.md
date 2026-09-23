# Smaller common-law cores give ten-prime noncoverage and a prime cutoff of one million

A finite family of pairwise distinct odd numerical moduli greater than one cannot cover the integers if its prime support satisfies either of the following conditions:

* at most five support primes are below 43, and at most ten are at most 1000000;
* at most six support primes are below 53, and at most ten are at most 1000000.

There is no restriction on original residues, finite exponents, the number of larger support primes, or the number of primes occurring together in a modulus. These are restricted noncoverage deductions. They do not cover the first ten odd primes or settle unrestricted Erdős #7.

The finite-head argument uses the exact five- and six-core common-law bounds of [report461](461-query-stop-loss-gives-a-common-law-six-core-completion-margin.md), rather than rounding their query constants to 10 and 14. It applies [report463](463-two-actual-prime-extensions-preserve-a-common-core-law.md)'s finite-prime product construction. The large-prime continuation is the existing correlated-head theorem of [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md). The source construction and arbitrary-height comparisons retain their attribution to Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1, and the verification boundary recorded in the [source entry](../../../../../Library/Arith/schroeder2026nine.md). The new deductions are ordinary proofs with exact rational checks, not Lean certification.

## Finite-prime extension with actual pure survival

Fix an old-core period K resolving all relevant original and query exponents. Suppose one probability mu on its actual survivor set simultaneously satisfies

\[
 R_K(\mu)=\sum_{1<d\mid K}\max_a\mu(a\bmod d)\le A,
 \qquad \mu\le\Lambda H_K.
 \tag{FQ1}
\]

Let Q be a finite set of distinct new odd primes, disjoint from K. All moduli in the head family being processed have prime support contained in the old core together with Q. At the fixed coordinate heights, let V_q be the actual avoid-set of the original pure q-power classes, and write a_q=H_q(V_q). Numerical distinctness gives

\[
 a_q\ge\frac{q-2}{q-1}>0.
\]

Define rho_q=H_q(.|V_q), and form the single product probability nu=mu tensor product_q rho_q before deleting any remaining original class. An exponent-e query on coordinate q has probability at most q^(-e)/a_q. Put

\[
 b_q=\frac1{(q-1)a_q},\quad
 P=\prod_{q\in Q}(1+b_q),\quad S=\sum_{q\in Q}b_q.
\]

Every remaining original modulus has a unique expression d product_{q in E}q^{e_q}, with d|K, nonempty E subset Q, and all e_q>=1. Fixing E and its complete exponent vector leaves at most one original query for each d. For |E|=1 the d=1 class is already removed by V_q, so the old-query sum is at most A. For |E|>=2, d=1 is a genuine multi-prime modulus and must be included; the sum is at most A+1. All phases are the original CRT projections.

The union bound under this same nu, followed by the geometric exponent sums, gives

\[
 \begin{aligned}
 E(A,Q)&=A\sum_q b_q+(A+1)
       \sum_{|E|\ge2}\prod_{q\in E}b_q\\
       &=(A+1)(P-1)-S,\\
 m(A,Q)&=1-E(A,Q)=A+2+S-(A+1)P.
 \end{aligned}
 \tag{FQ2}
\]

Thus m>0 gives one actual live submeasure, obtained by deleting the complete original mixed union once. Its mass is at least m and its density at most Lambda/product_q a_q. Consequently the actual enlarged avoid-set U satisfies

\[
 H(U)\ge\frac{m\prod_q a_q}{\Lambda}.
 \tag{FQ3}
\]

This subtracts only the pure single-prime classes; no d=1 multi-prime class is discarded. Finite original inventories only decrease the all-exponent upper bound. No separate favorable law is chosen for different exponent groups or query layouts.

For arbitrary pure classes use b_q=1/(q-2). The resulting conservative Haar expression is

\[
 h(A,\Lambda,Q)=\frac{A+2+S-(A+1)P}{\Lambda P}.
 \tag{FQ4}
\]

Larger actual pure avoid-sets improve both the deletion bound and the product-density conversion. Formula (FQ4) decreases with every b_j, since

\[
 \frac{\partial h}{\partial b_j}
 =-\frac{A+1+\sum_{i\ne j}b_i}
         {\Lambda(1+b_j)P}<0.
 \tag{FQ5}
\]

It therefore increases as any new prime increases. Omitting a new prime sets its b to zero and also improves the expression. For any fixed core size and its uniform seed constants, putting the smallest support primes in the core is the best scalar split. Comparing different core sizes means choosing one whole-family certificate before its construction; it does not permit pointwise or phase-dependent switching between their different laws.

## Two positive ten-prime families

The same-law seed pairs from report461 are

\[
\begin{array}{c|c|c}
k&A_k&\Lambda_k\\ \hline
5&354268696184847779107405/37639127656852367739093
 &84375000000/1812390307\\
6&8034293665870716452955503975561029997134562974/
581858869356700257567944700688463416886232987
 &10125000000000/68006602781.
\end{array}
\]

They satisfy A_5=9.4122451352... and A_6=13.8079766228..., with Lambda_5=46.5545416316... and Lambda_6=148.8826023644.... Query and density bounds are used from the same seed, without combining independently optimized constants.

For a core of at most five primes and at most five new primes all at least 43, monotonicity and distinctness reduce to Q=(43,47,53,59,61). For a core of at most six primes and at most four new primes all at least 53, use Q=(53,59,61,67). Exact rational evaluation gives the following bounds; decimal entries are rounded approximations:

| Core plus new primes | Distorted live-mass lower bound m | Exact Haar head lower bound h |
| --- | --- | --- |
| five plus five | ≈0.009175482315 | 758925898988086401704759981 / 4254306957863460122625000000000 > 1/6000 |
| six plus four | ≈0.013493434693 | 20780797372750944435897944289447648087106979923 / 245640385728810904867359431593980664170000000000000 > 1/12000 |

These bounds hold for arbitrary actual core primes and all original phases and finite heights. Smaller cores can be padded with unused primes and projected back, as in report461. The critical A values at these two new-prime lists are respectively

\[
 \frac{35015347}{3685915}=9.4997706132\ldots,
 \qquad
 \frac{1236442}{88335}=13.9971925058\ldots.
\]

Hence even A=9.5 or A=14 loses positive m; the earlier convenient bounds 10 and 14 cannot establish these cases.

The complete-family split controls below use the same exact five- and six-core seeds, and report462's seven-core pair A_7=70874/3375, Lambda_7=455625. Entries are rounded approximations of the sufficient mass expression m, not actual survivor masses.

| Actual support | five-core split | six-core split | seven-core split |
| --- | ---: | ---: | ---: |
| 3,5,7,11,13,43,47,53,59,61 | 0.009175482 | -0.086497030 | -0.157651029 |
| 3,5,7,11,13,17,53,59,61,67 | -0.350020971 | 0.013493435 | -0.065732133 |
| 3,5,7,11,13,37,41,43,47 | 0.010762484 | -0.023604691 | 0.009228064 |

In the last row both five- and seven-core splits work, but their Haar lower bounds are respectively 0.0002092713967... and 0.00000001934159534.... A larger core is therefore not automatically a stronger certificate. Negative entries only show failure of this sufficient scalar comparison.

## Arbitrarily many support primes above one million

Let R be the chosen head support of at most ten primes. Resolve all original head exponents, including the head parts of classes touching outside primes. Starting from the actual head avoid-set U, use the unnormalized measure H restricted to U. Its mass is at least h from the preceding section and its joint density at most one. This explicit change of seed uses no query estimate for the new Haar-restricted measure.

For the two reference heads, the full Haar second-moment factor is

\[
\begin{array}{c|c}
R&M_2(R)=\prod_{p\in R}p(p+1)/(p-1)^2\\ \hline
3,5,7,11,13,43,47,53,59,61&1446009325937/74029529600\\
3,5,7,11,13,17,53,59,61,67&16830979471677/788155596800.
\end{array}
\]

Every factor decreases with p, so these are uniform upper bounds for the stated head families. Apply Chapter33's arbitrary correlated-head transfer with B=1000000, ell=12, and c_ell=289/287. Its applicability conditions B>=286, ell>=4, and 3^ell=531441<=B hold. The all-prime tail allowance is

\[
 \tau_7(B,\ell)=\frac{c_\ell^7}{B}
 \left(\frac B{B-3}\right)^2
 \sum_{j=0}^7\frac{7!}{(7-j)!\ell^j}.
\]

The exact consumer checks, even after rounding the head mass down, that

\[
 \frac1{6000}-\frac{1446009325937}{74029529600}\tau_7
 >\frac1{10000}>0,
\]
\[
 \frac1{12000}-\frac{16830979471677}{788155596800}\tau_7
 >\frac1{100000}>0.
 \tag{FQ6}
\]

Every remaining original class is charged once at its last exposed outside prime. The existing normalized kernels and final global deletion give positive mass avoiding the entire original family, hence an uncovered integer on its complete finite period. The remaining mass in (FQ6) belongs to the distorted tail law; it is not a final Haar-density lower bound. Chapter33's analytic prime-product and arbitrary-height premises, and their verification status, remain unchanged.

To obtain the opening support-count statements, put every actual support prime at most B into the head. Pad to exactly ten, if necessary, using unused distinct primes in [43,B] or [53,B]. In the first case the last five head primes are at least 43; in the second the last four are at least 53. Apply the respective finite-head result, then expose all actual remaining primes, which exceed B. Padding adds no forbidden class, and an avoiding point projects to the original coordinates. Thus the count formulation does not impose an additional phase or height assumption.

## Reproducible arithmetic and remaining boundary

The [consumer](../../frontier/cover-geometry/finite_prime_extension_splits.py) reads the SHA-pinned [five/six-core summary](../../frontier/cover-geometry/query_stoploss_completion.json) and [seven-core comparison summary](../../frontier/cover-geometry/seven_core_last_stage_bridge.json). It writes [exact result data](../../frontier/cover-geometry/finite_prime_extension_splits.json), checks the complete-support grouping in (FQ2), both ten-prime bounds, contrasting splits, and the exact Chapter33 tail margins. It does not rerun source producers or geometry enumerations. All checks remain active under optimization.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite_prime_extension_splits.py \
  --query-seed docs/reports/erdos7-odd-covering/frontier/cover-geometry/query_stoploss_completion.json \
  --seven-seed docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven_core_last_stage_bridge.json
```

For the first nine and first ten odd primes, all three exact seed splits have negative sufficient mass expressions, even if the new-prime pure classes are absent. This is a comparison boundary, not a covering example or an all-law obstruction. Laws are asserted for each fixed finite original family and period, jointly for all queries on that period; no compatible inverse system of independently chosen laws is claimed. No uniform continuation through all small-prime supports follows from these results.
