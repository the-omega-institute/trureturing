# Seven- and eight-prime heads admit quartic tails at unrestricted heights

Let C be a finite family of congruence classes with pairwise distinct
numerical moduli, each odd and greater than one. Each of the following
conditions implies noncoverage:

| Cutoff B | At most this many prime divisors of the full LCM are at most B |
|---:|---:|
| 1500 | Seven |
| 10000 | Eight |

Every original exponent is unrestricted, as are the number of actual
prime divisors strictly greater than B and the support arity of every
original modulus. Original phases are arbitrary and fixed once. The
eight-prime row takes Schroeder's attributed uncovered-density corollary
as an ordinary mathematical source premise. Neither row is a solution of
unrestricted odd covering, a new named open-problem resolution, or a new
Lean verification.

The proof extends the complete-query absolute tail from cubic to general
integer moment order k >= 2, then uses order four. The same actual head
source supplies its mass and all complete query moments; deletion and
moment propagation use one live measure throughout. This is an
application of the existing source and distortion framework, not a claim
that the underlying method or source theorem is new.

## 1. Full-height head sources and their actual joint bounds

Choose as head every actual support prime at most B. For the seven-prime
source, pad to seven coordinates with unused odd primes below B if
necessary. The eight-prime source already covers at most eight primes. Padding
adds no original class. For the seven-prime construction, the first two
ordered coordinates may also be padded to heights at least 3 and 2, as
in Chapter33. Fix the finite height of every head coordinate
large enough to resolve the ENTIRE original family, including all
head exponents of originals also involving a later tail prime. Only the
actual head-only originals are forbidden in the head source. Projected
pieces of tail originals must not be inserted as additional head classes.

[Chapter33 SH1–SH4](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md), using the inherited [Chapter31 construction](../../../problem-details/31-seven-vertex-block-noncoverage-with-actual-prime-measures.md), gives for
seven arbitrary odd head primes one positive actual submeasure eta7 with

    eta7(X) >= m7 = 7235955529/450000000000,
    eta7 <= D7 H_head,       D7 = 27/2.                 (HM1)

These bounds hold on the SAME source. The joint density follows from
the construction's conditional whole-coordinate Haar kernel caps before
actual union deletion; it is not inferred from unconditional marginal
caps. Their factors are (1,1,3/2,5/3,3/2,2,9/5).

The extension from the benchmark primes 3,5,7,11,13,17,19 to arbitrary
seven odd primes uses Chapter33's averaged digit-injection transport.
For each independently shifted coordinate injection F, the preimage of
each original cylinder is empty or one benchmark cylinder of the same
exponent vector. Distinct numerical moduli remain distinct. Choose an
avoiding source eta_F for that one pulled-back family, then apply
eta_F <= D7 H_benchmark pointwise BEFORE averaging F_*eta_F. A fixed
benchmark word has a uniform image on the target carrier. Thus the
averaged target measure has both mass at least m7 and joint density at
most D7. Dependence of eta_F on F is allowed. A mere existence pullback
would not justify this quantitative transport.

For eight arbitrary odd head primes, Michael Schroeder, *Nine Prime
Divisors in Odd Distinct Covering Systems*, edition1.0.1,
`cor:uncovered-density`, gives uncovered density at least1/1002375 for
the actual head-only distinct-modulus family at arbitrary finite heights.
On the finite full period this is Haar density. Uniformly lift its
survivor U to every additional head digit required by the tail originals
and use the explicit source

    eta8 = H_full_head restricted to U,
    eta8(X) >= m8 = 1/1002375,       eta8 <= H_full_head. (HM2)

The source archive SHA256 is
`9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`.
[the source entry](../../../../../../Library/Arith/schroeder2026nine.md) records the attribution and local
verification boundary. The complete arbitrary-height theorem has not
been locally replayed in Lean; the finite geometry replay does not
replace that theorem. The present consumer uses it as an explicitly
attributed ordinary source premise.

## 2. Complete k-query moments on one finite positive measure

For a finite period Q, a complete query has one globally fixed phase at
each divisor d of Q, including the unit term. If nu is a positive finite
measure, keep its absolute mass and a number K such that EVERY k complete
queries satisfy

    integral Q1 ... Qk dnu <= K.                        (HM3)

A uniform bound on integral Q^k gives (HM3) by Holder on this SAME finite
measure, without probability normalization. Conversely all queries may
be chosen equal. No separately optimized laws or selected formal-query
fields can substitute for this complete actual dictionary.

On product Haar, a compatible intersection of k congruence cylinders has
mass the reciprocal of the lcm of its labels; an incompatible one is
empty. There are (j+1)^k-j^k nonnegative ordered exponent k-tuples whose
maximum is j. Consequently, if nu <= D H_head, then

    integral Q1 ... Qk dnu
      <= D product_(p in head) M_k(p),
    M_k(p) = 1 + A_k(p),
    A_k(p) = sum_(j>=1) [(j+1)^k-j^k] p^(-j).            (HM4)

Actual exponent sums are finite and bounded above by this convergent
infinite sum. Positivity transfers the Haar bound through JOINT density
domination. The source need not be a product. Each M_k(p) decreases with
p directly from its positive-term series, so the first seven or eight
odd primes give uniform benchmark products.

At order four, the geometric series differentiated finitely many times
gives

    M4(p) = (p^4+11p^3+11p^2+p)/(p-1)^4.

Equivalently, writing t=1/(p-1),

    A4(p)=15t+50t^2+60t^3+24t^4.                         (HM5)

Thus (HM1)-(HM2) supply the absolute quartic potentials

    K7 = (27/2) product_(p=3,5,7,11,13,17,19) M4(p)
       = 82461631627375/127401984,
    K8 = product_(p=3,5,7,11,13,17,19,23) M4(p)
       = 16379878645983125/190768545792.                 (HM6)

No division by m7 or m8 occurs. That would change to a different invariant.

## 3. Exact live deletion and general moment propagation

Expose the remaining actual primes in increasing order. At a fresh prime
p, let H be its largest exponent in the actual family. Assign each
original to its last exposed tail prime. For every earlier numerical
cofactor d and current exponent e, distinctness of the full numerical
moduli permits at most one original phase. Hence, at fixed e, the old
activation load is a partial complete query and may be completed upward
to a genuine complete old query Q_e. Pure p-powers use the unit cofactor.

For an old point x let B_x be the union of the ACTUAL currently forbidden
p-cylinders, and beta(x)=H_p(B_x). Fix 0<delta<1 and define

    R_x(dy)=1_(y outside B_x) H_p(dy)
                  /[1-min(beta(x),delta)].              (HM7)

This is defined even if beta=1, when its numerator is zero. It has

    R_x(X)=(1-beta)/(1-min(beta,delta)) <= 1,
    1-R_x(X)=(beta-delta)_+/(1-delta).                   (HM8)

Every depth-j p-cylinder has R_x-mass at most p^(-j)/(1-delta). For depth
zero use the stronger bound R_x(X)<=1. The new measure nu'=nu R is still
supported on actual avoidance and remains unnormalized.

The actual beta is bounded by the completed load

    alpha(x)=sum_(e=1..H) p^(-e) Q_e(x),
    theta=sum_(e=1..H) p^(-e),
    integral alpha^k dnu <= K theta^k.                  (HM9)

The last inequality expands the k-th power and applies (HM3) to every
exponent tuple on the SAME old measure. Alpha can exceed1 and must NOT
replace beta in (HM7)'s denominator.

For every a>=0 and integer k>=2,

    (a-delta)_+ <= (k-1)^(k-1) a^k/(k^k delta^(k-1)).

For a>=delta, maximize (a-delta)/a^k: its derivative has the sign of
k delta-(k-1)a, and its maximum occurs at a=k delta/(k-1). For a<delta
the inequality is immediate. At k=4 there is the explicit remainder

    27a^4-256delta^3(a-delta)
      =(3a-4delta)^2(3a^2+8a delta+16delta^2).           (HM10)

Combining (HM8)-(HM10), the actual absolute loss is bounded by

    D_p <= C_(k,delta) K theta^k <= C_(k,delta)K/(p-1)^k,
    C_(k,delta)=(k-1)^(k-1)/[k^k delta^(k-1)(1-delta)]. (HM11)

Now expand ANY k complete new queries by their current exponent tuple.
For fixed old labels, the new-coordinate intersection is empty or a
prefix of depth equal to the largest exponent. At the all-zero tuple
use row mass1; otherwise use the prefix cap in (HM7). After dropping
possible incompatibility, the remaining old factors are k complete old
queries, so (HM3) applies. Counting tuples by their maximum gives

    K_new <= K [1+A_(k,H)(p)/(1-delta)]
          <= K [1+A_k(p)/(1-delta)],
    A_(k,H)(p)=sum_(j=1..H)[(j+1)^k-j^k]p^(-j).         (HM12)

Nothing here assumes independence in nu or simultaneous maximizers of
its different query products. Iterating (HM7) gives one actual measure;
its mass telescopes to at least initial mass minus the sum of (HM11).
All originals are assigned exactly once, with their full earlier
cofactors, heights and fixed phases retained.

## 4. An explicit allowance for every finite tail above B

Suppose an integer r gives a growth envelope valid for all t>=0:

    1+A_k(p)/(1-delta) <= (1+t)^r,   t=1/(p-1).          (HM13)

The inherited Rosser--Schoenfeld Theorem8 premise, as used in Chapter33
SH11 and recorded in [the prime-product source entry](../../../../../../Library/Arith/rosser1962approximate.md), implies

    product_(B<p<=z) p/(p-1) <= c_ell log(z)/log(B),
    c_ell=(2ell^2+1)/(2ell^2-1),                        (HM14)

when B is an integer, B>=286, ell>=4, 3^ell<=B and z>=B. It follows by dividing the positive
lower prime-product bound at B into the upper bound at z. Here log B>ell
because log3>1. No Riemann-hypothesis premise is used.

Assume also k ell>=r. Enlarging the prior growth product to every prime
in (B,q] gives K_before_q<=K_initial c_ell^r(log q/log B)^r. Omitting
primes can only decrease the actual product. Replacing the actual finite
tail charge sum by all integers n>B and using
(n/(n-1))^k <= (B/(B-1))^k gives

    sum D_q <= C_(k,delta) K_initial c_ell^r [B/(B-1)]^k
                     sum_(n>B) (log n/log B)^r n^(-k).

The summand's continuous version is decreasing on [B,infinity), since
k log B>k ell>=r. Therefore its sum is at most its integral from B.
Repeated integration by parts, using k>1, yields exactly

    integral_B^infinity (log x/log B)^r x^(-k) dx
      = B^(1-k)/(k-1)
          sum_(j=0..r) r!/[(r-j)!((k-1)log B)^j].

Replacing log B by its lower bound ell in this positive expression gives

    sum D_q <= K_initial tau_(k,delta,r)(B,ell),
    tau = C_(k,delta)/(k-1) * c_ell^r * B/(B-1)^k
            * sum_(j=0..r) r!/[(r-j)!((k-1)ell)^j].      (HM15)

The strict endpoint q>B and complete infinite exponent allowance are
retained. No enumeration cutoff on tail primes enters this bound.

## 5. Fixed quartic applications

For the seven-prime source take delta=1/4, r=20, B=1500, ell=6.
Then C_(4,1/4)=9 and

    1+(4/3)A4 = 1+20t+(200/3)t^2+80t^3+32t^4
                 <= (1+t)^20.

The degree-one coefficients are equal; the remaining binomial
coefficients dominate term by term. Also 3^6=729<=1500 and 4*6>20.
Exact substitution into (HM15) gives

    K7 tau =
      12920685555032221280338216348648725860046131680830754239736427491578125
      /1403418957047753843622097174783727937667480781592126779946610801774166016
      = approximately0.009206577615434456,
    m7-K7 tau > 3/500.                                  (HM16)

For the eight-prime source take delta=2/5, r=25, B=10000, ell=8.
Then C_(4,2/5)=5625/2048 and

    1+(5/3)A4 = 1+25t+(250/3)t^2+100t^3+40t^4
                 <= (1+t)^25.

Again every coefficient is dominated. Here 3^8=6561<=10000 and4*8>25.
The exact loss is

    K8 tau =
      460548988903266365955866608354082646611042938276873980151641338124351800743955322265625
      /488530861815658980798932624135430011424518333192315250744512248496633244935788144489767370752
      = approximately0.0000009427224048683515,
    m8-K8 tau > 1/20000000.                              (HM17)

The positive residuals are approximately0.0068733235601210994 and
0.00000005490822239190535. These fixed rational parameters are certified
choices, not claims of optimal cutoffs.

| Same full-height source | Earlier second-moment cutoff in Chapter33 | Quartic cutoff |
|---|---:|---:|
| Seven-prime source (HM1) | 100000 | 1500 |
| Attributed eight-prime Haar restriction (HM2) | 100000000 | 10000 |

[Report733](733-a-cubic-boundary-potential-closes-unrestricted-large-prime-tails.md)
uses a cubic potential at 4000/9000 for larger shallow heads, retaining
its specified restrictions. It does not imply the unrestricted-height
rows here. These comparisons concern the inspected statements; no
exhaustive literature novelty claim is made.

## 6. What the positive mass proves, and what remains open

The final actual measure is supported outside every original class and
has positive mass on the finite full CRT carrier. It therefore contains
an avoiding tuple and gives an uncovered integer. Dummy coordinates can
be projected away. No exponent or mixed-support restriction was added.

The margins in (HM16)-(HM17) are distorted masses, not Haar densities of
the same sizes. If s is the actual number of tail primes, the initial
joint Haar cap is D7 or1 and each live kernel has density at most
1/(1-delta). Valid Haar-density lower bounds are consequently

    (1/2250)(3/4)^s,       (1/20000000)(3/5)^s.          (HM18)

No positive Haar-density bound independent of s follows from this
conversion. Families having at least eight support primes at most1500
and at least nine support primes at most10000 remain outside these two
sufficient noncoverage conditions. The entire odd-covering problem is
not decided by these numerical improvements.

## 7. Exact finite controls and source boundaries

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_quartic_prime_tail.py) and its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_quartic_prime_tail.json) pin the seven-prime source certificate SHA256
`b6c47c2e710cdb27e599b92ccfe7d1b5c4e55b4b4082ad8058d196c1e964b9b2`.
They verify its specified source row, threshold tuple, mass and density
factors, all quartic initialization products, both complete growth
polynomial comparisons, every analytic-range substitution and both
strict rational residuals. The eight-prime density and analytic theorem
are explicitly marked inherited ordinary premises.

Finite controls exhaust1024 live kernel rows on all subsets of a
height-two ternary coordinate at the two thresholds, and13312 true
prefix caps. Sixteen exponent-quadruple sums check the maximum-exponent
count. For the actual CRT stage with originals(3,0),(9,3),(15,7),(45,14),
both thresholds exhaust all91125 complete45-query phase layouts:

| Threshold | Old mass | New mass | Actual max fourth moment | Propagated bound |
|---:|---:|---:|---:|---:|
| 1/4 | 3/4 | 26/45 | 767/15 | 467/9 |
| 2/5 | 3/4 | 121/180 | 617/10 | 577/9 |

Independent arithmetic derives both quartic seeds, both tail debits,
the polynomial growth coefficients and both positive margins. A separate
scope review checks cutoff partitioning, padding, full original heights,
source attribution and passage from positive mass to an actual integer.
These finite controls and reviews support the formula and implementation checks; they do not replace the general
ordinary proof in (HM3)-(HM15), the inherited source constructions, or
Rosser--Schoenfeld's theorem. No new Lean theorem is claimed.
