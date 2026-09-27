# One uniform owner threshold removes the parent-count bound

Keep the complete fixed-head, actual pure-source, relational-root and
ordinary-private-interface hypotheses of
[Report620](620-growing-parent-sets-preserve-a-common-survivor.md).
There is now a single owner threshold independent of the number of parents:

| Owner prime v | Permitted parent union |
| --- | --- |
| 37 <= v < V | The Report620 conditions: r <= 3; or r = 4 and v >= 1253; or r >= 5 and v >= 2(3r)^r + 3 |
| v >= V | Any fixed finite set of distinct smaller head or network parent primes, with no parent-count growth condition |

With V = 2^115 the extendible head Haar mass remains greater than 1/26000.
With V = 2^109 it is greater than 1/80000. The corresponding full survivor
densities are greater than 1/(26000 Q_off) and 1/(80000 Q_off), where Q_off
is the product of the actual outside resolving prime powers.

At each owner, all syntactic tuples are merged into one fixed parent union,
actual numerical labels are deduplicated, and one normalized row is chosen
for the entire inventory. Every actual modulus has one globally fixed
phase. Network size, depth, width and all exponent heights are arbitrary
finite quantities. The estimate covers the complete infinite prime tail
uniformly over all such finite instances.

This removes Report620's arity-dependent thresholds above one universal
threshold. It retains every head and ordinary-interface restriction, and
retains the owner restrictions below V. In particular it does not prove
unrestricted Erdős #7. The proof is ordinary mathematics with exact
rational checks; no new Lean verification is claimed. No threshold
optimality is asserted.

## 1. The actual inventories and one common normalized law

Use the literal head primes

    P = {3,5,7,11,13,17,19,23,29,31}.

The complete Report617 head conditions remain, including the fixed
central pure source and the prescribed equalities and inequalities
between outside roots in its relational-root extension. The full head
law mu is an unnormalized submeasure. Its queried-coordinate marginals
and full density obey

    mu_J <= 2^|J| H_J for every J subset P,
    mu <= C H_P, C = 138320/2673, alpha = 1/C.        (UT1)

Sample this same head first, and then all outside network owner coordinates
in increasing numerical prime order. Every parent belongs to P or is an
earlier declared network owner, so it is already available. Ordinary
private-interior primes are not additional undeclared parents. For a
fixed finite parent union A_v, the actual mixed
inventory at v is a finite subset of

    (product_(p in A_v) p^e_p) v^h,
    e_p >= 0, sum_p e_p > 0, h >= 1.                 (UT2)

Different exponent vectors and owner heights give different numerical
moduli. Multiple presentations of a numerical label are combined before
forming UT2. Pure owner powers are assigned once to its ordinary domain,
and every original belongs once to the head, an owner or an ordinary block.
The parent union and phases do not vary between sampling histories.

For v < V use exactly the Report620 row. For v >= V select no nonunit
parent pattern in advance: N = 0. The ordinary private extension domain
R_v already accounts for the pure powers and satisfies

    H_v(R_v) >= 1 - 2/(v-1) = (v-3)/(v-1).          (UT3)

Use the existing normalized half-threshold capped row relative to
H_v(. | R_v). For each complete prior history let t be the base mass of
the forbidden owner fibre. The row is normalized even at t = 1, its
density relative to the base is at most 2, and its bad probability is

    (2t-1)_+ <= t^2.                                (UT4)

Thus the chosen N = 0 and its cap belong to the same row:

    D_v = v-3,
    dK_v/dH_v <= 2(v-1)/(v-3) < 4 <= v/4.           (UT5)

The final inequality holds at every new owner in either stated range.
No surviving fibre is assumed, and there is no global conditioning on
survival. All rows are normalized at every complete prior history. Their
product with mu gives one joint submeasure Pi, preserving the head
marginal and all earlier event masses.

All actual ordinary domains, private-interior disjointness and component
gluing hypotheses are unchanged. The proof does not authorize undeclared
crossings through those private interiors.

## 2. Keep the actual finite caps

Use the following cap c_p at a parent coordinate:

* c_p = 2 for each of the ten head primes, in the joint-subset sense UT1;
* c_p = 2(p-1)/D_p for each prime 37 <= p < 971, using that prime's
  actual Report619 finite row and its actual D_p;
* c_p = 4 for every prime p >= 971.

There are 152 finite outside rows, hence 162 small-prime factors including
the head. The exceptions must be kept: for example c_967 = 161/16 > 4.
Every old three-parent row at p >= 971, every Report620 higher-arity
cubical row, and every new N = 0 row satisfies the third line. Below 971,
Report620 permits only its old at-most-three-parent rows, so its actual
finite table applies unchanged.

For a joint query of positive prefix depths j_p at any set of actual
parent coordinates, integrate queried outside parents in reverse
sampling order. Each queried row pays c_p p^(-j_p); unqueried normalized
rows integrate to one. Finish with the joint head bound UT1. This gives

    Pi(joint parent cylinders)
       <= product_(queried p) c_p p^(-j_p).          (UT6)

This is a common-law conditional argument, not independence of the
parents and not multiplication of separately optimized marginals. If two
queries use the same coordinate, their intersection is empty or a single
prefix cylinder at the maximum depth; its cap is paid only once.

## 3. A full cofactor moment with no arity parameter

For one actual coordinate define

    k_p(i,j) = 1 if i=j=0,
               c_p p^(-max(i,j)) otherwise.

There are 2m+1 exponent pairs with maximum m >= 1. Summing the convergent
geometric and arithmetic-geometric series yields

    T_p(c_p) = sum_(i,j>=0) k_p(i,j)
             = 1 + c_p[3/(p-1) + 2/(p-1)^2].        (UT7)

For owner v use its actual finite parent union A_v. Expanding a square
of the full remaining cofactor sum and applying UT6 gives the moment
majorant

    M(v) <= product_(p in A_v) T_p(c_p)
         <= product_(3<=p<v, p prime) T_p(c_p).      (UT8)

The second inequality pads missing parent primes by factors greater than
one. Including the zero exponent vector also enlarges the moment; it
does not add a second actual pure-power original.

Here is the full owner-height argument. For parent exponent vector e
and owner height h, let I_(e,h) be the indicator of its actual parent
congruences, or zero if that numerical modulus is absent. The base
forbidden fraction is at most

    t <= (1/(v-3)) sum_e sum_(h>=1) w_h I_(e,h),
    w_h = (v-1)v^(-h), sum_(h>=1) w_h = 1.           (UT9)

This follows from UT3 and the union bound for the actual owner cylinders.
Numerical distinctness gives at most one actual label at each pair (e,h).
Different heights may have different globally fixed parent phases; the
intersection bound UT6 is valid for each such pair. Consequently UT4,
UT6 and UT9 give, under this same Pi,

    Pi(owner-v violation) <= M(v)/(v-3)^2.           (UT10)

All cross terms between different syntactic tuples occur in this single
square. All finite original heights are retained; the infinite geometric
sums are convergent nonnegative upper bounds on their finite inventories.

## 4. A finite correction and a complete Euler-product bound

For p >= 971 put u = 1/(p-1). The binomial coefficients give

    T_p(4) = 1+12u+8u^2
           <= (1+u)^12 = (1-1/p)^(-12).             (UT11)

Keep every finite exception by defining the exact rational correction

    A = product_(3<=p<971, p prime)
                   T_p(c_p)(1-1/p)^12.             (UT12)

Multiplying all ten head caps and all 152 actual finite outside caps
gives

    0 < A < 3/1000.                                 (UT13)

The exact value is retained in the certificate; its decimal value is
approximately 0.0028640807766858074. No factor below one has been
discarded, and no finite cap has been replaced by 4. Since v >= V > 971,
all small primes occur in the padded product UT8, so UT11--UT13 imply

    M(v) <= A [product_(3<=p<v, p prime)
                                  (1-1/p)^(-1)]^12. (UT14)

We use an elementary uniform estimate: for every integer k >= 2,

    product_(3<=p<=2^k, p prime) (1-1/p)^(-1)
       <= 4(k+1).                                  (UT15)

To prove it, in a dyadic band 2^(j-1) < p <= 2^j every such prime
divides the central binomial coefficient choose(2^j,2^(j-1)). The product
of these distinct primes therefore divides it. Since the binomial
coefficient is at most 2^(2^j),

    sum_(2^(j-1)<p<=2^j) log p <= 2^j log 2.

For odd primes in this band, p-1 >= 2^(j-1). Summing j = 2,...,k gives

    sum_(3<=p<=2^k) log p/(p-1) <= 2k log 2.         (UT16)

Set s = 1+1/k. Expand the logarithms of the two finite Euler products.
The inequality 1-exp(-u) <= u for u >= 0 gives

    log product_p [(1-p^(-s))/(1-p^(-1))]
      = sum_p sum_(m>=1) (p^(-m)-p^(-sm))/m
      <= (1/k) sum_p log p/(p-1) <= log 4.          (UT17)

All primes here are odd and at most 2^k. Unique factorization and the
positive geometric expansions show

    product_p (1-p^(-s))^(-1) <= sum_(n>=1) n^(-s)
      <= 1 + integral_(1 to infinity) t^(-s) dt
      = k+1.                                      (UT18)

Multiplying UT17 and UT18 proves UT15. All the displayed infinite series
converge at s > 1, and the logarithmic series for each of the finitely
many factors at exponent 1 also converge. No external prime asymptotic
or finite prime cutoff is needed.

## 5. The entire arbitrary-parent prime tail

For a prime in 2^k <= v < 2^(k+1), UT14 and UT15 give

    M(v) <= A[4(k+2)]^12.

For k >= 109, v-3 >= 2^(k-1). The band contains exactly 2^(k-1) odd
integers; overcounting primes by all of them gives

    sum_(2^k<=v<2^(k+1), v prime) M(v)/(v-3)^2
      <= B_k := 2A[4(k+2)]^12 2^(-k).               (UT19)

Its successive ratio decreases with k, and at k = 109 is

    B_(k+1)/B_k = (1/2)((k+3)/(k+2))^12
      <= (1/2)(112/111)^12 < 3/5.                  (UT20)

Thus for every K >= 109 the complete tail, not a finite window, satisfies

    W_large(K) <= sum_(k>=K) B_k
      <= 5A[4(K+2)]^12 2^(-K)
      < (15/1000)[4(K+2)]^12 2^(-K) =: E_K.        (UT21)

Two exact readings are

    E_115 = 19740202146111572828188083
              /495176015714152109959649689600,
    E_109 = 10495351790806902569309763
              /7737125245533626718119526400.        (UT22)

These are respectively approximately 0.000039865020759622 and
0.0013564924255123703. Every actual finite family has finitely many
owners and finite parent unions. The positive infinite sum UT21
majorizes all of them uniformly, without a maximum parent count.

## 6. Common-law budget and simultaneous gluing

All old Report620 fee estimates require UT1 and the conditional cap
p/4. Every new row satisfies that cap by UT5, and all earlier rows are
unchanged. Hence the old estimates hold on this new joint Pi; they are
not imported from an independently favorable old probability law.

Pay the whole old Report620 bound for owners below V, even though that
bound also charged old rows at primes above V. In addition pay UT21 for
the actual new rows at v >= V. This is a conservative sum of nonnegative
bounds. Each actual owner uses only one row. The inherited head-bad and
ordinary Type I payments leave the raw reserve

    R = 147/5000 - 531/20000 - 1/65536
                    - 1/1250 - 1/10^7
      = 10417363/5120000000.                        (UT23)

Consequently Pi(good) > R-E_K. Projecting this good set to the head
uses the full density C in UT1, giving

    H_P(U_ext) > alpha(R-E_K).                      (UT24)

Exact arithmetic yields

    alpha(R-E_115)
      = 8250927239526750261442876276861281
          /214039832792442249530058578329600000000
      > 1/26000,

    alpha(R-E_109)
      = 43828196065829974682348993091729
          /3344372387381910148907165286400000000
      > 1/80000.                                   (UT25)

The surviving joint configurations satisfy all head and owner tests in
one actual assignment. Each owner lies in its ordinary extension domain,
so the declared private witnesses and separate ordinary components can
be filled simultaneously by the inherited disjoint-interface argument.
CRT then gives an integer avoiding every original congruence class.
For each extendible head configuration there is at least one outside
assignment among Q_off possibilities, which gives the full-density
bounds in the opening statement. These bounds still depend on the
actual outside heights through Q_off.

The unresolved hypotheses are the complete head conditions, Report620's
small-owner restrictions below V, and the ordinary private-interface
restrictions. Neither taking a very large V nor bounding its entire tail
removes those conditions. What is new is that no additional parent-count
restriction remains at any owner above the same universal V.

## Exact certificate

The [producer](../../frontier/cover-geometry/uniform_large_owner_forward_kernels.py)
and [data](../../frontier/cover-geometry/uniform_large_owner_forward_kernels.json)
retain all 162 actual small-prime cap factors, their full rational
correction, current Report619/620 source bindings, dyadic ratio and
complete-tail constants, and both positive head bounds. The 192 exact
checks pass with Python optimization enabled. The universally quantified
arguments are UT6--UT21; finite checks do not replace them.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/uniform_large_owner_forward_kernels.py

No new Lean source was added or compiled for this result.
