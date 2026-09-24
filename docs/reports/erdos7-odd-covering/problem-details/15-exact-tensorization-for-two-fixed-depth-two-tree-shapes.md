[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md) · [Next](16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md)

<a id="exact-tensorization-for-two-fixed-depth-two-tree-shapes"></a>
### Exact tensorization for two fixed depth-two tree shapes

Let `p,q` be distinct odd primes. Consider probability laws on residues
modulo `p²` and `q²`, each supported on four leaves in two depth-one roots.
For either of the following two cases, with arbitrary real nonnegative
probability weights on the four leaves, one has

\[
 \Gamma_{p^2q^2}(\mu\times\nu)
   =\Gamma_{p^2}(\mu)\Gamma_{q^2}(\nu).
 \tag{TT}
\]

The two cases are separate: both root partitions are `2+2`, or both are
`3+1`. Leaves may have zero weight. Residues `0,p,1,p+1` realize `2+2`;
residues `0,p,2p,1` realize `3+1`. The analogous choices work modulo `q²`.
These statements do not cover a product of different shapes, additional
roots, higher powers or arbitrary complete-survivor supports. They supply
no new numerical covering-head bound.

A complete one-coordinate test layout contains divisor one, one chosen
root cylinder and one chosen leaf cylinder. Root and leaf choices are
independent; the leaf need not lie in the selected root. Every cylinder
with zero intersection with the support can be replaced by a supported
cylinder without decreasing the load. Hence the two roots and four leaves
give exactly eight relevant one-coordinate choices. If `x` is a probability
vector, write their squared-load vectors as `s_0,…,s_7`. Then

\[
 \Gamma(x)=\max_{0\le i<8}s_i\cdot x.
\]

For `3+1` these vectors, ordered by root and then leaf, are

\[
 (9,4,4,1),\ (4,9,4,1),\ (4,4,9,1),\ (4,4,4,4),
\]
\[
 (4,1,1,4),\ (1,4,1,4),\ (1,1,4,4),\ (1,1,1,9).
\]

In particular the nonnested constant-load branch `(4,4,4,4)` is retained.
For example `(21,21,21,37)/100` has `Γ=4`, attained by selecting the
three-leaf root and the other root's leaf. Its two nested alternatives have
values `197/50` and `99/25`, both strictly smaller. The verifier derives
the corresponding eight vectors directly for each fixed root partition.

For each `i`, let

\[
 P_i=\{x\ge0:\ \textstyle\sum_jx_j=1,
                \ (s_i-s_k)\cdot x\ge0\text{ for every }k\}.
\]

These compact rational polytopes cover the probability simplex, and
`Γ(x)=s_i·x` on `P_i`. A vertex in this three-dimensional normalization
hyperplane has three linearly independent active inequalities. Enumerating
all triples, solving with exact signed minors, normalizing and checking all
inequalities therefore gives every vertex. Empty and lower-dimensional
regions are handled by the same enumeration; a nonempty compact polytope
has a vertex.

A complete product layout chooses one product cylinder independently for
each exponent pair in `{0,1,2}²`. All nine divisors, including old-only and
mixed cofactors, are present. The choices total

\[
 2\cdot4\cdot2\cdot4\cdot8\cdot4\cdot8\cdot16=262144.
\]

For any such layout, let `M` be its squared-load matrix on the sixteen
supported point pairs. Its second moment under `x×y` is `xᵀMy`. On
`P_i×P_j` the proposed upper-bound margin is

\[
 (s_i\cdot x)(s_j\cdot y)-x^{\mathsf T}My,
\]

which is bilinear. Minimizing a linear function on the first polytope and
then on the second proves that its minimum occurs at a pair of vertices.
Thus it suffices to compare every complete layout at every pair from the
union of all local polytope vertices.

The fixed certificate gives these exact counts:

| Root partition | Vertex counts for the eight local regions | Distinct vertices | Vertex pairs | Integer comparisons |
| --- | --- | ---: | ---: | ---: |
| `2+2` | `8,8,0,0,0,0,8,8` | 15 | 225 | 58,982,400 |
| `3+1` | `10,10,10,4,0,0,0,10` | 18 | 324 | 84,934,656 |

The standalone standard-library plus NumPy verifier recomputes every
polytope vertex using rational arithmetic and checks every displayed
integer comparison. For every vertex pair, the maximum layout moment
numerator equals the product of the two local Gamma numerators. These
checks prove the upper bound in (TT). The reverse inequality follows for
all weights by choosing the product of two maximizing one-coordinate
layouts, whose complete product load factors pointwise.

The integer arithmetic has an explicit overflow bound. A full product load
is between one and nine. After clearing each vertex's denominator, the
maximum integer weight sum is 27 for `2+2` and 40 for `3+1`. Consequently
all moment numerators and local-Gamma products are at most
`81·27²=59049` and `81·40²=129600`, respectively. The verifier checks these
bounds before and after the `int64` comparisons. It uses explicit errors,
so optimized Python retains every check.

The [standalone verifier](../verify_two_root_tensorization.py)
and [fixed rational certificate](../certificates/two_root_tensorization_certificate.json)
are the complete runtime artifacts. The default invocation verifies
both fixed shapes; `--shape 2+2` or `--shape 3+1` selects one. This is an
ordinary mathematical polytope reduction with exact integer verification;
no Lean formalization or general tensorization theorem is claimed.

<a id="coherent-constant-potential-does-not-bound-actual-gamma"></a>
### Coherent constant potential does not bound actual Gamma

The coherent-center potential is not an upper bound for arbitrary test
layouts, even in one prime coordinate. For the ternary `RestrictedSpine`
of height 4, with side digit 1, spine digit 2 and layer weights `3,5,7,9`,
the recurrence law has 41 supported residues modulo 81. Its per-leaf
weights on the disjoint groups `1 mod 3`, `5 mod 9`, `17 mod 27`, `{53}`
and `{80}` are respectively `3671/174309`, `4628/174309`, `5980/174309`,
`2600/58103` and `2600/58103`; their cardinalities are `27,9,3,1,1`.
Every supported center has coherent score `248995/58103`, and every
other center has score at most that value. The nonnested layout with
residues `(2 mod 3, 8 mod 9, 17 mod 27, 53 mod 81)` instead has score
`249255/58103`, exceeding it by `260/58103`. Exact enumeration of all
`2*5*14*41=5740` supported-cylinder layouts proves that this latter score
is the actual `Gamma`. Unsupported cylinders have zero mass, so replacing
them by supported cylinders cannot decrease the load; the enumeration
therefore also determines the unrestricted maximum. The
[existing exact verifier](../verify_star_survivor_obstruction.py)
checks all 81 coherent centers and all 5740 layouts against its
[certificate](../certificates/star_survivor_obstruction_certificate.json).
This refutes only the bridge from a coherent-potential bound to an
actual-`Gamma` upper bound. It does not refute product tensorization or
the existing star-family lower-bound argument, which uses a law of test
centers. The finite computation is an exact certificate, not a Lean
formalization.

<a id="the-boundary-of-scalar-fibre-reweighting"></a>
### The boundary of scalar fibre reweighting

The conditional-cap criterion alone does not improve the optimized T6
recurrence. Within the scalar certificate described below, arbitrary
reweighting of old fibres and the exact bounded second-moment inequality
reduce to the BBMST clipping rule and its optimized T6 value. This is a
limitation of that certificate, not an impossibility theorem for actual
covering systems or for reweighting that retains joint-layout information.

Moreover, for every prime p>=13 there is an actual distinct-modulus
family and two old survivor laws with identical Gamma, R, exact density
cap 16/15, and first two forbidden-fibre moments, but different feasibility
for the same pair of old-marginal and conditional-density caps. Thus those
scalars do not determine the missing capacity information even for actual
congruence families.

<a id="1-the-scalar-certificate-and-its-optimal-weight"></a>
#### 1. The scalar certificate and its optimal weight

Let mu be a probability on a finite old survivor carrier X, let U be
uniform on Y=Z/p^H, and let B_x be the actual new forbidden union in row x.
Write alpha(x)=U(B_x), s(x)=1-alpha(x), and Gamma(mu)<=G. As in T1, set
a=sum_{e=1}^H (2e+1)p^{-e}, or use its infinite-height upper bound.

Choose a nonnegative old-row multiplier h, zero on rows where s=0.
Give each surviving point of row x raw density h(x)/s(x) relative to
mu(x)U(y), and normalize by Z=E_mu h>0. The old marginal of the resulting
complete-survivor law is h mu/Z. For a positive raw measure rho extend
Gamma homogeneously: Gamma(rho)=max_L integral L^2 d rho.

The weighted joint-layout transfer W1 gives

    Gamma(new law) <= [Gamma(h mu)+a Gamma((h/s)mu)]/Z.       (1)

The ratio h/s is defined to be zero on s=0. This follows by bounding each
positive outside-prefix mass by p^{-e}/s(x), then retaining the weighted
old-layout moment until the final step. It includes every old cofactor.
No fibre with s=0 is assigned positive mass.

Consider the scalar certificate that replaces the two weighted moments by

    h<=1, h/s<=C, C>=1
    ==> Gamma(new law) <= G(1+aC)/E h.                     (2)

Here C bounds the raw joint-density multiplier h/s, not the normalized
conditional multiplier 1/s. Clipping can keep a row with s<1/C by
reducing its old mass. A law required to satisfy the conditional cap
must instead remove that row, as in the separate capacity criterion.

At fixed C its pointwise largest feasible h is

    h_C(x)=min(1,C s(x)).                                 (3)

Every competing weight satisfies h<=h_C, so (3) maximizes the denominator
in (2) while preserving its numerator. It therefore gives the best value
certified by (2) at fixed caps. This statement concerns the scalar bound:
another h can have better actual weighted moments in (1).

Write C=1/(1-delta), 0<=delta<1. Then

    E h_C = 1 - E b_delta(alpha),
    b_delta(t)=(t-delta)_+/(1-delta).                      (4)

The raw surviving-point density is 1/(1-alpha) when alpha<=delta,
and 1/(1-delta) otherwise. This is exactly the complete-survivor part
of the BBMST clipped law, followed by normalization. Unlike the full
BBMST law, this restricted law carries no forbidden points.

<a id="2-sharp-bounded-second-moment-loss-and-optimized-t6"></a>
#### 2. Sharp bounded second-moment loss and optimized T6

Suppose 0<V<1 and E alpha^2<=V, with 0<=alpha<=1. The exact worst value
of E b_delta(alpha) over all such scalar probability distributions is

    q(V,delta) = V/[4delta(1-delta)]
                 if 0<delta<=1/2 and V<=4delta^2;
               = (sqrt(V)-delta)/(1-delta)
                 if 0<=delta<=1/2 and V>=4delta^2;
               = V
                 if 1/2<=delta<1.                        (5)

The formulas agree at their common boundaries, including delta=0.
For delta<=1/2, view b_delta(t) as a function of u=t^2. Its least
concave majorant is the line from (0,0) tangent at u=4delta^2, followed
by (sqrt(u)-delta)/(1-delta). Jensen's inequality gives (5).
For V<=4delta^2 equality is attained by alpha in {0,2delta}, with mass
V/(4delta^2) at 2delta. For V>=4delta^2 equality is attained by the
constant alpha=sqrt(V). For delta>=1/2, b_delta(t)<=t^2 on [0,1], and
the distribution with mass V at alpha=1 and 1-V at zero gives equality.
These extremizers certify the scalar moment problem; no realizability
claim for every extremizer as a congruence family is made.

Consequently the best guarantee from (2) and the bounded second moment is

    inf_{0<=delta<1} G[1+a/(1-delta)]/[1-q(V,delta)].       (6)

For 0<=delta<=sqrt(V)/2, the expression is

    G(1-delta+a)/(1-sqrt(V)),

which decreases as delta increases. For delta>=1/2 its denominator is
1-V and its numerator increases. Hence the optimum is attained in
[sqrt(V)/2,1/2], exactly the region where (5) is the ordinary quadratic
BBMST loss. Thus (6) equals

    min_{0<delta<=1/2}
      G[1+a/(1-delta)]/[1-V/(4delta(1-delta))],             (7)

where only positive denominators are admitted. No smaller threshold
outside the interval can improve it: there the quadratic loss only
overestimates (5), whose best boundary value already occurs inside.

For a>0 the unique minimizing threshold solves

    a delta^2 + (V/2)delta - (1+a)V/4 = 0,

and is

    delta_*=[sqrt(V^2+4a(1+a)V)-V]/(4a).                  (8)

Substitution into the quadratic shows sqrt(V)/2<=delta_*<=1/2.
If a=0 the endpoint delta=1/2 attains the minimum. Taking
V=G/(p-1)^2 and a=(3p-1)/(p-1)^2 recovers optimized T6 exactly.

This rules out a strict improvement merely from using the sharp bounded
second-moment problem instead of t^2/(4delta), or from replacing BBMST
clipping by another h certified only through the two supremum caps in (2).
It does not rule out improvements from the known lower bound L^2>=1,
the actual prefix occupancies, a first-moment constraint, or the weighted
moments in (1). Those additional facts lie outside certificate (2).

<a id="3-hard-fibre-trimming-is-dominated"></a>
#### 3. Hard fibre trimming is dominated

Keeping only rows alpha<=delta and making their conditional law uniform
gives conditional density cap 1/(1-delta). Using only Markov's inequality
from E alpha^2<=V certifies retained mass at least 1-V/delta^2, and hence

    G[1+a/(1-delta)]/[1-V/delta^2].                        (9)

For delta<=1/2, T6 at the same threshold has the same numerator and a
larger denominator, since delta^2<4delta(1-delta). For delta>=1/2,
T6 at threshold 1/2 improves both numerator and denominator: its loss
is V, at most V/delta^2. Thus every positive-denominator hard-trimming
certificate (9) is dominated by a T6 certificate. The result is unchanged
if V came from multiplying a reference-law moment bound by an RN cap.

<a id="4-concrete-obstruction-to-scalar-capacity-closure"></a>
#### 4. Concrete obstruction to scalar capacity closure

Fix any prime p>=13. The old period is 15 and its only forbidden class
is 0 mod 3. Identify its survivor carrier with {1,2} x Z/5 by CRT.
The two old laws below are uniform on {1,2}; only their 5-coordinate
weights differ.
The 5-coordinate is an unused padded old coordinate: the old actual
modulus lcm is 3. This is an arbitrary finite distinct-modulus family,
not an assignment of a forbidden class to every nonunit divisor of 15.

Let T=p^2+p+1, epsilon=1/(120pT), and define

    v=(1,-T,pT,-p^3),
    nu_+(0)=nu_-(0)=16/75,
    nu_+(j)=59/300+epsilon v_j,
    nu_-(j)=59/300-epsilon v_j,  j=1,2,3,4.               (10)

The identities sum v_j=0 and |epsilon v_j|<=1/120 show that both are
strictly positive probability laws; every j>0 weight is at most
59/300+1/120=41/200<16/75. Hence they have the same maximum weight
16/75, attained at zero.

For the old period 15, the complete layout has the four divisors
1,3,5,15. Every cylinder and every intersection is bounded by the
appropriate product of the maximum ternary and quinary masses. These
individual maxima are attained simultaneously by taking all test
classes through one point of maximum mass. Therefore, for both laws,

    Gamma = (1+3/2)(1+3*(16/75)) = 41/10,
    R = 1/2+16/75+(1/2)(16/75) = 41/50,
    max dmu/dU_old_survivors = 5*(16/75) = 16/15.          (11)

Adjoin a p-coordinate of height four. Forbid 0 mod p, and for each
j=1,2,3,4 forbid the CRT class

    x_5=j mod 5,  y=1 mod p^j,

whose modulus is 5p^j. These moduli and the old modulus 3 are distinct.
The mixed classes are disjoint from the pure p exclusion because their
p-residue is one. Within each old row their forbidden density is exactly

    alpha(0)=1/p,
    alpha(j)=1/p+p^{-j}, j=1,2,3,4.                       (12)

There are no empty fibres; alpha<=2/p<1. The construction neither
assumes nested test layouts nor introduces multiple classes per modulus.

The four-vector in (10) obeys

    sum_j v_j p^{-kj}=0, k=0,1,2.                        (13)

For k=1,2, multiply by p^{4k}; the resulting polynomials vanish by
direct expansion. Consequently both laws have the same E alpha and
E alpha^2 as well as all three scalar invariants in (11). Their common
moments are

    E alpha = 1/p+(59/300)sum_{j=1}^4 p^{-j},
    E alpha^2 = 1/p^2+(59/150p)sum_{j=1}^4 p^{-j}
                       +(59/300)sum_{j=1}^4 p^{-2j}.     (14)

Now require conditional density cap C=2p/(2p-3) at every depth and
old-marginal reweight cap D=300/241. Since 1-1/C=3/(2p), the good set
{s>=1/C} consists of exactly the rows with x_5!=1. Its two masses are

    mu_+(good)=241/300-epsilon < 1/D,
    mu_-(good)=241/300+epsilon > 1/D.                     (15)

The corresponding raw weighted joint-layout moments also differ:

    Gamma(1_good mu_+) = 433/120-(5/2)epsilon,
    Gamma(1_good mu_-) = 433/120+(5/2)epsilon.              (16)

Indeed the maximum quinary point weight remains 16/75, so the raw
product moment is (5/2)[mu(good)+3*(16/75)]. This is a concrete instance
of weighted information required in (1) that the listed scalars omit.

The exact fibre-cap criterion therefore makes the requested law
impossible for mu_+ and feasible for mu_-. In the feasible case restrict
mu_- to good rows, normalize, then use the uniform conditional survivor
law; its old density factor is 1/mu_-(good)<D. In the impossible case
the singleton caps force support inside good, whose available old mass
under the cap D is less than one.

This is an actual-family distinction with identical Gamma, R, RN cap,
and first two forbidden-fibre moments. It does not preclude a universal
upper recurrence using worst-case values of those scalars. It proves
that they cannot determine exact reweighting feasibility or reconstruct
the weighted joint-layout profiles discarded in (2). No assertion is
made that the two laws are the specific NC1 adaptive policy; they share
its stated density bound, showing that this bound alone is insufficient.

<a id="5-consequence-at-the-current-four-prime-seed"></a>
#### 5. Consequence at the current four-prime seed

At G=4939031/47730 and p=13 put V=G/144 and a=19/72. Every admissible
T6 value exceeds 256. After multiplying a proposed comparison with 256
by its positive denominator and by 4delta, the excess numerator is

    4(256-G)delta^2 + 4[(G-256)+aG]delta + 256V.

Its global quadratic minimum is strictly positive, verified exactly in
the accompanying certificate. Thus even the optimal scalar-fibre
certificate (6) produces a bound greater than 16^2 at the first new
prime. At the next prime 17 its implied second-moment bound is greater
than one, so this certificate gives no positive universal retained mass.
This failure concerns the supplied seed bound and this proof language,
not the actual optimal measure or the Erdos #7 assertion.

`verify_fibre_scalar_boundary.py`, with `fibre_scalar_boundary_certificate.json`, checks exact extremizing distributions for (5),
the quadratic comparison at p=13, identities (10)-(16) for the requested
primes 13 through 61, and the complete actual p=13 residue assignment.
The continuous arguments and all-prime identities above carry the
universal statements; finite checks are boundary verification, not proofs
by enumeration over a bounded collection of families.

The reusable starting points are the repository's weighted rectangle
transfer W1 and the finite conditional-cap criterion. Public BBMST
1811.03547, section 2, Lemmas 2.1-2.2 and 1901.11465 give the clipping
kernel and its distortion bounds, but no weighted-layout correlation
bound closing (1). Koperberg 2202.02092, Theorem 1, supplies the different
global marginal Hall criterion. No new Lean declaration or full Lean
formalization is asserted here.

<a id="random-tail-extensions-give-pointwise-layout-certificates"></a>
### Random tail extensions give pointwise layout certificates

For the explicit complete height-four congruence family specified below,
every probability mu on its actual survivor set satisfies

    Gamma(mu) >= C = 121.54782913540919... .

Here Gamma is the maximum second moment of one complete divisor layout.
The fixed certificate gives C as an exact rational number and verifies a
pointwise lower bound at all 791 coarse survivor residues. The number is
below 138877/1000. It supplies neither an upper bound on Gamma nor a proof
of the Gamma-73 assertion or its negation. The construction below is a
reusable evaluator for finite distributions of layouts; no optimality of
the supplied distribution is required.

<a id="a-random-extension-of-an-arbitrary-complete-layout"></a>
#### A random extension of an arbitrary complete layout

Let P be a finite set of distinct primes, choose caps c_p>=1 and heights
H_p>=c_p, and put

    Q_c = product_p p^c_p,       Q_H = product_p p^H_p.

A coarse layout assigns b_d modulo d to EVERY d dividing Q_c, including
one. No compatibility between b_d and b_e is assumed. For D dividing Q_H,
write d=clip(D)=gcd(D,Q_c). Independently for each prime choose a uniform
T_p modulo p^(H_p-c_p). Define a residue for D in its p-coordinate by

    b_d mod p^a                         if a=v_p(D)<=c_p,
    (b_d mod p^c_p)+p^c_p T_p mod p^a  if a>c_p.

CRT gives a unique residue b_D(T) modulo D. Thus each value of T gives
one genuine complete fine layout. It restricts to b on the coarse
divisors. There is no separate random choice for each test modulus or
coarse root: one shared T_p suffices.

For x modulo Q_H let x_0 be its reduction modulo Q_c, and set

    I_d(x_0) = 1{x_0=b_d mod d},
    L_b(x_0) = sum_{d|Q_c} I_d(x_0).

Write L_p=H_p-c_p and

    S_p = sum_{t=0}^{L_p} p^(-t),
    V_p = sum_{t=0}^{L_p} (2t+1)p^(-t).

For coarse divisors d,e define W_de as the product over p of the factor

    1    if neither v_p(d) nor v_p(e) is c_p;
    S_p  if exactly one is c_p;
    V_p  if both are c_p.

Then the exact random-extension identity is

    E_T [L_{b(T)}(x)^2]
       = sum_{d,e|Q_c} W_de I_d(x_0) I_e(x_0).             (1)

To prove it, expand the square over ordered pairs of fine divisors D,E.
If either coarse indicator is zero, the corresponding product is zero
for every T. If both are one, every positive extra p-height t imposes

    T_p = floor(x_p/p^c_p) mod p^t.

The target is the same for both divisors, even though the original coarse
layout was arbitrary. The two conditions have simultaneous probability
p^(-max(t,u)). If only one fine divisor has positive extra height, the
same formula applies with the other height zero. Across primes these
probabilities multiply. Finally, the map from a fine divisor to its
coarse divisor and allowed extra exponents is a bijection. Summing all
extra exponents gives S_p in the one-capped case, and

    sum_{t,u=0}^{L_p} p^(-max(t,u))
       = sum_{t=0}^{L_p} (2t+1)p^(-t) = V_p

in the two-capped case. This proves (1) and accounts for all fine
divisors, all ordered cross terms, and the divisor-one term.

For comparison, if the coarse layout is coherent, its top p-cylinder
coefficient becomes

    2c_p S_p+V_p
      = sum_{e=c_p}^{H_p} (2e+1)p^{-(e-c_p)}.

This recovers direct averaging of a coherent center's finer digits.
Also V_p>=S_p^2: these are the second and first moments of the same
random nested-prefix load. Neither fact assumes that arbitrary layout
suprema tensorize.

<a id="exact-center-probabilities-on-a-pure-survivor-tree"></a>
#### Exact center probabilities on a pure survivor tree

For an outside prime p>=3, forbid exactly one class at each depth,

    a_(p^e) = (p^(e-1)-1)/(p-1),        1<=e<=H.

Its p-adic digits are e-1 copies of 1 followed by a 0. The forbidden
classes are pairwise disjoint. The surviving tree has at every critical
node one dead child (digit 0), p-2 complete children, and one continuing
critical child (digit 1). Let S_p be the set of surviving leaves.

A coherent center b has load

    ell_b(x) = 1+sum_{e=1}^H 1{x=b mod p^e},

and hence symmetric kernel

    K_p(x,b)=ell_b(x)^2
       =1+sum_{e=1}^H (2e+1)1{x=b mod p^e}.               (2)

The following finite construction gives a probability nu_p supported on
S_p whose potential sum_b nu_p(b)K_p(x,b) is exactly g_p for every x in
S_p and at most g_p on all leaves. It does not assert that g_p is the
minimum of the full, potentially incoherent layout objective.

Let F_e,C_e be the equal-potential costs of complete and critical
subtrees entered at depth e, including that depth's coefficient 2e+1.
Initialize F_H=C_H=2H+1, then for e=H-1,...,1 use

    F_e = (2e+1)+F_(e+1)/p,
    C_e = (2e+1)+[(p-2)/F_(e+1)+1/C_(e+1)]^(-1).        (3)

Finally set

    g_p = 1+[(p-2)/F_1+1/C_1]^(-1).                     (4)

All denominators are positive. The probability construction is explicit:
in a complete node distribute mass equally among its p children; in a
critical node whose live child costs are r_j, give child j the fraction

    alpha_j = (1/r_j)/(sum_k 1/r_k).

There are p-2 children of cost F and one of cost C. Thus the fractions
sum to one and alpha_j r_j is the same number for every live child.
Inductively the potential within each live subtree is constant; adding
the common prefix coefficient proves (3). The root has common
coefficient one and proves (4). A point in a dead branch receives no
further contribution, so its potential is no larger. This proves the
claimed equality on S_p and inequality off it.

The same calculation is the elementary parallel-resistance identity

    min_{alpha_j>=0, sum alpha_j=1} sum_j r_j alpha_j^2
       = (sum_j 1/r_j)^(-1).

Equality holds at the displayed fractions, and weighted Cauchy--Schwarz
proves the lower inequality. Symmetry of (2) consequently shows that
g_p is the exact value of the pure COHERENT-center game: use nu_p as a
distribution of centers for its lower bound, and as the point law for its
upper bound. The present certificate only needs its pointwise lower half.

<a id="combining-the-core-and-outside-potentials"></a>
#### Combining the core and outside potentials

Let R_c be any coarse survivor set. Choose a finite probability
rho=(rho_j) on coarse complete layouts b^(j), and form

    Phi(x_0)=sum_j rho_j sum_{d,e|Q_c}
                    W_de I_d^(j)(x_0) I_e^(j)(x_0).

Suppose Phi(x_0)>=m for every x_0 in R_c. Sample j and the shared tails
T_p, and independently sample each outside center from nu_p. For a full
divisor D=D_core D_out, take the CRT join of its extended core residue
and the outside center residues. This again assigns one residue to every
full divisor. For each realization its load factors exactly as

    L_full(x)=L_core(x_core) product_{p outside} ell_(b_p)(x_p),

because the complete divisor index is the Cartesian product of its core
and outside divisor indices. Squaring and averaging this particular
random construction, using (1)--(4), gives at every point with
x_0 in R_c and x_p in S_p

    E_layout L_full(x)^2 = Phi(x_0) product_{p outside} g_p
                         >= m product_{p outside} g_p.    (5)

The actual full survivor set may be a proper subset of these points;
additional forbidden classes do not invalidate (5). For ANY probability
mu on that actual survivor set, interchange the two finite averages and
bound their layout average by the maximum over complete layouts:

    Gamma(mu) >= E_layout E_mu L_full^2
               >= m product_{p outside} g_p.              (6)

There is no independence assumption on mu. Independence is used only
for the explicitly constructed random layout, whose distribution is
under our control.

<a id="the-fixed-rational-certificate"></a>
#### The fixed rational certificate

The instance uses core caps (3,3),(5,2),(7,1), so Q_c=4725, and common
full height H=4 at all 20 odd primes through 73. The JSON specifies all
23 nonunit coarse forbidden residues. Direct enumeration leaves exactly
791 coarse residues. All outside primes are at least 11 and use the
pure classes in (2)'s construction.

For definiteness this extends to a complete nonempty forbidden family.
Choose w by CRT with w=3 modulo 4725 and w=-1 modulo the product of the
outside fourth powers. Keep the coarse assignments and outside pure
assignments, and for every other nonunit divisor d of the full modulus
forbid (w+1) mod d. The point w survives: it survives the coarse and pure
assignments, while equality with the last residue would imply d divides
1. The verifier constructs and checks such a witness. In particular the
lower bound is about actual probability laws on a nonempty survivor set.

There are 738 listed coarse layouts with positive integer numerators
summing to 10^10. The coherent all-zero layout has numerator 363; it
completes the listed rational probability. All 24 coarse divisors,
including one, appear in every row. The shared-tail random domain has
cardinality 25725. The matrix W has common denominator 25725, and the
verifier reconstructs it in two ways: the three local formulas and direct
summation over all 125^2 ordered fine-core divisor pairs.

`random_tail_layout_certificate.json` contains every coarse potential with common denominator
10^10 times 25725. Exact evaluation gives

    m = 413450618877603/21437500000000
      = 19.28632624501938...,

with the minimum attained at coarse residue 4134. Equations (3)--(4) give

    product_{outside p} g_p = 6.302280050188326... .

Multiplying by m gives

    C = 121.54782913540919... < 138.877.

The full fraction, all 791 potential numerators, every outside recurrence
value and child probability, and the positive comparison margin
138877/1000-C are stored and recomputed in the fixed certificate.

verify_random_tail_layout_certificate.py uses only the Python standard
library. It accepts an optional certificate path so that other coarse
families and layout distributions can use the same evaluator. It reads
no NPZ arrays, saved solver rows, numerical dual values, repository files,
or external libraries. Normal, optimized (-O), and isolated (-I) runs all
exit zero. The layout correspondence and tree induction above are ordinary
mathematical proofs; no Lean kernel certification is claimed.

The existing H73 lower bound exceeding 162.1563 concerns the separate
cylinder-maxima quantity kappa. Since Gamma<=kappa, that result does not
supply or dominate a Gamma lower bound. The existing uniform-survivor
score above 142.3789923 concerns a different family and only its uniform
law. It does not dominate the all-supported-laws conclusion (6). No
stronger same-family Gamma lower bound is used or asserted here.
