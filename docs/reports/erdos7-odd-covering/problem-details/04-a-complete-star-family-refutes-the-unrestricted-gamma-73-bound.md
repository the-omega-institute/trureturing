[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md) · [Next](05-unrestricted-axis-deletions-a-complete-head-bound.md)

<a id="a-complete-star-family-refutes-the-unrestricted-gamma-73-bound"></a>
### A complete star family refutes the unrestricted Gamma-73 bound

Let P be the 20 odd primes at most 73. Choose H_3>=31 and H_p>=8 for
p>=5, and put Q=product_(p in P) p^H_p. There is one actual forbidden
residue for every nonunit divisor of Q, with a nonempty survivor set R,
such that every probability mu supported on R satisfies

    Gamma_Q(mu) > 13959/100 > 138877/1000.                  (1)

Here Gamma_Q(mu) is the maximum over all complete test layouts
b=(b_d mod d)_(d|Q) of the second moment of
L_b(x)=sum_(d|Q) 1[x=b_d mod d], including d=1. The counterexample concerns
this universal arbitrary-prime-power survivor-measure assertion. It does
not refute the odd distinct covering-systems conjecture: the family
below explicitly has survivors. The proof uses only coherent complete
layouts for its lower bound, while mu may have arbitrary correlations.

<a id="the-actual-complete-forbidden-assignment"></a>
#### The actual complete forbidden assignment

In the CRT p-coordinate define, for 1<=e<=H_p,

    F_(p,e) = {x_p = p^(e-1)-1 mod p^e},
    C_(p,e) = {x_p = 2p^(e-1)-1 mod p^e},
    S_p = (Z/p^H_p Z) minus union_e F_(p,e),
    C_p = union_e C_(p,e),       D_p = S_p minus C_p.

For each pure-power divisor p^e forbid F_(p,e). For each divisor 3^i p^j
with p>=5 and i,j positive, forbid the unique CRT residue specifying
C_(3,i) and C_(p,j). For every other mixed divisor forbid zero. This
specifies exactly one residue for each distinct nonunit divisor. The
last classes are redundant: a zero mixed residue is already zero modulo
one of its prime factors, and F_(p,1) forbids zero modulo p.

Read digits from least significant to most significant. F_(p,e) has
first e-1 digits p-1 and next digit zero. C_(p,e) has the same prefix
and next digit one. Hence S_p consists of points whose first digit
different from p-1 belongs to {1,...,p-2}, together with the all-(p-1)
point. D_p has allowed first differing digits {2,...,p-2}, together with
that same exceptional point. All C_(p,e) lie in S_p. In particular,

    D_3={-1 mod 3^H_3},       S_3=C_3 disjoint-union D_3.

For each p>=5, the union of all star rectangles is exactly C_3 times C_p.
The actual complete survivor set consequently is

    R = R_a disjoint-union R_b,
    R_a = {-1 mod 3^H_3} times product_(p>=5) S_p,
    R_b = C_3 times product_(p>=5) D_p.                    (2)

There is no additional restriction from the remaining mixed divisors.
The CRT point x_3=1 and x_p=2 for p>=5 lies in R_b, so R is nonempty.

<a id="a-constant-potential-coordinate-distribution"></a>
#### A constant-potential coordinate distribution

For x,t modulo p^h, let ell(x,t) be the largest e in {0,...,h} for which
x=t modulo p^e. The coherent coordinate kernel is

    J_(p,h)(x,t)=(1+ell(x,t))^2
      =1+sum_(e=1)^h (2e+1)1[x=t mod p^e].                (3)

For 1<=k<=p-1, let T_(p,k,h) contain points whose first digit different
from p-1 is in {p-k-1,...,p-2}, plus the all-(p-1) point. Define
u_h=v_h=0, and for r=h-1,...,0, with w_r=2r+3, set

    u_r=(w_r+u_(r+1))/p,
    v_r=[k/(w_r+u_(r+1))+1/(w_r+v_(r+1))]^(-1),
    V_(p,k,h)=1+v_0.                                      (4)

At a node on the distinguished all-(p-1) path at depth r, give each of
its k allowed side children probability v_r/(w_r+u_(r+1)); give its
continuing child probability v_r/(w_r+v_(r+1)). These probabilities are
positive and sum to one by (4). After taking a side child, choose all
remaining digits uniformly. Continuing children follow the same rule,
and the depth-h point terminates. This defines a finite probability
lambda_(p,k,h) supported on T_(p,k,h).

The expected remaining contribution of a uniform suffix is u_r. For
any fixed admissible point below a distinguished node, only the matching
child contributes beyond that node. If the point takes a side child,
its contribution is
[v_r/(w_r+u_(r+1))]*(w_r+u_(r+1))=v_r. If it continues along the
distinguished path, induction gives the identical value with v_(r+1)
in place of u_(r+1). Induction from depth h proves

    E_(t~lambda_(p,k,h)) J_(p,h)(x,t)=V_(p,k,h)
      for every x in T_(p,k,h).                           (5)

This is a distribution of test centers, not a chosen survivor law.
The general construction is formalized by
[RestrictedSpineConstantPotential.restricted_spine_constant_potential](../../../../D5/S3/Arith/Congruence/RestrictedSpineConstantPotential.lean).
For any finite alphabet, a distinguished symbol excluded from its side set,
and any finite list of positive real layer weights, the theorem proves
nonnegativity, total mass one, support in the admissible words, and the exact
constant potential of the explicitly recursive test law. Empty words and an
empty side set are included. Taking weights `3,5,...,2h+1` supplies this tree
calculation; the word-to-residue embedding, CRT product, numerical threshold
and full star-family refutation are separate formalization obligations.

<a id="an-exact-depth-eight-lower-certificate"></a>
#### An exact depth-eight lower certificate

Take h=8 and

    B=V_(3,1,8) product_(p>=5) V_(p,p-3,8).

The ternary factor is for S_3; the other factors are for D_p. To bound
B using short integers, put M=10000 and initialize U_8=W_8=0. For
r=7,...,0 compute

    A_r=M(2r+3)+U_(r+1),   B_r=M(2r+3)+W_(r+1),
    U_r=floor(A_r/p),
    W_r=floor(A_r B_r/(A_r+k B_r)),
    m_p=M+W_0.                                            (6)

The functions a/p and ab/(a+kb) are increasing for positive a,b and
k>=1. Thus induction gives U_r<=M u_r, W_r<=M v_r, and
V_(p,k,8)>=m_p/M. Alternatively, every such inequality in this fixed
certificate is checked directly against the exact fractions from (4).

The integer table is

    p:    3     5     7    11    13    17    19    23    29    31
    m:44425 25593 17916 13925 13125 12215 11932 11539 11178 11092
    p:   37    41    43    47    53    59    61    67    71    73
    m:10897 10801 10761 10691 10607 10541 10522 10473 10445 10432.

Exact integer multiplication gives

    B >= product_p (m_p/10000)
      = 88201253955139641252118098948566841488891779660937472668777730852992559
        /625000000000000000000000000000000000000000000000000000000000000000000
      > 141.                                              (7)

The displayed rational is 141.12200632822342...; the full fraction
recurrence gives B=141.2182001288544... . No floating approximation is
used for any comparison in this proof or its certificate.

<a id="two-legal-complete-layout-distributions"></a>
#### Two legal complete-layout distributions

A full CRT center t determines one coherent complete layout b_d=t mod d.
For every x,

    L_t(x)^2=product_(p in P) J_(p,H_p)(x_p,t_p).            (8)

This follows by factoring the complete divisor index; each p-coordinate
contributes exactly 1+ell(x_p,t_p). Test centers may be anywhere modulo
Q and are not required to survive the forbidden assignment.

For distribution Pi_a choose t_3=-1 modulo 3^H_3. For each p>=5 choose
t_p independently and uniformly among the integer representatives
1,...,p-1, regarded modulo p^H_p. If x is in R_a then its ternary kernel
is (H_3+1)^2. Also x_p is nonzero modulo p, so

    E_(Pi_a) J_(p,H_p)(x_p,t_p) >= 1+3/(p-1).

Independence of these explicitly chosen test coordinates yields

    E_(Pi_a) L_t(x)^2
      >= (H_3+1)^2 product_(p>=5) (p+2)/(p-1)
      >= 32^2 * 1796039511175/124554051584
      > 14336,                   x in R_a.                (9)

For Pi_b independently choose t_3 modulo 3^8 from lambda_(3,1,8), and
t_p modulo p^8 from lambda_(p,p-3,8) for p>=5; set all higher digits of
t to zero. If x is in R_b, its ternary depth-eight projection is in
T_(3,1,8) and every other depth-eight projection is in T_(p,p-3,8).
This remains true when the first non-(p-1) digit occurs after depth
eight: the projection is the allowed all-(p-1) point. Higher matches
can only increase (3), so (5), (7), and (8) give

    E_(Pi_b) L_t(x)^2 >= B > 141,       x in R_b.            (10)

These factorizations concern the test distributions; they impose no
independence condition on mu.

<a id="a-pointwise-dual-bound-for-every-survivor-probability"></a>
#### A pointwise dual bound for every survivor probability

Use the one fixed normalized layout distribution

    Pi=(1/100) Pi_a+(99/100) Pi_b.

For x in R_a, (9) gives E_Pi L_t(x)^2>143.36. For x in R_b, (10) gives
E_Pi L_t(x)^2>139.59. Nonnegative contributions from the other mixture
component were only discarded. By the exact decomposition (2), every
x in R satisfies the latter strict lower bound. Therefore for any
probability mu on R, finite sums can be interchanged to obtain

    Gamma_Q(mu) >= E_(t~Pi) E_(x~mu) L_t(x)^2
                = E_(x~mu) E_(t~Pi) L_t(x)^2
                > 13959/100 > 138877/1000.

This proves (1). Keeping the exact rational (7) yields the stronger
uniform certificate lower bound 139.7107862649412... for this same
mixture; no optimization of its weight is necessary.

<a id="verification-scope"></a>
#### Verification scope

`verify_star_survivor_obstruction.py` uses only the Python standard library and
explicit error checks that remain active under optimization. It
reconstructs all 20 exact fraction recurrences, independently checks
all pinned floor integers, verifies the rational product and both
mixture-branch bounds, and compares its full output with `star_survivor_obstruction_certificate.json`.
It constructs a full height-31/8 CRT witness and checks every pure and star
exclusion, with all remaining mixed-zero exclusions ruled out by its nonzero
prime coordinates. It also exhaustively checks the explicit leaf laws and their equal
potentials for five small trees, and checks actual complete forbidden
assignments against decomposition (2) on 11700 small-modulus points.
Those small checks are regressions; the ordinary induction and CRT
argument above prove the arbitrary-height statement. No full huge
survivor enumeration, numerical optimization, or Lean kernel
certification is claimed.

<a id="irredundancy-does-not-repair-the-universal-head-target"></a>
#### Irredundancy does not repair the universal head target

Delete all redundant mixed-zero classes, retaining only the pure classes and
star rectangles. This family has the same survivors and least common multiple
`Q`, and every retained class has an exclusive witness. For a star rectangle
`C_(3,i) × C_(p,j)`, choose those two coordinates inside the indicated cylinders
and every other coordinate equal to 2, which belongs to `D_q`. For a pure class
`F_(p,j)` with `p>=5`, choose the ternary coordinate equal to -1 and all other
outside coordinates equal to 2. For a pure ternary class choose every outside
coordinate equal to 2. The first-differing-digit descriptions prove that each
point belongs only to its designated retained class. Thus requiring an
irredundant forbidden family does not repair Γ73 when Gamma still indexes all
divisors of its least common multiple.

This irredundant family is not a minimal cover: it does not cover. A genuine
finite irredundant cover has an additional necessary fibre property. If
`p^H` is the full p-part of its period Q and x is an exclusive point of a class
of p-height H, the p points `x+kQ/p`, `0<=k<p`, must all be covered. No class
of smaller p-height can meet this fibre: its membership is invariant on the
fibre and it misses x. Each class of height H meets at most one fibre point,
so at least p distinct such classes must meet the fibre. In the star family,
for any `p>=5`, the pure `p^H` exclusive witness with ternary coordinate -1 gives a fibre
whose other p-1 points are uncovered. This necessary property applies to an
actual cover of the whole period; it cannot be imposed without proof on its
73-smooth head alone. For example, choose a new prime `q>73` and `H_3>=q`.
The q distinct odd moduli `3^i q`, `1<=i<=q`, with CRT residues
`-1 mod 3^i` and `i-1 mod q`, cover the entire exceptional ternary fibre
`x_3=-1 mod 3^H_3` as its q-coordinate varies. This explicitly fills a fibre
missed by the head. It is not a full cover: the ternary root `1 mod 3`
misses every one of these new classes.

The published essential-class constraints are stronger than merely counting
the children in this top fibre. [Lettl--Sun, Theorems 1.3 and
2.1](../../../../Library/Arith/lettlsun2008cosets.md), imply that an essential modulus
`d_t` in a cover by `k` classes satisfies
`k >= 1 + sum_p v_p(d_t)(p-1)`. At a private point `a` of this class,
retain the original labels `j` whose prime-to-p part divides `a_j-a` but
whose whole modulus does not. Their weighted capacity obeys

\[
 \sum_j p^{-(v_p(d_j)-v_p(a_j-a)-1)}
 \ge v_p(d_t)(p-1).
\]

The integer ordinary-cover case of the first bound is attributed to
Znám (1975). These public results require a cover of the full period;
they give no such inequalities for an isolated noncovering head.

<a id="complete-star-heads-cannot-be-completed-by-arbitrary-odd-tails"></a>
### Complete star heads cannot be completed by arbitrary odd tails

**Theorem.** Let `P` be any subset of the odd primes at most 73 containing
3, and let `H_p>=1` for every `p in P`. Put `Q=prod_(p in P) p^H_p` and
use precisely the complete star forbidden assignment defined above on all
nonunit divisors of `Q`. Consider any finite family of additional classes
such that all moduli in the combined family are distinct and odd. Each
additional modulus has head part dividing `Q`, has a nonunit tail part,
and has all tail prime factors greater than 73. The combined family does not cover
the integers. There is no restriction on the number of tail primes in
one modulus, their exponents, the total number of primes, or the tail
interaction graph. The heights `H_p` resolve the entire original family,
including the head parts of classes whose largest prime occurs later.

The proof uses the actual broad-branch survivor law, the conditional convex
comparison in [Schroeder, Section 3](../../../../Library/Arith/schroeder2026noncoverage.md),
a finite exact positive-part calculation, and
[BBMST, Theorem 6.1](../../../../Library/Arith/balister2018covering.md).
It is an ordinary mathematical proof with an exact numerical certificate.
The unrestricted Erdős problem still allows arbitrary head assignments.

<a id="one-actual-head-law-at-every-positive-height"></a>
#### One actual head law at every positive height

Retain exactly the sets `C_3` and `D_p` in (2), and take

\[
 R_b=C_3\times\prod_{p\in P\setminus\{3\}}D_p,
 \qquad \mu_{\rm head}=\operatorname{Unif}(R_b).
 \tag{US1}
\]

This product law is supported on actual complete head survivors. In
particular, every mixed-zero head class is already excluded by a pure
class. The coordinate densities and resulting cylinder caps are

\[
 s_3=\frac{1-3^{-H_3}}2,\qquad
 s_p=\frac{p-3+2p^{-H_p}}{p-1}\quad(p\ge5),\qquad
 \mu_p\{x_p=b\bmod p^e\}\le\frac{p^{-e}}{s_p}.
 \tag{US2}
\]

All these densities are positive. For `p>=5`, use the height-independent
cap `c_p p^-e`, where `c_p=(p-1)/(p-3)`. The finite ternary cap needs a
separate argument; replacing it pointwise by `2*3^-e` would be invalid.

After applying conditional comparison and completing the divisor labels,
the ternary auxiliary height `K_(3,H)` has tails

\[
 \Pr(K_{3,H}\ge e)=\frac{2\,3^{-e}}{1-3^{-H}}\quad(1\le e\le H),
 \qquad \Pr(K_{3,H}>H)=0.
\]

Let `K_3` instead have tail `Pr(K_3>=e)=2*3^-e` for every `e>=1`.
For an increasing convex function `phi` on the nonnegative integers, its
increments `Delta_e=phi(e)-phi(e-1)` are nonnegative and nondecreasing.
With `w_e=2*3^-e`, the tail-sum identity gives

\[
 \mathbb E\phi(K_{3,H})=\phi(0)+
 \frac{\sum_{e=1}^H w_e\Delta_e}{\sum_{e=1}^H w_e}
 \le\phi(0)+\sum_{e\ge1}w_e\Delta_e
 =\mathbb E\phi(K_3).                                 \tag{US3}
\]

Here `sum_(e>=1) w_e=1`, and the truncated weighted average uses only
the smallest increments. Both heights have mean 1. For any fixed
`z>=1`, both functions `phi(k)=h(z(1+k)-1)` and
`phi(k)=h(z(1+k))` are increasing convex whenever `h` is. This is the
specific convex-order replacement used below, after auxiliary independence
has been established. For other head primes, the finite auxiliary heights
are directly stochastically bounded by independent `K_p` with tails
`Pr(K_p>=e)=c_p p^-e`. Adding omitted head primes as independent factors
`1+K_p>=1` only increases the completed loads.

<a id="normalized-tail-kernels-preserve-the-original-labels"></a>
#### Normalized tail kernels preserve the original labels

Process tail primes in increasing order, with `delta=2/5` through the
finite stopping prime. Each prime-power coordinate has the full height
appearing anywhere in the original family. First let `U_q` be uniform on
the actual survivors of all pure `q`-power classes. Distinct moduli and
`sum_(e>=1) q^-e=1/(q-1)` show that this is a probability, with

\[
 U_q\{y=b\bmod q^e\}\le\frac{q-1}{(q-2)q^e}.
\]

Assign every other class with a nontrivial tail part to its largest tail
prime `q`. Given the entire earlier history, let `B_q` be the actual
union of its active `q`-cylinders, and put `alpha_q=U_q(B_q)`. The BBMST
kernel relative to `U_q` has densities

\[
 \frac{1}{1-\min(\alpha_q,\delta)}\quad\text{off }B_q,
 \qquad
 \frac{(\alpha_q-\delta)_+}{\alpha_q(1-\delta)}
       \quad\text{on }B_q,                            \tag{US4}
\]

with the latter defined to be zero when `alpha_q=0`. Each row integrates
to one and is bounded by `1/(1-delta)`, including a completely forbidden
fibre. Thus future kernels preserve every prefix marginal. The final
probability of this assigned mixed union is exactly
`E(alpha_q-delta)_+/(1-delta)`, and every pure-tail class has probability
zero. There is no conditioning on survival during these steps. The
conditional cylinder caps at each earlier tail prime `p` are consequently
`c_p p^-e`, where

\[
 c_3=2,\qquad c_p=\frac{p-1}{p-3}\ (5\le p\le73),
 \qquad c_p=\frac{p-1}{(p-2)(1-\delta)}\ (p>73).
 \tag{US5}
\]

The value `c_3=2` is only the auxiliary value after (US3). The actual
head law always retains its finite-height cap from (US2). Head coordinates
are initially independent, and all the stated tail caps hold conditional
on the entire earlier history under the same normalized law.

Write each original modulus assigned to `q` as `d q^e`, with `d>1` an
old cofactor, retaining its actual old residue as part of that original
label. Set `w_e=(q-1)/q^e`. The uniform-pure-survivor bound gives

\[
 \alpha_q\le\frac{R_q}{q-2},\qquad
 R_q=\sum_{\text{original labels }d q^e}
        w_e\,\mathbf1_{\text{actual old cylinder}}.     \tag{US6}
\]

At fixed `d` and `e` there is at most one label because the original
moduli are distinct. Different original moduli can have the same projected
cofactor `d`; no distinctness of such projections is asserted.

Schroeder's Section 3 proposition **Conditional comparison**, source label
`prop:comparison`, applies to any finite family of weighted coordinate
rectangles. If their coordinate events `A_(label,p)` have deterministic
caps conditional on the entire past, it bounds the expectation of every
nonnegative increasing convex function of their load by the corresponding
load formed from independent uniforms, one common uniform per coordinate.
The sets and residues may depend on the whole modulus label. Its proof
replaces coordinates in reverse order by increasing supermodular
rearrangement. It does not require the actual events to be nested or the
actual coordinates to be independent.

Apply it to (US6) with `h(u)=(u-(q-2)delta)_+`. In the compared load,
`d=prod p^a_p` is active exactly when `a_p<=K_p` for every old prime.
For each fixed cofactor, `sum_e w_e<=1`. Completing all nonunit cofactor
labels therefore bounds this load by `D_q-1`, where

\[
 D_q=\prod_{3\le p<q\atop p\ \text{prime}}(1+K_p).
\]

First complete within the actual finite heights, then apply (US3) and
extend the other auxiliary heights. Monotone convergence permits this
nonnegative completion; the moments displayed below are finite. The
subtraction of 1 excludes the unit cofactor, whose classes were already
removed as pure powers. Hence the actual mixed-union probability is at most

\[
 b_q=\frac{\mathbb E\bigl(D_q-1-(q-2)\delta\bigr)_+}
              {(q-2)(1-\delta)}.                      \tag{US7}
\]

This is the positive-part estimate in the proof of Schroeder's Section 8
**Unrestricted second-moment charge**, before its quadratic relaxation,
with the head caps supplied by (US1)--(US3). No restriction on a modulus's
tail support was used.

<a id="a-simultaneous-complete-layout-moment-under-the-same-law"></a>
#### A simultaneous complete-layout moment under the same law

For any complete test layout on the enlarged prefix modulus through `B`,
apply the same conditional comparison with `h(u)=u^2`, keeping each test
modulus and its own residue as an individual label. The completed load is
bounded by `D=prod_(3<=p<=B)(1+K_p)`. Formula (US3) applies here with
`phi(k)=(z(1+k))^2`. Consequently every complete layout has second moment
at most

\[
 J_B=\mathbb E D^2
   =\prod_{3\le p\le B\atop p\ \text{prime}}
       \left(1+c_p\frac{3p-1}{(p-1)^2}\right).          \tag{US8}
\]

Indeed, the tail formula gives
`E(1+K_p)^2=1+sum_(e>=1)(2e+1)c_p p^-e` and the displayed geometric sum.
The head product through 73 is exactly the existing `K_0<177` in (BS6).
Auxiliary independence factors `J_B`; no tensorization assertion about
actual-layout `Gamma` is needed.

Put `charge_B=sum_(73<q<=B) b_q`. The actual law constructed by (US4) is
already supported on head survivors and pure-tail survivors. The union
bound and preservation of assigned-event probabilities show that its
event `E` of avoiding every prefix class has mass
`lambda>=1-charge_B`. When `charge_B<1`, condition this law **once** on
`E`. For every complete layout, its load `L` includes the unit divisor,
so `L^2>=1` everywhere. Thus the resulting law is supported on actual
prefix survivors and simultaneously satisfies

\[
 \Gamma\le1+\frac{J_B-1}{\lambda}
          \le G_B:=1+\frac{J_B-1}{1-\operatorname{charge}_B}.
 \tag{US9}
\]

The event bound and `J_B` belong to this same preconditioning law; they
are not combined from separately optimized measures.

<a id="exact-positive-part-certificate-and-the-bbmst-stop"></a>
#### Exact positive-part certificate and the BBMST stop

Take `B=2048`, whose last prime is 2039 and whose global prime index,
counting 2, is `k=309`. Absent primes can be included as unused coordinates;
this does not change actual noncoverage and only enlarges the nonnegative
auxiliary bounds. There are 288 processed tail primes between 73 and `B`.
The [existing exact verifier](../verify_star_block_obstruction.py)
recomputes the entry `unrestricted_star_stoploss` in its
[certificate](../certificates/star_block_obstruction_certificate.json).

Here is its directed calculation. Use scale `S=10^18` and store the
probabilities of all integer product states `1<=d<=819`. The multiplier
`f=1+K_p` has atom probabilities

\[
 a_1=1-\frac{c_p}{p},\qquad
 a_f=\frac{c_p(p-1)}{p^f}\quad(f\ge2).
\]

Starting with `W_1=S` and all other `W_d=0`, round every `a_f` upward to
`A_f/S`, and update

\[
 W'_d=\left\lceil\frac{\sum_{f\mid d}W_{d/f}A_f}{S}\right\rceil.
\]

Induction gives `W_d/S>=Pr(D=d)`: every coefficient is nonnegative.
Multipliers greater than 819 cannot enter a retained state because all
multipliers are at least 1. Their moments are not discarded. Separately
propagate upper bounds for `E D` and `E D^2` by multiplying, respectively,
by the exact positive factors
`1+c_p/(p-1)` and `1+c_p(3p-1)/(p-1)^2`, rounding each result upward on
the same grid. The independent prime-list check uses trial division.

Before processing `q=p`, put `T=1+(p-2)delta=(2p+1)/5`. The exact identity

\[
 \mathbb E(D-T)_+=\mathbb E D-T+
        \sum_{d\le T}(T-d)\Pr(D=d)                    \tag{US10}
\]

has nonnegative coefficients on the approximated mean and low-state
probabilities. If `M/S` is the stored mean bound, then rounding

\[
 \frac{5M-(2p+1)S+
       \sum_{d\le\lfloor T\rfloor}(2p+1-5d)W_d}{3(p-2)}
\]

upward gives an upper bound for `S b_p`. The largest queried state is
815 at `p=2039`, within the 819 retained states. All 288 step charges,
the final moments and the final low-state digest are recomputed; the
digest is not a mathematical input. Exact arithmetic yields

\[
 \operatorname{charge}_B\le
 \frac{197210774016889569}{500000000000000000}<1,\qquad
 J_B\le\frac{2622709946291465704821}{1000000000000000000},
\]
\[
 G_B\le\frac{2622315524743431925683}{605578451966220862}
       <4331<4732<\frac{10350367}{2187}.                \tag{US11}
\]

For the stopping threshold, the first two positive `atanh` terms give
`log 2>=56/81`. Since `k=309>=256`, this implies
`log k>=448/81>4` and `log log k>=log 4>=112/81`. Therefore

\[
 k(\log k+\log\log k-3)^2
 \ge k\left(\frac{317}{81}\right)^2
 =\frac{10350367}{2187}>G_B.                           \tag{US12}
\]

The exact margin between the final rational threshold and the certified
`G_B` is `532955172528371903287633/1324400074450125025194>0`.

Restart the joint-load transfer (T1)--(T6) from the normalized actual
survivor law in (US9). Its initial budget is at most `G_B`, with positive
survivor mass, and (US12) is precisely the sufficient stopping inequality
of BBMST Theorem 6.1. That theorem's recurrence continues with the standard
uniform-base kernels for all later primes; the earlier pure-survivor base
is not assumed for this continuation. Its prime index is the full global
index `309`, including absent primes and 2. If the family ends before
the stop, its already positive prefix-survivor mass suffices. Otherwise
the BBMST continuation retains positive survivor mass through every
remaining prime. Finite CRT then produces an integer avoiding the whole
original family, proving the theorem.

The conditional comparison and BBMST continuation are published ordinary
proofs; the changed head input, finite-height convex-order argument,
same-law conditioning and exact finite charge are the deductions here.
The audited upstream Lean theorem still assumes at most three prime factors
per modulus and does not certify this extension. The local Lean result
in (DG2) proves the selected-coordinate cylinder step, not this entire
unrestricted-tail star theorem. The graph and bounded-support star bounds
below remain quantitative refinements for their respective subclasses.

<a id="arbitrary-cross-point-1113-heads-and-full-height-continuation"></a>
### Arbitrary cross-point 11/13 heads and full-height continuation

A further noncoverage theorem permits both 11 and 13 at arbitrary finite
heights. Let the full `{3,5,7}` part of every original modulus divide 315,
and choose the canonical supported 315 law. At every point in its support,
suppose the active classes d·11 forbid at most one first 11-digit and the
active classes d·13 forbid at most one first 13-digit, for d|315. Then the
family cannot cover. All twelve possible d·143 classes may have arbitrary
residues, and the later prime heights and interactions are unrestricted.

The [degree-weighted grid proof](../profile-notes/001-064/03-arbitrary-height-transfer-for-matching-kernels.md#arbitrary-point-holes-and-a-common-diagonal)
allows arbitrary point-hole patterns in each available 10-by-12 rectangle,
including a whole row deleted by cross classes. The number of actual holes
has mean at most 271/86. Retaining its correlation with old complete test
loads gives the same full-height supported law both a square bound
`51464038499033/2027599359660` and a complete convex comparator of mean
`46851298771/11264440887`. The mean belongs to the comparator and is not
asserted to equal the actual maximum old-load mean.

The fixed 414-step certificate ends at 2903, global prime index 420:

    survivor mass >= 44564898975571389/250000000000000000,
    Gamma <= 1751428432885843299077/178259595902285556
          < 9826 < 9833 < 420(log420 + loglog420 - 3)^2.

AP2–AP6 and the existing BBMST transfer finish every later prime. The
previous single-hole result remains a quantitative refinement with its
258-step certificate. The full-family 315 height restriction and the
first-power axis restrictions remain genuine hypotheses. This is an
ordinary theorem with exact arithmetic, not unrestricted Erdős #7 or
an end-to-end Lean proof.

The unnormalized weighted grid component is formalized by
`D5.S3.Arith.Congruence.ArbitraryHoleGram.degree_reweighted_grid_second_moment_le`
in [ArbitraryHoleGram.lean](../../../../D5/S3/Arith/Congruence/ArbitraryHoleGram.lean),
for arbitrary finite axes of size at least three and arbitrary hole
relations under its small-perturbation hypothesis. The normalization,
arithmetic head integration and tail conclusion remain ordinary proofs;
the zero-perturbation extension to smaller axes below is also an ordinary
Laplacian argument.

The [star-head perturbation theorem](04b-arbitrary-star-head-residues-with-unrestricted-tails.md)
pays an actual reference-head bad mass up to9/20 once and retains arbitrary
tail primes above73. In two separate sufficient classes it permits
arbitrary residues at every head modulus divisible by27, or at every
head modulus with at least four distinct prime factors, with the other
head residues canonical. These two free-label sets are not combined.
