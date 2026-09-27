[Index](../../marked_head_profile.md) · [Private budgets and resets](357-original-private-swaps-and-prime-reset-transport.md) · [Actual synchronized source](354-synchronized-prime-private-cofactor-matching.md)

# A local first-hit map transports actual child sources to parent-private points

An actual child source can be transported to its original parent's
private set by a literal CRT prefix replacement followed by a bounded
search along that parent AP. The map has an explicit Haar congestion
bound. At sufficiently large child depth it is injective, preserves a
specified block coordinate, and its target determines the entire input.
There is also a controlled version whose target must escape the child's
P-prefix. This supplies a single-step source-to-parent-private map left
unconstructed in 357; it does not control indefinite iteration or rule
out a distinct odd whole cover.

## 1. Actual labels, the complete carrier, and source normalization

Use one finite original family with period Q and Haar probability H_Q.
Let A_m=a_m mod m be essential relative to that complete family, and
let the original child be

    d=P^e m,  m>1,  P not dividing m,  e>=1.

Write D=P^e, L=Q/m. Then D divides L. The full original CRT carrier
retains every original prime-power height. Write A_d=K x C, where K
is its literal P-prefix modulo D and C its cofactor residue modulo m.
The actual parent has cofactor residue B. In the extremal application
of 350, divisor closure supplies this parent and comparable-class
disjointness gives B intersect C empty. The local map below needs the
actual essential parent, not a new parent residue chosen for convenience.

Let kappa be the number of other original APs intersecting A_m. Under
the parent parameterization

    n=a_m+m y,   y in Z/L,

each of those intersections is one residue class modulo
d'/gcd(d',m), a divisor of L. Their union misses exactly the actual
parent-private y positions. Since A_m is essential, the restricted
competitor family does not cover all integers. The standard interval
theorem recalled in 357 therefore
puts a private position in every W=2^kappa consecutive y positions.
Repeated restricted moduli are allowed. A whole cover is not needed
for this local assertion; the original parent must be essential.

For a synchronized tuple tau from 354, put

    U_tau=R_P intersect intersection_r C_r,
    theta_tau=H_T(J_tau),
    lambda_tau=H_X(U_tau) theta_tau.

Here lambda_tau is raw mass on the cofactor--tail carrier. Lifting its
event to one particular actual first-P root r gives the full-Q event
`{r} x J_tau x U_tau`, of mass **lambda_tau/P**. This is a subset of the
selected actual child. A different, expanded child source `K_r x U_tau`
has mass

    H_X(U_tau)/P^(e_r)
      =lambda_tau/(theta_tau P^(e_r)).               (LT1)

At the largest P both events lie in the actual pre-P survivor. The
expanded event need not realize the entire original tuple at every
tail; its original child label remains valid. Neither lambda_tau nor
H_X(U_tau) alone is the full-Q mass of a fixed-root source.

## 2. Literal cofactor alignment and the first-private map

Define Phi on K x C by replacing, for each q dividing m, only the
lowest v_q(m) digits of its full q-coordinate by those of a_m. Keep
all higher q-digits and every full coordinate at primes not dividing m.
Thus Phi is a bijection

    Phi: K x C -> K x B.                             (LT2)

Its inverse uses the original child's cofactor digits. It fixes the
entire P-coordinate and preserves the size 1/Q of every Haar atom.
It can create other original memberships; those are tested in the
next step, rather than assumed absent.

For z in the actual child, write Phi(z)=a_m+m y_0 modulo Q. The P-prefix
condition is one congruence

    y_0=c mod D,

where c is fixed by K and the actual parent residue. Search the W
positions y_0+1,...,y_0+W and take the first actual parent-private one.
The interval theorem guarantees success, even if y_0 itself was private.
Let its positive offset be k(z), and define

    T_priv(z)=Phi(z)+m k(z) mod Q in Priv(A_m).        (LT3)

All competing original labels are checked: those not intersecting A_m
cannot occur anywhere on this search, while all the others are in the
kappa restricted APs. This is a location-dependent bounded search using
the actual original family, not an independent sample from its private
set. It works whether or not the private set escapes K.

For any target y, a possible aligned source is y_0=y-k modulo L with
1<=k<=W and y_0=c mod D. Thus k has one prescribed residue modulo D.
There are at most ceil(W/D) such offsets, and at most L/D distinct
source anchors. Periodic repetitions only reduce their number. Put

    C_priv=min(L/D, ceil(W/D)).

For every finite source measure lambda supported on the actual child,

    lambda<=M H_Q
      ==> (T_priv)_*lambda<=C_priv M 1_(Priv(A_m)) H_Q. (LT4)

Total source mass is preserved. This statement also applies to either
actual source in LT1. A source normalized to probability has its own
M, potentially 1/H_Q(source); normalization is not free.

## 3. Large depth gives an injection with an explicit inverse

If D>W, every selected offset lies strictly between 0 and D. Therefore
the output automatically avoids K and C_priv=1. The injectivity is also
visible directly in the rotated parent coordinate

    (y-c mod L)=D b+t,   0<=t<D.

The aligned source has t=0; its output has t=k(z) and the same block b.
Given a target y, recover

    y_0=c+D floor((y-c mod L)/D) mod L,              (LT5)

then recover the original source by Phi inverse. This deals with wrap
around the full period as well as ordinary blocks. The target alone,
together with the fixed original labels, determines the complete input.
The map preserves the actual parent residue modulo m and this rotated
D-block coordinate. In particular

    D>2^kappa ==> (T_priv)_*lambda
                      <=M 1_(Priv(A_m) intersect K^c) H_Q. (LT6)

For general depths the first-private map can have multiple inputs per
target; LT4 counts that loss explicitly.

## 4. Requiring escape at smaller depth

Let Z=Priv(A_m) intersect K^c. If Z is nonempty, the kappa restricted
competitor APs together with K are a noncovering family of kappa+1 APs.
Every W'=2^(kappa+1) consecutive y positions therefore meet Z. Searching
forward from each aligned anchor for its first such point defines
T_esc with

    C_esc=min(L/D, ceil(2^(kappa+1)/D)),
    (T_esc)_*lambda<=C_esc M 1_Z H_Q.                (LT7)

The same residue count proves this bound. Since the anchor itself is
in K, the first escape actually has positive offset less than both W'
and L; LT7 uses a convenient slightly larger cap. It remains valid when
W'>L. For D>W use the sharper injection from section 3 instead.

If Z is empty, T_priv still exists, but no positive-mass transport into
Z exists. The two-label swap in 357 remains a separate possibility;
its source comparison uses that report's additional fixed-modulus
minimum. That minimum is not a hypothesis of LT3--LT7.

## 5. Composition with the actual prime reset

Suppose q divides m, A_q is an original, and every other q-bearing
original is disjoint from A_q, as in the extremal system. A point in
Priv(A_m) can be reset at its first q-digit into Priv(A_q), as proved
in 357. All points of this one parent have the same first-q root, so
that reset is injective on the entire transported target. For a single
parent it adds no q-1 congestion factor to LT4 or LT7. When m=q it is
the identity.

Uniformly resampling the q-tail afterwards averages the density on
that root and also preserves its upper bound. Thus the composed output
has the corresponding bound

    lambda_out<=C M 1_(Priv(A_q)) H_Q
              <=C M 1_(O_q^c) H_Q,                 (LT8)

where C is C_priv, C_esc, or 1 in the deep case. This is domination by
the actual raw pre-q killed Haar law, not an identification with it.
Since q differs from P, the reset and re-tail preserve the P-coordinate
of the repaired target; an escape already obtained remains an escape.
Combining different actual parents assigned to q requires the distinct
source-root accounting of 357, rather than the single-parent factor 1.

The alignment Phi preserves the stated original CRT digits, but the
subsequent shift by m k may change higher m-prime digits and all
coordinates at primes not dividing m. It need not preserve previously
imposed exclusions at other primes. Even when LT5 makes the whole
source recoverable, those coordinates need not be literally unchanged.
The bounded local search costs at most W or 2W sets of kappa original
membership tests (and the K test for escape); it is not a claim of
uniformly cheap computation. One may stop after a full parent period
when that is shorter.

## 6. Checks and the remaining global obligation

The [standalone exact checker](../../frontier/retained-transport/parent_escape_transport.py)
uses only the Python standard library. It retains the entire periods
12, 144 and 960 of three actual distinct covers with even moduli, plus
the explicit odd noncover `0 mod3, 0 mod5, 1 mod75`. It checks every
essential parent and every prime-power prefix available outside that
parent's support. These parent-anchor checks are distinguished from
the checks whose input is an actual original child AP. Missing divisor
parents in these nonextremal fixtures are not invented.

Checks include literal CRT replacement and its inverse, first-hit
minimality, actual complete-family privacy, shallow congestion, deep
block recovery, W'>L wraparound, nonconstant rational source densities,
single-parent reset and uniform re-tail, and the actual-source factors
in LT1. The whole-cover fixtures are not distinct odd covers; the odd
fixture has uncovered points. These checks validate the finite
implementation interfaces and do not replace the general proofs above.
No Lean verification or literature novelty is claimed.

The retained fixtures give 30 essential parents and 406 parent/prefix
cases: 153 deep and 253 shallow. They supply 6,051 first-private and
5,427 first-escape anchor checks, 1,025 deep inverse checks, 635 actual
child-to-target checks, and 35 reset/re-tail compositions. There are
19 empty-escape cases and 234 nonempty shallow-escape cases; 139 escape
windows exceed the parent period. Eight fixed-root mass checks include
a period-144 tuple with theta=1/3 and lambda_tau=1/12: each fixed-root
event has mass 1/36, while its modulus-6 expanded child source has mass
1/12. Ordinary execution and isolated execution of a physically copied
script, with assertions optimized out, both exit successfully and give
byte-identical output. The checks use explicit exceptions, not assertions.

The maps settle the existence of this controlled single-step transport,
including shallow nonempty escapes. Global use must still pay for its
density cap, the mass retained when selecting a synchronized tuple, any
combination of parent channels, and each new observation or re-tail.
Later cofactors may contain larger primes, and the repair does not
preserve all earlier coordinate exclusions. No strictly descending
prime sequence, uniform bound for repeated transport, cover-preserving
replacement from these point maps, or unrestricted noncoverage result
has been established.
