# One shallow eight-prime source supports two arbitrary fresh heights

Let

    M=315*11*13*17*19*23=334639305.

Fix distinct primes q>=29 and r>=31. Consider any finite family of distinct
odd nonunit numerical moduli, each of the form d*q^e*r^f with d|M and
e,f>=0. All residue choices are arbitrary. Then its uncovered Haar density
is greater than1/4200.

Thus the primes through23 remain shallow: v3<=2 and v5,v7,v11,v13,v17,v19,v23
are at most one in EVERY original modulus, including those involving q
and r. The two fresh exponents are unrestricted finite heights. This is
ordinary mathematics and exact rational arithmetic, not Lean
verification or an unrestricted-support result.

## The same actual source and its two bounds

The [common shallow construction in Report 725](725-one-common-shallow-carrier-admits-an-arbitrary-height-last-prime.md) gives a subset E of the actual old-only
survivors modulo M and its uniform probability mu, with

    h=|E|/M >=104726/6084351,
    E_mu L^2 <= G=2607189975/7283281<358

for EVERY complete independent old divisor-query load

    L(x)=sum_(d|M)1_(x=a_d mod d).

Both statements use this same E and mu. The source is chosen once from the
actual old-only family; it is not selected separately for fresh-coordinate
heights, stars, cross labels, or the later quadratic costs. The unit query
term is one, so G>=1. Missing old labels may be completed by adding
forbidden classes, which only shrinks the original survivors.

## Finite padding retains the actual original phase choices

Take finite H,K resolving all actual exponents at q,r, increasing either
to one if it is unused. For every1<=e<=H, complete the old projections of
the actual q-only labels d*q^e to one old query A_e, retaining every actual
projection. Complete missing query slots arbitrarily once, independently
of the row x. Include the unit d=1. Define B_f analogously for r-only
labels. For every(e,f), complete the old projections of the cross labels
d*q^e*r^f to a complete query C_ef, again including d=1.

These completions only provide upper bounds on actual deletion loads.
They do not replace original residues or create a different actual source.

Put

    u=q-1, v=r-1,
    w_e=u*q^(-e), z_f=v*r^(-f),
    t_q=q^(-H), t_r=r^(-K).

The finite geometric sums give sum w_e=1-t_q and sum z_f=1-t_r.
Define

    Abar=sum_e w_e*A_e+t_q,
    Bbar=sum_f z_f*B_f+t_r,
    Cbar=sum_(e,f)w_e*z_f*C_ef+[1-(1-t_q)*(1-t_r)].

Every expression is a finite convex combination of complete queries and
the constant function one. Consequently Abar,Bbar,Cbar>=1 and, by pointwise
convexity of the square followed by integration against the SAME mu,

    E_mu Abar^2 <=G,
    E_mu Bbar^2 <=G,
    E_mu Cbar^2 <=G.                                      (F1)

There is no actual infinite configuration, infinite family, or free future
information in this construction. The constant-one residual is an explicit
finite tail weight; its square is at most G.

## Actual fibre survival before any renormalization

Fix an old row x and use the original full-coordinate Haar laws at q and r.
At exponent e, all actual q-only events, including the pure q^e class,
have union measure at most q^(-e)*A_e(x). Thus their complete union has
measure at most Abar(x)/u. The actual q-only survivor has measure at least
(1-Abar/u)_+. Similarly the r-only survivor has measure at least
(1-Bbar/v)_+.

Before cross labels are deleted, these two sets depend on different fresh
coordinates. Their product is the actual joint unary survivor. Each actual
cross label costs at most q^(-e)*r^(-f) times its old incidence, so the
complete cross union has ambient Haar measure at most Cbar/(uv). Removing
it from the unary product gives the actual conditional fibre lower bound

    V_(u,v)(Abar,Bbar,Cbar)
      =[(1-Abar/u)_+*(1-Bbar/v)_+-Cbar/(uv)]_+.            (F2)

The cross cost is an ambient union upper bound; no independent-cross-event
assumption or normalization after unary deletion is used.

For nonnegative A,B,C, V_(u,v) is nondecreasing in each denominator u,v.
If its previous value is zero this is immediate. If it is positive, then
u>A and v>B; increasing u to u' changes its unclipped value by

    (1/u-1/u')*[A*(1-B/v)+C/v]>=0.

The same reasoning applies to v. Hence u>=28,v>=30 imply

    actual fibre >= W/840,
    W=[(28-Abar)_+*(30-Bbar)_+-Cbar]_+.                   (F3)

This proves transport to larger fresh primes using the NORMALIZED fibre
function, rather than comparing only its numerator.

## One pointwise cost pays a positive fibre area

For real A,B,C>=1 let

    S=10*A^2+10*B^2+C^2,
    W=[(28-A)_+*(30-B)_+-C]_+.

The following elementary inequality holds:

    S+20*W >=7750.                                      (F4)

If A>=28 or B>=30 then already S>=7851 or S>=9011, respectively.
Otherwise put P=(28-A)*(30-B), u=28-A>=0 and v=B-1>=0. Since
W=(P-C)_+>=P-C, completing squares gives

    S+20*W
      >=10*A^2+10*B^2+20*P-100+(C-10)^2
       =7750+20*u+20*v+10*(u-v)^2+(C-10)^2
      >=7750.

This proves(F4) for all real A,B,C>=1, without an enumeration, interval
grid, or numerical optimization.

By(F1), E_mu S<=21*G. Integrating(F4) therefore yields

    E_mu W >=(7750-21*G)/20>0.                           (F5)

In particular only the coarse common bound G<358 is needed, since
7750-21*358=232>0.

## Original Haar density

The old law is uniform on E, so restricting original old Haar to E and
then averaging the actual fresh fibre gives original full Haar mass

    >=h*E_mu W/840
    >=h*(7750-21*G)/16800
    >=3549034855753/14889516779972016
     >1/4200.

The rational lower bound is approximately0.0002383579607. Replacing G by358
gives the simpler certified lower

    1518527/6388568550 >1/4250.

This conversion uses the joint actual carrier and its uniform law, not a
product of marginal density claims. It remains valid after lifting the
old coordinates to the full original period, and unused coordinates can
be padded without altering Haar density.

## Exact checks and retained scope

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_two_fresh_heights.py)
first checks the hashes of its Report725 dependencies and replays their
complete source construction, comparing the freshly computed result with
the retained data. It then verifies the old/unary/cross numerical inventory
partition at sixteen finite height pairs, the finite geometric padding at
seventy-five parameter choices, the exact polynomial coefficient identity
in(F4), and the rational density comparisons. General finite heights are
covered by the geometric-series proof above, not by extrapolating those
checks. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_two_fresh_heights.json)
is reproduced under `python3 -I -S -B -O`.

An independent implementation reconstructs the inherited six-shape moment
bounds, finite mixture identities and the analytic square completion. The
proof of(F4) is valid for all real A,B,C>=1; no interval grid or numerical
optimization is required.

The conclusion permits arbitrary simultaneous phases and arbitrary finite
heights at TWO fresh primes. It does not remove the old divisor restriction
d|M, allow arbitrary additional primes, or settle unrestricted Erdos#7.
The existing seven/eight-prime arbitrary-height results remain prior
results, as attributed in Report725. The present conclusion applies the
common quantitative source to the stated larger support class; no claim
of literature priority or new Lean verification is made.

The next missing interfaces are the core's higher-power removals and
additional fresh-prime blocks on that same actual source. A scalar
union-fee failure does not preclude a joint fibre proof: Report725's
19*(59/840)>1 bound for q=29,r=31 is overcome here by(F2)–(F5).
