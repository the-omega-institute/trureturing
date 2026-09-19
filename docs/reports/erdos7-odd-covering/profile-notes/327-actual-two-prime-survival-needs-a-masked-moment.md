[Index](../marked_head_profile.md) · [Same-law target](j-source/303-the-same-law-gamma19-scalar-comparison-needs-joint-observations.md) · [Arbitrary-head transfer](../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md)

# Actual 19-to-23-to-29 survival needs a masked second moment

Two actual finite families have the same incoming19 law, the same23
kernel, and the same complete physical distribution of the29 forbidden
fraction, but different final surviving mass. Thus these scalar readings
do not determine the two-step loss in the general supported19 interface.
The missing observation is an actual23-survivor-weighted29 moment.
The identities below reuse problem-details/08 (T1--T5, W1--W3),
profile-note23 (CT1--CT3), and the scope distinctions in303/304/310.
This is an ordinary proof and exact finite counterexample, not a new Lean
result, an aligned-J counterexample, or unrestricted continuation.

## One actual family and its unnormalized laws

Fix one finite original forbidden family, with all original prime heights
resolved through29, including powers of earlier primes occurring in later
moduli. Let Q be its entire old19 period. Let sigma be a finite positive
measure supported on the actual complete19 survivors, with mass m>0.
It may be the actual killed19 measure itself; no renormalization is needed.

Use uniform full-prime fibres and put every actual p-ending forbidden class,
including pure p powers, into B_p. For p=23,29 choose the normalized clipped
kernel K_p of08(T4), with 0<delta_p<=1/2. Its killed part is
K_p^-=K_p 1_(B_p^c). Define

    D23=K23-K23^-, beta23=D23(1), beta29=1-K29^-(1),
    mu=sigma K23, xi=sigma K23^-, eta=xi K29^-,
    b23=sigma beta23, b29=mu beta29.

The physical29 source remains mu. The unnormalized xi is used only where
the actual survivor restriction requires it. Kernel normalization preserves
old coordinates; it does not assert independence of the actual events.
An AP kernel relative to a preconditioned pure-prime base may also enter
the abstract identities, but its own base masses and full-Haar prefix caps
must replace the numerical full-uniform formulas below.

## The exact survival observation and a two-step sufficient condition

Direct positive-kernel composition gives

    s29=eta(1)=m-b23-b29+omega,
    omega=sigma D23 beta29 >=0.                         (TS1)

This is the probability of the29 ending event on histories already removed
at23, measured with the SAME physical23 law and the same actual29 kernel.
It is not the product b23*b29. Positivity is exactly

    b23+b29-omega<m.                                    (TS2)

Write alpha29 for the actual full-uniform29 forbidden fraction, and
k29=1/[4 delta29(1-delta29)]. The existing clipped-quadratic bound is
beta29<=k29 alpha29^2. Therefore

    s29 >= m-b23-k29 M29_surv,
    M29_surv=xi alpha29^2
             =mu alpha29^2-sigma D23 alpha29^2.         (TS3)

Thus a directly useful additional observation is the second29 fibre moment
restricted by the actual23 surviving mask. Equivalently retain its physical
second moment and the removed23/29-square cross moment. The exact residual
in this inequality is also nonnegative:

    s29=m-b23-k29 mu alpha29^2
          +k29 sigma D23 alpha29^2
          +xi[k29 alpha29^2-beta29].                   (TS4)

The subtraction in(TS4) is justified on the same family before taking any
extremum. The deficit of one test or family cannot be subtracted from an
independently maximized source upper bound.

## A source-side bound retaining the first killed prefix geometry

Let q23=K23^-(1)=1-beta23, and for every actual23 depth t let

    M23_t^-(x)=max_(a mod23^t) K23^-(x,{y=a mod23^t}).

Extend Gamma homogeneously to finite positive measures. The existing
weighted rectangle proof with a subprobability row has the zero layer
weighted by q23 and all positive maximum-depth-t pairs weighted by M23_t^-:

    Gamma_(Q*23^H23)(xi)
       <= Gamma_Q(q23 sigma)
          +sum_(t=1..H23)(2t+1) Gamma_Q(M23_t^- sigma). (TS5)

This follows by the same pair expansion as08(W1): the old-old term is
exactly weighted by row mass q23; every other current intersection is
empty or one actual depth-t prefix. Weighted Cauchy--Schwarz applies to
each pair of its OWN old tests. Their residues and optimizers need not
agree. All original old cofactor labels, including1, remain present.

Apply08(T2) homogeneously to xi and the actual29 forbidden family. Its
distinct original29-ending labels give legal partial old23 loads, which
are completed separately to full layouts. With
S29(H29)=sum_(e=1..H29)29^-e, this gives

    M29_surv <= S29(H29)^2 * [Gamma_Q(q23 sigma)
              +sum_(t=1..H23)(2t+1)
                          Gamma_Q(M23_t^- sigma)].     (TS6)

Combining(TS3) and(TS6) supplies a two-step survival test without replacing
the killed23 law by its normalized or physical counterpart.

The actual killed prefix weights have a simple exact formula in the
full-Haar convention fixed above. Set

    alpha=U23(B23,x), theta=min(alpha,delta23),
    m_t=min_(a mod23^t) U23(B23,x intersect {y=a mod23^t}).

The killed row has density 1_(B23^c)/(1-theta), so

    q23=(1-alpha)/(1-theta),
    M23_t^-=(23^-t-m_t)/(1-theta).                     (TS7)

These formulas include alpha=0 and alpha=1; 1-theta is always positive.
For c_t=23^-t/(1-delta23),

    c_t-M23_t^-=
       23^-t(delta23-theta)/[(1-delta23)(1-theta)]
          +m_t/(1-theta) >=0.                         (TS8)

This killed cap differs from08(W2)'s normalized physical cap, whose
occupancy subtraction has coefficient theta/alpha. Substituting the
physical formula for(TS7) would silently put removed23 points back.

Let G=Gamma_Q(sigma). Define the nonnegative aggregate rebate

    R23=G-Gamma_Q(q23 sigma)
        +sum_(t=1..H23)(2t+1)
                    [c_t G-Gamma_Q(M23_t^- sigma)].    (TS9)

For A23(H23)=sum_(t=1..H23)(2t+1)23^-t, equations(TS3)--(TS6) give

    s29>=m-b23-k29*S29(H29)^2
                  *[(1+A23(H23)/(1-delta23))*G-R23].   (TS10)

This isolates the quantitative obligation: certify either the actual
masked moment in(TS3), or a sufficient same-source lower bound on R23.
The always-valid unit-term observation gives only

    R23 >= b23+sum_(t=1..H23)(2t+1)
                                 sigma(c_t-M23_t^-).

Indeed all complete old layouts have load at least1, so
c Gamma(sigma)-Gamma(w sigma)>=sigma(c-w) for0<=w<=c.
The stronger gain couples this weighted loss to the old test's deficit
from maximizing Gamma, as already explained at the end of08's saturation
example. Positive charge by itself does not force any additional gain.

All heights remain complete. One may use

    S29(H29)<=1/28, A23(H23)<=17/121.

If only depths through h are observed, retain the zero-layer rebate and
those first h nonnegative terms of R23; discard the unmeasured rebates,
not their costs. The complete generic cost tail is priced by

    sum_(t>h)(2t+1)23^-t
      =23^-h[(2h+1)/22+46/22^2].                     (TS11)

For example, with delta23=delta29=1/2 and m=1, the unoptimized sufficient
test is

    s29>=1-b23-[(155/121)G-R23]/784>0.               (TS12)

Using also b23<=G/484 gives the stronger-assumption sufficient criterion
R23>351G/121-784. This is a conditional measurement target, not a new
capacity claim. In particular325's bound on J cannot be inserted as G:
J is not Gamma19.

## The same scalar readings can give different actual surviving mass

Here is an explicit obstruction to recovering(TS1) or(TS3) from the old
source plus separate scalar stage readings. All original labels are
distinct, the two families use the same modulus inventory, and every
class in either family has a private integer. This is an arbitrary
supported19-law example, not an asserted aligned-J or prescribed-AP19
source fixture.

Let P={3,5,7,11,13,17,19}, Q=product P. At each old prime forbid1 mod p.
The old point x=0 mod Q survives. Take sigma=delta_0. Retain these two
23-ending classes, written in literal CRT coordinates:

    modulus3*23: (x3,y23)=(0,0),
    modulus5*23: (x5,y23)=(0,1).

At the only charged old point, alpha23=2/23. Choose delta23=1/23.
The normalized physical23 row has mass1/44 at y=0,1 and1/22 at each
other y. Its killed row is zero at0,1 and1/22 elsewhere. Hence b23=1/22.

Both alternatives add exactly the moduli7*23*29 and11*23*29:

| Family | Modulus7*23*29 CRT residue | Modulus11*23*29 CRT residue |
|---|---|---|
| A | (x7,y23,z29)=(0,0,0) | (x11,y23,z29)=(0,1,0) |
| B | (x7,y23,z29)=(0,2,0) | (x11,y23,z29)=(0,2,0) |

Take delta29=1/58. On an active29 row alpha29=1/29 and beta29=1/57.
For A the active rows are y=0,1, whose combined physical mass is1/22;
for B the active row is y=2, whose physical mass is also1/22. Thus

| Same-law quantity | A | B |
|---|---:|---:|
| Complete old source and actual23 kernel | identical | identical |
| b23 | 1/22 | 1/22 |
| Physical b29 | 1/1254 | 1/1254 |
| Physical mu alpha29^2 | 1/18502 | 1/18502 |
| omega=sigma D23 beta29 | 1/1254 | 0 |
| xi alpha29^2 | 0 | 1/18502 |
| Actual final survival mass | 21/22 | 598/627 |

The final masses differ by1/1254. All old19 observations, including its
entire incoming law and Gamma, are unchanged. Even the full physical
distribution of alpha29 is identical, so all its scalar moments agree.

To see actual irredundancy and activity, fill every unspecified prime
coordinate by2. For each designated original class, set its specified
coordinates to that class's CRT residue. The resulting point belongs to
exactly that class: the23 classes test only old3 or old5, while the29
classes test old7 or old11, which are independent CRT coordinates.
In particular a29 class supported on y=0 or1 at sigma's charged point
still removes genuine preceding survivors with old3=old5=2. Thus these
are not globally redundant29 labels. The all-2 point survives every class.

The [exact checker](../frontier/two_step_23_29_joint_obstruction.py) reconstructs all
11 original classes in both families, verifies all22 private CRT points,
and computes the23 and29 normalized/killed rows with exact fractions.
It checks the equal full physical distribution of alpha29, every entry
of the displayed table, and both same-law identities. This is a finite
fixture check with no family search, optimizer, or large-period scan.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/two_step_23_29_joint_obstruction.py
```

## What the current18 source bounds do and do not provide

317's eighteen observations are mass, mean, AP11-0/1/2, H2/3/5/6/8,
cost0, H4, square, factorial2/3/5, and costs48/49, on the common actual
357 source. Each scalar bound applies uniformly to its OWN old test.
They feed the original59 envelopes and52 costs; they are not weighted
moments of the actual23 or29 masks on sigma, mu or xi. The current
357 carrier and row-transport states also retain no such later masks.

Consequently there is no direct presently established substitution of
those18 upper bounds into M29_surv, omega, Gamma(q23 sigma), or
Gamma(M23_t^- sigma). The generic rectangle/cap bounds recover their
known scalar majorants, but a new quantitative improvement needs new
same-law mask weights or a theorem controlling them. The actual pair
above proves that old data plus physical alpha29 moments do not determine
the missing masked moments for the general supported19 interface. It
does not rule out a useful uniform lower bound restricted to the actual
aligned-J family class; that narrower bound remains unproved.

For a subsequent Gamma29 bound after proving s29>0, reuse CT1--CT3 with
primes23 and29 and the same literal zero29 and zero23 test blocks. Its
required observations include beta23*A^2, beta29*B^2, and removed23 mass
times the29 positive-increment energy. Those inherited loads cannot be
replaced by separately maximizing layouts. Proving survival through29
alone does not establish arbitrary later-prime continuation, as304's
finite-horizon distinction and310's family-aware example already show.

## A same-source hinge11 observation also suffices for23-to29 survival

Fix a finite actual original family whose357 source satisfies325's literal
guard: it lies in the effective9 chart, original45 and135 are present and
aligned in one surviving root1 mod9 cell, and

    qJ>=1-10^-14, rho<=2/675+10^-14.

Let nu13 be the SAME supported13 probability used by the original J
comparison, and retain its prescribed normalized physical17/19 kernels
and actual killed parts. Write

    eta19=nu13 K17^- K19^-, m=eta19(1),
    U=399926243355/1000000000,
    d=403-U=614751329/200000000>0.

Here m is the killed19 mass, not325's raw AP13 denominator E and not the
raw357 source mass. All old prime-power heights resolve the entire given
family, including earlier powers appearing in later-ending moduli.

The original52-cost comparison includes T13(81). Thus22(KC13), with
tau=81 and W=403, and325's bound on that SAME comparison give, for every
complete original through19 test A,

    integral(A^2-484)deta19<=U-403=-d,
    Gamma19(eta19)<=484m-d.                         (HC1)

This is the same homogeneous implication used in303; its old saturated
source numerical Gamma estimate is not transferred to the present source.
J itself is not Gamma19. Every complete test contains its unit term, so
Gamma19(eta19)>=m. Consequently

    m>=d/483=614751329/96600000000>0.                (HC2)

For each original23 exponent e, retain the partial old-cofactor load F_e
of the actual classes with modulus a*23^e. Complete F_e to an old19 test
A_e, keeping every present label's projected residue and adding residues
only at absent labels. Different exponents retain independent own tests.
Define

    T23=sum_(e=1..H23)23^-e integral(A_e-11)_+ deta19,
    H19,11=max_A integral(A-11)_+ deta19.            (HC3)

The second maximum includes EVERY complete original old19 test. These are
measurements on eta19, not hinges of a357 source law.

Use the full-uniform23 clipped kernel with delta23=1/2, placing all actual
23-ending classes, including pure powers, in its forbidden union. Its
actual fraction satisfies alpha23<=sum_e23^-e A_e. Since
11 sum_(e>=1)23^-e=1/2,

    (alpha23-1/2)_+<=sum_e23^-e(A_e-11)_+,
    b23=2 integral(alpha23-1/2)_+ deta19<=2T23.      (HC4)

No exponent's test is replaced by another exponent's optimizer.
Problem-details/08(T1) and the complete23 coefficient give

    A23(infinity)=sum_(t>=1)(2t+1)23^-t=17/121,
    Gamma(eta19 K23)<=(155/121)Gamma19(eta19)
                       <=620m-(155/121)d.           (HC5)

The unnormalized killed23 law is dominated by this physical law. Apply
the actual29 clipped kernel with delta29=1/2 to it. Since
sum_(e>=1)29^-e=1/28,08(T2)--(T4), in their homogeneous form, bound its
29 killed charge by its complete square divided by784. Hence the final
actual survivor mass satisfies

    s29>=(41/196)m+(155/94864)d-2T23.               (HC6)

Both current kernels are normalized row by row even on entirely forbidden
fibres; no intermediate positivity or conditioning is assumed. The final
strict test itself proves positivity. Complete geometric coefficients
include every original current exponent, regardless of its finite height.

Thus either of the following is sufficient for s29>0:

    T23<(41/392)m+(155/189728)d;                    (HC7)
    H19,11<(451/196)m+(155/8624)d.                  (HC8)

Indeed T23<=H19,11/22. Non-strict inequalities here also cover zero hinge
or zero intermediate mass; strictness is imposed only in the sufficient
tests. Instead of separately estimating mass and hinge, a consumer may
estimate the single signed objective

    max_A integral[(A-11)_+-451/196]deta19
                <(155/8624)d.

Its negative mass term must keep the actual eta19 mass or a valid lower
bound; domination by a larger physical measure cannot be used on that
signed objective without separately pricing the mass.

Using only the already established(HC2), a test needing no further mass
measurement is

    H19,11 < [451/(196*483)+155/8624]d
             =(94709/4165392)d
             =58222483618261/833078400000000
             =0.069888360589184643366... .           (HC9)

For comparison, discarding the positive mass contribution in(HC8) gives
the weaker sufficient target

    H19,11<(155/8624)d
            =19057291199/344960000000
            =0.055244930423817254174... .

The exact fractions govern both tests; the decimals only display them.
If an improved same-source U or measured m is available, use(HC7)/(HC8)
directly rather than the fixed conservative(HC9).

A finite observation of the sharper T23 can also retain its entire tail.
For every integer n>=1,

    (n-11)_+ <= (11/483)(n^2-1).

For n>=12 the difference after multiplication by483 is
(n-22)(11n-241)>=0 at every integer n; for n<=11 the claim is immediate.
By(HC1), H19,11<=11m-11d/483. Therefore the unobserved exponent part after h
is bounded by

    sum_(e>h)23^-e integral(A_e-11)_+ deta19
       <=23^-h H19,11/22
       <=23^-h(m/2-d/966).                        (HC10)

This pays every omitted exponent with its own lawful test. It does not
justify computing early integrals under a changed or truncated old law.

No value of H19,11 or T23 is established here.317's18 bounds belong to
the actual357 source and its original59 target envelopes; they do not
currently supply(HC3) on the post19 killed measure. The earlier hinge11
in profile-note08 is an interpolation on its different initial source,
not this statistic. A new transport bound, actual masked measurement, or
same-source upper certificate remains necessary. This conditional route
uses existing transfer and comparison theorems and does not claim a new
abstract theorem, a uniform rebate from active classes, survival already
proved through29, or continuation through arbitrary later primes.
