# A joint second moment extends complete cubic tails to ten primes

Let r_1<...<r_10 be any ten odd primes. Consider a finite family of
pairwise distinct numerical moduli greater than one, supported on these
primes, with one arbitrary globally fixed residue at each modulus.
Require every mixed modulus supported on r_1,...,r_7 to be squarefree
or to have some prime exponent at least 3. Pure powers are unrestricted,
as are all original moduli touching r_8, r_9 or r_10. Then the Haar
density of the complete survivor satisfies

    H(U)>=1173087/3604832000>1/4000.                    (JM1)

The number of originals and their finite exponent heights are unrestricted.
Mixed means at least two prime divisors. The restriction still excludes
arbitrary non-squarefree mixed labels of maximum exponent 2 on the first
seven coordinates. It does not settle unrestricted Erdős #7.

The proof reuses [Report591](591-two-centre-star-boundary-closes-complete-height-three-tails.md)'s
actual seven-prime source and joint star boundary, but controls the complete
second moment needed by [Chapter08](../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md).
This extends the support from nine to ten primes. Report591 retains its
stronger density and extra-square allowance on its nine-prime domain.
This is ordinary mathematics with exhaustive exact rational arithmetic,
not a new Lean result.

## 1. The same seven-prime source, before continuation

First take P={3,5,7,11,13,17,19}, with new primes 23,29,31. Let rho,
J, g_T and the six screens A_T,B_T,C_T,D_T,E_T,F_T be exactly those of
Report591 TC2--TC8. In particular,

    eta=rho restricted to U_P intersect J^c,
    s=eta(1)>=s_0(t)=a(t)-L(t),
    eta<=D H_P, D=3458/405.                           (JM2)

U_P avoids every actual P-supported original. Auxiliary star deletions
remain in eta, including slots where no positive-mass original was present.
All original residues and complete pure survivors are fixed before any
query is chosen. The ternary root mass t lies in [1/3,2/3].

This eta is taken BEFORE Report591's continuation through 23 and 29.
No budget from that continuation is spent or reused in the present proof.

For a P-supported numerical modulus d put

    q_d(eta)=max_(a mod d) eta([a]_d), q_1(eta)=s.

Choose a finite head period Q resolving all P-coordinate exponents of
every original, including those also touching the new primes. A complete
query layout selects one residue b_d for each divisor d of Q, including 1.
Its phases need not be mutually compatible. Define

    Gamma_Q(eta)=max_b integral [sum_(d|Q)1_[b_d]_d]^2 deta.

The homogeneous convention allows eta to be a subprobability.

## 2. Ordered query pairs and all-height screen weights

For fixed query moduli d,e, their cylinders intersect in either the empty
set or a single cylinder of modulus lcm(d,e). If f divides Q, the number
of ordered pairs (d,e) with lcm(d,e)=f is

    c(f)=product_(p|f)(2 v_p(f)+1).

Indeed, at a coordinate of exponent h, exactly 2h+1 ordered nonnegative
exponent pairs have maximum h. Therefore, for every layout,

    Gamma_Q(eta)<=s+sum_(1<f|Q)c(f)q_f(eta)
                <=s+Wbar(t).                         (JM3)

Wbar is obtained by applying TC8's SAME six screens and summing every
numerical query label and every height. It is an upper bound, not an
assertion that all independently maximal cylinder masses are attained
by one query layout.

For p>=5, the complete weighted coordinate series is

    omega_p=sum_(e>=1)(2e+1)c_p(e)
           =3/(p-1)+[2p/(p-1)^2+3/(p-1)]/(p-2).       (JM4)

At p=3 the first layer has weight 3; the deep series is

    sum_(e>=2)(2e+1)*2/3^e=2.

Since D_T,F_T already include the unweighted deep series 1/3, multiply
them by 6, while C_T,E_T are multiplied by 3. Thus, for S subset
{5,7,11,13,17,19}, T=S without 5, and omega(S)=product_(p in S)omega_p,
use X=A_T or B_T and (Y,Z)=(C_T,D_T) or (E_T,F_T), according as 5 is
absent or present. The complete weighted sum is

    Wbar=sum_(S nonempty) X omega(S)
         +sum_(all S) (3Y+6Z) omega(S).               (JM5)

The second sum includes S empty. The unit-unit pair was already counted
as s in JM3, and is not charged again in JM5. Geometric tails are summed
analytically; no cutoff on query or original heights enters the result.

## 3. One uniform head probability with Gamma below 170

For each of the 16^5 root/equality layouts, both s_0(t) and
169s_0(t)-Wbar(t) are concave functions of t. The block mass a(t) is
affine; every subtracted term is a nonnegative coefficient times an
affine function or a maximum of affine functions. Their minima over
[1/3,2/3] therefore occur at the endpoints.

The exact two-profile scan of all 2*16^5=2097152 endpoint cases gives

    min s_0=95343795217072807/456983714259072000>1/5,
    min (169s_0-Wbar)
       =9734678258390705651/101239469005086720000>0.    (JM6)

The mass minimum has layout code 214082 and t=2/3; the moment-margin
minimum has code 148546 and t=2/3, in Report591's layout encoding. At
the latter witness,

    s_0=95683229036595283/456983714259072000,
    Wbar=143647035377416939/4070582968320000.

Use the one actual probability mu=eta/s. Since s>=s_0 and Wbar>=0,
JM3 and JM6 imply

    Gamma_Q(mu)<=1+Wbar/s<170,
    mu<=5D H_P.                                      (JM7)

Neither the source nor the original phases depend on the maximizing
layout used to define Gamma. In particular, this does not select a
different survivor law for each query.

## 4. Three capped-deletion steps on one physical law

Apply Chapter08 T1--T5 at new primes 23,29,31 with

    delta_23=2/5, delta_29=9/20, delta_31=1/2.

Assign each new original to its largest new prime. Its old cofactor
retains every earlier exponent and original phase. Numerical distinctness
gives a partial old query layout at each new-prime exponent; pure new
originals use the unit cofactor. Complete original heights are retained.

Starting from g=170 and v=1, propagate the certified bounds

    charge=g/[4 delta(1-delta)(q-1)^2],
    v'=v-charge,
    g'=g[1+(3q-1)/((1-delta)(q-1)^2)].                (JM8)

Here g bounds the joint moment of the physical law, and v bounds its
mass on the complete survivor. The normalized conditional kernels
preserve the entire previous joint law. They may keep mass on forbidden
fibres; the probability is not conditioned on survival between steps.
All forbidden sets are accounted for on this same law.

| After prime | Certified survivor mass v | Joint moment upper bound g |
| ---: | ---: | ---: |
|23|3683/5808|76160/363|
|29|1464319/4024944|2344640/9317|
|31|1694459/20124720|127079488/419265|

Every survivor bound is positive. The three conditional density caps
multiply to

    (5/3)(20/11)2=200/33.

Together with JM7 the final physical law has density at most
5D*(200/33) relative to full Haar. Its survivor mass gives

    H(U)>=[1694459/20124720]*33/(1000D)
         =1173087/3604832000>1/4000,

proving JM1 on the first ten odd primes. The full head period can be
lifted to any additional P-heights used by a new original; JM3--JM7
already cover them uniformly.

## 5. Transport to any ten ordered odd primes

Reuse [Chapter33, Section2](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md)'s
digitwise injection. At every coordinate i and every digit position,
inject the source alphabet of size p_i into the target alphabet of size
r_i>=p_i using an independently uniform additive shift modulo r_i.
Work at finite heights resolving all original target constraints.

For every fixed injection F, the inverse image of a target original is
empty or one source cylinder with the same complete exponent vector.
Distinct numerical target moduli give distinct source numerical moduli.
The hypotheses in JM1 depend only on these vectors and which of the
ten coordinates they use, so the pulled-back family satisfies them.
Consequently its source Haar survivor has mass at least the constant h
in JM1, for every F.

For every fixed source point, averaging its shifted image gives uniform
target Haar. If U_target is the actual target survivor, then

    H_target(U_target)=E_F H_source(F^(-1)(U_target))>=h.

This uses prefix cylinders, not a ring homomorphism between unequal
prime moduli. It reuses the existing transport argument and establishes
the stated ten-prime corollary; it does not remove the first-seven
mixed-square restriction.

## 6. Verification and the remaining continuation gap

The [producer](../../frontier/cover-geometry/two_centre_moment_profile.py),
[integer engine](../../frontier/cover-geometry/two_centre_moment_scan.cpp),
and [data](../../frontier/cover-geometry/two_centre_moment_profile.json)
retain both profiles, all 192 coefficient rows, endpoint extrema, and
independent rational reconstructions of their witnesses. The producer
reuses Report591's original-loss coefficients and source definition;
JM4--JM5 supply the new query weights. Its signed integer accumulation
bound uses 101 bits, below the engine's checked 126-bit bound.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_centre_moment_profile.py

All 25 checks pass, including the complete scan, exact witness
reconstructions and three positive continuation steps. These computations
support the finite boundary calculation; the all-height assertion uses
the analytic series and the source/transport arguments above.

For comparison, [Report304](../257-320/304-an-actual-star-blocks-a-universal-scalar-restart-at19.md)'s
exact inverse-capacity calculation gives a through-37 scalar threshold
between 148.12367893956504881375800837665461827 and
148.123678939565048813758008376655. The seed upper bound 170 does
not by itself pass that threshold. This is insufficiency of the present
bound and recurrence, not a covering example or an impossibility result
for a better source or a more informative continuation.

The two outstanding directions remain arbitrary first-seven mixed
squares and unrestricted additional primes. The former needs the actual
joint prefix phases, as the following regression makes explicit.

## 7. An actual mixed-square fibre that the old marginal cannot preserve

On P take pure originals 1 mod p for every p, and all eleven star
originals 0 mod 15, 0 mod 3q and 0 mod 5q for q=7,11,13,17,19.
Let eta_0=rho restricted to J^c and nu_0=eta_0/eta_0(1). These are the
star-only measures, not JM2's full-survivor eta after extra originals.
They have

    eta_0(1)=2087/3072.

Add the three distinct numerical classes

    2 mod45, 23 mod63, 35 mod99.                      (JM9)

On the first-root event

    E={x_3=2 mod3, x_5=2 mod5, x_7=2 mod7, x_11=2 mod11},

their ternary mod9 phases are respectively 2,5,8. They delete every
second ternary digit, although

    eta_0(E)=1/480, nu_0(E)=32/10435>0.

Thus any probability supported on the new complete survivor must change
the old full first-root distribution; its total variation distance from
that distribution is at least 32/10435. No internal redistribution
preserving the entire old root marginal can repair this fibre.

Replace only JM9 by 2 mod45, 2 mod63, 2 mod99. Each individual added
class has exactly the same eta_0 mass and the same first-root conditions
as before, but this family preserves two thirds of E. The distinction
is the joint occupation of second ternary digits. Therefore first-root
data plus the separate original masses do not determine the joint loss.

Nor can a low global query norm be used as a proportional local cost.
Here the complete nonunit norms satisfy

    R_P(nu_0)=145308365957/41544990720<566/49,
    R_P(nu_0 restricted E)/nu_0(E)
      =431784355/14155776>566/49.                     (JM10)

For a finite witness to the second inequality, every one of the 15
nonunit squarefree divisors of 3*5*7*11=1155 has a phase-2 query
containing E. They already give local cost at least 15 times its mass.

The [regression program](../../frontier/cover-geometry/mixed_square_dead_fibre.py)
and [data](../../frontier/cover-geometry/mixed_square_dead_fibre.json)
check both actual 21-original families, private witnesses for every
original, equal single-class masses, different joint losses, and the
complete query series. They also exhibit a global survivor, so this
is explicitly not a covering counterexample.

This instantiates existing dead-fibre and event-query principles from
Reports564, 571, 584 and 586 at the remaining mixed-square boundary of
Report591. It is a regression for proposed marginal-preserving repairs,
not a new general impossibility theorem. The required next relation is
one controlling actual joint square deletion together with the cost of
changing the old boundary and continuing on a single resulting law.
