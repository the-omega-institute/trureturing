# Weighted distortion separates a valid external extension from an exhausted cylinder envelope

The two actual eleven-class heads from [Report715](715-actual-heads-obstruct-every-law-in-the-direct-scalar-continuation.md) admit arbitrary extensions through11,13,17,19,23,29 when those eleven classes are the complete subfamily supported on3,5,7. The added external originals may have arbitrary nonternary exponents; the whole family must have distinct odd nonunit moduli, support in the stated nine primes, and v3<=2. Explicit positive Haar-density lower bounds are given below.

Allowing additional 3,5,7-only high-power originals creates a different problem. For the same-source prefix construction and its sum-of-cylinder-cap second-moment envelope, no choice of the head probability law, the order of the six outside primes, or one scalar distortion parameter per step can pass the complete sufficient gate. Exact rational primal/dual certificates establish this obstruction. It does not exclude a sharper joint second moment, mixed first/second-moment bounds, or a different process.

These are ordinary proofs and exact rational certificates, not new Lean verification or a resolution of unrestricted Erdős#7.

## 1. Actual heads and the weighted distortion identity

Both heads contain 0 mod 3,1 mod 9,0 mod 5,0 mod 7. Their remaining classes are:

| Numerical modulus | Opposite-root phase | Same-root phase |
|---:|---:|---:|
|15|11|1|
|45|2|22|
|21|1|1|
|63|58|16|
|35|3|3|
|105|74|74|
|315|187|47|

Their actual survivor sets in Z/315 Z have 75 and 85 elements. These are literal numerical phases, not independent choices at different leaves.

Use the prime-exposure construction of [Balister–Bollobás–Morris–Sahasrabudhe–Tiba, arXiv1811.03547v1](https://arxiv.org/html/1811.03547v1). At step i, B_i is the union of actual new original classes, and alpha_i(x) is its proportion in the uniform new-prime fiber over the old CRT point x. The capped kernel K_i preserves the old marginal and has pointwise density at most 1/(1-delta_i) relative to the uniform new coordinate.

The paper's Lemmas 2.1,2.2 and 3.3 imply the following weighted version. Fix an old stage k and a nonnegative old-measurable f supported on the actual survivor set R_k. Then

    E_i[f 1_Bi]
       = E_(i-1)[f(alpha_i-delta_i)_+]/(1-delta_i)
       <= min{E_(i-1)[f alpha_i],
               E_(i-1)[f alpha_i^2]/[4delta_i(1-delta_i)]}.       (WD1)

For 0<delta_i<=1/2 this follows directly by multiplying the paper's fiberwise proof by the constant f on that old fiber. Old-measurable functions retain their expectations after every later step. Consequently a complete cover would force

    E_k[f] <= sum_(i>k) min{E_(i-1)[f alpha_i],
               E_(i-1)[f alpha_i^2]/[4delta_i(1-delta_i)]}.       (WD2)

This identity also describes an arbitrary finite starting measure eta_k=fP_k transported by those same kernels. It does not requireeta_k to be a probability or a thinning of Haar. Completely removed fibers retain their old mass; there is no assumption of survival in each fiber.

Theorem 3.2 of the paper supplies progression and moment bounds for its specified distorted measures starting from uniform Haar. Applying that numerical bound to a different head measure requires an additional comparison; WD2 alone does not give one.

## 2. Why the uniform Haar-domination shortcut is unavailable

Choose head distortion parameters zero, so the head reference measure is Haar. For the six subsequent primes take

    (delta11,delta13,delta17,delta19,delta23,delta29)
       =(7/22,5/14,23/60,17/40,25/54,1/2).                     (WD3)

The complete all-height Haar second-moment seed for 3,5,7 is 35/4. The standard recursion gives total later cost

    C6=571565231731969973/1234875417431040000
      =0.4628525466326147... <1/2.                            (WD4)

Ifeta has mass G, support in the actual head survivorsR, and eta<=kappa Haar, the uniform comparison would requireG>kappa C6. But support and domination always imply

    G/kappa <= Haar(R).                                      (WD5)

For the two heads Haar(R)=5/21 and 17/63, both belowC6. Thus this shortcut cannot work for any weights or mass supported on either head. Already the common pure-only support has Haar mass 8/21<C6. A source of mass at least 1/2 is not thereby a Haar subdensity of mass at least 1/2.

These sources have valid actual CRT carriers; what fails is a sufficiently small Haar-density cap. Requiringeta(a modd)<=kappa/d for every divisor d of the full head period is equivalent to pointwise domination, because the full-period cylinders are singletons. Checking only the separate prime marginals is weaker and insufficient: the 3 x 5 table

    [[3,2,0,0,0],[0,1,3,1,0],[0,0,0,2,3]]/15

has uniform 3- and 5-marginals but an intersection atom of mass 1/5, three times its Haar mass. The moment proof needs joint intersection information.

## 3. A common-source quadratic replacement

The [arbitrary-head joint-load transfer](../../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md) supplies the needed alternative. For a finite head measure eta define

    Gamma_Q(eta)=max_layout integral L_layout(x)^2 d eta(x),
    L_layout(x)=sum_(d|Q)1_(x=a_d modd).                      (WD6)

The unit divisor is included. A layout chooses one residue for each numerical divisor; these query residues need not be compatible. Every summand is evaluated on the same measure.

For a new prime q with scalar parameterdelta, that transfer proves

    Gamma' <= Gamma[1+a_q/(1-delta)],
    new forbidden mass <= b_q Gamma/[delta(1-delta)],
    a_q=(3q-1)/(q-1)^2, b_q=1/[4(q-1)^2].                   (WD7)

It expands pairs of actual query cylinders, bounds each new-coordinate intersection at its maximum exponent, and uses Cauchy–Schwarz for the two old layout loads. This proof accepts an arbitrary correlated old source. It is not a direct application of the paper's uniform-head product bound to a nonuniform measure.

For WD3, summing the homogeneous losses from an initial Gamma gives

    beta=571565231731969973/10805159902521600000,
    beta=C6/(35/4), 1/beta=18.904508711594577... .             (WD8)

An initial survivor measure of mass G therefore passes this continuation when G>beta Gamma.

## 4. Positive extension when the eleven classes are the complete head

Assume the listed eleven classes are the entire actual subfamily whose moduli have support contained in{3,5,7}. Every other original must contain at least one prime from{11,13,17,19,23,29}. All its phases and nonternary exponents are arbitrary, with whole-familyv 3<=2.

Choose one probabilityeta uniformly on the actual 75 or 85 surviving 315 residues, with independent Haar higher 5/7 digits. The head CRT period may include higher powers occurring in later mixed originals; this uniform extension supplies them.

Forj=0,1,2 andD subset{5,7}, write

    d(j,D)=3^j product_(q inD)q,
    C_(j,D)=max_(a modd(j,D)) eta(x=a modd(j,D)),
    Z_(j,D)=(2j+1)product_(q inD)[q(3q-1)/(q-1)^2].

For a prime exponent e, there are 2 e+1 ordered exponent pairs with maximum e. Higher-digit Haar transport gives a factorq^(1-e) relative to the first cylinder. Hence, including the unit term,

    Gamma(eta) <= Gamma_bar(eta):=sum_(j,D)Z_(j,D)C_(j,D).    (WD9)

Indeed sum_(e>=1)(2 e+1)q^(1-e)=q(3 q-1)/(q-1)^2. The three ternary exponents are retained exactly. Each bound dominates every finite head height; no original exponent is truncated.

The exact uniform-source values are:

| Actual head | Gamma_bar | Distorted survivor mass lower 1-beta Gamma_bar |
|---|---|---|
|opposite-root|23053/1350|1410672581287056212431/14586965868404160000000|
|same-root|21163/1224|1129480721542757861401/13225515720686438400000|

Both lower bounds are positive. The initial Haar-density cap is 315/75 or 315/85. The six later pointwise cap factors have reciprocal product

    product_(q)(1-delta_q)=24679/591360.

Therefore the complete actual family has Haar survivor density at least

| Actual head | Exact Haar lower bound | Decimal |
|---|---|---:|
|opposite-root|40909504857324630160499/42573234043414609920000000|0.00096092077044|
|same-root|32754940924739977980629/34058587234731687936000000|0.00096172341791|

This leaves all external phases and heights arbitrary but does not allow further 3,5,7-only originals. That restriction is essential to this positive statement.

## 5. Adding head-only high powers uses the same source

The eleven fixed labels exhaust every nonunit 3^j 5^e 7^f with j<=2 and e,f<=1. Distinctness forces any further 3,5,7-only label to have 5- or 7-exponent at least 2.

Allow any probability p on the actual 315 survivors, and extend it by Haar higher digits. Let C_(j,D) be its actual maximum shallow cylinder mass and

    L_D=product_(q inD)q/(q-1),
    A(p)=sum_(j,D)(L_D-1)C_(j,D).                           (WD10)

The first-cylinder identity gives the exact deeper cylinder ratioq^(1-e). Removing the all-one exponent vector from the complete geometric sum leavesL_D-1. Thus A pays every additional head-only high-power original once, including pure high powers.

Restrict that same eta by the actual additional head-only classes. The resulting nu has mass at least 1-A, and Gamma(nu)<=Gamma(eta)<=Gamma_bar. The joint sufficient gate is therefore

    A(p)+beta Gamma_bar(p)<1.                              (WD11)

No independently chosen source enters either term. Normalizing nu gives the same test, and no earlier tail budget is added again.

## 6. All prime orders and scalar distortion parameters have a common lower cost

The second-moment-only multiplicative bound WD7 has a homogeneous coefficient depending on the prime order and its parameters. LetS be a subset of the six outside primes. For a first prime q inS, parameter 0<delta<1, and a subsequent coefficient R, its value is

    b_q/[delta(1-delta)]+[1+a_q/(1-delta)]R.                (WD12)

A lower certificate consists of 64 rational valuesr(S), withr(empty)=0. For every q inS put T=S minus{q}. It is sufficient to verify the quadratic

    b_q+[(1+a_q)r(T)-r(S)]delta+[r(S)-r(T)]delta^2 >=0.    (WD13)

Multiplication bydelta(1-delta)>0 shows that WD13 means WD12, with R=r(T), is at least r(S). The multiplier of R is positive. Induction therefore proves the lower bound for every order and every parameter choice, including choices made jointly with the initial source.

The retained rational table has 192 subset/next-prime pairs. In every case the quadratic's leading coefficient is positive and its discriminant is nonpositive, so it is nonnegative for every real delta. Its full-set value is

    r({11,13,17,19,23,29})=105794741/2000000000>1/19,
    r(full)-1/19=10100079/38000000000.                     (WD14)

This proves a lower bound simultaneously for all 720 orders and one shared scalar parameter per prime in(0,1). Numerical square roots may propose such a table, but no numerical approximation is needed to verify its 192 rational quadratic inequalities.

## 7. Exact optimization still fails even at the more favorable coefficient 1/19

Put c=1/19. Since every coefficient in the preceding class is greater than c, it suffices to obstruct

    A(p)+c Gamma_bar(p)<1.                                (WD15)

This is a finite LP on 75 or 85 actual head cells. Normalize sum_x p_x=1 and impose, for every shallow mode and phase,

    sum_(x=a modd(j,D))p_x<=C_(j,D), p_x>=0.

There are eleven nonunit modes; the unit cap is exactly 1 and contributes the constantc. The objective coefficient of a nonunit cap is

    (L_D-1)+c Z_(j,D).

A nonnegative dual assigns weightsy_(m,a) with

    sum_a y_(m,a)<=(L_D-1)+c Z_(j,D)

for modem=d(j,D). For every feasible p its objective is at least

    c+min_(x in actual survivors)sum_(m,a:x=a mod m)y_(m,a).  (WD16)

Exact feasible primal and dual certificates attain equal values:

| Actual head | Exact minimum of A+Gamma_bar/19 | Margin above 1 |
|---|---|---|
|opposite-root|187297/166896|20401/166896|
|same-root|51419/45828|5591/45828|

The attaining primal costs are respectively

    A=91/366, Gamma_bar=145801/8784;
    A=133/536, Gamma_bar=80095/4824.

Thus no probability on either actual head, with Haar higher digits, can pass WD11 using the declared sum-of-cylinder-cap quadratic envelope and the WD7 second-moment-only continuation. This remains true for every outside-prime permutation and every shared scalar per-step delta in(0,1).

The boundary is specific. WD9 may overestimate the actual jointGamma; WD7 may overestimate its subsequent growth. The original paper also permitsmin(M 1,M 2/[4 delta(1-delta)]), which can outperform the second-moment-only bound. None of those sharper alternatives, row-dependent or adaptive parametersdelta(x), non-prefix source classes, or other distortion constructions is ruled out here. The negative certificate is not a covering example.

## 8. Exact verification

The certificates retain the actual numerical original classes, the common primal probability tables, and every dual modulus/phase weight. A standard-library rational consumer enumerates actual integers 0 through 314, reconstructs every phase fiber, verifies primal support and normalization, recomputesA and Gamma_bar, checks every dual mode budget and every surviving cell's dual coverage, and obtains the exact equalities in the table.

The same verification suite checks the 64-subset lower table through all 192 quadratic discriminants, the explicit positive-continuation parameters, and the conversion to Haar density. No optimizer is needed to consume the certificates. Optimization supplies candidate vectors; only exact rational feasibility and primal/dual agreement establish the reported minima.

The weighted identity uses BBMST Lemmas 2.1–2.2 and 3.3; the uniform comparison uses its Theorem 3.2. The arbitrary correlated-head replacement reuses the project's joint-load transfer. The resulting positive bridge and negative envelope certificate have the distinct scopes stated above.


The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_distortion.py)
reconstructs the [rational witnesses](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_distortion_witnesses.json)
and checks the [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_distortion.json).
It rejects unsupported primal atoms, violated dual budgets, stale output,
and invalid subset lower bounds without relying on Python assertions.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_distortion.py
```
