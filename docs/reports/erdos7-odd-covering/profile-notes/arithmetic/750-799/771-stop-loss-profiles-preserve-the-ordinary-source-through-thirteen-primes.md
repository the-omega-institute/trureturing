# Stop-loss profiles preserve the ordinary source through thirteen primes

The ordinary eight-prime source of
[763](763-a-joint-query-head-admits-an-unrestricted-prime-tail-above-1400.md)
admits a full increasing-convex query comparison, not only its displayed
second moment. Retaining its stop-loss profile through five half-clipped
extensions at31,37,41,43,47 leaves distorted survivor mass greater than1/125.
Consequently a finite family of pairwise distinct odd moduli m>1 on at
most thirteen primes, missing at least one of3,5,7,11, is noncovering. All original phases and
finite prime-power heights are unrestricted.

This uses the SAME original eight-prime source and caps as763, including
C17=4/3. It does not require a new source with better mass/Gamma ratio.
The scalar obstruction in
[767](767-the-exact-source-ratio-gap-before-an-eleventh-prime.md)
continues to hold for that scalar relaxation. The improvement comes from
retaining the nonlinear cost before the quadratic relaxation.
The proof and exact arithmetic below are ordinary mathematics, not Lean
verification. They do not settle unrestricted Erdős #7 or assert priority
over external noncoverage results.

## The full comparison on one physical source

For a full finite CRT period Q, a complete query layout Phi chooses one
prefix cylinder at every numerical divisor d|Q, including d=1. Write

    L_Phi(x)=sum_(d|Q) 1_(x in Phi_d).

The query residues are arbitrary and need not be mutually compatible.
They do not change the original forbidden family or the physical law.
For p>1 and A>=1/p define the anchor comparison submeasure on j>=0 by

    pi_anchor(p,A)(0)=A-1/p,
    pi_anchor(p,A)(j)=(p-1)/p^(j+1), j>=1.

For 0<=C<=p define the normalized capped comparison law

    pi_cap(p,C)(0)=1-C/p,
    pi_cap(p,C)(j)=C(p-1)/p^(j+1), j>=1.

Let Pi0 be the product of the two anchor factors(3,1/2),(5,3/4) and
the six capped factors

    (7,3/2),(13,3/2),(17,4/3),(19,9/5),(23,11/7),(29,7/4).

On this product submeasure set M0=product_p(1+J_p). The ordinary source
mu0 constructed in763 has mass at least

    m0=10237584019/168750000000,

and, for EVERY complete Phi and nonnegative increasing convex f,

    integral f(L_Phi) dmu0 <= integral f(M0) dPi0.       (1)

The quantifiers are: for each fixed original family there is ONE
prescribed source, then(1) holds for every layout and cost. It is not a
source chosen after seeing a favorable query. Nor does a second-moment
bound alone imply(1).

Here is the direct source proof. The live law is dominated by the law
with the same fixed normalized full-coordinate kernels before deletions.
Enlarge its anchor from the actual A to P3^c times P5^c, as permitted by
the positive-linear domination statement used in763. These two restricted
Haar factors have masses1/2,3/4 and depth-e caps p^(-e). Extend the same
later kernels to removed histories; their caps remain the displayed C_p.

Apply the ordered-increment lemma from
[Schroeder edition1.0.1](../../../../../../Library/Arith/schroeder2026nine.md),
Section4, conditionally at the last coordinate, then backwards. Its
comonotone upper events have tail probabilities C_p/p^e. Labels at a
common depth remain separate; no original numerical label is discarded.
The two anchor coordinates use the same paper's subprobability comparison,
giving tails p^(-e) and the zero atoms above. At fixed auxiliary runs,
the full exponent inventory contains at most product_p(1+J_p) terms.
Monotonicity permits completing finite inventories to this product.
This proves(1). The independent auxiliary variables are comparison
variables only, unavailable to the actual conditional kernels.

The same argument applies at any full finite original heights; the
infinite auxiliary tails give an upper bound by nonnegative truncation.
For the costs used here their expectations converge by the geometric
moment formulas below. Undoing the source's prefix-preserving normalizations
does not change the family of admissible complete queries.

The finite random prefix injections of763 also preserve(1) for any
ordered eight-prime tuple dominating(3,5,7,13,17,19,23,29). For a fixed
target query, its pullback is at most one source query per full exponent
vector. Complete empty entries and apply the increasing cost inequality
for each injection, then average. The chosen source may depend on that
injection and the original family, but works for all target queries.

## Restriction and a new capped coordinate preserve the profile

For a comparison pair(Pi,M) put

    S_Pi(t)=integral (M-t)_+ dPi, t>=0.

Assume a current finite positive measure mu satisfies the analogue of(1).
Restricting mu to an actual survivor set decreases every nonnegative
cost integral, so preserves the comparison without renormalizing.

Next append a full prime coordinate q with any normalized conditional
kernel whose pointwise density is at most C relative to full-coordinate
Haar, with C<=q. Conditional ordered increments replaces the current
prefix indicators by a run J with law pi_cap(q,C). At a fixed J=j,
the load is a sum of old layouts L_0+...+L_j; missing finite-depth
layouts may be filled in to give this upper inventory. In general these
layouts have DIFFERENT old phases. Jensen gives

    f(sum_(e=0..j)L_e)
      <=1/(j+1) sum_(e=0..j) f((j+1)L_e).

Each right-hand integrand is an increasing convex function of one old
layout, so(1) bounds its integral by integral f((j+1)M)dPi. Averaging J
proves the new comparison with

    Pi'=Pi times pi_cap(q,C),   M'=M(1+J).              (2)

This uses one physical kernel for all layouts and costs. It introduces
no independence assumption on the actual prime coordinates. Subsequent
actual restriction again preserves(2).

## The exact clipping loss requires different exponent layouts

Let alpha(x) be the actual Haar fraction of the new q-fibre covered by
the assigned original classes. Group originals by their positive
q-exponent e. Pairwise-distinct numerical moduli provide at most one
old prefix query for each old divisor in that group. Fill missing old
queries to obtain a layout L_e. Then the correct pointwise bound is

    alpha(x)<=sum_(e>=1) q^(-e) L_e(x).                 (3)

It is generally invalid to replace all L_e by a single fixed layout.
To repair this, use weights w_e=(q-1)q^(-e), whose infinite sum is1.
For finite actual heights, fill the absent groups by arbitrary layouts
or by a zero summand before applying Jensen. Thus

    integral (alpha-delta)_+ dmu
      <=1/(q-1) sum_e w_e
                    integral (L_e-delta(q-1))_+ dmu
      <=S_Pi(delta(q-1))/(q-1).                       (4)

For 0<delta<1 use the normalized kernel of Chapter08: when alpha<=delta
its good-fibre density is1/(1-alpha) and its bad-fibre density is zero;
otherwise its good density is1/(1-delta) and bad density is
(alpha-delta)/(alpha(1-delta)). Direct integration proves normalization,
the cap C_delta=1/(1-delta), and the exact bad-mass identity

    nu(B)=integral (alpha-delta)_+ dmu/(1-delta).

These formulas remain valid on alpha=0 and alpha=1 without undefined
division, with the stated case split. The general comparison below
additionally requires C_delta<=q. Half and quarter clipping satisfy this.
After actual deletion, mass and comparison therefore obey

    m' >= m-S_Pi(delta(q-1))/[(1-delta)(q-1)],
    Pi'=Pi times pi_cap(q,C_delta).                    (5)

The complete profile closes under the declared operation. The source
is never replaced by a law separately optimized for the next cost.

The familiar scalar estimate follows from
(z-t)_+<=z^2/(4t): replacing S_Pi(t) by integral M^2/(4t) in(5) gives
the old quadratic deletion charge. This replacement is strictly lossy
for the present product comparator, which has positive mass at many
loads besides0 and2t.

## Exact all-height computation needs only finitely many small products

Each comparison factor R=1+J has

    anchor: mass=A, E R=A+1/(p-1), E R^2=A+(3p-1)/(p-1)^2;
    capped: mass=1, E R=1+C/(p-1), E R^2=1+C(3p-1)/(p-1)^2.

For any positive rational threshold T,

    S_Pi(T)=integral M dPi-T*mass(Pi)
             +sum_(m<T)(T-m) Pi(M=m).                 (6)

The last sum is finite because M is a positive integer. Its atoms are
computed by multiplicative convolution of factor atoms with R<T.
The first two terms use the COMPLETE infinite factor moments. Thus(6)
neither truncates original prime-power heights nor discards a numerical
tail. It also handles noninteger rational clipping thresholds exactly.

For Pi0 these quantities are

    mass(Pi0)=3/8,
    integral M0 dPi0=109395/57344,
    integral M0^2 dPi0=26010182627/1040449536.

The last value equals763's old square bound; the stronger statement(1)
has the independent argument given above.

Use delta=1/2 at31,37,41,43,47, adjoining each capped factor after its
loss. Exact evaluation of(6) gives the following decimal displays;
the accompanying consumer retains the full rational values.

| Added reference prime | Threshold | Stop-loss before extension | Remaining mass lower bound |
|---|---:|---:|---:|
|31|15|0.188848676400|0.048077252797|
|37|18|0.183654221869|0.037874240471|
|41|20|0.195380340912|0.028105223425|
|43|21|0.217939922101|0.017727131897|
|47|23|0.223625090472|0.008004301876|

For a short rational certificate of the first three stages, their
stop-loss values are respectively less than188849/10^6,183655/10^6,
195381/10^6. Therefore their remaining mass is greater than

    m0-188849/(15*10^6)-183655/(18*10^6)-195381/(20*10^6)
      =9485479913/337500000000 >281/10000.

After all five stages the exact lower mass is greater than1/125.
For actual new primes above these references, fixed-cap comparison
tails C/q^e decrease, while delta(q-1) and(1-delta)(q-1) increase.
Monotonicity of the product load and decreasing stop-loss in its
threshold prove that the reference calculation upper-bounds every loss
and dominates the updated actual comparator.

If the original support has at most thirteen primes and omits one of
3,5,7,11, pad with unused odd coordinates, excluding a chosen missing
prime, to get thirteen coordinates. Their ordered tuple dominates
(3,5,7,13,17,19,23,29,31,37,41,43,47). Assign each original to its
largest coordinate, preserving its full exponent vector and phase.
Apply the eight-prime source and the five extensions. The positive
final measure avoids every original. Its finite CRT points project to
avoiding integers in the original coordinates.

## Verification and boundary

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_stop_loss.py)
pins and invokes763's consumer, freshly re-evaluating its32 source
formulas against their retained result. The old geometry maxima remain
the explicitly inherited premises. It independently convolves the
small-product atoms in(6), checks the full moments, all five clipping
charges, the rational lower bounds and the
[retained exact profiles](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_stop_loss.json).
Because the inherited source uses assertions, the canonical entry
rejects Python -O; its new arithmetic helper checks are explicit.

An independent mathematical review confirmed both uses of Jensen,
source enlargement under fixed kernels, prime-injection averaging,
restriction and the cap domain C<=q. An independent divisor-sum
convolution reproduced every retained small-product atom, full moment,
hinge, charge and remaining mass through all five stages, including
the negative53 ledger below.
These checks do not replace the ordinary proof of(1)--(5) with a finite
test over original families.

Appending53 with the same old source and another half-clipped step
gives a negative sufficient ledger, approximately-0.000492156. This
does not show that fourteen-prime families cover or that another
source or clipping schedule fails. The all-four-small-primes case
also remains outside the present source hypothesis. Any use of an
arbitrary larger-prime tail must still pay for its complete additional
loss; positivity of the finite head alone is insufficient.
