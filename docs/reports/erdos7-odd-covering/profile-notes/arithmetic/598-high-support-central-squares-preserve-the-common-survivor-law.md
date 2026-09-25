# All 800 high-support central-square labels can be added to Report597

This is an ordinary consequence of the completed [Report597 certificate](597-a-common-pair-survivor-law-closes-the-outside-square-slice.md) and a same-source restriction inequality. It is not new Lean verification and does not resolve unrestricted Erdős #7.

Let P={3,5,7,11,13,17,19}. Keep every original allowed by Report597, including all pure powers, all mixed P-originals with some exponent at least three or with v3,v5<=1, and every original touching23,29 or31. Add simultaneously every numerical label

    m=product_(p in P)p^e_p,
    e_p in{0,1,2}, max e_p=2,
    e_3=2 or e_5=2,
    number of nonzero exponents>=5.

There are exactly800 such labels, all new relative to Report597. Each may be absent or present once, with an arbitrary globally fixed residue. The combined survivor has

    H(U)>=26345885990886052732242307711
          /468579418066477236879360000000000
         >1/18000.

Equivalently, the new mixed-core condition is

    some exponent>=3, or
    (v3<=1 and v5<=1), or
    at least five prime divisors.

No original or query height is truncated.
[Report592](592-joint-second-moment-extends-cubic-tails-to-ten-primes.md)'s
finite-height digit-injection averaging transports this bound to any ten
ordered odd primes: every nonempty pullback cylinder preserves its exponent
vector, support cardinality and first-seven/last-three roles; distinct target
moduli remain distinct source labels. Averaging the shifted injections
restores target Haar. This does not add arbitrary further support primes.

## The homogeneous moment loses its unit mass under restriction

For each finite resolving height Q, Report597 supplies one actual submeasure eta<=rho, with rho<=D H_P, D=3458/405, and the uniform gate

    s-c Gamma_Q(eta)>=K,
    s=eta(1), c=1084133/201247200,
    K=548601319573/131072000000000.

Gamma_Q is the maximum of the complete squared query load INCLUDING THE UNIT QUERY, with one globally selected layout per maximization. The report's stronger unit-separated upper envelope implies this gate simultaneously at every height.

Let A be the union of the added actual original cylinders, set delta=eta(A), and eta_new=eta restricted outside A. For every complete query layout b its load L_b(x) is at least1, because the unit query is present. Consequently

    integral L_b^2 d eta_new
      =integral L_b^2 d eta-integral_A L_b^2 d eta
      <=integral L_b^2 d eta-delta.

Take the maximum over the SAME set of layouts:

    Gamma_Q(eta_new)<=Gamma_Q(eta)-delta.

Since eta_new(1)=s-delta,

    eta_new(1)-c Gamma_Q(eta_new)>=K-(1-c)delta.      (A1)

The coefficient1-c is justified by the unit term; merely invoking monotonicity of Gamma would only give the weaker cost delta. All query labels remain present. Choose Q to resolve all old and new originals, then any additional query heights; Report597's all-height statement covers each such Q.

## Raw source caps pay every new original once

Use the same actual product pure-survivor source rho from Report597. Its coordinate caps are

    kappa_3(e)=2/3^e,
    kappa_p(1)=1/(p-1),
    kappa_p(e)=1/[(p-2)p^(e-1)] for p>=5,e>=2.

For every fixed residue modulo m, rho(C_m)<=kappa(m)=product kappa_p(e_p). This uses actual product coordinates before the star/pair restrictions, not independence under the correlated pair-survivor law. Since eta<=rho,

    delta<=rho(A)<=sum_(present new labels m)kappa(m)
                   <=sum_(all800 labels m)kappa(m)=B.

Independent literal exponent enumeration and the support-generating polynomial give

    B=2931380251141127/2284918571295360000.

For the polynomial check, the coefficient of x^k in

    [(1+(2/3+2/9)x)(1+(1/4+1/15)x)
       -(1+(2/3)x)(1+(1/4)x)]
        *product_(p=7,11,13,17,19)
             [1+(1/(p-1)+1/(p(p-2)))x]

is the total cap for central-square labels with support k. Sum coefficients k=5,6,7. The respective label counts are400,304,96, giving800 in total. These are one jointly paid union, not separate budgets assumed simultaneously attainable.

Substitution in (A1) gives

    K_new=K-(1-c)B
       =26345885990886052732242307711
          /9055182074115772514304000000000>0.

The actual source and its density bound remain fixed; mixed deletions do not change the source's pure inventory. Positivity also implies eta_new has positive mass. The same capped continuation construction at23,29,31 applies to this one restricted head, with its three density multipliers multiplying to200/33. Therefore

    H(U)>=33K_new/(200D),

which is the displayed density bound. No previously selected continuation kernels are silently inherited from a different normalized head.

## Remaining central inventory and verification

Before this augmentation, the finite max-exponent-two central exclusion contains1213 mixed labels: at least one of e3,e5 equals2. After the800-label addition, precisely413 remain in this exponent box:

    support2:23 labels;
    support3:110 labels;
    support4:280 labels.

Thus 45,63,75 and the other low-support central-square configurations are not implicitly included. [Report596](596-a-six-leaf-boundary-admits-the-central-square-label63.md)'s separate63 result has not been combined with this theorem. Nor have individually affordable alternatives such as a particular25q been added on top of the800-label union.

The [producer](../../frontier/cover-geometry/central_high_support_augmentation.py)
and [data](../../frontier/cover-geometry/central_high_support_augmentation.json)
read the completed Report597 certificate. They read K directly, recover c
from all192 exact combined-coefficient identities, and recover D from the
recorded Haar consequence. The source JSON has no separate c/D fields, so
these recovery equations are explicit. The producer independently recomputes
c by the three continuation steps and D by the product-source density
formula. All five inherited source fingerprints match. The inherited277
checks and358963200-case coverage are reused; this computation does not
rerun that scan.

The new arithmetic enumerates all2187 exponent vectors, checks numerical
distinctness and factorization, retains the800 added and413 remaining
literal numerical labels, and compares each support's cap sum with the
independent generating polynomial. All37 named checks pass under

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/central_high_support_augmentation.py

The deletion inequality above is an ordinary proof; the finite program
checks its arithmetic inputs and resulting bound. Neither constitutes
new Lean verification.
