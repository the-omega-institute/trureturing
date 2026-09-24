# A weighted mixed inventory puts the actual survivor-Haar law in G

A finite actual distinct-modulus core on P={3,5,7,11,13,17,19} admits a useful sufficient condition stated entirely in its complete pure inventories and mixed numerical labels. If the mixed capacity defined below is at most 2/3, the uniform law on its FULL actual survivor belongs to [report534](534-one-entropy-budget-controls-every-pure-prime-chain.md)'s same entropy-density class G and has total occupied-mixed query cost at most 2. In particular, every core with at most eight shallow mixed labels and arbitrarily many original pure or deeper mixed labels satisfies the criterion. No special relative phases of those shallow originals are required. The three-label case has the sharper total mixed bound 9/16.

The construction is ordinary mathematics with fixed rational checks, not new Lean verification or a resolution of unrestricted Erdős #7. It supplies a sufficient region and closes the stated eight-label case inside report534's existing G-law route. It does not claim that every larger mixed inventory meets the criterion.

## Relation to existing results

[Report530](530-one-supported-law-controls-unused-and-deep-occupied-labels.md) defines the complete unused-label Gibbs budget, and report534 rewrites it as

    nu supported on U, nu<=Lambda H,
    R_unused(nu)+D_H(nu)<=log Lambda,

where alpha=7235955529/6075000000000, Lambda=1/alpha and H is product Haar probability. It leaves the shallow mixed core sum below delta=51863873/25500000, explicitly noting the trivial at-most-two-label case. Its triple-intersection density test already supplies the large-lcm screening condition; that direct specialization is not the result here.

Pure-coordinate survivor conditioning and product/delete estimates are existing project tools: see [chapter10's cylinder-profile construction](../../problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md), [report380](380-small-prime-survivors-and-original-haar-costs.md)'s complete pure survivors, and [report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md)'s actual pure-anchor conditioning. [Report439](439-actual-residual-lifting-and-exact-free-coordinate-cost.md) treats a different residual lifting and complete second-moment interface. Reports531--533 constrain other sampling/payment certificates; they do not preclude this particular actual survivor-Haar law. Reports535--536 require preserving one source law and every occupied numerical label, which the construction below does.

The additional bridge is the exact sum of UNUSED cylinder caps after removing the occupied pure and mixed numerical slots. Its small seven-coordinate envelope proves that this specific uniform survivor law satisfies G, rather than merely proving a standalone noncoverage or total-query estimate. No priority claim is made for the underlying conditioning operations.

## Complete pure inventory and weighted mixed capacity

First take an irredundant actual core M0 preserving the original complete survivor U. Every label removed when taking the core remains a query label and is unused relative to M0. All retained residues stay fixed globally.

For each p in P, the pure original p-power cylinders in M0 are pairwise disjoint. Otherwise one is contained in another and would be redundant even in the full family. Let S_p be their complete coordinate survivor and put

    u_p=H_p(S_p complement)=sum_(p^e in M0)1/p^e,
    w_p=1-u_p,
    a_p=1/w_p,
    W=product_p w_p.

All actual pure exponents are included, including those above 10^9. Then

    0<=u_p<=1/(p-1),
    1<=a_p<=(p-1)/(p-2),
    W>=W_min=935/4096,
    D_max=1/W_min=4096/935<9/2.                    (WM1)

Take the ONE product probability

    rho0=product_p H_p(. | S_p)=H(. | product_p S_p).

For every P-smooth numerical label d, including d=1, define

    K_d=(1/d)*product_(p|d)a_p,     K_1=1.

Every cylinder [b]_d has rho0 probability at most K_d. Define

    F=product_p(1+a_p/(p-1)),
    b=F-1-sum_p(a_p-1),
    v=sum_(d in M0, d mixed)K_d.                  (WM2)

Here v includes EVERY occupied mixed label, at every original height. It is a bound on actual mixed deletion under rho0, with no assertion of mixed independence. Different fixed phases may improve the actual deletion but are not optimized separately.

The complete Euler sum of nonunit caps is F-1. The occupied pure cap sum at p is

    sum_(p^e in M0)K_(p^e)=a_p*u_p=a_p-1.

Consequently the exact cap sum over the UNUSED numerical labels is

    sum_(d>1, P-smooth, d not in M0)K_d=b-v>=0.    (WM3)

This is an identity between sums of the explicit K_d. It is not subtraction of upper bounds from an actual query sum. The indexing retains all original labels removed from the core and all unused query heights.

## The unused-cap envelope is no larger than the original Euler tail

Put

    A=product_p p/(p-1)-1=212731/110592.

On the full box 1<=a_p<=(p-1)/(p-2), one has

    b<=A.                                       (WM4)

Proof. The expression b is affine in each a_p separately. For p>=5 its slope is

    (1/(p-1))*product_(q!=p)(1+a_q/(q-1))-1
      <=D_max*(p-2)/(p-1)^2-1
      <=D_max*(3/16)-1
      =-167/935<0.

The first inequality uses the maximum a_q for every other coordinate. The elementary bound (p-2)/(p-1)^2<=3/16 for p>=5 is equivalent to (p-5)(3p-7)>=0. Lower every a_p with p>=5 to 1; this cannot decrease b. Its remaining slope in a_3 is

    (A+1)/3-1=-8453/331776<0.

Lower a_3 to 1 as well. At that corner b=A. This proves the full-box inequality, not a finite set of sampled pure inventories. It allows absent primes and arbitrary finite pure heights.

## One full-support law satisfies all three budgets

Assume

    v<=2/3.                                     (WM5)

Let r=rho0(U). The actual mixed union bound gives r>=1-v>=1/3. Thus U has positive Haar mass h=Wr. Condition this same rho0 on avoiding ALL actual mixed originals:

    rho=rho0(. | U)=H|U/h.

This is one probability on the complete actual survivor, with full support there. Its density, unused-query sum and occupied-mixed query sum obey

    rho<=D_max/(1-v) H<=3D_max H<27H/2,
    R_unused(rho)<=(b-v)/(1-v)<=(A-v)/(1-v)<=3A-2,
    sum_(d in M0, d mixed)q_d(rho)<=v/(1-v)<=2.   (WM6)

The unused estimate first sums the cylinder cap inequality over unused labels using WM3. Its numerator is nonnegative. The last comparison uses A>1, so (A-v)/(1-v) increases with v. Each query maximum is computed under rho; no source law changes between labels.

The relative entropy is exactly D_H(rho)=log(1/h). Hence

    D_H(rho)<log(27/2)<8/3,
    R_unused(rho)+D_H(rho)<3A-2+8/3
                             =237307/36864
                             <13/2<log Lambda.    (WM7)

The logarithm bounds have elementary rational certificates. From e>8/3 and (8/3)^8>(27/2)^3 follows log(27/2)<8/3. From e<11/4, (11/4)^13<800^2 and Lambda>800 follows log Lambda>13/2. Also 3D_max<Lambda. Thus rho belongs to report534's original G without spending a second entropy budget or changing its density cap.

Since 2<delta=51863873/25500000, WM6 pays report534's entire remaining shallow mixed sum, and in fact pays every occupied mixed query. Independently, the same elementary profile gives the direct total-query bound

    R_P(rho)<=(F-1)/(1-v)<=3(D_max-1)
             =9483/935<565/51.                   (WM8)

The direct bound is the ordinary product/delete consequence. WM3--WM7 additionally certify that its particular source law is inside G, which a standalone total-query bound would not imply.

## A finite certificate retaining every deeper original

Let B=10^9. To certify WM5 without listing every higher-depth mixed term in v, set

    s_B=sum_(d in M0, d<=B, d mixed)K_d,
    v_hat=s_B+(1/W)*tau_P(B),
    tau_P(B)=sum_(P-smooth d>B)1/d.

Because K_d<=1/(W*d), all occupied deeper mixed originals together cost at most tau_P(B)/W. Therefore

    v<=v_hat,
    v_hat<=2/3  implies WM5.                      (WM9)

The retained tail may overcount deep pure and unused labels; that is a conservative upper bound. No original is removed from U. One can replace each a_p by (p-1)/(p-2) and 1/W by D_max to obtain a purely numerical sufficient certificate from the shallow mixed label inventory.

The exact tau_P(B) already retained in report530 is less than 1/200000, and D_max*tau_P(B)<1/10000. The present arithmetic consumer reads that pinned result; it does not regenerate the label inventory or rerun its producer.

## The three-label case is covered uniformly

Every mixed label has at least two distinct prime factors. The factors

    (p-1)/(p*(p-2))

strictly decrease with p>=3, adding a new prime factor multiplies the cap by a number below one, and raising an exponent multiplies it by 1/p. Thus the largest saturated mixed cap is

    K_d<=8/45, attained by the envelope at d=15.

If at most three shallow mixed core labels occur, then

    v_hat<=3*(8/45)+D_max*tau_P(10^9)<2/3.        (WM10)

All other original pure labels and every original deeper mixed label are retained. Equations WM5--WM7 give the requested rho in G, and even the coarse bound gives shallow mixed query sum below 7/6, far below delta. The statement is uniform over all original phases and all remaining finite heights.

Numerical distinctness permits a sharper optional bound without a scan. The three largest distinct saturated mixed caps are at 15,21,33. To see this, a mixed label without 3 costs at most Kmax(35)=8/175. A label containing 3 and 5 other than 15 costs at most Kmax(15)/3. A label containing 3 and 7, but not 5, other than 21 costs at most Kmax(21)/3. Every remaining mixed label containing 3 costs at most Kmax(33)=20/297. These alternatives prove the top-three claim. Their sum is

    S=8/45+4/35+20/297=3736/10395.

Moreover 9/25-S=31/51975>9/400000, while D_max*tau_P(B)<9/400000. Hence

    v<=S+D_max*tau_P(B)<9/25,
    sum_(all occupied mixed d)q_d(rho)<9/16.       (WM11)

The strict upper bound 9/25 is supplied by the retained tail margin. This strengthened conclusion also includes the deeper occupied mixed queries, not merely the three shallow terms.

## At most eight shallow mixed labels need no phase condition

Outside the three labels 15,21,33, every saturated mixed cap is at most 8/135. If 3 is absent, the cap is at most 8/175. If 3 and 5 occur and the label differs from 15, the cap is at most Kmax(15)/3=8/135. If 3 and 7 occur but 5 is absent and the label differs from 21, it is at most Kmax(21)/3=4/105. If 3 and 11 occur but 5 and 7 are absent and the label differs from 33, it is at most Kmax(33)/3=20/891. The remaining case containing 3 uses another prime at least 13, so its cap is at most Kmax(39)=8/143. Extra prime factors or larger exponents decrease these bounds. Every alternative is at most 8/135.

Consequently any eight distinct shallow mixed labels have total cap at most

    8/45+4/35+20/297+5*(8/135)=2272/3465.

The first three slots in this estimate are conservative even if one of those numerical labels is absent. Since

    2/3-2272/3465=38/3465>9/400000>D_max*tau_P(B),

every core with at most eight shallow mixed labels satisfies

    v<=2272/3465+D_max*tau_P(B)<2/3.              (WM12)

The general theorem therefore gives one full actual-survivor rho in G with all occupied-mixed query cost at most 2. This is a dominance classification, not a search over original phases or a generated numerical label inventory. No claim of optimality for the number eight is made.

## Verification and unresolved region

The [fixed consumer](../../frontier/cover-geometry/pure_survivor_mixed_capacity.py) and its [result](../../frontier/cover-geometry/pure_survivor_mixed_capacity.json) consume the retained [tail data](../../frontier/cover-geometry/phase_resampling_arithmetic.json), pinned at SHA256 da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f. Its final result has 20 exact checks, covering the general envelope constants, both logarithm certificates, G's density and entropy budget, the coarse three-label corollary and the eight-label capacity comparison. It performs no original-family scan or old producer rerun. The affine monotonicity and the distinct-label classifications are the ordinary arguments above.

The sufficient criterion need not hold for arbitrary mixed inventories. If its upper bound exceeds 2/3, no impossibility is inferred: actual phase overlap, smaller exact caps, another supported law or the joint methods of reports534--536 may still work. The existence of a suitable law for every larger shallow mixed core remains unresolved by this criterion. No part of this deduction implies that three mixed terms always have small sum under every law in G; it constructs the single required actual survivor-Haar law.

[Report541](541-shared-ternary-roots-certify-sixteen-mixed-heads.md) uses the ACTUAL mixed union loss l instead of v in the conditioning denominator, while preserving the exact unused-cap identity and l<=v. A joint block for the six originals 3p and an infinite-label cap frontier prove l<173/250 for every core with at most sixteen shallow mixed labels, so the same full-survivor Haar law belongs to G and has complete query sum below158050/14399<565/51. Its explicit irredundant 32-class core has eleven shallow mixed labels and actual v>2/3, separating the two sufficient hypotheses without refuting this report's conclusions.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_survivor_mixed_capacity.py
```
