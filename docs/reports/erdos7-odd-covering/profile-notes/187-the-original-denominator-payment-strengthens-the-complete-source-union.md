[Index](../marked_head_profile.md) · [Original denominator payment](186-the-original-survival-margin-pays-its-own-target-change.md) · [Previous complete comparison](185-the-joint-source-gap-and-mass-improve-the-complete-global-comparison.md)

# The original denominator payment strengthens the complete source union

The complete actual-source comparison satisfies

    K <= 1051509159125290189926379823581098597358300063/2065622326993962861279374212379668766484000
       = 509.051991442946582468234380... .                    (DG1)

The gain over185 is 0.200447657456988092388647.... The proof
retains exactly the two complete source domains181 and170, all52
original numerator costs and the full survival denominator, eight
fallbacks and both terminal errors. It replaces the complement's
joint mass payment with186's original allocated-denominator payment.

The sole controlling endpoint remains sigma=1/18,rho=0. The smaller
complete sufficient gap above403 is
106.052566443264724367059214....
Unrestricted Erdos7 remains unresolved. No actual-family attainment,
Lean verification or frozen-truth claim is made.

## 1. Reuse the complete local domains on their actual sources

The domains from185 remain

    D0: sigma<=1/20, rho<=1/1000, actual r<=5rho<=1/200;
    D1: sigma<=1/18, rho<=1/13000, actual r<=5rho<=1/2600.

Their complete bounds are505.701239618792632674... and
506.975514690183036952..., respectively. Both are strictly below
(DG1). Neither domain imposes an independent slot-loss cutoff.
Each retains all original numerator indices0..51, positive complete
denominator and remaining mass coefficient, and all exponent/count
tails proved in its original source theorem.

Outside their union,185's exhaustive three-region partition applies:

    0<=sigma<=1/20: rho>=1/1000;
    1/20<=sigma<=1/18: rho>=1/13000;
    1/18<=sigma<=1: rho>=0.                         (DG2)

The closed boundaries enlarge the complement and therefore suffice.

## 2. Use the same original survival margin in the target change

Let q=23/42, e(s)=gamma2*s-(gamma2-gamma1)*s^2. Retain186's exact
positive coefficients

    c0=240585528019/3208936500000,
    c1=90112853/106964550000,
    c2=272569433/3208936500000.

Its full-source theorem gives

    Phi(K0-h)>=e(sigma)-h*(c0+c1*sigma+c2*sigma^2)
                         +(A-q*h)*rho,
    0<=h<=H=0.618581269720449377... .                (DG3)

This result reweights both true concave-function coefficients before
Jensen and applies the same original allocated survival-margin lower
bound used in each signed-gap row. It does not subtract unrelated
lower bounds. The payment polynomial is a coefficient in this joint
bound; it is not asserted to bound the actual denominator separately.

For each interval in(DG2), substitute its residual lower endpoint R.
The result is a concave polynomial in s, with quadratic coefficient
-(gamma2-gamma1+h*c2)<0. The residual coefficient A-q*h is positive.
Thus all points in each region follow from its two endpoint checks.
Their exact rational capacities are recorded in the certificate:

|Branch|sigma|R|Decrement capacity (decimal)|
|---|---:|---:|---:|
|low_zero|0|1/1000|0.718671919556859689725243|
|low_low_radius|1/20|1/1000|1.085419372015106126450162|
|bridge_low_radius|1/20|1/13000|0.425246330734723643444644|
|bridge_wide_radius|1/18|1/13000|0.464087796357134909660313|
|outer_wide_radius|1/18|0|0.408697072736790236134839|
|outer_one|1|0|0.618581269720449377004927|

Choose their minimum,

    h=79947643802683680484682370257043938129799343609193/195615895331287812044356572920327140953854722968000
     =0.408697072736790236134839...,
    K=K0-h.                                        (DG4)

The minimum lies strictly inside186's interval[0,H]. At this h,
all six endpoint margins are nonnegative and only sigma=1/18,R=0
has zero margin. The other coefficient K0-b-h in186's original
survival-margin decomposition also remains positive. The complete
source theorem therefore applies throughout(DG2).

## 3. Preserve the entire original comparison

The exact consumer verifies that each complete local bound is below
(DG1), with all52 indices, positive denominator and remaining mass
coefficient. All eight inherited fallback bounds are below(DG1).
The original positive survival factor and division conditions remain.
All sources and carriers, including partial and empty carriers, are
covered by the existing full-source theorem or the original fallbacks.

Both full terminal errors are inherited unchanged from185. Their
resulting sufficient gaps above403 are

    all20: 106.052566443264724367059214...;
    nonuniform: 106.272511851159250494208365... .

The exact box coordinates and error fractions remain in the
certificate. None of these positive sufficient gaps is a covering
counterexample or a proof of unrestricted Erdos7.

The [helper](../frontier/joint_gap_denominator_global_comparison.py)
reconstructs186's full same-source denominator proof, checks all
six complement endpoints, and retains every complete inherited
local, fallback and terminal input. The
[certificate](../certificates/source_norms/joint_gap_denominator_global_comparison.json)
records the exact result and its input closure. The arbitrary-source
and infinite-tail claims use the accompanying ordinary proofs.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/joint_gap_denominator_global_comparison.py --check
```
