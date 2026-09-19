[Index](../marked_head_profile.md) · [Same-source interpolation](183-the-original-signed-gap-retains-its-own-mass-through-interpolation.md) · [Previous complete union](179-the-wider-source-union-reaches-the-far-escape-boundary.md)

# The joint source gap and mass improve the complete global comparison

The complete actual-source comparison is

    K <= 10565606821587225526441284867937135354881778020767824045201/20747287612900610517562741273961662131285982487700000000
       = 509.252439100403570560623027... .                    (JG1)

It retains the complete local comparisons181 and170, all52 original
numerator costs, the full AP11/AP13 denominator, eight original
fallbacks and both full terminal errors. The improvement over179 is
0.020445672282561707211527.... The source complement now uses183's
joint gap/mass inequality. No separate upper bound for its quadratic
payment is asserted.

The controlling endpoint is sigma=1/18,rho=0. This is a boundary
of these inequalities, without any claim that one actual family
attains every relaxed equality. The smaller complete terminal gap
above403 is 106.253014100721712459447861....
Unrestricted Erdos7 remains unresolved; this is an ordinary proof
and exact finite consumer, not a Lean theorem or frozen result.

## 1. Keep the two complete source domains

For the same actual source, rho=S-S0>=0 and the actual marked slot
loss satisfies r<=5rho. The existing complete domains are

    D0: sigma<=1/20, rho<=1/1000, r<=1/200;
    D1: sigma<=1/18, rho<=1/13000, r<=1/2600.        (JG2)

The last condition in each domain follows from the first two and
the actual loss inequality; it adds no independent exclusion.
Profile181 gives K<=505.701239618792632674... on D0.
Profile170 gives K<=506.975514690183036952... on D1.
Both are strictly below(JG1). Their numerators keep every original
cost index0..51 and complete tails. Their denominators and remaining
mass coefficients are strictly positive.

Outside D0 union D1, it suffices to check the three closed regions

    0<=sigma<=1/20:        rho>=1/1000;
    1/20<=sigma<=1/18:     rho>=1/13000;
    1/18<=sigma<=1:        rho>=0.                (JG3)

Closing the endpoints only enlarges the region to be checked.
Every original effective source is covered by(JG2) or(JG3).

## 2. Apply the joint source bound before choosing a target

Write e(s)=gamma2*s-(gamma2-gamma1)*s^2, d=53/360 and b=1/360.
The original signed mass coefficient A is the one in71, not a
rounded conservative substitute. Profile183 proves, on every source,

    Phi(K0-h)>=e(sigma)-h*(d+b*sigma^2)+(A-h)*rho,
    0<=h<=H=(20/3)*gamma1.                       (JG4)

The proof reweights the true concave mass function before Jensen.
Consequently d+b*sigma^2 is a coefficient in this joint signed
bound; it need not bound S0 or the actual denominator separately.
The same actual rho occurs exactly once.

For each region in(JG3), let R be its residual lower bound.
Because A-h>0, insert rho>=R. The resulting polynomial

    gamma2*s-(gamma2-gamma1+h*b)*s^2-h*d+(A-h)*R

is concave in s. Its endpoint values therefore control its whole
closed source interval. The six endpoint decrement capacities are

|Branch|sigma|R|Capacity (decimal; exact rational in certificate)|
|---|---:|---:|---:|
|low_zero|0|1/1000|0.366173034578690616046655|
|low_low_radius|1/20|1/1000|0.553319900074325248919664|
|bridge_low_radius|1/20|1/13000|0.216679197523737463018801|
|bridge_wide_radius|1/18|1/13000|0.236482690374128637338323|
|outer_wide_radius|1/18|0|0.208249415279802143746192|
|outer_one|1|0|0.313006238328734060891108|

Their unique minimum gives

    h = 79947643802683680484682370257043938129799343609193/383903329069455998326568496825891644270043900000000
      = 0.208249415279802143746192...,
    K = K0-h.                                    (JG5)

The exact consumer checks0<h<H, A-h>0 and
gamma2-gamma1+h/360>0. At this h all six endpoint margins are
nonnegative, with equality only at sigma=1/18,R=0. Concavity and
residual monotonicity prove(JG4) throughout(JG3).

The smaller source radius1/20 remains a junction of complete local
theorems, while the far endpoint sigma=1 has positive margin. No
marked branch or extrapolation of its domain enters this proof.

## 3. Complete the original comparison

The two local actual-source theorems and the source-complement
argument jointly prove the effective-source bound. The exact
consumer then verifies each of the eight original fallback bounds
is below(JG1), retains the original positive survival factor, and
checks the original mass coefficient after the target change.
Thus every original branch of179 is present.

For the two terminal boxes, their entire existing error terms are
added without alteration. Their resulting sufficient gaps above403
are

    all20: 106.253014100721712459447861...;
    nonuniform: 106.472959508616238586597012... .

The exact box labels and error fractions are inherited unchanged
from179 and recorded in the new certificate. Neither a local bound
nor a positive sufficient gap is a proof or counterexample to
unrestricted Erdos7.

The [helper](../frontier/joint_gap_mass_global_comparison.py) and
[certificate](../certificates/source_norms/joint_gap_mass_global_comparison.json)
retain the source theorem and both local input closures, construct
all six rational endpoints, and check the complete fallback and
terminal interfaces. Every infinite tail remains governed by the
analytic proofs of the inherited complete inputs.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/joint_gap_mass_global_comparison.py --check
```
