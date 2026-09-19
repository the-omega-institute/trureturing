[Index](../marked_head_profile.md) · [Complete heavy costs](201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md) · [Common complete square](199-one-six-label-head-controls-the-square-and-both-complete-crosses.md) · [Original all-load costs](65-endpoint-numerator-from-common-cost-constraints.md)

# Eight original costs have an exact load-two remainder

Eight complete original numerator costs admit the same four-function
representation, with an explicit nonnegative remainder supported
only at load two. The identities hold on every positive integer
load, not only on a bounded range or on a chosen actual source.
Their integration strengthens the complete201 face comparison while
retaining both new heavy costs and the full199 square.

    K<=40008937217043554501640531720643762707451921
        /88190635723129569535697728438314813000000
      =453.664234178442326970903010322108... .          (LT0)

The complete gain over201 is0.2959000609902735932.... The result
still exceeds the sufficient threshold403.

## 1. Four functions and one retained atom

For an integer v>=1 put

    Q1(v)=v²-1, R9(v)=(v²-9)_+,
    H4(v)=(v-4)_+, T5(v)=(v-5)_+*(v-4)/2.

Let f_i be the exact original cost at index i in the52-cost inventory.
Indices41--45 are the five original AP quadratic costs. Indices49--51
are the original raw81 functions with divisors4,5,6 respectively.
Then

    f_i(v)=a_i*Q1(v)+b_i*R9(v)+c_i*H4(v)+e_i*T5(v)
                                      -k_i*1_(v=2).       (LT1)

All the following coefficients are nonnegative, and every k_i is
strictly positive:

| i | a_i | b_i | c_i | e_i | k_i |
| ---: | ---: | ---: | ---: | ---: | ---: |
|41|312522845/736900164|127212451/736900164|948/143|632/429|636062255/736900164|
|42|34907/145002|1928/24167|0|0|9640/24167|
|43|4955/145002|56/24167|0|0|280/24167|
|44|1180709/4360356|404875/4360356|0|0|2024375/4360356|
|45|198959/4360356|1975/622908|0|0|9875/622908|
|49|63/128|65/128|0|0|189/128|
|50|18/25|7/25|0|0|7/5|
|51|27/32|5/32|0|0|25/32|

To prove(LT1), evaluate the original functions at every integer
below the larger of5 and their original polynomial entrance. The
difference between the positive combination and f_i is zero except
at2, where it is exactly k_i. Above that entrance the combination
has polynomial coefficients

    constant:  -a_i-9b_i-4c_i+10e_i,
    linear:     c_i-(9/2)e_i,
    quadratic:  a_i+b_i+e_i/2.                         (LT2)

For each row these equal the original exact constant, zero linear
coefficient and leading quadratic coefficient. This proves the
whole infinite continuation. In particular the first row's two
extra functions have cancelling linear terms; no unbounded linear
remainder is discarded.

These are direct identities for the existing original functions.
They require no hypothesis about which test layout produced v.

## 2. Every test retains its own remainder event

Let mu be one actual finite survivor measure and A_i its original
positive-integer test load. Write D=mu(1), and suppose the following
uniform bounds hold for every original test on this same measure:

    integral A_i² dmu<=Q,
    integral R9(A_i)dmu<=U9,
    integral H4(A_i)dmu<=U4,
    integral T5(A_i)dmu<=V5.

Integrating(LT1) gives

    integral f_i(A_i)dmu
      <=a_i*(Q-D)+b_i*U9+c_i*U4+e_i*V5
                                        -k_i*mu(A_i=2).   (LT3)

Discarding the last nonnegative charge gives a uniform upper bound.
No positive lower bound on mu(A_i=2) is asserted. Different original
tests need not have the same load-two event, layout or maximizing
source. Each application of(LT3) uses its own A_i and the same
actual mu; the uniform estimates permit the subsequent sum with
the original positive cost weights.

The negative mass coefficient uses the exact D. An unrelated upper
bound for mass cannot be substituted into that position.

## 3. Complete face consumer

On both whole actual saturated K faces use

    D=53/360, Q=8201/1800,
    U4=938213/4630500, V5=619/720.

The original index48 is exactly R9; its current201 upper is U9.
The H4 and T5 bounds retain their original complete source proofs.
For each of the eight indices take the minimum of the old201 cost
upper and the right side of(LT3) without its final charge. Keep
the other44 costs, the signed mass coefficient and the complete
square coefficient unchanged.

All eight replacements are strict. The complete numerator decreases
by0.0236210494684487993... to

    7755859413418575373479498007323169389317
      /224864850579771678391856815074000000000.

The denominator stays50511415637/632754738000>0. Together with the
unchanged offset185694867601/8599322160 these give(LT0).

This evaluates one complete numerator. It does not add decrements
obtained using different numerator vectors or different denominators.
The denominator still includes every AP11 block, the separate AP13
loss and the complete infinite count tail. All original independent
residues and infinite exponent tails remain in their source bounds.

The [helper](../frontier/load_two_cost_remainders.py) and its
[certificate](../certificates/source_norms/load_two_cost_remainders.json)
retain the eight complete integer identities, their low-load gaps
and identical infinite polynomial tails, the entire201 cost vector,
and the complete numerator and denominator.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/load_two_cost_remainders.py --check
```

These are ordinary algebraic identities and rational certificate
checks. The consumer is restricted to the stated actual faces;
the identities themselves hold on all positive integer loads.
No actual attainment, positive load-two mass, Lean verification,
new global K or unrestricted Erdos7 resolution is claimed.
