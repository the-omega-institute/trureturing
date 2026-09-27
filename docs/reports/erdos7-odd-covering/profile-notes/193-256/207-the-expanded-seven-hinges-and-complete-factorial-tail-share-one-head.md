[Index](../../marked_head_profile.md) · [Complete preceding comparison](206-the-second-seven-depth-improves-the-first-complete-ap11-block.md) · [Expanded seven interface](201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md) · [Complete factorial head](../129-192/174-the-pure-three-factorial-tail-retains-its-original-head.md) · [Exact original-cost identities](202-eight-original-costs-have-an-exact-load-two-remainder.md)

# The expanded seven hinges and complete factorial tail share one head

Two original quadratic costs retain one head across their complete
positive hinge expansion and the whole factorial tail. The resulting
uniform raw-square9 bound also strengthens202's eight exact integer
identities, together with174's complete uniform factorial bound.
All52 original costs are reaggregated on206's complete denominator.

The full comparison is

    K<=19623224597703524188214714920875489514886273
        /46029432886765179637490140688937184500000
      =426.31906080567376... .

This improves206 by1.6064249229092546... and remains above403.

The original cost bounds are

    Cost47<=125420431/38896200=3.2244905929113896...,
    Cost48<=17859883/4630500=3.8570096101932836... .  (EQ1)

These are whole-source bounds on both entire actual saturated K
faces, with r=rho=0,D=53/360 and L=1151/1800. Every original residue
and infinite exponent tail remains allowed. The result does not
assert an off-face extension, a new global K bound or an unrestricted
Erdos7 resolution.

## 1. Two exact positive-integer quadratic expansions

Put

    h_t(v)=(v-t)_+,
    Phi5(v)=(v-5)_+*(v-4)/2.

The original cost47 is the raw81 function with divisor2, and
cost48 is the raw81 function with divisor3. Their identities on
every positive integer v are

    (v²-81/4)_+=(19/4)*h4(v)+(17/4)*h5(v)+2*Phi5(v),
    (v²-9)_+=7*h3(v)+2*h4(v)+2*Phi5(v).           (EQ2)

Every coefficient is nonnegative. The checker reconstructs the
identities from the original functions, verifies every finite
transition and all coefficients of their infinite quadratic tails.
For the first identity both sides vanish at1,...,4; for v>=5 the
right side has quadratic coefficient1, zero linear coefficient and
constant-81/4. For the second, the only additional transition at4
has value7, and its infinite tail has constant-9.

Thus each entire original cost has the form

    f(v)=f(1)+sum_t a_t*h_t(v)+theta*Phi5(v),
    a_t>=0, theta=2.                              (EQ3)

Each application keeps that cost's own original test. It does not
identify the independent cost47 and cost48 residue choices.

## 2. The factorial charge stays with its own original head

For each original six-label layout ell,174 proves the whole bound

    integral_mu Phi5(A)<=J174(ell)+P,
    P=2539/3600.                                  (EQ4)

The head J174 includes the pure-five and pure-three replacements
in the original complete pair partition. Their subtracted pair
allowances are already inside J174. Consequently P remains the
entire original distinct-tail-pair complement, without any new
subtraction.

The helper reconstructs J174 for every one of the12500 original
layouts through the original public component APIs. It checks the
complete `head_components_sha256` against174, including each
pure-five and pure-three component, and recovers

    max_ell J174(ell)=319/2160,
    max_ell J174(ell)+P=2303/2700.                 (EQ5)

Let H2(ell,r21,s35) and H4(ell,r21,s35,c63,r105,s105) be201's
two complete upper bounds for sum_t a_t*integral_mu h_t(A).
They retain the same original head as J174 and retain their own
complete complementary tails. For the one fixed original test,
(EQ3) and(EQ4) therefore give

    integral_mu f(A)
      <=f(1)*D+theta*P
         +min(H2+theta*J174(ell),H4+theta*J174(ell)). (EQ6)

The factorial head is inside both branches before their maximum
over ell. The complete theta*P and f(1)*D are outside. This avoids
using a separately maximizing factorial head for the hinge part.
The mean correction, where a1 is nonzero, remains inside201's
complete H2 and H4 expressions.

## 3. The uniform joint maximum covers all original choices

For each cost, enumerate every original ell and21/35 choice.
Evaluate the complete joint old upper H2+theta*J174(ell). A known
candidate value b for the maximum bounds all50 containing63/105
choices whenever this joint old upper is at most b. Otherwise,
evaluate H4+theta*J174(ell) for every one of those choices and take
the minimum in(EQ6).

This covers all6,250,000 original choices for each cost. The
unexpanded branches have complete joint uppers below the final
maximum. All source LPs carry matching exact feasible primal and
dual values. A common integer scale includes both201's hinge scale
and all denominators of the174 factorial head.

The implementation uses an explicit joint objective and passes the
layout's factorial value directly. No global mutable head state or
replacement of imported functions is used. The certificate retains
the two complete maxima, branch counts and maximizing witnesses.

Adding the full outside term theta*P in(EQ6) gives(EQ1).

The exact scan counts and joint inner maxima are:

| Original cost | Outer branches bounded | Outer branches expanded | Four-projection evaluations, including500 seed choices | Exact LPs | Joint inner upper |
| ---: | ---: | ---: | ---: | ---: | ---: |
|47|124986|14|1200|126210|3527759/1944810|
|48|124995|5|750|125760|22656611/9261000|

Cost47 is controlled by layout(1,3,2,1,2,3,2), with projection
choices(r21,s35,c63,r105,s105)=(1,4,3,1,4) and J174=32/225.
Cost48 is controlled by layout(0,1,2,0,2,1,2), projections
(0,2,1,1,2) and J174=319/2160. Their different heads are kept
independent. The outside term in both rows is2539/1800.

## 4. The new uniform moments feed each original integer identity

The second original function in(EQ1) is exactly R9(v)=(v²-9)_+.
For every independent original test on the same actual survivor,
the available uniform bounds are now

    integral A²<=Q=8201/1800,
    integral R9(A)<=U9=17859883/4630500,
    integral h4(A)<=U4=295741/1543500,
    integral Phi5(A)<=T5=2303/2700.               (EQ7)

The last bound is174's entire factorial theorem(EQ5), which is
stronger than the older619/720 bound used in202. It is a uniform
bound on this separate original test, so using it here does not
add another credit to either of the two joint maxima in(EQ6).

For i in41,...,45,49,50,51,202 gives the exact original identity

    f_i(v)=a_i*(v²-1)+b_i*R9(v)+c_i*h4(v)
                       +e_i*Phi5(v)-k_i*1_(v=2).  (EQ8)

The helper rechecks each full identity against its original cost,
including all finite exceptions and the exact infinite polynomial
continuation. All four moment coefficients are nonnegative and
k_i>0. Integrating against the same actual survivor, with each
test's own load-two event, yields

    integral f_i(A_i)
       <=a_i*(Q-D)+b_i*U9+c_i*U4+e_i*T5.          (EQ9)

The omitted term is a nonnegative remainder for that test. No
positive lower bound on its load-two mass is claimed. The negative
mass coefficient uses exact D, and no independent mass upper is
substituted there.

Each new bound is minimized with its preceding206 bound. The same
whole-integer majorant propagation then retains every bound for
all52 original functions. The original positive cost weights,
signed mass coefficient and complete square coefficient are kept.

## 5. One complete numerator uses the unchanged206 denominator

The full denominator remains

    d>=1423627769987/17084377926000>0.

It contains all four independent AP11 blocks, the separate AP13
loss and the entire count tail3337/52707600. The numerator is
rebuilt from the complete accepted52-cost vector. No numerical
decrement from an earlier comparison is added separately.

The original offset is185694867601/8599322160, so the new full
comparison is that offset plus N/d.

Exactly indices41,...,45,47,...,51 improve. The full numerator is

    N<=3791829658027044318087117402935727344971
         /112432425289885839195928407537000000000
      =33.72541015859549...,

    N206-N=6411263195037274630030967
            /47894527320224612227200000
          =0.13386212483466697... .               (EQ10)

All other42 original costs keep their206 bounds. The complete
comparison decreases by

    6411263195037274630030967/3991013276503703805326400
      =1.6064249229092546... .

The [helper](../../frontier/moments-survival/expanded_seven_quadratic_comparison.py) and
[certificate](../../certificates/source_norms/moments-survival/expanded_seven_quadratic_comparison.json)
contain the reconstructed174 head digest, both joint scans, all eight
integer identities, the full cost vector and complete comparison.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/moments-survival/expanded_seven_quadratic_comparison.py --check
```

This is ordinary source mathematics with exact rational certificates.
Neither actual simultaneous attainment nor Lean verification is claimed.
