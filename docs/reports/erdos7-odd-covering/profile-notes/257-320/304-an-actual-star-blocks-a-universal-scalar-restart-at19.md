[Index](../../marked_head_profile.md) · [Joint-load transfer](../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md) · [Actual star construction](../../problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md)

# An actual star blocks a universal scalar restart at19

There is an actual finite family on the seven odd primes through19,
with nonempty survivors, for which every survivor probability satisfies

    Gamma19 > 53.71877660361228481616353125.

The existing full-height worst-case scalar recurrence T6, even with
arbitrary real controls at every prime, can proceed from19 through101
only when its incoming seed is below

    53.112508688514123588948565520565128... .

Consequently choosing a better survivor probability at19 cannot by itself
make this scalar route universal. The obstruction is to using only T6's
full-height worst-case coefficients at every subsequent prime. It does
not exclude retaining actual forbidden labels, omitting inactive steps,
using finite-height coefficients, or controlling joint deletion and test
energy. The exhibited family has explicit survivors; it is no covering
counterexample. A strategy that first proves extra necessary conditions
for a hypothetical covering family is not excluded by this example.

## Exact capacities for the inherited scalar recurrence

For a prime p put r=p-1, a=(3p-1)/r^2 and b=1/(4r^2). The existing T6 is

    R_p(f,delta) = f*(1+a/(1-delta))
                    / (1-b*f/[delta*(1-delta)]),
    0<delta<=1/2.

Every denominator must be strictly positive. The final step at q admits
some control exactly when f<(q-1)^2. This is the supremum of
4*delta*(1-delta)*(q-1)^2; equality is excluded.
Allowing1/2<delta<1 cannot improve the capacity: replacing delta by1-delta
keeps its denominator and decreases its numerator.

For a finite required output H>0, substitute t=delta/(1-delta). Then
0<t<=1, and R_p(f,delta)<H is equivalent to

    f < H / [(a+Hb)*t+(1+a+2Hb)+Hb/t].

This strict inequality also implies positivity of the original denominator:
after multiplication, H times that denominator equals a positive numerator
plus a strictly positive margin. Thus the transformation introduces no
inadmissible pole branch.

The variable part of the denominator is minimized at
t=sqrt(Hb/(a+Hb)), which lies strictly between0 and1. Indeed

    (a+Hb)*t+Hb/t-2*sqrt(Hb*(a+Hb))
      = [sqrt((a+Hb)*t)-sqrt(Hb/t)]^2.

The exact input capacity is therefore

    C_p(H)=H/[1+a+2Hb+2*sqrt(Hb*(a+Hb))].            (SC1)

Its reciprocal is

    1/C_p(H)=(1+a)/H+2b+2*sqrt(b^2+ab/H),

so C_p is strictly increasing in H. For any consecutive finite prime
list ending at q, begin with H=(q-1)^2 and apply C_p backwards through
the preceding primes. By induction the resulting number is precisely
the open incoming interval endpoint for feasibility of every step.
This considers all continuous controls, not a sampled control grid.

The exact rational companion encloses every radical by integer-square
comparisons and propagates the bounds monotonically. Selected capacities
for a seed after19 are:

| Last required prime | Capacity, displayed approximately |
| --- | ---: |
|23|484|
|29|271.2441789278905423|
|31|186.0888693687130369|
|43|107.3079487180801879|
|73|63.4501915967667449|
|97|54.6367684946353455|
|101|53.1125086885141236|
|127|47.0161785496520618|

The result includes all23 horizons from23 through127. Each interval has
width less than10^-30. Independently supplied rational controls, starting
strictly below each lower endpoint, pass all276 corresponding forward T6
steps with exact positive denominators. These controls confirm finite
feasibility; none is asserted to provide unrestricted continuation.

The two-step29 threshold is also
47432/(118+7*sqrt(66)). Passing just23 and29 therefore requires much less
than passing the complete subsequent list. Neither threshold by itself
is a sufficient condition for continuing through all later primes.

## An actual finite family exceeds the101 capacity

Specialize the existing complete-star construction to

    P={3,5,7,11,13,17,19}, H3=31, Hp=8 for p>3,
    Q=product_(p in P) p^Hp.

For each pure power p^e, forbid p^(e-1)-1 modulo p^e. Define its disjoint
side cylinders C_(p,e) by residue2*p^(e-1)-1. For each mixed modulus
3^i*p^j with p>3, forbid the CRT residue in C_(3,i) times C_(p,j).
Every other nonunit divisor of Q gets the zero residue. These remaining
mixed classes are redundant, because each pure p already forbids0 mod p.
All original modulus labels are distinct and receive exactly one residue.

Write S_p for the pure-power survivors, C_p for the union of the side
cylinders, and D_p=S_p minus C_p. The exact survivor decomposition is

    R_a={-1 mod3^31} times product_(p>3) S_p,
    R_b=C_3 times product_(p>3) D_p,
    R=R_a disjoint-union R_b.                       (SC2)

The CRT vector x3=1 and xp=2 for p>3 is an explicit survivor. The
coordinate argument and complete assignment are the existing star proof;
no assertion about arbitrary families being of this form is used.

For each CRT test center t, the coherent complete test has b_d=t mod d.
Its squared load is the product of (1+ell_p(xp,tp))^2, where ell_p is the
common p-adic prefix length. The existing two test distributions give:

* On R_a, fix t3=-1 and use independent uniform nonzero first residues
  at the other primes. The potential is at least
  D=32^2*product_(p>3)(p+2)/(p-1)=12103/2=6051.5.
* On R_b, use the existing depth-eight constant-potential coordinate
  laws. The committed floor table, restricted to these seven primes, is
  (44425,25593,17916,13925,13125,12215,11932)/10000.
  Its product is B=54.261390508699277592084375, a lower bound for the
  potential under the original certificate.

Mix these two test distributions with weights1/100 and99/100. At every
point of R its potential is strictly above

    L=min(D/100,99B/100)
     =99B/100=53.71877660361228481616353125.          (SC3)

Every coherent complete test includes the unit term and so has square
at least1. Thus the two mixture branches are at least D/100+99/100 and
99B/100+1/100 respectively, both strictly above L. Strictness does not
require recomputing the old tree potentials beyond their stored floors.
For any probability mu
on R, averaging over this one legal test distribution and interchanging
finite sums gives Gamma_Q(mu)>L. The test distribution is a proof of a
uniform lower bound; it imposes no independence on mu.

The exact L exceeds the upper enclosure for the through101 scalar
capacity by more than0.6062679150981612272149657294348. Hence any valid
scalar upper seed f>=Gamma_Q(mu) lies outside that method's feasible
interval, independently of how mu was chosen.

To make every later prime through101 physically present, one may add
the distinct classes0 mod(3p). They are already excluded by0 mod3, so
the survivor set is the old R times the new coordinate spaces. The old
test lower bound persists under arbitrary joint survivor laws by taking
their old marginal. This padding is unnecessary for the scalar arithmetic,
but makes its limitation explicit: T6 with worst-case full-height
coefficients discards exactly the redundancy that these actual labels
reveal. A method that retains that information is outside the obstruction.

## Verification and remaining scope

The [companion](../../frontier/cover-geometry/scalar19_capacity_star_obstruction.py) consumes
the committed star certificate through the existing artifact reader and
reuses its coordinate floors. It computes the new seven-prime product,
all finite capacities, the forward controls and their strict comparison.
The [result](../../certificates/source_norms/cover-geometry/scalar19_capacity_star_obstruction.json)
retains exact rational intervals and controls.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/scalar19_capacity_star_obstruction.py --check
```

Independent rational checks eliminate the radicals by positive squared
comparisons; a separate check uses the original concave quadratic in
delta. Both give the same enclosure and obstruction. The general star
construction and T6 are reused ordinary mathematics. This result adds no
Lean theorem, freeze, new universal Gamma bound, or unrestricted answer
to Erdős7. It identifies a route that cannot be repaired solely by
improving the choice of the supported19 probability.
