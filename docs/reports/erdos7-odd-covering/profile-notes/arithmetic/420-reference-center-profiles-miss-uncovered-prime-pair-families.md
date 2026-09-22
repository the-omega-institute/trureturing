[Index](../../marked_head_profile.md) · [Original no-prime budget](380-small-prime-survivors-and-original-haar-costs.md) · [Prime-star overlaps](382-prime-star-overlaps-and-no-prime-excess.md)

# Reference-centre profiles miss uncovered prime-pair families

There is an explicit family of **703 distinct odd nonunit congruences**
for which every reference-centre profile is strictly greater than one,
although the integer 2 is uncovered. Its largest modulus is 25591.
More generally, such profiles can be uniformly arbitrarily large on
noncovering families. These examples admit no expected-load-below-one
certificate under a translated uniform unit law or any positive mixture
of those laws.

The same family has an exact positive survivor formula under the unit
law once its joint overlaps are retained. These are ordinary finite
proofs and exact arithmetic controls, not Lean certification or a
resolution of unrestricted Erdős #7. No literature originality is claimed.

## The exact reference-centre interface

Let C consist of original classes a_i modulo m_i, with distinct odd
m_i>1, arbitrary canonical residues, and L=lcm_i m_i. Keep every
original modulus label. Put

    N_C(x)=sum_i 1_[x=a_i mod m_i],
    mu_s=uniform probability on s+(Z/LZ)^units,
    F_C(s)=sum_(i:gcd(a_i-s,m_i)=1) 1/phi(m_i).

Reduction from the units modulo L onto the units modulo m_i is
surjective, with every fibre of size phi(L)/phi(m_i). This follows
prime by prime from CRT: a unit modulo p^e has p^(H-e) unit lifts
modulo p^H, and a prime absent from m_i contributes all its units.
Consequently, for the very same mu_s and all original classes,

    mu_s([a_i mod m_i])=1_[gcd(a_i-s,m_i)=1]/phi(m_i),
    F_C(s)=E_(mu_s) N_C.                                  (RC1)

Whole coverage implies F_C(s)>=1 for every s. Conversely, any centre
with F_C(s)<1 proves noncoverage by the union bound. The strict
inequality is essential; the converse implication from all F_C(s)>=1
to coverage fails even when L is squarefree.

The value depends only on s modulo rad(L) and each a_i modulo
rad(m_i). This is a probability identity for a restricted family of
laws, not a freedom to choose each class's law separately.

## A prime-pair construction and its exact global minimum

For a finite set P of odd primes, take exactly the original classes

    0 modulo p           for every p in P,
    1 modulo pq          for every unordered pair p<q in P.   (RC2)

Unique prime factorization makes these numerical moduli distinct.
They are all odd and exceed one. The integer 2 belongs to none of
the classes. No covering assumption or quotient relabelling is used.

Write w_p=1/(p-1) and W=sum_(p in P) w_p. A centre coordinate
s modulo p outside {0,1} activates both the prime class and every
incident prime-pair test. Replacing that coordinate by zero removes
the prime contribution and leaves every prime-pair contribution
unchanged. Thus a global minimum is attained with all coordinates
in {0,1}; every such choice is realized by CRT.

Let B={p:s=0 mod p}; its complement has s=1. The prime classes
contribute W-sum_B w, while the surviving pair classes have both
primes in B. Therefore

    F_C(s)=W-b+sum_(p<q in B) w_p w_q,
    b=sum_(p in B) w_p.                                  (RC3)

The minimum over B has an exact exchange proof. Minimize

    h(B)=-sum_B w+sum_(p<q in B) w_p w_q.

If weight w is selected, deleting it cannot improve a minimizing
set, so the sum b_other of the other selected weights satisfies
b_other<=1. Replacing w by a larger omitted weight v changes h by
(v-w)(b_other-1)<=0. Repeated exchanges therefore give a minimizing
set that is an initial segment of the weights in decreasing order.
This is a statement about one common subset, not separately attained
termwise minima.

Adding the next weight w to such a segment changes h by w(b-1).
If P contains 3,5,7,11, then its four largest weights satisfy

    w_3+w_5+w_7=11/12<1,
    w_3+w_5+w_7+w_11=61/60>1.

Every later weight is positive. The minimizing prefix is exactly
{3,5,7,11}, whose pair sum is 41/120. Hence

    min_s F_C(s)=W-27/40.                                (RC4)

This holds for every finite prime set containing those four primes;
the other primes need not form a consecutive segment.

Take P to be the 37 odd primes from 3 through 163. Exact arithmetic gives

    W=19843435788369581/11827018732969440,
    min_s F_C(s)=11860198143615209/11827018732969440
                =1+33179410645769/11827018732969440>1.    (RC5)

There are 37+binomial(37,2)=703 original labels. The largest is
157*163=25591. A minimizing centre has residues zero at 3,5,7,11
and one at every other prime. Its least nonnegative CRT representative is

    2543597018249131922313887015587671367268452948875576441529581870

modulo

    2883076109987975829511815017668067153282692007803033159928034405.

The preceding initial segment, ending at 157, has W<67/40. Thus 37
is the first successful length within this particular prime-pair
construction on initial prime segments; no globally smallest
counterexample is claimed. The large period is not enumerated.

The reciprocal-prime sum diverges and 1/(p-1)>=1/p. By extending P,
RC4 makes min_s F_C(s) arbitrarily large, while 2 remains uncovered.
For any probability rho on centres, the same actual mixed law
nu=sum_s rho_s mu_s has

    E_nu N_C=sum_s rho_s F_C(s)>=min_s F_C(s)>1.           (RC6)

Thus randomizing or optimizing the centre cannot provide a
first-moment sum-of-class-masses-below-one certificate for this family.
This does not exclude a use of intersections or other joint information.

## A related full squarefree-divisor formula

For comparison, keep every nonunit divisor of the squarefree product
of P, assigning phase zero to primes and phase one to composites.
The same binary-centre reduction yields

    F(s)=W+product_(p in B)(1+w_p)-1-2 sum_(p in B) w_p.   (RC7)

For a minimizing B, removing a selected w cannot improve the value,
so the product over its other selected weights is at most two.
Swapping in a larger omitted weight therefore does not increase the
objective. A minimizing set again is a decreasing-weight prefix.
Its next-weight increment is w(product_previous-2). The first
crossing of two occurs at {3,5,7}, giving, whenever these primes are present,

    min_s F(s)=W-31/48.                                  (RC8)

For the 33 odd primes through 139 the minimum is
535926723659837/532748591575200>1. RC2 is the smaller retained
counterexample: it needs only the prime and prime-pair labels, not
all squarefree composites. Neither formula permits repeated moduli.

## What the complete profile retains

The threshold failure above does not mean that F_C always loses the
complete load function. If L is squarefree, CRT writes RC1 as a tensor
product of the prime-coordinate averaging matrices

    T_p=(J_p-I_p)/(p-1),
    T_p^(-1)=J_p-(p-1)I_p.                               (RC9)

Here J_p is the all-ones p by p matrix. Their product is the identity,
so the complete exact profile F_C determines N_C in this squarefree
case. The inverse has negative entries: pointwise F_C>=1 does not
imply pointwise N_C>=1. The counterexample RC2 has squarefree period
and therefore separates this order implication even without losing N_C.
Recovering N_C does not claim unique recovery of an original class
decomposition.

For general L, first average N_C over each fibre modulo rad(L).
The same tensor operator acts on that coarse load. Thus F_C determines
this averaged load, while higher prime-power phases can be lost.
For a concrete original-label example, the two families

    C_0={(0 mod 9),(0 mod 27)},
    C_1={(0 mod 9),(3 mod 27)}

have the identical profile

    F(s)=0 if 3 divides s, and F(s)=2/9 otherwise.

Yet their unions contain respectively 3 and 4 residues modulo 27.
Their numerical moduli remain distinct and unchanged. Consequently
the general profile is not a complete higher-phase or coverage record.

## Joint overlaps recover an exact survivor law

For RC2, a point survives every prime class exactly when each prime
coordinate is nonzero. Among these points it survives every prime-pair
class exactly when at most one coordinate is one. Hence, with L=product P,

    |H|=product_(p in P)(p-2)
          +sum_(p in P) product_(q in P, q!=p)(q-2)
        =product_(p in P)(p-2) (1+sum_(p in P)1/(p-2)).    (RC10)

This is strictly positive for every finite P. Its quotient by L is
the exact uncovered Haar density, with all original labels retained.

Under the very same law mu_0, let

    T(x)=sum_(p in P) 1_[x=1 mod p].

The coordinate indicators are independent Bernoulli variables with
probabilities w_p, all prime-class indicators vanish, and the entire
original load is N_C(x)=binomial(T(x),2). Therefore

    mu_0(H)=Pr(T<=1)
      =product_(p in P)(1-w_p)
           (1+sum_(p in P)w_p/(1-w_p))>0.                (RC11)

RC11 recovers survival from the joint load even when its mean RC1
exceeds one. It uses one fixed actual probability throughout.

The underlying unit law is already present in
[361, PR6](../321-384/361-prime-overlap-reservation-for-composite-parents.md),
[380, section 8](380-small-prime-survivors-and-original-haar-costs.md),
and [382, PS1--PS6](382-prime-star-overlaps-and-no-prime-excess.md).
After normalizing original prime classes to zero, their no-prime
region is exactly the unit set; its conditional Haar law is mu_0.
The present prime-pair family also satisfies comparable-class
disjointness. Its shared phase-one tests make the full overlap load
explicit, extending the same-law accounting of 382's prime stars.
These facts concern the actual example and the stated interfaces;
they do not settle arbitrary odd distinct families.

## Exact controls

[`reference_center_profile_obstruction.py`](../../frontier/cover-geometry/reference_center_profile_obstruction.py)
generates the 703 distinct original labels directly, verifies the
uncovered integer and an attaining CRT centre, and evaluates the exact
prefix minima and survivor formula. It checks RC1 by literal unit
averaging on small complete periods, independently counts their actual
survivors and loads, applies the squarefree inverse to recover N_C,
and verifies the two higher-phase families modulo 27. Input validation
uses explicit exceptions and remains active under optimization.

Run from the repository root:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/reference_center_profile_obstruction.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/reference_center_profile_obstruction.py

The exchange arguments establish the all-centre and growing-family
claims. Finite controls support the implementation and exact constants;
they do not replace those proofs or enumerate the large period.
