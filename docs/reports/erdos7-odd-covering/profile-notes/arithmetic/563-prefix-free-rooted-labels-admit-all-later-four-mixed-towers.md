# Actual root-prefix budgets admit every later-four mixed tower

Let P={3,5,7,11,13,17,19}, Q=P minus{3}, and
L={11,13,17,19}. Consider any finite family of pairwise distinct
nonunit P-smooth numerical moduli, with arbitrary fixed residues and
arbitrary finite heights. Allow all pure prime powers. Every mixed
original must either contain3 or have all its prime factors in L.

For each fixed numerical Q-part u>1, require that the actual3-local
cylinders belonging to the present labels3^a*u are pairwise disjoint
on the pure3 survivor S3. There is no restriction on their Q-local
phases, which may depend on the full label and every exponent.

Then the uniform Haar law rho on the actual full survivor U satisfies

    R_P(rho)<=35198810825365453128135695634830231134
                 /3213347360622843627619739560176294375
              =10.953938953721723...<565/51.          (PF1)

The source calculation also gives H(U)>=65869/1658880. Arbitrary
additional distinct23/29-touching originals, with P-smooth cofactors
and arbitrary fixed phases, retain positive Haar survivor mass.

Thus every non-3 mixed support on the four later primes is allowed:
six pair supports, four triple supports and the four-prime support,
with every exponent vector. This class complements
[report561](561-all-three-rooted-supports-have-a-common-query-law.md):
the latter handles arbitrary3-phases when every mixed label contains3,
and a different class with rooted triangles and three old pair towers.
Neither class contains the other. The prefix-free assumption here is
not inferred from numerical distinctness. Removing it, allowing arbitrary
omitted supports, and unrestricted Erdős #7 remain unresolved.
Section5 permits overlapping root prefixes under a measured collision
budget; this is not a universal bound on arbitrary root phases.

This is an ordinary application of the existing dependency-graph
avoidance theorem and complete-query comparison, with exact rational
certificates. No new Lean proof is claimed.

## 1. Condition on one actual coordinate without resetting the source

Write S_p for the complement of all actual pure-p originals and
nu_p=H_p(.|S_p). Numerical distinctness and the full geometric sum give

    w_p=H_p(S_p)>=(p-2)/(p-1),
    nu_p([r]_(p^e))<=a_p/p^e,
    a_p=1/w_p<=(p-1)/(p-2).                         (PF2)

Use the actual product source nu0=product_p nu_p. For the label3^a*u,
write A_(a,u) for its3-local cylinder restricted to S3 and B_(a,u)
for its Q-local cylinder under nu_Q. These are the original fixed
residues, with no replacement or label-dependent choice of probability law.

Fix x3 in S3. The prefix-free condition implies that at most one
present label3^a*u is active for each complete numerical u. If u has
support S and exponents e_q>=1, its active Q-event has probability at most

    mu_u=product_(q in S) a_q/q^e_q.

Summing over all possible exponent vectors gives

    sum_(u with support S)mu_u
       <=product_(q in S)a_q/(q-1)
       <=c_S,  c_S=product_(q in S)1/(q-2).          (PF3)

The old labels with no3 factor are distinct numerical u's. For a mixed
support S contained in L, they supply at most another c_S. Thus the
sum of event weights at each nonempty Q-support is bounded by

    v_S=2*c_S, if S subset L and |S|>=2,
        c_S,   otherwise.                          (PF4)

These are bounds for one conditional family under nu_Q. Rooted and old
events sharing a support may have entirely different phases. They are
not identified as sets, and no independence is asserted between them.

## 2. Support aggregation and every induced positivity condition

Join two conditional events exactly when their Q-supports intersect.
An event and any collection of its nonneighbors depend on disjoint
coordinates of the product law nu_Q. This is the required dependency
condition for [Scott--Sokal, Theorem4.1(a)](../../../../../Library/Arith/scottsokal2003repulsive.md),
applied to avoidance in the same original probability space.

For R subset Q and nonnegative support weights z_S, define

    Phi_R(z)=sum_(F pairwise disjoint nonempty supports in R)
                     (-1)^|F| product_(S in F)z_S.  (PF5)

Events with the same support are adjacent twins; an independent family
selects at most one of them. Summing their individual weights therefore
gives exactly this polynomial, rather than an assumption about equal
phases or independent events.

The finite certificate below verifies Phi_R(v)>0 for all64 coordinate
subsets R. This supplies ALL induced-event conditions as follows.
Induct on |R|. For each nonempty S subset R,

    partial Phi_R(z)/partial z_S=-Phi_(R minus S)(z). (PF6)

The smaller-coordinate induction gives positivity on every box
0<=z<=v. Consequently Phi_R decreases in every coordinate throughout
that box, so Phi_R(z)>=Phi_R(v)>0. For an arbitrary induced subfamily
of actual events, its aggregated weights still lie in this box. Its
independent-set polynomial is therefore positive. Checking only the
full-set endpoint would not have proved this premise.

The cited theorem now gives, for every x3,

    nu_Q(no active rooted or old event | x3)
       >=Phi_Q(v)=65869/378675.                    (PF7)

The displayed conditioning fixes x3 in the product source; nu_Q itself
is unchanged. Integrating with its actual nu_3 distribution proves

    s=nu0(U)>=s0=65869/378675.                     (PF8)

All dependence on x3 was retained until this integration. No new
ternary phase or separate source is selected on a Q-query branch.

## 3. An exact sixty-four-subset certificate

For i in R the polynomial obeys

    Phi_R(v)=Phi_(R minus{i})(v)
       -sum_(S subset R, i in S) v_S*Phi_(R minus S)(v),
    Phi_empty=1.                                  (PF9)

This recurrence enumerates the independent families according to
whether i is unused or belongs to their unique support containing i.
The producer also independently enumerates disjoint support families;
there are877 on the full six-coordinate set, including the empty family.
Both calculations retain all original exponents through PF3 rather
than imposing any height cutoff.

With only the rooted inventory, the endpoint is70991/378675. Adding
only the six old pair supports inside L gives66184/378675. Completing
all eleven old mixed supports inside L gives65869/378675 as in PF7.
Every coordinate-subset value in the final table is strictly positive.
These are three support inventories, not separate probability laws
whose benefits are added together.

| Number of coordinates | Minimum Phi_R for the final inventory |
| --- | ---: |
|0|1|
|1|2/3|
|2|7/15|
|3|49/135|
|4|83/297|
|5|329/1485|
|6|65869/378675|

## 4. The same uniform survivor law handles every query

Since U is contained in the pure survivor product, rho=nu0(.|U) is
also H(.|U). For each finite query box choose all phases maximizing
under this one rho. The complete-query comparison of
[report557](557-complete-query-comparison-allows-three-more-old-pair-towers.md)
bounds the nonunit load N by the independent auxiliary heights

    Pr(K_p>=e)=[(p-1)/(p-2)]/p^e,
    E_nu0(N-5)_+<=B5,
    B5=19132074022251234990036997833948759259
          /18473247078046657922374787501704265625.  (PF10)

Condition once and exhaust the increasing finite boxes to obtain

    R_P(rho)<=5+B5/s0,                             (PF11)

which is PF1. The sufficient survivor threshold is51*B5/310, strictly
below s0. In fact 1-s0=312806/378675 exceeds33/40, so the rounded
loss criterion in report557 is not enough; its exact hinge criterion
is used here.

The pure-source mass bound yields

    H(U)>=(product_p w_p)*s0
        >=(378675/1658880)*(65869/378675)
         =65869/1658880.                           (PF12)

Under the same rho and independent new coordinates, the total cost of
all distinct additional labels touching23 or29 is at most
(1+R_P(rho))*51/616. The right side of PF1 is below565/51, so this
cost is strictly below one. The exact positive Haar lower bound after
these originals is

    400037385456245883730046551436559491
      /977467017710272250888728779236659200000
    =0.00040925921612510065....

No new complete-query bound after that further conditioning is claimed.

## 5. An actual collision budget permits overlapping root prefixes

Keep the same original-support inventory, but allow arbitrary3-phases.
For each rooted label let v_(a,u)=nu_Q(B_(a,u)), its actual Q-event
probability. For a fixed x3 put I_u(x3)={a:x3 in A_(a,u)} and define

    Omega=E_(nu3) sum_u [sum_(a in I_u(x3))v_(a,u)
                          -max_(a in I_u(x3))v_(a,u)],           (PF13)

with the empty maximum zero. All labels and probabilities belong to
the fixed actual family. Among the active labels for each u, designate
one of greatest v_(a,u), using a fixed tie-break. This selection depends
on x3 and the fixed event probabilities, not on the subsequently sampled
Q-coordinates.

The designated rooted events and all old events satisfy PF3--PF7 on
every fibre. Union-bound the omitted rooted events under the same
original nu_Q law, then integrate over nu3. Their total charge is
exactly Omega, so

    nu0(U)>=s0-Omega,
    R_P(H(.|U))<=5+B5/(s0-Omega), if Omega<s0.       (PF14)

No cost is computed under a separately conditioned Q-source.
The target follows whenever

    Omega<s0-51*B5/310
      =400037385456245883730046551436559491
         /112288364592048312861493806382908281250
      =0.003562589827624709....                     (PF15)

In particular Omega<=1/300 gives

    R_P(H(.|U))
      <=139563693496258701984384463372540640161
          /12607079481450752404847294407349120625
       =11.07026363255691...<565/51.               (PF16)

The Haar lower bound becomes(935/4096)*(s0-Omega). The same fresh-prime
argument applies, with a strictly positive bound at Omega=1/300. The
producer retains these constants. Prefix-free root cylinders imply
Omega=0; the converse is unnecessary and can fail for zero-mass Q-events.

This is a finite arithmetic certificate. For each u, sort its present
labels so v_(a1,u)>=v_(a2,u)>=..., retaining a fixed order for ties.
Then exactly

    Omega_u=sum_(k>=2) v_(ak,u)*nu3(
                     A_(ak,u) intersect union_(i<k) A_(ai,u)). (PF17)

The finite3-adic cylinders and pure survivor determine every term.
This formula retains the actual joint prefix overlaps; numerical
distinctness alone supplies no upper bound as small as PF15.

There is a finite root-depth sufficient condition. For each actual u,
require disjointness on S3 only among its present root cylinders with
a<=6; all root phases at a>6 may be arbitrary. At a fixed x3 there is
at most one active low label. Whether the largest active weight belongs
to a low or high label,

    sum_active v-max_active v<=sum_(active a>6)v.

Since each full numerical label occurs at most once, PF2--PF3 give

    Omega<=sum_u mu_u * sum_(a>6)2/3^a
         <=[product_(q in Q)(1+1/(q-2))-1]*3^-6
          =(1113/935)*3^-6=371/227205<1/300.        (PF18)

The resulting sharper query bound is11.010360123156282..., and
H(U)>=24469/622080. The exact query fraction and positive fresh-prime
Haar bound are in the result data. This is not a height truncation:
every high-root original remains in U and is paid by PF18, and the
Q-exponents are entirely unrestricted.

## 6. Ordered prime carriers and scope

Replace3,5,7,11,13,17,19 by any seven ordered odd primes
r0<r1<...<r6. Require pairwise disjoint r0-local cylinders on the
actual pure survivor for each fixed remaining numerical part u.
Allow arbitrary old mixed originals supported on {r3,r4,r5,r6}.

Each1/(r_i-2) decreases from its reference value, so every PF4 ceiling
decreases. PF6 and the certified positivity box preserve the avoidance
lower bound. The auxiliary tails [(p-1)/(p-2)]/p^e also decrease with p;
a common-uniform coupling makes the increasing query hinge no larger.
Finally the pure mass factors (p-2)/(p-1) increase. All stated constants
therefore remain valid. Two new primes s>=23,t>=29 need only be
mutually distinct and disjoint from the core; they need not exceed its
largest prime. The collision extension also holds with the same
threshold if Omega is measured under this carrier's actual pure source;
no monotonicity of Omega across different carriers is assumed.
For PF18, the root tail becomes1/[(r0-2)*r0^6]<=3^-6 and the total
Q-part ceiling is at most1113/935. Thus the same six-layer sufficient
condition and its constants also transport.

The prefix-free condition is an actual arithmetic condition, checked
separately for every numerical u. Nested active prefixes at different
r0-exponents can violate it while all original moduli remain distinct.
This theorem supplies neither a universal bound on such overlapping
prefixes nor a reduction of arbitrary prime sets to seven coordinates.

## 7. Reproduction

The [producer](../../frontier/cover-geometry/prefix_free_later_four_shearer.py)
and [result](../../frontier/cover-geometry/prefix_free_later_four_shearer.json)
retain every coordinate-subset polynomial for the rooted, six-pair and
complete later-four inventories, along with the exact query and Haar
bounds. Direct set-partition enumeration and the separate recurrence
agree in all three cases. An independent expansion by the added old
supports also gives

    70991/378675-5143/378675+7/126225=65869/378675.

The negative term selects one old support; the positive term selects
two disjoint old pairs. No three old supports can be disjoint inside
four coordinates.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix_free_later_four_shearer.py
```

All417 explicit checks pass, and `--output` selects another result path.
These finite polynomial and rational checks certify the stated constants.
The source reduction, all-induced positivity argument, avoidance theorem
and complete-query comparison provide the ordinary general proof.
