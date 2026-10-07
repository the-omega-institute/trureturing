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
[Report564](564-integrated-actual-profiles-permit-empty-root-fibres.md)
adds an integrated actual-profile certificate that retains every success
of this collision criterion and permits zero-survivor root fibres.

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
condition for [Scott--Sokal, Theorem4.1(a)](../../../../../../Library/Arith/scottsokal2003repulsive.md),
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

The [producer](../../../frontier/cover-geometry/prefix-free-later-four-shearer/prefix_free_later_four_shearer.py)
and [result](../../../frontier/cover-geometry/prefix-free-later-four-shearer/prefix_free_later_four_shearer.json)
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
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix-free-later-four-shearer/prefix_free_later_four_shearer.py
```

All417 explicit checks pass, and `--output` selects another result path.
These finite polynomial and rational checks certify the stated constants.
The source reduction, all-induced positivity argument, avoidance theorem
and complete-query comparison provide the ordinary general proof.

<a id="mixed-ternary-label-gaps-give-an-eight-prime-source"></a>
## 8. Mixed ternary label gaps give an eight-prime source

Let P8={3,5,7,11,13,17,19,23}, Q7=P8 minus{3}, and let F be a finite
family of distinct nonunit P8-smooth numerical moduli, with one fixed
original residue for every present modulus. Write D for its numerical
inventory and U for its full actual survivor. Assume

    3n in D => 9n,27n,81n not in D, for every Q7-smooth n>1.   (MT1)

Every pure prime-power original is allowed. So are every3-free mixed
support and arbitrary higher mixed ternary levels. In particular, a row
without3n may contain every higher3^j*n, while a row containing3n may
contain all heights j>=5. No disjointness condition on the original phases
is imposed.

There is one probability nu supported on U such that

    B_P8(nu):=sum_(d>=1,P8-smooth) max_a nu([a]_d)
        <=4061891809/185389950<22.                          (MT2)

This B includes the unit label; R elsewhere in this report omits it. It
also includes labels absent from F and every query height. The law is
fixed before any query. Haar coordinate laws can equivalently be resolved
on a finite CRT carrier with independent uniform tails.

The proof reuses the pure-root capacities of
[Report528 FC708--FC709](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md#pure-ternary-holes-require-a-joint-prefix-capacity-boundary),
PF5--PF9's support aggregation and polynomial, and the relative-avoidance
estimate in [Hough--Nielsen, Appendix C, Theorem16](https://arxiv.org/html/1703.02133v2).
The added arithmetic input is the actual-row bound MT4 below. These are
ordinary applications with exact rational constants, not a new general
Shearer theorem or an unrestricted Erdős#7 result.

### 8.1. A single pure-survivor reference and its row inventory

For p in P8 let V_p avoid the actual pure-p originals. For q in Q7 use
lambda_q=H_q(.|V_q). PF2 gives depth-j caps

    k_q(j)=[(q-1)/(q-2)]q^-j, sum_(j>=1)k_q(j)=1/(q-2).

Choose two ternary first roots avoiding the possible actual modulus3
original; if none is present, choose any two. Each chosen root retains
Haar mass at least1/3-sum_(j>=2)3^-j=1/6 after all higher pure originals,
as in FC708. Put probability1/2 on each root's actual pure survivor and
normalize Haar within it. The resulting law lambda3 satisfies

    k3(1)=1/2, k3(j)=3^(1-j) for j>=2,
    lambda3([a]_(3^j))<=k3(j), sum_(j>=1)k3(j)=1.           (MT3)

The factor1/2 is part of the root mixture: a root-normalized law alone
has the larger FC709 bound. Restricting the source to two roots neither
adds an original class nor changes any original phase. Put
lambda=lambda3 tensor product_(q in Q7)lambda_q. It already avoids all
actual pure originals.

For a complete numerical cofactor n>1 define

    s_n=(1/2)1_(3n in D)
           +sum_(j>=2,3^j*n in D)3^(1-j).

Without3n this is at most1/2. With3n, MT1 gives

    s_n<=1/2+sum_(j>=5)3^(1-j)=1/2+1/54=14/27.             (MT4)

Group actual mixed originals of exact prime support S into their union
A_S. For |S|>=2, under the SAME lambda,

    lambda(A_S)<=t_S:=product_(p in S)t_p,
    t3=14/27, t_q=1/(q-2).                                (MT5)

For S containing3, write S={3} union T. The numerical-row calculation is

    lambda(A_S)
      <=[product_(q in T)(q-1)/(q-2)]
           sum_(supp(n)=T)s_n/n
      <=(14/27)product_(q in T)1/(q-2).

Distinct complete original labels supply the first inequality; geometric
summation bounds their finite inventory without adding actual classes.
The3-free case is PF2's product geometric sum. Events on disjoint prime
supports have independent full sigma-algebras under lambda. No such
independence is asserted for overlapping supports.

MT1 can be replaced by the weaker127 actual-inventory inequalities

    sum_(supp(n)=T)s_n/n
        <=(14/27)product_(q in T)1/(q-1), empty!=T subset Q7. (MT6)

These finite sums use original numerical labels. They are sufficient
conditions, not consequences of numerical distinctness alone.

### 8.2. Relative avoidance and every query on the final law

Use PF5's polynomial with singleton weights zero and mixed-support
weights t_S:

    rho(T)=sum_(M disjoint blocks S subset T, |S|>=2)
                     (-1)^|M| product_(S in M)t_S.

The exact certificate gives all256 coordinate-subset values and

    min_(T subset P8)rho(T)=rho(P8)=1235933/14313915>0.      (MT7)

Let Z(T)=lambda(no A_S with S subset T). The cited clique-Shearer
relative-avoidance estimate, using the upper activities MT5, gives

    Z(T)/Z(S)>=rho(T)/rho(S), S subset T.                   (MT8)

Its upper-activity use has the same induction as the cited theorem.
When adjoining a coordinate to R, subtract the event bounds
lambda(A_S)Z(R minus S)/Z(R). The induction gives an UPPER bound
rho(R minus S)/rho(R) on that subtracted ratio, and lambda(A_S)<=t_S;
PF9 then gives the next polynomial ratio. All denominators are positive
by MT7. Thus neither an inequality reversal nor a new event realization
is required.

In particular Z(P8)>0, so define nu=lambda(.|all mixed avoidance). This
one law avoids every actual original. For a numerical query d, let S_d
be its prime support and K(d)=product_(p^j exactly dividing d)k_p(j).
Discarding forbidden events that touch S_d, then using product
independence and MT8, gives

    max_a nu([a]_d)<=K(d)rho(P8 minus S_d)/rho(P8).          (MT9)

The reference lambda is a product; the final nu generally is not.
Every query phase is bounded under this same nu. Summing the nonnegative
terms over all heights yields

    B_P8(nu)<=[sum_(S subset P8)rho(P8 minus S)
                                 product_(p in S)b_p]/rho(P8),
    b3=1, b_q=1/(q-2).                                    (MT10)

The actual-original activity t3=14/27 differs from the full-query weight
b3=1. In particular no query at ternary height2,3 or4 was removed.
The numerator and initial bound are respectively

    166489454/71569575,
    B_P8(nu)<=166489454/6179665<27.

At query labels3,5,9,15, the MT9 bounds are respectively

    45443799/12359330, 146430436/92694975,
    15147933/6179665, 40899294/30898325.

All four exceed1. Replacing just these terms by the elementary probability
bound1 gives MT2. This correction applies to the already constructed
survivor law, not to an unrelated raw comparator.

### 8.3. A seven-prime companion and the remaining boundary

MT2 also supplies a restricted nine-prime noncoverage consequence. Keep
an actual P8 family satisfying MT1, and add any finite set of distinct
originals q^j*d with one fresh prime q>=29, j>=1 and P8-smooth d>=1.
All added phases and heights are arbitrary and fixed globally. Under
nu tensor H_q, their actual union has probability at most

    sum_(j>=1,d P8-smooth)q^-j max_a nu([a]_d)
        =B_P8(nu)/(q-1)<22/28=11/14.

The old originals are already avoided, so more than3/14 of this SAME
product source survives all added originals. The finite CRT survivor is
therefore nonempty. This is the usual first-moment continuation, with
MT2 as its supplier; it does not cover unrestricted nine-prime families
whose old P8 inventory violates MT1, or several new primes at once.

For any finite distinct Q7-smooth original family, let W be its full
survivor. Applying the same calculation on Q7, with event and query
weights both1/(q-2), gives

    rho(Q7)=5049311/7952175>0,
    B_Q7(H_Q7(.|W))<=A:=13463054/5049311.                  (MT11)

Here pure-conditioned product Haar, followed by conditioning on all
remaining mixed avoidance, is precisely Haar conditioned on W. All
original and query heights remain included.

For an unrestricted P8 family, let V3 avoid its actual pure ternary
originals and let W avoid all its actual3-free originals. Set
U0=V3 times W and delta=H(U)/H(U0). The pure ternary query sum including
the unit is at most2, so MT11 gives, WHEN delta>0,

    B_P8(H(.|U))<=1+(2A-1)/delta.                          (MT12)

The unit query remains exactly1. A uniform reserve delta>=1/6 would
make this bound less than28, as would the weaker strict threshold

    delta>21876797/136331397.

Both proposed uniform reserve conditions are FALSE.
[Report529's eight-prime comb](../500-549/529-an-irredundant-comb-separates-fibre-credits-from-supported-query-laws.md#eight-prime-combs-refute-a-uniform-relative-haar-reserve)
has delta<1/6 at height5 and below the weaker threshold at height6.
Those are complete actual survivor ratios, and every original has a
private integer. The same families nevertheless admit another source
with B_P8<11025/1024. Thus failure of MT12's reserve supplier does not
refute the existential query target or MT2's restricted theorem.
The unrestricted support majorant also fails positivity:

    rho(P8;t3=1)=-3364432/7952175<0.

This negative value only rejects that sufficient majorant. It does not
prove any all-law query obstruction.

There is one necessary pattern for a genuine obstruction. If an actual
family admitted no supported law with B_P8<28, delete any whole original
class contained in another retained original. The union and U are
unchanged. The remaining inventory must contain3n and3^j*n for some
n>1 and j in{2,3,4}, or MT1--MT2 would supply such a law. These two
retained classes must have incompatible residues modulo3n; otherwise
the higher class would be contained in the lower. This is a necessary
pattern, not a classification or an existence assertion.

### 8.4. Exact arithmetic consumer

The [consumer](../../../frontier/cover-geometry/prefix-free-later-four-shearer/mixed_tower_inventory.py)
and [exact result](../../../frontier/cover-geometry/prefix-free-later-four-shearer/mixed_tower_inventory.json)
retain the polynomial tables, distinct event/query weights, four query
corrections and MT11. The PF9 recurrence is independently compared with
a signed-partition elementary-symmetric expansion for640 subset values:
256 for MT1,128 for Q7, and256 for the unrestricted majorant. All384
coordinate-subset values needed by MT7 and MT11 are checked positive.
The consumer recomputes the result and rejects stale saved data; it uses
no assertions disabled by Python optimization.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix-free-later-four-shearer/mixed_tower_inventory.py
```

All1054 exact checks pass. `--output PATH` generates the result at the
chosen path. These checks certify finite rational constants; the
source construction, relative avoidance and all-height summation above
supply the ordinary mathematical argument. A scoped Lean check also
verifies14 rational identities and inequalities for the root bound,
event/query totals, four-query correction and continuation margin, using
only the standard axioms. It does not formalize the source construction,
Shearer application or all-height sum. No new Lean proof of that source
theorem is claimed.
