# Integrated root profiles and a five-depth noncoverage criterion

Actual conditional support profiles give a sufficient complete-query
certificate even when some root fibres have no survivor. Combining this
certificate with the pointwise collision estimate preserves every success
of [report563's collision criterion](563-prefix-free-rooted-labels-admit-all-later-four-mixed-towers.md)
on P={3,5,7,11,13,17,19}.
An irredundant thirteen-label family passes the new certificate and fails
that report's fixed collision criterion. This is a strict extension of a
sufficient certificate, not a claim that this finite family was previously
unknown to be noncovering.

A uniform theorem follows when the rooted mixed originals at each of the
first five root exponents share one root residue, independent of their
remaining numerical part. The five residues need not lie on one root path
or have disjoint cylinders. All higher root phases, all other exponents
and phases, and every old mixed tower on L={11,13,17,19} remain arbitrary.
Section6 proves a common query bound11.011636<565/51 and positive Haar
survival after arbitrary23/29-touching additions.

Two actual arithmetic counterexamples identify the remaining obstruction:
a twelve-label irredundant family has an empty positive-mass root fibre,
and a two-label family shows that applying the support polynomial to
averaged loads can overstate the actual survivor mass. Neither arbitrary
root overlap nor unrestricted Erdős #7 is resolved. The results use ordinary
proofs and exact rational computation; no Lean verification is claimed.

## 1. Keep the actual conditional profile before integrating

Let P={3,5,7,11,13,17,19}, Q=P minus{3}. Fix any finite family of distinct
nonunit P-smooth numerical moduli and their original residues. Every
finite height and every mixed support is allowed in this section.
Let S_p be the actual pure-p survivor and use the single product source

    nu0=nu3 x nuQ, nu_p=H_p(.|S_p), nuQ=product_(q in Q)nu_q.

For each x3 in S3 and nonempty S subset Q, let E_S(x3) be the union of
the Q-events of all actual mixed originals whose Q-support is S and whose
3-part, if present, matches x3. Originals with no3 factor are always active.
Set p_S(x3)=nuQ(E_S(x3)). These are exact unions under the same Q-source,
including all same-support phases and overlaps between numerical labels.
Only this fixed family's avoidance calculation uses the union; numerical
identities are retained for collision charges and continuation tasks.

Write

    Phi_R(p)=sum_(F pairwise-disjoint nonempty supports inside R)
                  (-1)^|F| product_(S in F)p_S,
    h(x3)=Phi_Q(p(x3)) if Phi_R(p(x3))>0 for every R subset Q,
          0 otherwise.                                             (IP1)

Then the actual fibre survivor U_x3 satisfies

    nuQ(U_x3)>=h(x3),
    nu0(U)>=G0,  G0=integral h dnu3.                               (IP2)

To prove this, join two scope events when their coordinate supports
intersect. Under the product law nuQ, an event is independent of every
collection of its nonneighbors. On a fibre satisfying IP1, the64 coordinate
tests imply positivity for every induced event subgraph. Indeed

    partial Phi_R/partial p_S=-Phi_(R minus S), S nonempty.

Induction on |R| proves positivity throughout the box from0 to the tested
vector and monotonic decrease in every coordinate. Removing arbitrary
scope events sets their weights to zero, so all induced polynomials are
positive. [Scott--Sokal, Theorem4.1(a)](../../../../../Library/Arith/scottsokal2003repulsive.md)
now gives the first inequality. On an uncertified fibre, zero is a valid
lower bound, even when the fibre actually has survivors. Integration gives
the second inequality. The test is sufficient, not necessary.

Upper bounds on the union probabilities may also be used if all64 tests
are positive for those upper bounds. In particular, sums of the individual
event probabilities give the earlier support-aggregation version. Exact
unions can improve it without replacing the original event family.

All actual root and pure-root cylinders have finite heights. Their finite
laminar partition of S3 makes p and h constant on finitely many regions.
Their masses and the Q-union probabilities are exact finite CRT/source
calculations. This gives a finite certificate for each input family; it
provides no uniform bound on the required computation or certificate size.

## 2. Preserve the collision theorem by taking a pointwise maximum

For this section assume report563's support inventory: every mixed original
either contains3 or is supported on L={11,13,17,19}. Root phases may overlap.
For rooted label3^a*u, let A_(a,u) and B_(a,u) be its actual root and Q
cylinders, and v_(a,u)=nuQ(B_(a,u)). Define

    omega(x3)=sum_u [sum_(a:x3 in A_(a,u))v_(a,u)
                    -max_(a:x3 in A_(a,u))v_(a,u)],
    s0=65869/378675,  Omega=integral omega dnu3,
    g(x3)=max(h(x3), max(0,s0-omega(x3))),
    G=integral g dnu3.                                             (IP3)

The maximum over an empty set is zero. Report563's designation argument
gives nuQ(U_x3)>=max(0,s0-omega(x3)) on each fibre: designate one active
event per numerical u before drawing Q, apply its uniform bound, and
charge the omitted actual events by the union bound under nuQ. Therefore

    nu0(U)>=G>=G0,
    G>=s0-Omega.                                                   (IP4)

The maximum selects between two valid lower bounds on the same fibre and
source; it does not add incompatible savings or select different laws.
Thus all successes of the earlier collision criterion on this P, including its
prefix-free and six-layer corollaries, are retained.

For either IP2 or IP4, write G_* for the chosen positive lower bound.
There is one uniform survivor law rho=H(.|U)=nu0(.|U), and

    R_P(rho)<=5+B5/G_*,
    B5=19132074022251234990036997833948759259
         /18473247078046657922374787501704265625.                   (IP5)

Here R_P sums maximal residue probabilities over all nonunit P-smooth
query labels, including arbitrarily high powers. For each finite query
box choose maximizing phases under this same rho. The pure-product
complete-query comparison in
[report557](557-complete-query-comparison-allows-three-more-old-pair-towers.md)
gives E_nu0(N-5)_+<=B5 uniformly in the box and phases. Conditioning once
on U gives IP5; increasing cofinal boxes give the full nonnegative sum.
No replacement query law is chosen on a root fibre.

In particular G_*>51*B5/310 gives R_P(rho)<565/51 and the existing
positive-survival extension by arbitrary23/29-touching originals with
P-smooth cofactors. No post-extension query bound is asserted. A universal
inequality at this threshold for arbitrary actual profiles is still missing.

## 3. Thirteen irredundant labels separate the two certificates

Take no pure originals, and take

    0 mod15, 36 mod45;
    0 mod product(S), for every pair S subset L;
    1 mod product(S), for every triple S subset L;
    2 mod46189.                                                    (IP6)

There are thirteen distinct odd numerical moduli. The first two have
root cylinders0 mod3 and0 mod9, with the same remaining numerical part5
but different5-residues0 and1. Their full original classes are disjoint;
same-phase redundancy removal cannot eliminate either one.

In fact all thirteen originals are irredundant. CRT witnesses modulo
2078505=9*5*11*13*17*19 are specified as follows:

* For0 mod15, use x3=3 mod9, x5=0, and every late coordinate3.
* For36 mod45, use x3=0 mod9, x5=1, and every late coordinate3.
* For an old support S of size k, use x3=1 mod9, x5=3, the value k-2
  on S, and3 on L minus S.

Each witness belongs to its indicated original and avoids all others.
The result data retain integer representatives and check all memberships.

The old block polynomial is

    Phi_L=1-sum_(pairs S)1/prod(S)-sum_(triples S)1/prod(S)
              +2/46189
         =44801/46189.                                            (IP7)

The positive term accounts for the three disjoint pair-pair selections,
less the single four-coordinate event. All64 coordinate tests on every
root region are positive. The root regions have masses2/3,2/9,1/9;
their5-coordinate forbidden probabilities are0,1/5,2/5. Hence

    G0=G=(41/45)*(44801/46189)=1836841/2078505,
    R_P(rho)<=100759055040065243579847527636422087384
                /16325396203562801717962105960494665625
             =6.171920961898365...<565/51.                         (IP8)

The actual Haar survivor is1841638/2078505. A separate enumeration of
all46189 late-coordinate assignments gives44918 survivors; independent
enumeration of the45 root/5 residues gives41 survivors.

However Omega=1/45, so the old fixed certificate gives

    s0-Omega=57454/378675<51*B5/310,
    5+B5/(s0-Omega)=11.825982611179311...>565/51.                    (IP9)

This separates the sufficient criteria on an actual irredundant family.
It is not a comparison with every existing noncoverage method or every
possible law, and the finite example supplies no universal profile bound.

## 4. A positive-mass root fibre can have no survivor

Take pure originals0 mod3,0 mod5,0 mod7. For each a=1,2,3 take three
rooted originals with CRT coordinates

    x3=1 mod3^a, x5=a;
    x3=1 mod3^a, x7=a;
    x3=1 mod3^a, x5=4, x7=a+3.                                    (IP10)

These twelve moduli are distinct and odd. Their nine mixed
(modulus,residue) pairs, grouped by a, are

    (15,1),   (21,1),   (105,4);
    (45,37),  (63,37),  (315,19);
    (135,28), (189,136),(945,244).

On the root fibre1 mod27 all nine are active. The singleton5 events leave
only x5=4 in its pure survivor; the singleton7 events leave x7=4,5,6.
The three joint5/7 events delete all these possibilities. This fibre
therefore has actual survivor mass zero, although its nu3 mass is1/18.
It refutes a uniformly positive bound on every actual root fibre when
root phases are unrestricted, already within the all-rooted inventory.

The four root strata, indexed by the number j of active depths, have

| j | nu3 mass | Actual Q-fibre survival |
|---|---:|---:|
|0|1/2|1|
|1|1/3|7/12|
|2|1/9|1/4|
|3|1/18|0|

The corresponding scope polynomial on {5,7} is

    (1-j/4)*(1-j/6)-j/24=((4-j)*(6-j)-j)/24.

It equals the displayed actual survival. IP1 uses zero on the last
stratum, and integration gives G0=13/18 exactly. In the full period945,
312 residues survive, giving Haar mass104/315. Every original has a
residue that belongs to it alone, so the obstruction persists on this
irredundant family. The exact witnesses are in the result data.

This does not refute an integrated bound, a differently reweighted
common-law construction, report561, or Erdős #7. It rules out only a
positive lower bound required separately on every root fibre.

## 5. Averaging loads before the polynomial changes the answer

Take0 mod15 and1 mod21, with no pure originals. The root residues0,1,2
give support weights (p5,p7)=(1/5,0),(0,1/7),(0,0), respectively. All
fibres pass the positivity test, and their actual survival is the support
polynomial. Therefore

    integral Phi_Q(p(x3)) dnu3=(4/5+6/7+1)/3=31/35,
    Phi_Q(integral p(x3) dnu3)=(1-1/15)*(1-1/21)=8/9.               (IP11)

The latter overstates actual survival by1/315. Exactly93 of105 residues
survive, independently confirming the first expression. This is an
actual globally fixed arithmetic counterexample to the proposed
mean-field lower bound, not a relaxed nonrealizable support profile.
The root dependence must be retained through the nonlinear calculation.

## 6. Active-depth budgets give a uniform class with overlapping prefixes

Keep the support inventory of Section2. For every positive exponent a,
let A_a^* be the union, inside S3, of the distinct3-local cylinders of all
present rooted mixed originals3^a*u. A root cylinder is counted once in
this union even when many numerical Q-parts use it. Define

    N(x3)=sum_a 1_(A_a^*)(x3),
    beta=E_nu3 N=sum_a nu3(A_a^*),
    p0=nu3(N=0).                                                  (IP12)

The actual finite original family determines these quantities. They count
active depths, not original events, and keep all pure3 exclusions in nu3.

At N=1, only one root exponent is active. Numerical distinctness therefore
gives at most one active rooted label for each complete numerical u.
The support ceilings of report563 apply, so h>=s0. At N=0 only the old
L-events remain. Their full cap polynomial is

    c_old=1-sum_(S subset L, |S|>=2) product_(q in S)1/(q-2)
              +3/(9*11*15*17)
         =2689/2805,
    c_old-2*s0=231277/378675>0.                                   (IP13)

All its induced coordinate polynomials are positive: there are at most
two disjoint old supports, and1 minus the sum of all old weights is
8066/8415>0. The positive-box argument then gives h>=c_old for every
actual old-only profile. At N>=2 use h>=0, whether or not that fibre
passes the stronger profile test. These three cases prove

    h(x3)>=s0*(2-N(x3))+(c_old-2*s0)*1_(N=0)(x3),
    G0>=s0*(2-beta)+(c_old-2*s0)*p0.                              (IP14)

In particular beta<=1 gives G0>=s0 and the same complete-query bound
10.953938953721723 as report563, without requiring disjoint root prefixes.
Dropping the nonnegative p0 term gives the more general sufficient test

    beta<2-51*B5/(310*s0)=1.0204810108393294... .                  (IP15)

This is an actual-source depth-union criterion; arbitrary families are
not asserted to satisfy it. The thirteen- and twelve-label families
above have beta=4/9 and13/18, respectively. Both satisfy the criterion,
and neither requires all root fibres to survive.

### Shared root phases at each depth

Suppose that, for every a, all present rooted labels3^a*u have the same
3-residue alpha_a modulo3^a, independent of u. There is no compatibility
condition between alpha_a at different depths, and all Q-residues may
depend on the full original label. With w3=H3(S3)>=1/2,

    beta<=sum_(a>=1)1/(w3*3^a)=1/(2*w3)<=1.                       (IP16)

Thus IP14 proves the uniform source bound s0 for this whole class, with
arbitrary finite heights and every old-L mixed support. Overlap between
the root cylinders is allowed. The estimate integrates the extra reserve
on zero-depth fibres; it does not require a uniform positive bound on
each multiple-depth fibre, which Section4 disproves.

### Only five shared low depths suffice; every higher phase is arbitrary

It is enough to impose the preceding common-phase condition for a<=D.
For this estimate remove the higher rooted mixed originals temporarily,
while retaining the complete original pure source and all old-L originals.
Let N_low count the active low depths. Since c_old>=2*s0, the same three
cases give the useful affine bound

    low_fibre_survival>=c_old-(c_old-s0)*N_low,
    E_nu3 N_low<=1-3^-D,
    nu0(low_family_survivor)>=s0+(c_old-s0)*3^-D.                  (IP17)

Now charge every higher rooted original under this same nu0. Numerical
distinctness and the complete geometric sums give

    sum_(a>D,u>1) nu0(actual class3^a*u)
       <=[product_(q in Q)(1+1/(q-2))-1]*sum_(a>D)2/3^a
       =(1113/935)*3^-D.                                        (IP18)

The sum is over actual labels, bounded by all possible numerical labels;
all actual residues remain fixed. Every high original is retained among
the constraints defining the final survivor U. Combining IP17 and IP18,
with no change of source, gives

    nu0(U)>=s_D=s0-(153619/378675)*3^-D.                           (IP19)

At D=5 this yields

    s_5=15852548/92018025,
    R_P(H(.|U))<=35044610507390662344298654333344771759
                   /3182507297027885470852331299879202500
                =11.01163555543722...<565/51,
    H(U)>=3963137/100776960.                                     (IP20)

The resulting Haar lower bound after arbitrary distinct23/29-touching
originals with arbitrary P-smooth cofactors and fixed residues is

    637734526107735968960930201833297223
      /2932401053130816752666186337709977600000>0.                 (IP21)

These additions need not satisfy the common-root-phase condition. The
complete query estimate pays them with the same product-extension factor
51/616 used in report563. No complete-query bound after the additional
conditioning is asserted.

For this explicit affine estimate, D=4 gives s_4=5542/32805 and query
bound11.130449711268232, which does not cross the target. The positive
coefficient in IP19 makes five the least integer D for this estimate;
this is not an impossibility claim for four shared depths or for other
source constructions.

IP19 is a bound on the actual full survivor after the charged high
originals. It is not a claim that the full family's IP1 polynomial itself
inherits the low-family polynomial minus that charge. The final uniform
survivor law and the all-height query comparison in IP5 use the actual
mass lower bound, so they remain valid.

## 7. Reproduction and remaining uniform obligation

The [producer](../../frontier/cover-geometry/integrated_actual_root_profiles.py)
and [result](../../frontier/cover-geometry/integrated_actual_root_profiles.json)
retain all original labels, irredundancy witnesses, coordinate-subset
polynomials, exact source weights and rational comparisons.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/integrated_actual_root_profiles.py
```

All330 explicit checks pass; `--output` chooses a different result path.
The finite computations certify the stated examples and constants. The
source argument, all-induced positivity implication and complete-query
comparison supply the ordinary proof of the conditional general criterion.
The active-depth inequalities and geometric tail charge prove the uniform
classes in Section6; the program also checks their exact constants and
their application to the two earlier actual families.

No bound G_*>51*B5/310 has been proved for every unrestricted root-phase
arrangement or every non-rooted support inventory. Bad fibres cannot be
discarded and nu3 renormalized without accounting for the changed root
query law. A uniform integrated estimate or a reweighted replacement with
a controlled complete-query numerator remains necessary for this route.
There is also no reduction here from arbitrary prime sets to seven
coordinates. The unrestricted #7 goal remains open.
