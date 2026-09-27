# A common star product admits arbitrary pair endpoints and central pure tails

All twelve labels on every outside edge can have independently chosen
central phases and outside endpoints under the coherent seven-star geometry
below. No pairwise shared-root condition remains. The central first pure
roots remain2mod3 and4mod5, and the central15 mask remains0mod15. The actual
pure9, pure25 and all higher central pure phases and finite heights may be
arbitrary, with missing originals allowed. A single rational central
thinning gives ten-prime Haar survivor mass at least

    904989942890553166134679994443
      /13705947978444459178721280000000000 >1/17000.     (RP0)

For the uniform central-source special case in section1, the stronger
bound is

    165833464880934928533269023673
      /355108652168788260539596800000000 >1/2200.        (RP1)

The first bound permits arbitrary central square and higher pure phases;
the second uses a narrower pure inventory. Both retain the same coherent
star-central layout, all120 free pair labels, the remaining mixed inventory
and unrestricted23/29/31 continuation. Neither is the arbitrary-star target
of [Report629](629-free-pair-endpoints-need-a-common-source-with-dead-fibres.md).
The proofs use one actual product source before all pair deletions, and a
global complete loss/query budget. They require no positive avoidance source
in every central fibre and no strict Shearer condition for pair unions.
These are ordinary proofs and exact rational arithmetic, not new Lean
verification or a resolution of unrestricted Erdős #7.

## 1. Exact star geometry and the uniform-source special case

Keep the literal head primes{3,5,7,11,13,17,19,23,29,31}, with
Q={7,11,13,17,19}. All numerical originals are distinct, greater than1
and odd, and each has one globally fixed residue.

For the stronger uniform-source special case RP1, the central pure
originals are2mod3,1mod9,4mod5,1mod25. A missing one
may be imposed as an auxiliary deletion. Every further central pure
original is absent or contained in these deletions. This last condition
is needed for the displayed uniform source; arbitrary additional live
higher-pure deletions are excluded from RP1 but allowed in RP0 by section5. Outside pure
originals on Q retain arbitrary phases and finite heights.

The central15 original is0mod15, or impose it as an auxiliary deletion
if absent. Let rho3 be uniform on the five mod9 residues avoiding2mod3
and1mod9, and rho5 uniform on the nineteen mod25 residues avoiding4mod5
and1mod25. Extend these laws with independent Haar higher digits. Then

    rho3<=(9/5)H3<=2H3,
    rho5<=(25/19)H5<=(4/3)H5.

Index their live root leaves by

    residue3(l)=3(l mod3)+floor(l/3), 0<=l<6,
    residue5(m)=5(m mod5)+floor(m/5), 0<=m<20.

Thus w_l=1/5 except w_3=0, and v_m=1/19 except v_5=0. Delete the
central15 rectangle(floor(l/3),floor(m/5))=(0,0), without renormalizing.
There are80 positive unmasked cells, of total central mass16/19.

At every q in Q fix these central parts of the seven stars:

| Numerical label | Central residue |
| --- | --- |
|3q,3q^2|0mod3|
|5q,5q^2|2mod5|
|15q|12mod15|
|9q|0mod9|
|25q|2mod25|

Their outside first roots and higher lifts are arbitrary independently;
missing stars are allowed. The same central roles are used at all five
outside coordinates. In the normalized leaf coordinates this is the
single coherent template(R,C,I,J,L,M)=(0,2,0,2,0,10).

Retain all120 pair labels

    3^a5^b q^i s^j,
    a,b in{0,1}, {q,s} subset Q,
    (i,j) in{(1,1),(2,1),(1,2)}.                        (RP2)

Each may be present or absent. Its central residue, both outside first
roots and every higher lift are arbitrary, independently between labels.
In particular even the four primary qs labels need not share endpoints.

Every other mixed first-seven original satisfies the same disjunction
as Report626: maximum exponent at least3, both central exponents at most1,
or support cardinality at least5. The special35 star and120 pair labels
are removed once from that remaining-original inventory. Originals
involving23,29 or31 are unrestricted, as in Report626. The theorem does
not assert an arbitrary-head-prime transfer for these fixed central roles.

## 2. Construct the star product on one actual family

Use Report626's actual root-balanced pure survivor rho_q at each q in Q.
Write r_q=1/(q-1) and a_q=1/[q(q-2)] for its first- and second-prefix caps.
At central cell c=(l,m), the union of the actual active stars costs no
more than the full-slot sum. Hence its actual survivor has mass at least

    Z_q(c)=1-(r_q+a_q)(1_(l//3=0)+1_(m//5=2))
              -r_q(1_((l//3,m//5)=(0,2))
                    +1_(l=0)+1_(m=10)).               (RP3)

Missing or already source-null originals only lower the actual loss.
The bound remains positive: Z_q>=1-5r_q-2a_q, whose minimum over Q is
23/210. Uniformly thin the entire actual star survivor to mass Z_q,
obtaining xi_q(c)<=rho_q. Thus all original prefix caps remain valid,
regardless of outside root collisions or overlaps.

At each unmasked cell take the product of these five xi_q. Mix with the
fixed original central probabilities w_l v_m to obtain one actual
submeasure sigma. For T subset Q define the raw response

    R_T(c)=product_(q in Q\T) Z_q(c).                 (RP4)

It gives sigma(1)=sum_c w_l v_m R_empty(c). Every outside cylinder on
support T has the simultaneous bound

    product_(q in T) cap_q(A_q) R_T(c).

All32 responses come from this same product source. They remain valid
upper bounds after any further deletion. No avoidance conditioning on
the pair events is used, so dead pair fibres cause no construction problem.

## 3. Pay every actual pair once, with global central phases

For central exponent modes a,b in{0,1}, let S_(a,b,T)(R) be the maximum
of the corresponding inherited central selector applied to R_T. The
selector is the whole central law if that exponent is zero, or its
restriction to one root when it is one; source-null selections have zero
mass. Every actual fixed central phase is bounded by this maximum.

The exact added pair-loss coefficient, for T={q,s}, is

    P_(a,b,T)=r_q r_s+a_q r_s+r_q a_s,
    a,b in{0,1};                                    (RP5)

all other pair coefficients are zero. Enumerating the three outside
exponent types and four central types gives exactly120 distinct numerical
labels. Each present label is charged once at its appropriate outside
prefix cap and one central selector value. Summing the full inventory
is a uniform upper bound when some labels are missing.

The maxima in RP5 concern one global central role per numerical label;
they do not choose a new phase at each cell. They are upper bounds on
the one fixed actual family, not a claim that different maxima must be
realized simultaneously or by disjoint events.

Let L_j,W_j be the full512 remaining-original and weighted nonunit-query
coefficients inherited from Report604. Put eta=sigma restricted outside
all actual pair and remaining mixed originals, and s=eta(1). A global
union bound and source domination give

    s>=sigma(1)-sum_j(L_j+P_j)S_j(R),
    Gamma_h(eta)<=s+sum_j W_j S_j(R).                 (RP6)

Gamma_h is the complete squared query load including the unit, at any
finite resolving height. The unit contribution in this upper envelope
is the actual retained mass s. All nonunit query bounds use the same
sigma and all512 inherited costs; none are dropped after deletions.

For c0=1084133/201247200 and g=1-c0, RP6 yields

    s-c0 Gamma_h(eta)
      >=g sigma(1)-sum_j[g(L_j+P_j)+c0 W_j]S_j(R).   (RP7)

Unlike a pointwise strict-good-cell test, this estimate permits negative
local mass lower estimates and actually empty central fibres. It only
needs a positive total right side. All actual original constraints are
enforced by the final restriction defining eta.

## 4. Exact complete gate and continuation

The standard-library computation retains every raw response and every
one of the512 selector readings. It obtains

    sigma(1)=11599698645680023/22970080875456000,
    sum_j L_j S_j(R)=5347027234297882073/30148231149036000000,
    sum_j P_j S_j(R)=967331169770663/7308662096736000,
    sum_j W_j S_j(R)=3044411096726147788325141/93773058165961574400000.

Therefore the complete gate in RP7 is

    gamma_raw=165833464880934928533269023673
                /8577984268789500979814400000000
             >1/52.                                  (RP8)

All heights are handled by the inherited complete coefficient bounds;
this computation does not truncate original or query heights.

Construct the normalized23/29/31 continuation from this particular eta,
using its gate and actual source domination as in Reports598/626. The
central uniform densities are no larger than the inherited caps, so
alpha=2673/110656 remains a valid Haar conversion. Multiplication of RP8
by alpha gives RP1. No continuation kernel from a differently normalized
core is silently reused.

## 5. One common thinning allows arbitrary central square and higher pure phases

Now retain only the first central pure roots2mod3 and4mod5, imposing them
as auxiliary deletions if absent, and the central15 phase0mod15. Keep
all seven star roles in section1 exactly as written. Release the actual
pure9 and pure25 phases and every higher central pure phase and finite
height. These originals may be missing; there is still at most one
original at each numerical modulus.

Use Report624's actual central pure-survivor construction. If the actual
pure9 cylinder is absent or source-null after the first-root deletion,
choose one auxiliary live square leaf to delete. Let z be its resulting
null leaf in{0,...,5}. Similarly choose the actual or auxiliary quinary
null leaf z' in{0,...,19}. All actual higher pure deletions are enforced.
Their total raw Haar costs are at most1/18 and1/100 respectively, so the
remaining leaf capacities admit normalized laws with

    w_z=0, 0<=w_l<=2/9, sum_l w_l=1;
    v_z'=0, 0<=v_m<=4/75, sum_m v_m=1.                (RP9)

The actual laws are dominated by2H3 and(4/3)H5. They need not be uniform
inside their leaves; full-height query bounds use those density caps.

Every nonnull w_l is at least1/9, and every nonnull v_m at least3/75,
since all the other coordinates together cannot carry mass1. The two
source polytopes have the explicit vertex decompositions

    w=sum_(l!=z)(2-9w_l) w^(z,l),
    v=sum_(m!=z')(4-75v_m) v^(z',m),                  (RP10)

where w^(z,l) has weight0 at z,1/9 at l and2/9 at the other four leaves;
v^(z',m) has weight0 at z',3/75 at m and4/75 elsewhere. All coefficients
in each sum are nonnegative and sum to1. No numerical vertex is substituted
for the already fixed actual source; these will be comparison weight vectors.

Use the following ONE thinning t(l,m), independently of z,z',w,v and of
all pair phases. All rows and columns refer to the same normalized leaf
coordinates as section1.

| Ternary leaf | Quinary column0 (m=0..4) | Quinary columns1,3 (m=5..9 or15..19) | Quinary leaf10 | Other column2 leaves (m=11..14) |
| --- | ---: | ---: | ---: | ---: |
|l=0|0|0|0|0|
|l=1,2|0|147/250|0|1|
|l=3,4,5|97/250|389/1000|377/500|119/200|

The central15 rectangle already has t=0. Everywhere0<=t<=1. At every
central cell multiply its entire raw star-product submeasure by this t,
then delete all actual pair and remaining original cylinders as before.
The resulting single measure is still dominated by the same original
product source. Every response is replaced by

    R_T^t(l,m)=t(l,m)R_T(l,m), for ALL32 supports T.   (RP11)

The grids are set to zero at null central leaves, just as those leaves
are excluded from the live selector menus. No central law is renormalized
and no query chooses its own thinning.
Any square-star or leaf-star slot already killed by the actual central
pure law needs no further avoidance; the full-slot Z in RP3 remains a
valid overpayment on live cells. At null leaves all mass and selectors
vanish. Thus releasing square phases does not require a different STAR.

For a fixed null pair(z,z'), the live selector-index sets are constant
throughout RP9, because of the strict lower bounds on all nonnull weights.
Each individual selector reading of R^t is affine in w for fixed v and
affine in v for fixed w. The deep ternary selector is delta_l and the deep
quinary selector is(4/5)delta_m; they are constant in the corresponding
weight vector, not multiplied by an extra w_l or v_m. The mass is bilinear.
Taking maxima over the unchanged finite menus gives convex query readings
in either weight vector separately. Since all debit coefficients in RP7
are nonnegative, the complete gate G_t(w,v) is separately concave. Therefore

    G_t(w,v)>=sum_(l!=z,m!=z')
                (2-9w_l)(4-75v_m)G_t(w^(z,l),v^(z',m)). (RP12)

The same t is used on both sides and at every intermediate Jensen step.
Optimizing a different t at each vertex would not justify RP12.

It remains to check the6*5*20*19=11400 ordered null/weak corners. Use
only the subgroup preserving the entire STAR, central15 mask and t:

* on ternary leaves, permute{1,2} and{3,4,5}, fixing0;
* on quinary leaves, permute within column0; freely permute columns1 and3
  and their leaves; fix leaf10 and permute{11,12,13,14} within column2.

These are prefix-preserving permutations. They preserve RP3, the mask,
every entry of t and the complete selector menus when the entire null/weak
pair is transported. Thus they preserve the numerical gate. Their ordered
ternary null/weak pairs have8 orbits and quinary pairs16, giving128
simultaneous representatives. The program constructs the whole orbits,
checks disjoint coverage of all11400 corners and verifies every generator
on the full STAR/mask field and thinning. The old20 source orbits, which
do not keep this STAR fixed, are not used.

The exact least representative is(z,l,z',m)=(3,4,5,6). All128 gates are
at least

    gamma_t=904989942890553166134679994443
              /331080094584857932554240000000000
           >1/400.                                   (RP13)

Combining orbit invariance, RP12 and the actual source construction gives
this same lower bound for every allowed central square/higher-pure family.
The unthinned numerical envelope at this corner is negative; the fixed
thinning is therefore a material part of this certificate, rather than an
assertion that every unthinned source corner has a positive gate.

The actual thinned source still obeys the inherited full density caps.
Constructing23/29/31 from this actual core and multiplying RP13 by
alpha=2673/110656 proves RP0. This establishes one complete global source
while permitting central fibres to receive zero mass.

## 6. Verification and remaining scope

The portable [uniform-source producer](../../frontier/cover-geometry/free_pair_uniform_star_product.py) supports
`--source-dir` and `--output`. Its [exact data](../../frontier/cover-geometry/free_pair_uniform_star_product.json) pins canonical604 coefficient data
and626's conversion constant, records the actual central law, all80 cell
responses, all120 pair labels and the complete512 readings. Optimized
selector values are independently checked against direct products of the
original menus for all512 entries, including the deep selectors delta_l
and(4/5)delta_m; those terms receive no extra central weight.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/free_pair_uniform_star_product.py

The uniform-source producer passes615 named checks. The exact positive gate is a finite rational
consequence of RP7; the uniformity over phase choices and finite heights
comes from the ordinary source, union-bound and inherited-query arguments.
It is not a finite scan over phases or a new Lean proof.

The [common-thinning producer](../../frontier/cover-geometry/free_pair_fixed_star_thinning.py) is
self-contained and uses only the standard library. Its [exact data](../../frontier/cover-geometry/free_pair_fixed_star_thinning.json) retain all128 corner gates and the common witness. It reads the same
canonical coefficient/conversion data, constructs the source-corner orbits,
checks the common rational thinning and evaluates every representative with
all512 costs. At the least corner all512 optimized readings are again
checked against direct complete menus. Its800 named checks pass under

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/free_pair_fixed_star_thinning.py

The retained rational witness is verified directly; this producer does
not run an LP, claim an optimal thinning or rely on a floating-point lower
bound. The ordinary source and separate-concavity proofs supply the
uniform quantifiers beyond these exact finite comparisons.

Both results release all within-edge pair endpoints and central pair
phases. RP0 additionally releases every central square and higher pure
phase; RP1 retains the stronger density in its uniform-source subcase.
The central first-root phases2/4, central15 phase0 and the coherent
seven-star central layout remain fixed. Arbitrary first-root/mask geometry
relative to the stars and arbitrary seven-star central roles remain
outside these results. No arbitrary-head-prime or extra outside-network
consequence is claimed here. The common-source construction avoids the
pointwise obstruction of Report629, while the full arbitrary-role target
still needs a uniform complete gate on its larger domain.
