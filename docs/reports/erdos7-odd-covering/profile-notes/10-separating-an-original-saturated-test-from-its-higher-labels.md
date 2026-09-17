[Index](../marked_head_profile.md) · [Previous](09-fixed-convex-potentials-for-the-actual-cap-charge.md) · [Next](11-original9-higher-hinges-and-a-fixed-1113-continuation.md)

<a id="separating-an-original-saturated-test-from-its-higher-labels"></a>
### Separating an original saturated test from its higher labels

The unchanged PG1 probability satisfies the stronger all-height bound

    Γ ≤ 492647095380812739054683/14604022456869186140625
      <135/4=33.75.                                    (M9-1)

On this same probability, the threshold-two hinge is at most3 and
the mean is at most5, as established below.

Here the low geometry, all original3/5/7 exponent quantifiers and the
actual higher forbidden family are exactly those of(PG1). This bound
also transfers to its232 containing-carrier orbits. The improvement
keeps both the original mod3 test i and the original mod9 test j.
Unlike modulus3, modulus9 is a saturated projection. Its original
class must be separated from its descendants before applying the
convex-hull step.

<a id="the-original-class-and-the-projected-aggregate-are-different"></a>
#### The original class and the projected aggregate are different

Fix the original test classes C_3=i mod3 and C_9=j mod9. Projection9
has the original modulus9 and the higher pure ternary moduli27,81,….
After the additional-coordinate prefix comparison, its active terms
are bounded by

    1_(C_9) + min(Z_3,n_3)·1_(D_9),                   (M9-2)

inside the convex maximization. The first class stays fixed. Only
the active higher labels enter the convex average whose extreme
cylinder is D_9. At zero matching depth there are no such labels,
so the second term is zero. Increasing min(Z_3,n_3) to Z_3 gives the
uniform-in-height bound. Each higher exponent remains a different
original modulus; the averaging step only bounds the cost.

For a low layout θ of all remaining projected cylinders, put

    L_ij(z,θ)=1_(j mod9)+z_3·1_(D_9)
                       +Σ_(d|315,d≠9)w_d(z)1_(C_d),
    C_3=i mod3,
    F_ij(z)=max_θ E_μ L_ij(z,θ)².                    (M9-3)

The coefficient of the original unit label is one. Prefix comparison
followed by Jensen on the higher9 labels and the other projected
families gives E_λL²≤E_ZF_ij(Z). Both i and j are fixed across Z;
θ may maximize separately at each Z. Taking an aggregate cylinder
from(SH10) and calling it the original9 class would not justify this
formula.

In the pure7 and fixed-A relaxations, the low A load is therefore

    A_z=1+1_(i mod3)+(1+z_5)1_(C_5)+1_(j mod9)
        +z_3·1_(D_9)+(1+z_5)1_(C_15)
        +(1+z_3)(1+z_5)1_(C_45).                      (M9-4)

The high B load is unchanged: its cofactor9 belongs to original
modulus63 and its descendants, and retains coefficient1+z_3.
Both45 singleton coefficients remain(1+z_3)(1+z_5), so the existing
two-singleton elimination applies with different low and high base
loads. The fixed-A digit partition uses the same modified A and the
unchanged high-label coefficients.

<a id="complete-tail-and-actual-deleted-energy"></a>
#### Complete tail and actual deleted energy

The same pair-cap polynomial P still controls the omitted depths:

    F_ij(z)≤F_ij(0)+P(z)−P(0).                         (M9-5)

For proof fix θ, write L_ij(z,θ)=L_ij(0,θ)+Δ with Δ≥0, and expand
2L_ij(0,θ)Δ+Δ². Every coefficient is nonnegative. Each pair of low
cylinders has mass at most m_lcm(d,e), including a pair involving
the fixed original9 and its separately chosen higher D_9. Upon
grouping by projected labels, the coefficient increments sum to
w_d(z)w_e(z)−1. This proves the increment bound for the same θ.
Maximizing its zero-depth part gives(M9-5). No common residue between
original9 and D_9 is assumed.

Let H_ij be the pointwise minimum of the two finite relaxations at
the fixed μ. Equation(M3-5), with H_ij in place of H_i, gives U_ij,
including every geometric depth outside[0,8]×[0,5]×[0,4]. For the
actual complete test,

    L≥b_ij=1+1_(i mod3)+1_(j mod9).

For any reference C≥9, the positive finite measure(C−b_ij²)μ can be
used directly in the same grouped deletion bound. Consequently

    q_actual(E_(λ|F)L²−C)
                    ≤ U_ij+R_E((C−b_ij²)μ)−C.          (M9-6)

If q_actual≥q_0>0 and

    E=max(0,max_(i,j)[U_ij+R_E((C−b_ij²)μ)−C]),

then Γ_(λ|F)≤C+E/q_0. The reference C need not itself be a valid
moment bound. Here C=33 and the computed positive excess is

    E=5357177152064798207029/13783840971486886125000,
    q_0=25428074957/48000000336.

Their exact value33+E/q_0 is(M9-1). Its gap below135/4 is
954650154089172765643/58416089827476744562500>0. Thus this certificate
does not claim Γ≤33. The maximum excess occurs at i=2,j=2.

The PG1 support has two nonempty mod3 roots and five nonempty mod9
roots. A test class empty on that support can be moved to a nonempty
class, increasing the complete load pointwise before and after the
same conditioning. All ten remaining pairs are checked. The
probability weights and forbidden family are independent of that
test pair.

<a id="a-threshold-two-bound-on-the-same-probability"></a>
#### A threshold-two bound on the same probability

For the actual low weights define R_x=Σ_yμ_(x,y) and
v_x=max_yμ_(x,y). For any increasing convex g, a valid common-layout
upper bound is

    max_(A,B) Σ_x[(R_x−v_x)g(A_x)
                      +v_x g(A_x+(1+z_7)B_x)].         (M9-7)

Here A is(M9-4), with i,j fixed, and B retains the unchanged old45
weights. To prove the bound, fix all old cylinders and at each row
let t_y be the high-label load on digit y, with Σ_y t_y=t=(1+z_7)B_x.
The convex chord inequality gives
g(A_x+t_y)≤g(A_x)+(t_y/t)(g(A_x+t)−g(A_x)) for t>0.
Since Σ_yμ_(x,y)t_y≤v_xt, summing proves(M9-7). The case t=0 is
immediate. The bound allows rowwise concentration only as a cost
upper bound; no actual test cylinder or forbidden digit is moved.

For g(l)=(l−2)_+, the high term is linear because A≥1 and B≥1.
The maximizing B mean is the sum of its six weighted cylinder caps
under v, independent of A. Thus full enumeration of A suffices for
an exact maximum of this relaxation. The one-Lipschitz property of
g gives the complete outside-box estimate

    F_g,ij(z)≤F_g,ij(0)+Σ_d(w_d(z)−1)m_d.             (M9-8)

Its omitted coefficients are the exact first geometric moments
E[1_(Z∉B)(w_d(Z)−1)], all nonnegative. This includes the separated
higher9 term z_3; the fixed original9 contributes no increment.

The original test satisfies

    g(L)≥g(b_ij)=1_(i mod3)·1_(j mod9).

Applying the deleted-energy identity to g, with reference C=3, gives

    q_actual(E_(λ|F)(L−2)_+−3)
       ≤ U_g,ij+R_E((3−1_(i mod3)1_(j mod9))μ)−3.     (M9-9)

All ten right-hand sides are negative in the exact certificate, with
minimum margin43684194883477173419/1531537885720765125000>0.
The measure inside R_E uses the same low μ as the square bounds;
it is not normalized or averaged over j. Therefore

    sup_test E_(λ|F)(L−2)_+≤3,
    sup_test E_(λ|F)L≤5.                              (M9-10)

The second conclusion uses the pointwise inequality
L≤2+(L−2)_+. Both bounds hold together with(M9-1) for every actual
higher forbidden family, on exactly the same conditioned law.

`verify_original9_conditioned_geometry.py` binds the existing PG1
probability source by hash, reconstructs its support, and recomputes
both integer square maxima at all270depths for all ten pairs. It also
recomputes the threshold-two maxima, the independent positive mass,
the corresponding weighted deletion bounds, and the complete first
and second geometric remainders. The adjacent certificate
stores these finite arithmetic data and the exact excess conversion.
Run it with `python3 -I -O`. The proof above is an ordinary all-height
argument with an exact certificate; no new Lean endpoint, global
low-configuration bound or unrestricted-prime continuation is claimed.

<a id="a-uniform-86-point-profile-has-all-height-moment-bound-35"></a>
### A uniform 86-point profile has all-height moment bound 35

Fix the old forbidden classes

```text
(3,0), (9,4), (5,0), (15,1), (45,37)
```

and the pure-seven class `(7,0)`. The old complement, in increasing order, is

```text
X = [2,7,8,11,14,17,19,23,26,28,29,32,34,38,41,43,44].
b = [0,3,0,0,1,0,3,0,0,1,1,0,4,0,0,2,1].
```

For any actual choice of the five remaining original low classes, with moduli
21, 35, 63, 105 and 315, record the deletion mask in each nonzero seven digit.
Its coordinate sum is the deletion vector. Consider every actual carrier whose
vector is an image of `b` under an allowed old-coordinate automorphism. The
complete carrier classification gives six mask states, in three old-coordinate
orbits, represented by the full nonempty mask multisets

```text
[2,4160,36866,37442,70736]
[4160,36866,37442,70738]
[4162,36866,37442,70736].
```

Each is inclusion-minimal and has 86 points. The certificate gives an original
five-label realization of each representative. The verifier reconstructs all
actual states of this old shape, selects the entire vector orbit, and checks
these counts and realizations; it does not infer the full carrier from `b`
alone.

For every carrier in this profile let μ be the uniform probability law on all
its 86 actual points. For arbitrary finite nonnegative integers n3, n5, n7,
lift μ uniformly in the added prime-power digits to
`Q = 3^(2+n3) 5^(1+n5) 7^(1+n7)`, obtaining λ. Choose arbitrary actual higher
forbidden classes, at most one for each distinct original divisor of Q which
does not divide 315, and let F be their surviving event. Then λ(F)>0, and for
every complete test family with one residue class C_m for each m dividing Q,
including the unit class, its load L satisfies

```text
E_[λ(.|F)] L² ≤ 35.
```

The quantified higher family is arbitrary; its cylinders are not required to
be centered or nested. The proof uses a moment domination and a separate bound
on the actual deletion event.

For the moment bound, let independent auxiliary geometric variables have
`Pr(Z_p=k)=(p−1)/p^(k+1)`, for p in {3,5,7}. Saturate exponents at (2,1,1), and
put

```text
w_d(z) = product of (1+z_p) over p for which v_p(d) is saturated.
```

The saturated-prefix moment argument bounds E_λ L² by the expectation of the
largest weighted low-layout square. Original higher modulus labels retain
their extra exponents: equal saturated cofactors do not identify them. Keep
the original mod-3 test root i fixed, for i=1 or 2. At each height z write
`u=1+z7`, and let A_i and B range over complete old-45 test layouts with
cofactor weights

```text
cofactors:  1, 3, 5,       9,       15,      45
weights:   1, 1, 1+z5,    1+z3,    1+z5,    (1+z3)(1+z5).
```

Only A_i has its cofactor-3 root fixed to i. The pure-seven upper bound keeps
one common digit j for the pure-seven test class. With old-fibre masses R_x,
maximum point masses v_x and point masses μ_(x,j), it is the maximum of

```text
Σ_x [ R_x A_i(x)²
    + v_x (2u A_i(x)(B(x)−1) + u²(B(x)−1)²)
    + μ_(x,j) (2u A_i(x) + u²(2B(x)−1)) ].
```

This follows by expanding the square: terms involving the pure-seven class
use its one actual digit, while the other seven-divisible intersections are
bounded by v_x. All coefficients multiplying μ_(x,j) are nonnegative. Every
profile carrier has at most five occupied deletion digits, leaving a nonzero
digit untouched. Uniformity therefore gives `R_x=(6−b_x)/86`, `v_x=1/86`, and
a single digit attaining `μ_(x,j)=1/86` for every x. Consequently, at every
height and for both roots, the pure-seven upper bound is exactly

```text
H_i(z) = (1/86) max_(A_i,B) Σ_x [
              (6−b_x) A_i(x)² + 2u A_i(x)B(x) + u²B(x)² ].
```

This is an identity for the stated upper bound, not an assertion that every
relaxed intersection is jointly realizable. It explains why the same integer
moment computation applies to all three carrier orbits, at all heights.

Ordinary caps and the weighted caps used below also depend only on this
profile. For any nonnegative weight f(x) independent of the seven digit, and
e dividing 45, the caps of the finite measure fμ are

```text
m_e(fμ)  = (1/86) max_a Σ_(x≡a mod e) (6−b_x) f(x),
m_7e(fμ) = (1/86) max_a Σ_(x≡a mod e) f(x).
```

The second equality is attained at an untouched digit. Old-coordinate maps
preserve these cylinder families and the two mod-3 roots; common seven-digit
permutations preserve all relevant intersections. Thus moments and caps
transport to all six states.

The full geometric tail is retained. Put `B0=[0,8]×[0,5]×[0,4]`, with 270
heights, and β=Pr(Z∈B0). For ordinary caps m_d define
`P(z)=Σ_(d,e|315) w_d(z)w_e(z)m_lcm(d,e)`. The square increment of any fixed
layout is at most P(z)−P(0), since all weight-product increments are
nonnegative. For each root this yields

```text
U_i = (1−β)H_i(0) + Σ_(z∈B0) Pr(Z=z)H_i(z) + Σ_d η_out(d)m_d,
E_λ L² ≤ U_i.
```

Here η_out(d) is the exact coefficient of m_d in
`E[1_(Z∉B0)(P(Z)−P(0))]`. Its computation uses the one-prime pair moments
1, p/(p−1), or p(p+1)/(p−1)² according as neither, one, or both cofactors are
saturated. Subtracting the zero-height term and the finite-box contribution
leaves the nonnegative full remainder. No physical height or geometric tail
is discarded.

For deletions use the original one-extra-prime blocks

```text
E3={9,45}, E5={5,15,45,35}, E7={7,21,35,63,105,315}.
```

For a positive finite measure σ on the actual carrier define

```text
G(σ) = max_(selected low cylinders) ∫ [1−Π_p(1−A_p/(p−1))] dσ,
ρ_d  = E[w_d(Z)]−1−Σ_(p:d∈Ep) 1/(p−1).
```

Here A_p counts the selected cylinders in block p. The factors are
nonnegative, and all ρ_d are nonnegative. Independence of the added prime
coordinates, geometric averaging within each original projected label, and
separate affinity of the product give this grouped bound. Applying the union
bound to the remaining original labels yields

```text
∫_(Fᶜ) f dλ ≤ G(fμ) + Σ_d ρ_d m_d(fμ)
```

for each nonnegative low weight f used here. In particular,
`λ(F) ≥ 1−G(μ)−Σ_d ρ_d m_d(μ)`.

Equality of deletion vectors alone does not establish equality of grouped
maxima. The verifier enumerates all actual masks in the profile, reduces them
to the three representatives, and computes three independent group maxima
on each representative: f=1 and the two weights
`h_i=35−1−3·1_(x≡i mod3)`. These nine exact maximizations give the same results
on each carrier:

```text
86·48 G(μ)     = 1546,
86·48 G(h_1μ) = 52012,
86·48 G(h_2μ) = 48502,
q = 1−G(μ)−Σ_d ρ_d m_d(μ) = 2333/4128 > 0.
```

Taking the maximum over all three checked representatives therefore covers
the entire actual profile. The common final values are

| Root i | U_i | R_i = G(h_iμ)+Σ_d ρ_d m_d(h_iμ) | 35−U_i−R_i |
| --- | --- | --- | --- |
| 1 | 183628451886661/10976021437500 | 30233/2064 | 159032185718981/43904085750000 |
| 2 | 32905/1548 | 14095/1032 | 265/3096 |

Both margins are positive. The unit class and the original cofactor-3 test
class imply `L²≥1+3·1_(x≡i mod3)`. Therefore

```text
∫_F (L²−35) dλ
 = E_λ(L²−35) + ∫_(Fᶜ)(35−L²) dλ
 ≤ U_i−35 + ∫_(Fᶜ) h_i dλ
 ≤ U_i−35+R_i < 0.
```

Dividing by the independently verified λ(F)>0 proves the claimed conditional
bound. A mod-3 test root 0 is empty on the carrier; replacing it by root 1
only increases L, so the two checked roots cover every test family.

Finally, the exact support-inclusion matching covers 821 common-seven-digit
mask states, or 355 old-coordinate orbits, and exactly three minimal orbits.
For a containing carrier and any of its higher forbidden families, pull that
family back through the allowed coordinate map, apply the source result,
and push the source law forward. Extra low points receive zero mass. Thus
these 355 orbits inherit a supported law with the same all-height bound 35;
they are not claimed to satisfy this bound under their own full-support
uniform laws. The matching preserves complete deletion-mask multisets and
original modulus labels.

`verify_uniform_profile_geometry.py` and
`uniform_profile_geometry_certificate.json` reproduce the profile, the
270-height pure-seven computation, all nine actual group maxima, rational
tails and margins, and support counts. This is a finite exact computational
certificate with the all-height argument above; it is not a Lean kernel
verification or a claim about the remaining low-carrier profiles.

The old-support embedding matrix from the complete carrier reduction
separates this old45 shape from both preceding sources. Thus these355
orbits are disjoint from their384, giving739 carrier orbits and five
inclusion-minimal sources with an inherited bound35. The stronger PG1
bounds still apply to its own232 containing orbits. Among the56966
minimal orbits,56961 remain outside these five sources; the general
continuation through11,13,17 and all later primes remains unresolved.

<a id="a-deletion-bound-determined-by-row-counts-with-an-exactness-criterion"></a>
#### A deletion bound determined by row counts, with an exactness criterion

The grouped deletion cost admits a sufficient upper observation even when
the deletion vector does not determine the actual carrier. Fix a finite
old-coordinate set X⊆Z/45Z, numbers f_x≥0 for every x∈X, and N>0.
Let S be a subset of X×{1,…,6}, with exactly6−b_x retained points in row x,
and let the nonnegative finite measure σ give every retained point in
that row mass f_x/N. No probability normalization is required.
Keep the same original projected blocks E3,E5,E7 defined above. Write
A for a choice of the two old cylinders at9,45, and B for a choice of
the three old cylinders at5,15,45. Set T=2−A and M=T(4−B), pointwise on X.
For each choice define

    J_f(b;A,B) = Σ_x(6−b_x)f_x(24A_x+6T_xB_x)
                  +6 max_(a mod5) Σ_(x≡a mod5) f_xT_x
                  +Σ_(c|45) max_(a modc) Σ_(x≡a modc) f_xM_x.

Then the actual grouped cost satisfies

    48N G(σ) ≤ max_(A,B) J_f(b;A,B).                  (UP-1)

Thus this upper bound uses only X,b,f,N. If there are at least two
distinct digits y with X×{y} contained in S, equality holds in(UP-1).

To prove the upper bound, let I be the extra original mod35 cylinder
and C the sum of the six original E7 cylinders. The exact product-union
expansion on the actual carrier has numerator

    24A+6TB+6TI+MC−TIC.

All of T,I,C and f are nonnegative. Dropping the last term increases
the integral. The old-coordinate part integrates with row multiplicity
6−b_x. The single I cylinder is bounded by the displayed mod5 maximum;
each of the six C cylinders is bounded by its displayed old-cofactor
maximum. This proves(UP-1), without moving the actual forbidden family
or replacing its measure.

For equality, choose maximizing old A,B. Put I on one wholly retained
digit and all six C cylinders on the other. Choose each old residue to
attain its own maximum. These are allowed choices of the distinct
original projected labels, their digit supports are disjoint, and every
row used by any of them is retained. Hence TIC=0 and every preceding
upper comparison is an equality. This construction concerns the
maximization defining G; it does not identify or move actual higher
forbidden cylinders.

There is a weaker, layout-dependent equality criterion. Keep one wholly
retained digit for the six C cylinders. For some maximizing A,B and a
maximizing old mod5 residue a for I, it suffices that a different digit y
has zero missing fT mass on that old cylinder:

    Σ_(x≡a mod5, (x,y)∉S) f_xT_x = 0.                 (UP-2)

The same construction then attains the I maximum, while the two digit
supports still make TIC=0. All other upper comparisons are unchanged.

For the preceding profile, the three measures f=1,h_1,h_2 give exactly
1546,52012,48502 in the right-hand side of(UP-1). The two four-mask
representatives have two wholly retained digits. In the five-mask
representative, digit6 is wholly retained and digit5 is missing only
x=7. All three computed maximizers use old mod5 residue4 for I, so
(UP-2) holds on digit5. Thus the row-count formula independently
recovers all nine actual grouped maxima, including the five-mask case.

The verifier enumerates every distinct old cylinder, including one
representative of the empty cylinder when that cofactor has an empty
residue class. This is necessary for the general relaxed maximum:
dropping TIC does not justify assuming monotonicity in A or B.
Its witness check uses the reconstructed original-family carriers to
verify(UP-2). With only one wholly retained digit and no such witness,
(UP-1) remains an upper bound; equality is not asserted. This separates
sufficiency for a numerical upper bound from reconstruction of the
full carrier.

<a id="uniform35-bounds-on-a-full-deletion-profile-box"></a>
### Uniform35 bounds on a full deletion-profile box

Fix the canonical old45 shape `root1_same_other_column`, its17 old points X,
and the source deletion profile

    b*=(0,3,0,0,1,0,3,0,0,1,1,0,4,0,0,2,1).

For every actual original-label carrier whose deletion profile satisfies
0≤b≤b* coordinatewise, use its own uniform probability measure μ: each
surviving low315 point has mass1/N, where r=6−b and N=Σ_x r_x. The same
conclusion applies after an allowed old-coordinate map; these preserve
both named mod3 roots. There are exactly two images of b*.

Every such actual carrier has an untouched nonzero7 digit, since there are
only five mixed original labels and six available nonzero digits. Thus the
pure7 upper bound, for each original mod3 root i and every geometric depth z,
has unnormalized form

    H_i(r,z)=max_(A with original mod3 root i, B)
             [Σ_x r_x A_x² + Σ_x (2u A_xB_x+u²B_x²)],  u=1+z7.

The layout sets and second sum do not depend on r. Hence H_i is a maximum
of affine functions of r and is convex. Retaining the canonical270-depth
box and its entire exact geometric tail gives

    P_i(r)=(1−β)H_i(r,0)+Σ_(z in box)Pr(Z=z)H_i(r,z)
             +Σ_d η_out(d) C_d(r,1),

where the unnormalized caps are

    C_e(r,f)=max_a Σ_(x≡a mod e) r_x f_x,
    C_7e(r,f)=max_a Σ_(x≡a mod e) f_x,                  e|45.

All coefficients are nonnegative. P_i is therefore convex. Let V(r,f) be
the existing UP-1 old-coordinate group upper bound, written with row counts r.
It too is a maximum of affine functions, since its extra35/E7 contribution
is independent of r. Put h_i(x)=34−3·1_(x≡i mod3) and retain the canonical
nonnegative residual coefficients ρ_d. Define the unnormalized slacks

    S(r)=N−V(r,1)/48−Σ_d ρ_d C_d(r,1),
    M_i(r)=35N−P_i(r)−V(r,h_i)/48−Σ_d ρ_d C_d(r,h_i).

S and both M_i are concave functions of r. At any actual carrier, S/N is a
lower bound for the same-law higher survival probability and M_i/N is the
slack in the same original-mod3 signed35 criterion. There is no renormalization
of h_i μ. The measure and its independent higher-prime lift belong to the
actual carrier being certified; the convexity argument does not substitute
a supported measure or a mixture of source laws.

The box6−b*≤r≤6 has eight varying coordinates and256 vertices. At each vertex,
the retained program evaluates both270-depth moment maxima, all full-tail
coefficients, all caps, and the UP-1 maximum exactly. All256 vertices satisfy
S>0 and M_1,M_2≥0. The smallest normalized slacks are

    S/N  ≥ 2357/4176,
    M_1/N ≥ 159032185718981/43904085750000,
    M_2/N ≥ 265/3096.

For any constant c equal to one of these minima, S−cN or M_i−cN remains
concave and is nonnegative at every vertex. Every box point is a convex
combination of vertices, so the corresponding normalized lower bound holds
throughout the box. In particular, every actual carrier in the stated
profile region satisfies the same35 target on its own full-support uniform
law. This establishes inheritance throughout this source box, not global
coordinatewise monotonicity of the numerical objective.

Geometry-only enumeration of all165141 actual carrier states for this old
shape, followed by exact profile membership and old-map orbit reduction,
gives1339 states in562 orbits with477 distinct profiles. The existing
original-label resource criterion identifies8 inclusion-minimal orbits.
The former source-support region821 states/355 orbits is contained in this
box region. Thus the new region adds518 states/207 orbits and5 minimal
orbits. Membership uses no numerical query on individual carriers.

The verifier `verify_uniform_profile_box.py` pins the parent
`uniform_profile_geometry_certificate.json` by SHA-256. It imports only the
adjacent canonical point, classification and dominance algorithms. Its
certificate retains the rational corner values and hashes of all270-depth
root maxima. It reconstructs all actual carrier states and checks both
containment of former support coverage and the new minimal representatives.

For the moment computation, each old layout consists of a base layout L on
cofactors1,3,5,9,15 plus an old45 singleton of weight
s=(1+z3)(1+z5). For fixed base layouts L_a,L_b and A-singleton location i,
the constant part after eliminating the B-singleton is

    2u<L_a,L_b>+u²||L_b||²+2us L_b(i)
      +max_j[2us L_a(j)+u²(2sL_b(j)+s²)+2us²·1_(j=i)].

The inner maximum equals the larger of its unmodified maximum and its
value at i plus2us². The remaining row-dependent contribution is
Σ_x r_x L_a(x)²+r_i(2sL_a(i)+s²). Maximizing over i and both base layouts,
with only A's originalmod3 root fixed, computes H_i(r,z) exactly. The source
corner reproduces both parent270-depth hashes.
The grouped bound enumerates77760 old A/B pairs, retaining each nonempty
cylinder and one representative of an empty cylinder when present. It
precomputes each affine row coefficient and its r-independent extra35/E7
term, then evaluates every corner. Its nonnegative integer dot products
are bounded by1692,56856,53796 for1,h1,h2, so binary64 arithmetic is exact
below2^53; integers are checked before they enter rational calculations.
The moment calculation itself uses int64 arrays with the present finite
parameters. All guards use explicit exceptions and remain active under-O.

The two other certified old45 geometries are disjoint from this region.
Together the three geometries now cover946 carrier orbits and10
inclusion-minimal orbits at Gamma≤35. Of the56966 minimal orbits,
56956 remain outside these certified sources. The PG1 bounds retain
their stronger values on its232 containing orbits.

Replay the certificate from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/verify_uniform_profile_box.py

This is finite arithmetic verification plus the concavity argument above,
not a Lean kernel result. The stated profile region is a hypothesis;
no bound for another old shape is asserted here.
