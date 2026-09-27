[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](11-current-bounds-and-comparisons.md) · [Next](13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md)

<a id="coupling-the-shared-zero-exponent-layout"></a>
### Coupling the shared zero-exponent layout

For every finite distinct-modulus family supported on `{3,5}`, its uniform
complete-survivor law satisfies

\[
 \boxed{\Gamma_{35}\le55/4.} \tag{ZG1}
\]

Together with the established bound on the same uniform law, this gives
`(Γ35,R35)≤(55/4,15/7)`. The improvement comes from preserving the identity
of the zero-five-exponent test layout in all its cross terms.

Suppose first that an actual modulus-3 class is present. Use the actual
two-root parameters from the earlier budget argument:

\[
 y=1/4,\quad a=7/8,\quad x=(w+v)/3,\quad
 d=z-\alpha,\quad e=z-\beta,
\]
\[
 n=wd/3-t_A,\qquad m=ve/3-t_B,\qquad s=n+m.
\]

Here `1/2≤w,v≤1`, `w+v≥3/2`, `3/4≤z≤1`, `α,β≥0`, `α+β≤y`, and
`t_A,t_B≥0`, `t_A+t_B≤y/6`. Let `η` be the unnormalized uniform measure
on the pure-ternary survivor set. Its total mass is `x`, its two root masses
are `w/3,v/3`, and its depth-`j` cylinder caps are `3^{-j}` in either
surviving root. Write `μ` for the uniform complete `{3,5}` survivor law.
As positive measures on the full product period,

\[
 \mu\le s^{-1}(\eta\times U_5),
\]

where `U_5` is uniform on the whole finite 5-power coordinate. This
inequality drops the pure-5 and mixed exclusions, and applies whether or
not individual old fibres survive.

Fix one complete test layout. For each 5-exponent `b≥0`, stripping the
5-part of its divisors gives a complete pure-ternary layout with load
`L_b`. These loads include divisor one and every old cofactor. The selected
5-adic residue may depend on the old divisor. Put

\[
 A_0=\int L_0^2\,d\eta,\qquad B=\Gamma(\eta).
\]

The block with both 5-exponents zero contributes exactly
`E_μ L_0²`, since `L_0` depends only on the ternary coordinate. For the
two ordered blocks `(0,b),(b,0)` with `b>0`, each pair of outside cylinders
has uniform intersection mass at most `5^{-b}`. Bound this separately for
every old divisor pair, then sum and integrate the old indicators. The two
blocks together contribute at most

\[
 \frac{2\cdot5^{-b}}s\int L_0L_b\,d\eta
 \le\frac{5^{-b}}s(A_0+B),
\]

by the pointwise square inequality and `∫L_b²dη≤B`. Among pairs of
strictly positive 5-exponents with maximum `b`, there are `2b−1` ordered
pairs. Cauchy–Schwarz bounds each complete old cross moment by `B`.
Summing these nonnegative bounds gives

\[
 E_\mu L^2\le E_\mu L_0^2+
       \frac{yA_0+(a-y)B}s. \tag{ZG2}
\]

Indeed `∑_{b≥1}5^{-b}=y` and
`∑_{b≥1}(2b−1)5^{-b}=a−2y=3/8`. Thus the coefficient of `B` is
`y+(a−2y)=a−y=5/8`. At finite heights, only existing blocks are present;
the infinite series provide upper bounds with nonnegative terms. No old
cofactor, cross term or tail is omitted.

The same `L_0` occurs in both terms of (ZG2). If its modulus-3 test
chooses surviving root `A`, the existing root-labelled Bellman estimate gives

\[
 E_\mu L_0^2\le1+\frac{3n+\max(d,2e/3)}s,
 \qquad A_0\le x+w+1.
\]

For any complete old layout, the same estimate under `η` gives
`B≤x+max(w,v)+1`. Hence an `A`-selected layout satisfies

\[
 E_\mu L^2\le1+
 \frac{3n+\max(d,2e/3)+y(x+w+1)
                +(a-y)(x+\max(w,v)+1)}s.
 \tag{ZG3}
\]

The corresponding `B`-selected bound swaps the two roots. These are
consequences of the same finite-itinerary estimate used earlier: when the
initial root is fixed, the later tail under `η` contributes at most one,
while the initial diagonal and two constant crosses contribute `w` or `v`.
The global `B` permits either initial root; `A_0` retains the actual one.

If the modulus-3 test chooses the actual forbidden root, its event has zero
mass under both measures. The remaining-tail bounds are

\[
 E_\mu L_0^2\le1+\frac{2\max(d,e)}{3s},\qquad
 A_0\le x+2/3.
\]

This case is dominated by one of the surviving-root bounds. If `d≥e`,
choose the bound whose initial root is `B`: its numerator includes
`3m+max(e,2d/3)≥2d/3`, and its `η` cap `x+v+1` is at least `x+2/3`.
If `e≥d`, use root `A` symmetrically. Thus no additional optimization
assumption is needed for the forbidden-root test choice.

To maximize (ZG3), move all deep mixed deletion from the selected root to
the other root. This keeps `s` fixed and increases `n`; every other term
is unchanged. Enlarge the other-root deletion to `y/6`. The numerator is
positive and fixed during this enlargement, while the denominator decreases.
It therefore suffices to take

\[
 n=w(z-\alpha)/3,\qquad
 m=v(z-\beta)/3-y/6.
\]

Both roots remain positive: `n≥1/12`, `m≥1/24`. Expand the two maxima
in (ZG3) into their four affine branches. For each branch, numerator and
denominator are affine in each of `(α,β)`, `(w,v)` and `z` separately.
A ratio of affine functions with positive denominator at a convex
combination is the denominator-weighted average of its vertex ratios.
Applying this successively leaves exactly the eighteen parameter vertices

\[
 (w,v)\in\{(1/2,1),(1,1/2),(1,1)\},\qquad
 (\alpha,\beta)\in\{(0,0),(y,0),(0,y)\},\qquad z\in\{1-y,1\}.
\]

The fixed rational certificate checks all `18×4=72` branches. Their exact
maximum is `55/4`, proving (ZG1) for an actual modulus-3 exclusion. Root
exchange covers either surviving-root test choice. If the actual modulus-3
class is absent, the established unsplit uniform bound is `215/24<55/4`;
its normalization denominator is `1/2>0`. Missing higher pure classes,
missing mixed classes and arbitrary finite prime heights are already allowed
by the budgets and the nonnegative geometric-tail bounds above.

The old extremal parameter point illustrates the gain. At
`w=1/2,v=1,α=0,β=1/4,z=3/4,t_A=0,t_B=1/24`, one has `n=m=1/8`.
The old envelope gave `57/4`. Its pure old contribution selects root `A`,
while its independent positive-five bound can select root `B`. Retaining
that first choice in `A_0≤x+w+1=2`, alongside `B≤5/2`, gives `55/4`.

The parameter point itself is a genuine infinite-height limit, so it cannot
be removed by asserting a forced overlap of pure-ternary and deep mixed
exclusions. An explicit finite family with heights `H≥2,K≥1` is:

- forbid `2 mod 3`;
- for `2≤j≤H`, forbid `3^{j−1} mod 3^j` in root `A=0`;
- for `1≤b≤K`, forbid `5^{b−1} mod 5^b`;
- for each `3·5^b`, choose the CRT class `1 mod 3` and
  `2·5^{b−1} mod 5^b`;
- for each `3^j5^b` with `j≥2`, choose the CRT class
  `1+3^{j−1} mod 3^j` and `3·5^{b−1} mod 5^b`.

Every modulus is distinct. For any fixed prime, the displayed strings with
first nonzero digit at different depths are disjoint. The three 5-adic
colours `1,2,3` are also disjoint; pure higher ternary exclusions lie in
root `A`, while the deep mixed ternary factors lie in root `B`. Therefore,
with `r_H=∑_{j=2}^H3^{-j}` and `u_K=∑_{b=1}^K5^{-b}`, the exact parameters
are `w=1−3r_H`, `v=1`, `z=1−u_K`, `α=0`, `β=u_K`, `t_A=0`,
`t_B=r_Hu_K`. Their limits are exactly the old extremal parameters.
This realizes the budget limit, not equality in the old second-moment
bound; (ZG1) shows that the old bound is not tight for actual layouts.

The [standalone verifier](../verify_uniform_gamma_cofactor_coupling.py) checks
all rational branches and missing-modulus normalization against
the [fixed certificate](../certificates/uniform_gamma_cofactor_certificate.json). The layout correspondence and
continuous reduction above are ordinary mathematical arguments; no full
Lean formalization of (ZG1) is claimed.

<a id="the-shared-zero-exponent-envelope-for-arbitrary-outside-prime"></a>
### The shared zero-exponent envelope for arbitrary outside prime

Let q>=5 be prime and let mu be the uniform complete-survivor law of any
finite distinct-modulus family supported on {3,q}. Set

    y=1/(q-1),     a=(3q-1)/(q-1)^2=3y+2y^2.

The shared-zero-layout argument gives the uniform bound

    Gamma(mu) <= max{ A(y), B(y) },
    A(y)=(30y^2+28y+15)/(3-5y),
    B(y)=5(2y^2+y+1)/(1-2y).

This is the exact maximum of that argument's parameter relaxation, not a
claim that the actual layout supremum always attains it. Its branch change is

    y_*=(sqrt(1281)-31)/20,
    B(y)-A(y)=y(10y^2+31y-8)/((1-2y)(3-5y)).

Consequently the prime cases simplify to

    q=5:  Gamma(mu)<=55/4;
    q>=7: Gamma(mu)<=(15q^2-2q+17)/((q-1)(3q-8)).

In particular q=7 and q=11 give 123/13 and 181/25. These equal the existing
compatible-layout inputs. The formula also supplies the bound for every larger prime, without
a height restriction.

<a id="proof-of-the-envelope"></a>
#### Proof of the envelope

When a modulus-3 forbidden class is present, retain the two actual root
widths w,v in [1/2,1], with w+v>=3/2, pure-q density z in [1-y,1],
first-level deletion unions alpha,beta>=0 with alpha+beta<=y, and total
deep deletion at most y/6. Write x=(w+v)/3, d=z-alpha and e=z-beta.

For a fixed layout whose zero-q layer chooses the first surviving ternary
root, the identical shared-layer proof gives

    E_mu L^2 <= 1+
      [3n+max(d,2e/3)+y(x+w+1)+(a-y)(x+max(w,v)+1)]/(n+m).

Here n=wd/3-t_A and m=ve/3-t_B are the actual complete root densities.
The coefficient of the shared zero layer is sum(q^-b)=y; that of the
remaining old-layout supremum is a-y. Every strictly positive-positive
lcm block has coefficient (2b-1)q^-b, whose sum is a-2y=y+2y^2>=0.
The test residues may depend on their old cofactors; cylinder integration
precedes the old-layout sum, as in the q=5 proof. A test in the forbidden
ternary root is dominated by one of the two surviving-root estimates.

Moving all deep deletion to the unselected root and enlarging it to y/6
increases this bound, so use n=wd/3 and m=ve/3-y/6. Uniformly for
0<=y<=1/4, n>=1/12 and m>=1/24. Expanding both maxima gives four affine
branches. Each is separately linear-fractional in the three parameter
groups, so its maximum lies among

    (w,v)=(1/2,1),(1,1/2),(1,1);
    (alpha,beta)=(0,0),(y,0),(0,y);
    z=1-y,1.

Of these 72 symbolic branches, 69 are <=A(y) throughout [0,1/4]. The
remaining three are <=B(y); their formulas are

    (10y^2+9y+4)/(1-2y),
    B(y),
    (30y^2+23y+13)/(3(1-2y)).

The respective gaps below B are (1-4y)/(1-2y), zero, and
2(1-4y)/(3(1-2y)). Both A and B themselves occur among the branches.
The 69 comparisons are exact polynomial certificates: after cross
multiplying positive denominators, each gap P satisfies

    4^n(1+t)^n P(t/(4(1+t))) has nonnegative rational coefficients,
    n=degree(P).

This proves each inequality over the entire parameter interval, with
continuity at y=1/4. The adjacent verifier reconstructs these polynomial
identities from the parameter formula; its fixed JSON supplies every gap
and coefficient. No numerical sampling or solver is used for this step.

If an actual modulus-3 exclusion is absent, the pure-ternary density is at
least 5/6. The monotone unsplit bound is

    M(y)=(34y^2+31y+17)/(5-8y).

The numerator of A-M after cross multiplication is
24+12y-21y^2-70y^3, at least 691/32>0 on [0,1/4]. Thus this branch is
strictly smaller than A; its q=5,7,11 values are 215/24,208/33,73/15.
Arbitrary finite heights and missing higher moduli remain covered by the
same nonnegative infinite-tail bounds.

The [standard-library verifier](../verify_uniform_gamma_prime_parameter.py)
and its [fixed certificate](../certificates/uniform_gamma_prime_parameter_certificate.json) verify all symbolic
identities and interval signs. Normal, -O and -I runs exit 0. The proof is
an ordinary mathematical generalization; no new Lean statement is delivered.

<a id="transporting-actual-layouts-through-outside-lcm-blocks"></a>
### Transporting actual layouts through outside lcm blocks

The actual two-prime estimate (G1), together with the common-family density
bounds, improves the four-prime profile bound (P14) to (B6). Set
`A={3,5}`, `B={7,11}`, and let `ρ_p` be uniform on the pure-`p` survivors
of the original family. The same-family conditioning steps give

\[
 1-\frac{R_{35}}{7-2}\ge\frac47,\qquad
 1-\frac{R_{357}}{11-2}\ge\frac{1591}{3240}.
\]

Both denominators are positive. The product probability
`ν=μ_A×ρ_7×ρ_11` therefore dominates the final uniform survivor law
pointwise as

\[
 \mu_{35711}\le D\nu,\qquad
 D=\frac74\frac{3240}{1591}=\frac{5670}{1591}.
 \tag{B1}
\]

This permits completely deleted fibres; it asserts no preservation of
the earlier marginals. Each `ρ_p` has cylinder bound
`ρ_p(r mod p^k)≤C_p/p^k`, where `C_p=(p−1)/(p−2)`.

Fix one full test layout. Group its classes by the outside exponent vector
`e=(e_7,e_11)`. Removing the outside factors gives, for every `e`, one
complete old layout `L_e` on `A`, including divisor one. For a pair of
outside exponent vectors `e,f`, put `b=max(e,f)` coordinatewise. Expand
its contribution over old divisors `d,d′` before integrating the outside
coordinates. The outside test residues may depend arbitrarily on both
old divisors. For each pair their intersection has mass at most

\[
 k_p(b_p)=
 \begin{cases}1,&b_p=0,\\ C_p p^{-b_p},&b_p>0.\end{cases}
\]

This cap is independent of `d,d′`. Summing the old indicators afterwards
and using Cauchy–Schwarz under the same `μ_A` gives

\[
 \int_\nu \text{the ordered }(e,f)\text{ contribution}
 \le\prod_{p\in B}k_p(b_p)\int L_eL_f\,d\mu_A
 \le\prod_{p\in B}k_p(b_p)\,\Gamma_A(\mu_A).
 \tag{B2}
\]

Thus test residues need not be independent of the old divisor, or mutually
compatible across divisors. There are `N_B(b)=(2b_7+1)(2b_11+1)` ordered
outside exponent pairs with maximum `b`. With `G=57/4` from (G1), the
entire block under the final law is bounded by

\[
 T_b=DG\,N_B(b)\prod_{p\in B}k_p(b_p).
 \tag{B3}
\]

The existing profile gives another bound on exactly that block:

\[
 P_b=N_B(b)\sum_{a_3,a_5\ge0}
             (2a_3+1)(2a_5+1)u(a_3,a_5,b_7,b_{11}),
 \tag{B4}
\]

where `u` is the full projection envelope from (P14). For this profile,
the largest adjoining-coordinate ratio among both ordinary and
first-ternary coefficients is `1344/361<7` at prime 7 and
`3600/1591<11` at prime 11. Whenever an outside exponent is positive,
including its coordinate in a projection therefore weakly improves that
envelope term. Applying this to both coordinates shows that `P_b` factors
exactly according to its positive support `J={p∈B:b_p>0}`:

\[
 P_b=C_J\prod_{p\in J}\frac{2b_p+1}{p^{b_p}},\qquad
 T_b=T_J\prod_{p\in J}\frac{2b_p+1}{p^{b_p}},\qquad
 T_J=DG\prod_{p\in J}C_p.
 \tag{B5}
\]

The internal coefficient `C_J` is the exact weighted envelope sum on
`{3,5}`, using ordinary coefficients `c(U∪J)` and first-ternary
coefficients `b(U∪J)`. The finite/tail partition with cutoffs no larger than
`a_3=2,a_5=1` evaluates all internal exponents. All four coefficients
and the complete outside-height sums are:

| Outside support `J` | Profile `C_J` | Actual-layout `T_J` | Height sum | Chosen bound |
|---|---:|---:|---:|---|
| empty | 67971/1591 | 161595/3182 | 1 | profile |
| `{7}` | 37315227/574351 | 96957/1591 | 5/9 | actual layout |
| `{11}` | 85450/1591 | 89775/1591 | 8/25 | profile |
| `{7,11}` | 115830/1591 | 107730/1591 | 8/45 | actual layout |

The height sums use `Σ_{k≥1}(2k+1)p^(−k)=(3p−1)/(p−1)²`.
Summing the profile column with these weights recovers exactly
`187719326/1723053`, providing a check that every old block is accounted
for. For each actual layout take the smaller bound on each block, then
sum. Since all terms are nonnegative, extending any finite heights to
the full geometric sums remains valid, even when some blocks are absent.
Consequently

\[
 \begin{aligned}
 \Gamma_{35711}
 &\le\frac{67971}{1591}
      +\frac59\frac{96957}{1591}
      +\frac8{25}\frac{85450}{1591}
      +\frac8{45}\frac{107730}{1591}\\
 &=\boxed{\frac{168332}{1591}<105.802640.}
 \end{aligned}
 \tag{B6}
\]

This proves the intermediate bound (B6), including arbitrary finite exponents. It bounds the
maximum of a joint layout square, and does not assert the same bound for
the sum of separately maximized cylinders. The
[block verifier](../elementary-checks/verify_lcm_block_transport.py)
and [fixed certificate](../certificates/lcm_block_certificate.json)
reconstruct the profile, check the adjoining-coordinate ratios, both
complete geometric sums, and three positive-denominator steps from the
(B6) seed. The stronger seed and bridge in (P2) and (P8) are checked by the
shared-cofactor verifier below. The block argument and its four-prime
conclusion are not Lean formalized.

<a id="intermediate-four-prime-bound-from-shared-survivor-densities"></a>
### Intermediate four-prime bound from shared survivor densities

For every finite distinct-modulus forbidden family supported on
S={3,5,7,11}, let mu_S be its complete uniform survivor law. Then

    Gamma(mu_S) <= 5015891/47730 = 105.08885397024932...

Here Gamma is the maximum second moment of one complete residue layout.
The improvement over 168332/1591 is exactly 34069/47730. The proof retains
actual survivor densities in the compatible-layout transfer; no
independence between different subset-survival events is assumed.

<a id="one-common-product-law"></a>
#### One common product law

Let rho_p be the uniform law surviving the original pure p-power classes,
and P=product rho_p. The pure survivor density is at least
(p-2)/(p-1), so a p^e cylinder has rho_p-mass at most
(p-1)/((p-2)p^e).

For A subset S, let E_A be survival of all original mixed forbidden classes
whose prime support is contained in A, and let lambda_A=P(E_A). Empty and
singleton A have lambda_A=1. Define

    t=1/lambda_S,   v_A=lambda_A/lambda_S.

All these numbers concern the same original family. E_S is contained in
E_A, so 1<=v_A<=t. The established same-family bounds R35<=15/7 and
R357<=1649/360 give

    lambda35 >= 2/3,
    lambda357 >= (4/7) lambda35 >= 8/21,
    lambdaS >= (1591/3240) lambda357 >= 1591/8505.

Thus t<=8505/1591. All relevant conditional laws exist because these
lower bounds are positive.

Under P, all forbidden classes of exact support U have total mass at most

    r_U=product_{p in U} 1/(p-2).

Indeed each mixed modulus occurs at most once; summing its pure-coordinate
cylinder cap over positive exponents gives this product. For any collection
C of proper nonsingleton subsets of B, the union bound gives

    lambda_B >= sum_{A in C} lambda_A - (|C|-1) - r,

where r is the sum of r_U over supports U subset B not contained in any
member of C. This is valid even when the events in C overlap.

The shared laws do not satisfy an automatic positive-correlation rule.
For example, take just the actual forbidden classes `0 mod 15` and
`1 mod 21`. They lie in different ternary roots, hence are disjoint.
There are no pure forbidden classes, so `P` is uniform and

    lambda35=14/15, lambda37=20/21, lambda357=31/35
             < lambda35 lambda37=8/9,

with difference `-1/315`. Thus FKG cannot be invoked merely from the
prime-product coordinates: arbitrary forbidden residue events do not
supply its required monotonicity hypotheses. The union bounds above
retain this negative-correlation possibility.

A cylinder C_T restricted to coordinates T is independent of E_(S minus T)
under P. Since E_S is contained in that complement event,

    mu_S(C_T)
      <= v_(S minus T) product_{p in T} (p-1)/((p-2)p^e_p).       (1)

This cylinder bound and all density inequalities therefore use one law.

<a id="five-strictly-improved-independent-projection-coefficients"></a>
#### Five strictly improved independent projection coefficients

The common-density inequalities imply the following ordinary c coefficients
in the bound mu_S(C_T)<=c_T/product p^e_p:

| T | previous c_T | new c_T |
|---|---:|---:|
| {3} | 17010/1591 | 16412/1591 |
| {5} | 9360/1591 | 25264/4773 |
| {7} | 1344/361 | 5916/1591 |
| {3,11} | 18900/1591 | 18540/1591 |
| {5,7} | 13608/1591 | 12784/1591 |

For the first three, the missing-support union bounds give respectively

    v5711 <= 1+(7/9)t <= 8206/1591,
    v3711 <= 1+(5/9)t <= 6316/1591,
    v3511 <= 1+(53/135)t <= 4930/1591.

For the fourth, v57<=v357+(3/5)t and v357<=3240/1591 give
v57<=8343/1591. For the fifth, use the overlapping events E311 and E357.
The uncovered-support budget is 2/15, so

    v311+v357-(17/15)t <= 1.

Together with v357>=(8/21)t this gives
v311<=1+(79/105)t<=7990/1591. Applying (1) proves the table. These
coefficients alone improve the compatible-layout head to 1509236/14319;
the stronger result below uses the densities jointly.

<a id="retaining-v35-in-the-compatible-layout-transfer"></a>
#### Retaining v35 in the compatible-layout transfer

The exact pointwise domination is

    mu_S <= v35 (mu35 x rho7 x rho11).

Fix any complete test layout. Group its ordered pairs by their outside
lcm exponents at 7 and 11. For a fixed outside exponent pair, the outside
test residues may depend on both old divisors. Integrating each old pair
first over rho7 x rho11 gives a uniform outside-cylinder bound; only then
sum the old indicators. The remaining cross moment is between two complete
{3,5} layouts, hence is at most Gamma(mu35)<=57/4 by Cauchy--Schwarz.

Summing all blocks with positive 7 exponent, including all 11 exponents,
therefore gives the bound

    (57/4) v35
      * [sum_{e7>=1} (2e7+1)(6/5)7^(-e7)]
      * [1+sum_{e11>=1} (2e11+1)(10/9)11^(-e11)]
     = (57/4)(2/3)(61/45) v35
     = (1159/90) v35.                                  (2)

No positive 7 block is bounded by an independently optimized residue
layout. The complementary e7=0 blocks are bounded by the original c/b
profile and the common-density cylinders (1).

<a id="exact-e70-profile-sum-and-six-inequalities"></a>
#### Exact e7=0 profile sum and six inequalities

Use the original exact profile cutoffs (2,1,0,0). In a cell label
(s3,s5,s7,s11), values 3,2,1,1 denote the respective positive tail beyond
those cutoffs. The following ten cells use (1) with the displayed
projection support; the other e7=0 cells retain their old profile bound.

| Cell | Projection support |
|---|---|
| (0,0,0,1) | {11} |
| (0,1,0,0) | {5} |
| (0,1,0,1) | {5,11} |
| (0,2,0,0) | {5} |
| (0,2,0,1) | {5,11} |
| (2,0,0,1) | {3,11} |
| (3,0,0,0) | {3} |
| (3,0,0,1) | {3,11} |
| (3,2,0,0) | {3,5} |
| (3,2,0,1) | {3,5,11} |

Each chosen support contains every coordinate in that cell's tail, so its
tail factors exactly. Use

    sum_{e>L} (2e+1)p^(-e)
      = ((2L+3)(p-1)+2)/(p^L(p-1)^2).

The other cells, together with the unit term, sum to 332692/7955. Adding
(2) gives the affine head bound C+L, where C=332692/7955 and

    L = (704/6075)t + (1159/90)v35 + (56/135)v37
        + (32/45)v57 + (44/135)v711 + (16/45)v357
        + (7/6)v3711 + (8/9)v5711.                    (3)

The following six valid inequalities have the stated nonnegative
multipliers:

| Inequality, left side <= right side | Multiplier |
|---|---:|
| (4/7)v35-v357 <= 0 | 2135/108 |
| v57-v357-(3/5)t <= 0 | 1/54 |
| v35+v37+v57-v357-(31/15)t <= 0 | 56/135 |
| (1591/3240)v357 <= 1 | 66606/1591 |
| v35+v57+v3711-(97/45)t <= 1 | 5/18 |
| v35+v3711+v5711-(19/9)t <= 1 | 8/9 |

The first and fourth are the proved prime-adjoining inequalities. The
second uses the missing supports involving 3 in {3,5,7}, of budget 3/5.
The third unions all three pair events, leaving exact support {3,5,7},
whose budget is 1/15. The fifth uses C={{3,5},{5,7},{3,7,11}}, whose
uncovered supports have total budget 7/45. The sixth uses
C={{3,5},{3,7,11},{5,7,11}}, leaving total budget 1/9. Thus every row
follows from the stated common-law union bound or prime-adjoining bound.

The weighted sum of these six left sides differs from L only by

    (21017/6075)t + (44/135)v711.

Both variables are at most 8505/1591, and both coefficients are positive.
The six weighted right sides sum to 66606/1591+7/6. Consequently

    Gamma(mu_S)
      <= 332692/7955 + 66606/1591 + 7/6
         + (21017/6075+44/135)(8505/1591)
       = 5015891/47730.

The finite/tail cells cover all exponent heights. For finite periods,
absent blocks are simply zero and all added bounds are nonnegative.

<a id="exact-verification-and-continuation"></a>
#### Exact verification and continuation

[The common-density verifier](../verify_common_density_head.py)
and its [fixed certificate](../certificates/common_density_head_certificate.json)
independently reconstruct the original
profile, the ten cell choices, all tail sums, and the six-row rational
identity. Ordinary Python and Python -O both exit 0. It also verifies the
fixed prime-67/71/73 continuation, giving

    F73 = 18990969219984662521362/138335257526567659561
        = 137.2822052710416... < 138877/1000.

The fixed certificate records the ten selected density cells, thirteen remaining
profile cells, six nonnegative density-row multipliers, and two positive
variable-bound corrections. Its six density rows plus ten selected
cylinder inequalities are the sixteen used dual rows; no omitted solver
state is needed to check the result. No Lean kernel certification is
claimed for this mathematical proof.

<a id="shared-cofactor-refinement-of-the-four-prime-head-p2"></a>
### Shared-cofactor refinement of the four-prime head (P2)

For a finite distinct-modulus residue family supported on {3,5,7,11}, use
its actual product of pure-prime survivor laws P. Let lambda_A be the
P-probability of avoiding all mixed forbidden classes supported on A,
t=1/lambda_35711, and v_A=lambda_A/lambda_35711. All densities and layout
moments below concern this same family. The analytical two-prime input is
the uniform complete-survivor layout theorem Gamma_35 <= 55/4.

The common-density argument and its original cylinder profile give

    Gamma_35711 <= C + L,        C = 332692/7955,
    L = (704/6075)t + (671/54)v35 + (56/135)v37
        + (32/45)v57 + (44/135)v711 + (16/45)v357
        + (7/6)v3711 + (8/9)v5711.

Indeed, the blocks of positive 7-lcm exponent contribute at most

    (55/4) v35 (2/3)(61/45) = (671/54)v35.

The zero-7-lcm blocks use the common-density cylinder proof's ten
complement-density cells and thirteen remaining original-profile cells,
with the unit term counted separately. Their exact infinite tail sums
are unchanged. The proof of the positive-7 bound integrates the outside
cylinders first and then applies Cauchy--Schwarz to the two complete
{3,5} test layouts under the same mu35.

Use the following six inequalities with nonnegative multipliers:

| Left side <= right side | Multiplier |
|---|---:|
| (4/7)v35-v357 <= 0 | 854/45 |
| v57-v357-(3/5)t <= 0 | 1/54 |
| v35+v37+v57-v357-(31/15)t <= 0 | 56/135 |
| (1591/3240)v357 <= 1 | 64044/1591 |
| v35+v57+v3711-(97/45)t <= 1 | 5/18 |
| v35+v3711+v5711-(19/9)t <= 1 | 8/9 |

The first and fourth rows are the same-law prime-adjoining inequalities;
the others are actual forbidden-union bounds. Their weighted sum has
right side 64044/1591+7/6. Subtracting their weighted left sides from L
leaves exactly

    (21017/6075)t + (44/135)v711.

Both variables lie in [0,8505/1591]. Therefore

    Gamma_35711
      <= 332692/7955 + 64044/1591 + 7/6
         + (21017/6075+44/135)(8505/1591)
       = 4939031/47730 = 103.4785459878483... .

The exact decrease from the 57/4-input certificate is 2562/1591. The
changed coefficients satisfy the two direct identities

    (2135/108-854/45)(4/7) = 1159/90-671/54,
    (66606/1591-64044/1591)(1591/3240) = 2135/108-854/45,

so this refinement introduces no new density inequality.

The fixed recurrence

    F_next = F (1+(3p-1)/((p-1)^2(1-delta)))
                 / (1-F/(4 delta (1-delta)(p-1)^2))

has the following exact continuation, starting at F=4939031/47730:

| p | delta | Positive survival denominator | Output F |
|---:|---:|---:|---:|
| 67 | 1/4 | 150994879/155933910 | 17123620477/150994879 |
| 71 | 53/200 | 55931291964461/57643654012161 | 6921898229038187/55931291964461 |
| 73 | 27/100 | 138545600701541742901/142871787094690609776 | 18699964911029778700842/138545600701541742901 |

The final value is 134.973357626228... < 138877/1000, with positive margin

    540832477598233928020177/138545600701541742901000.

[The coupled-head verifier](../verify_common_density_head_coupled.py)
and its [fixed certificate](../certificates/common_density_head_coupled_certificate.json)
reconstruct the entire original profile, finite/tail cells, six-row
certificate and this continuation using exact standard-library rational
arithmetic. Normal, optimized (-O), and isolated (-I) invocations all
exit 0. These checks certify the arithmetic implication of the stated
analytical inputs; no Lean kernel certification is claimed.
