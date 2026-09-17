[Index](../marked_head_profile.md) · [Previous](07-a-common-weighted-low-layout-and-a-nonnegative-tail-correction.md) · [Next](09-fixed-convex-potentials-for-the-actual-cap-charge.md)

<a id="all-integer-schedules-through23-for-the-fixed-scalar-feature-map"></a>
### All integer schedules through23 for the fixed scalar feature map

Fix the probability law and exact mean, square and hinge bounds in
`saturated_convex_profile_certificate.json`, SHA-256
82b5211366625c3c9eed79d8124db700f7b24bd7a43f088d9b4487492c32d940.
The numerical statement below concerns the SH27--SH28 upper-certificate
functional built from these data. It does not lower-bound actual covering
probabilities or refute the existence of better supported laws.

For each p in 11,13,17,19,23 allow every integer 1<=T_p<=p-2. There are
9*11*15*17*21=530145 schedules. Put d=p-1-T, c=(p-1)/d,
a=(3p-1)/(p-1)^2 and k=1+ac. Every listed choice has d>=1,c<=p, so the
normalized full-history AP kernel and its auxiliary law exist.

<a id="the-exact-scalar-feature-map"></a>
#### The exact scalar feature map

Use the source's refined hinge2, H1=M-1, and its stated H3,H4,H5,H6,H8,
H10,H12. Put H7=(H6+H8)/2, H9=(H8+H10)/2, H11=(H10+H12)/2 and
Hj=H12 for 13<=j<=21. These are respectively convex interpolation and
monotonicity of the actual hinge transform. No separate law, uniform
comparator, altered source threshold or empirical fit is substituted.

Let w_n=Pr(N=n), n<22, and E=E N be the complete auxiliary mean for the
chosen earlier prime kernels. For 1<=n<T define

    r_(p,T,n)=n*H(T/n)-n*M+T>=0,

where H(T/n) is interpolation between its two adjacent integer knots.
For the charge hinge this is the exact positive-part representation on
integer initial test loads, with each hinge expectation then replaced
by its specified upper bound. The scalar charge coefficient is

    u_(p,T)=[M E-T+sum_(n<T)w_n r_(p,T,n)]/d.           (SO1)

For the non-charge part of SH27 put

    g(j)=a[(p-1)/(p-1-min(nj,T))-c], K=ceil(T/n),
    v_(p,T,n)=g(1)+(g(2)-g(1))(M-1)
             +sum_(j=2)^K[g(j+1)-2g(j)+g(j-1)]Hj.

It vanishes for n>=T. This is an affine-intercept calculation, not a
claim that the possibly nonconvex g has this expectation bound by itself.
The final SH27 combined cost has nonnegative feature coefficients under
its stated final-W condition. Define v_(p,T)=sum_(n<T)w_n v_(p,T,n).

Starting with B=0 and Z=G, update

    B_new=B+u_(p,T),       Z_new=k Z+v_(p,T).            (SO2)

The final SH28 certificate is exactly

    cert(W)-W=(Z-1)+(B-1)W.                            (SO3)

The multiplication in (SO2) accounts for all future square multipliers
on the earlier cost intercepts. The replay independently checks its
11/T4,13/T5 rational slope and intercept against the published SH29
fields, so the enumerated functional matches that published consumer.

The auxiliary update is exact divisor convolution:

    Pr(F=1)=1-c/p, Pr(F=f)=c(p-1)p^(-f) for f>=2,
    w'_n=sum_(m|n)w_m Pr(F=n/m), E'=E(1+1/d).          (SO4)

All divisors of n<22 are themselves below22. Higher states cannot
return to the stored range because F>=1. Their contribution to (SO1)
is exactly the affine full-mean term, and their contribution to v is
zero. No auxiliary mean or high-state contribution is truncated.

<a id="directed-integer-bounds"></a>
#### Directed integer bounds

Let S=10^18. All grid integers represent their value divided by S.
The verifier keeps lower and upper bounds on each low probability,
a lower complete mean, a lower accumulated B and a lower accumulated Z.
Initial lower constants are floor(SM),floor(SG); probability and mean
start exactly at one.

The fixed r values are nonnegative and rounded downward. In (SO1), use
the lower mean, lower probability and lower r in every positive product,
round every division downward, and subtract the exact integer T*S.
The result is a lower bound on the exact scalar certificate coefficient.
Taking max(0,lower) remains valid because that exact coefficient is
nonnegative. Adding these step lower bounds bounds B downward.

For the intercepts v_n, round each exact rational down. If this rounded
value is negative, multiply by the UPPER probability; otherwise multiply
by the LOWER probability. Floor each product after dividing by S. In
either case the result is <=w_n*v_n. Multiplying the previous lower Z
by the exact positive k and flooring, then adding these signed lower
products, bounds the new Z downward.

Convolution uses exact rational factor probabilities. Sum floor(w^-*Pr)
for each lower output and ceil(w^+*Pr) for each upper output. The full
mean update uses floor(E^-*(d+1)/d). These preserve the intervals by
induction, including all negative-intercept signs. They are bounds on
the exact certificate functional, not bounds on the actual physical
law's unknown charge or deficits.

<a id="finite-conclusion"></a>
#### Finite conclusion

The verifier visits exactly 9,99,1485,25245,530145 prefixes at the five
successive depths, with no pruning. Across every terminal schedule it
finds the uniform lower bounds

    B >=515109547377609039/500000000000000000 >103/100,
    Z-1>=10102503029019284371/100000000000000000 >101.

The grid-bound minimizers occur at thresholds (4,4,8,8,12) and
(1,1,1,1,1), respectively. They need not be the same schedule: both
lower bounds hold for every schedule, so they may be combined to give

    cert(W)-W >101+(3/100)W>0 for every W>0.

Consequently none of these 530145 schedules can satisfy SH28 using this
specific scalar feature upper bound. This is stronger than failing one
chosen W or one greedy policy. It remains a bounded numerical strategy
obstruction, not an impossibility theorem for SH28 with sharper whole
costs, other initial laws, noninteger thresholds, or different blocks.

<a id="the-missing-observation"></a>
#### The missing observation

The existing feature map takes separate maxima for M and each H_j, and
then another separate maximum for every auxiliary N. A next observation
that preserves original labels is

    F_mu(g_(p,b)),
    g_(p,b)(z)=E[1_(b<=K) h_p(Nz)/N],

where b is one fixed original earlier-prime exponent label. Its head
test cannot vary with N. The conditional comparison/Jensen step gives
the sum of these support functions; the current scalar map replaces
them by sums of independent feature maxima. The zero original label is
always active and is the cheapest initial query. The existing FL1--FL4
label-retention calculation supplies the finite-observation bookkeeping;
it must be evaluated on the same SH18 probability, including its actual
higher357 conditioning. Another possible new observation is the joint
weighted pair deficit E[(c_p-c_actual)A_e A_f], whose present proof only
uses A_e A_f>=1. Neither missing value is determined by the listed
separate scalar upper bounds.

The adjacent `verify_combined_schedule_obstruction.py` reconstructs
`combined_schedule_obstruction_certificate.json` using only the Python
standard library. Run it with `python3 -I -O`; the source profile is a
hash-bound prerequisite. All 530145 schedules are visited without
pruning. Directed-grid arithmetic bounds exact rational expressions;
it does not rely on floating optimization or a solver. This result
is an experimental strategy obstruction with the ordinary derivation
(SO1)--(SO4), not a new Lean declaration.

<a id="higher-hinge-observations-on-the-same-supported-law"></a>
### Higher hinge observations on the same supported law

Keep exactly the (SH18) probability, original-label comparison, 270-depth
box and same-law survival denominator. Applying (SH20)--(SH21) at the
nine further integer thresholds gives the following simultaneous bounds;
the displayed decimals are rounded upward.

| t | H_nu(t) upper bound |
|---:|---:|
|13|0.189271|
|14|0.161741|
|15|0.135712|
|16|0.112043|
|17|0.095693|
|18|0.079571|
|19|0.069949|
|20|0.060411|
|21|0.053283|

Each finite-box numerator maximizes over all 280-by-280 base layouts,
with both singleton45 labels restored exactly by (SH21). The entire
outside box is included through t*V_out/(4t^2-1), then divided by the
same positive q_* as in (SH20). No original high exponent is truncated
and no new supported probability is chosen.

These values improve the preceding monotonicity bound H_nu(t)<=H_nu(12)
for every listed threshold. Replace those nine constant extensions in
the existing (SH27) scalar feature map, keeping all its other features
and the integer schedule domain unchanged. The complete directed
enumeration again checks all 530145 threshold schedules through23 and
obtains the same uniform bounds

    B>=515109547377609039/500000000000000000>103/100,
    Z-1>=10102503029019284371/100000000000000000>101.

Hence its combined certificate still satisfies
cert(W)-W=(Z-1)+(B-1)W>101+(3/100)W for every W>0. Improving the flat hinge
extension by these nine same-law observations does not remove this
bounded strategy obstruction. This does not exclude sharper joint
costs, further improvements of the individual hinge bounds, another
initial probability, noninteger thresholds or a different prime block.

The separate `saturated_high_hinges_certificate.json` binds both prior
certificates by their hashes and retains all 2430 new integer maxima,
the complete geometric remainders and the enhanced schedule replay.
Three of those maxima are independently checked without (SH21), using
all 4480^2 ordered full-layout pairs at each selected depth/threshold:
(2,1,1)/13, (3,0,2)/17 and (8,5,4)/21. Their exact weighted numerators
are 79299012, 80659542 and 1403702325, respectively. The existing
low-law normalization supplies their common denominator.

Run `python3 -I -O docs/reports/erdos7-odd-covering/verify_saturated_high_hinges.py`.
The verifier reuses the current convex-query and directed-schedule
implementations, checks the three dense independent calculations, and
compares every computed certificate field. NumPy is required only for
the finite convex observations and the dense checks. These are ordinary
all-height estimates with exact numerical verification, not a new Lean
endpoint or a solution of unrestricted #7.

<a id="whole-convex-costs-with-one-fixed-original-exponent-label"></a>
### Whole convex costs with one fixed original exponent label

Retain exactly the77-point carrier, nonuniform low probability, uniform
higher-digit lift and actual conditioning event of(SH18). The full original
3/5/7 heights remain arbitrary finite ones. Let nu be that same probability,
q0=2577991831/4799999616 its established conditioning denominator, and

    M=19618622895502373704/3964266656997890625=2+H2,
    G=2512626164927510733601/70505216618162484375.

These bound every complete old test on one fixed nu. The actual11/13
kernels, full physical periods, original labels and parameters are those
of(SH25): T11=4,T13=5,delta11=1/3,delta13=4/11. In particular no new
probability is chosen to optimize a separate cost. Set W=3049/20 and use
the complete increasing convex costs h_p of(SH27), with f11=61/42,f13=1.

<a id="conditioning-a-complete-cost"></a>
#### Conditioning a complete cost

For any increasing convex h, put g(l)=(h(l)-h(2))_+. Since
h(l)<=h(2)+g(l), the unchanged actual conditioned law obeys

    max_L E_nu h(L) <= h(2)+[max_L E_lambda g(L)]/q0.

Only the nonnegative cut cost is divided by the lower denominator. The
constant h(2), which may be negative, is retained exactly once.
Use(SH19)--(SH21) to bound the entire g on one weighted low layout at each
auxiliary depth, before taking its maximum. This retains the relations
between all slopes and hinges of h.

The same270-depth box as(SH18) suffices. Let beta be its probability and

    Eout=U_B-sum_(z in box)Pr(z)F_square(z)-(1-beta).

For any a>=sup_(integer k>=2)g(k)/(k^2-1), the complete omitted contribution
is at most a Eout. Hence, if V_g(z) is the exact maximum of the whole
low cost at depth z,

    max_L E_nu h(L)
      <=h(2)+[sum_(z in box)Pr(z)V_g(z)+a Eout]/q0.

This does not truncate the original heights or the auxiliary tail.
For the costs below, g is affine from a known integer k0 onward, with
g(k)=A k-B and2A<=B<=k0 A. The ratio to k^2-1 is decreasing for real
k>=2k0, since its derivative numerator is at most
-A k(k-2k0)-A<0. A finite integer scan therefore computes the global
quadratic coefficient exactly.

<a id="an-original-zero-label-across-every-auxiliary-outcome"></a>
#### An original zero label across every auxiliary outcome

At the13 step write N=1+K11. Its full comparison distribution satisfies

    Pr(N=1)=28/33,
    Pr(N=n)=50/(3*11^n) for n>=2,
    E N=7/6.

The old11 exponent label zero is active in every outcome. Its completed
head test at each current13 depth is fixed before N is sampled. The
original-label Jensen comparison from(FL1)--(FL4) and(SH27) assigns weight
1/N to each of the N active old exponent labels. Thus, for any simultaneous
upper bounds B_n>=max_L E_nu h13(nL), the zero label may be collected first:

    cost13 <= max_L E_nu g0(L)
                 +E[(1-1/N)B_N],
    g0(l)=E[h13(Nl)/N].

The current13-depth weights sum to one. Their zero-label tests may differ
with that depth; the supremum of the same g0 bounds their weighted average.
This argument does not interchange an unrestricted expectation and maximum.

For n>=5, h13(nl)=W(nl-5)/7 for every integer l>=1. Put p_n=Pr(N=n),
Ptail=Pr(N>=5)=5/43923 and Etail=E[N;N>=5]=17/29282, and define

    gtilde(l)=sum_(n=1..4)(p_n/n)h13(nl)+(W/7)Ptail*l.

The omitted constant in g0 is -(5W/7)E[1/N;N>=5]. It cancels exactly
against the same constant from the other original labels. Therefore

    cost13 <= max_L E_nu gtilde(L)
      +sum_(n=1..4)p_n(1-1/n)B_n
      +(W/7)[M(Etail-Ptail)-5Ptail].

Every coefficient multiplying an unknown moment or test cost is
nonnegative. The remaining negative constant is exact; no reciprocal
moment approximation or omitted multiplier mass is used.

The n=1 residual coefficient is zero. Bound B2 by the complete-cost
calculation above. For n=3,4, h13(nl) is increasing and affine from l=2
onward, so for every integer l>=1,

    h13(nl)<=h13(2n)+(Wn/7)(l-2)_+.

Consequently B_n=W(nM-5)/7 is valid using M=2+H2. These bounds continue
to concern the same nu. At11 there is no old-tail multiplier, so its
entire cost is bounded directly by the whole h11 calculation.

<a id="exact-consumer"></a>
#### Exact consumer

The three complete costs are h11(l),h13(2l),gtilde(l). Their cut costs
have exact common denominators17640,1680,5488560, respectively. No
quantization is needed. The singleton45 elimination evaluates all810
new depth-cost maxima over280^2 base-layout pairs per query. Its convex
increment identity bounds every intermediate nonnegative sum by an
attainable or dominated complete cost, so the integer range is at most
D times the largest point cost. The largest certified range is
5467332906913332456, below2^63.

The resulting complete13 cost is

    4078973908904062879587704261867
      /108352191282098927867550000000.

Together with the complete11 cost, J=(1403/630)G and the unchanged
criterion(SH28), the exact positive margin is

    W-[J-1+cost11+cost13]
      =44282704320696511600648227253
         /108352191282098927867550000000 >0.

Write C=J-1+cost11+cost13. The computed margin gives 0<C<W, and for
every final complete test the proof of(SH28) gives

    E L^2-1+W B<=C.

Since B>=0 and C<=W, this also gives E L^2-1+C B<=C. Applying the
universal square floor and final conditioning as in(SH28) yields

    Gamma<=1+C=16582361047917383969674899272747
                 /108352191282098927867550000000
               <153.041308.                            (SH30)

The convex costs are still evaluated at W=3049/20; no convexity claim
at C or new kernel is needed. In particular the original target
Gamma<=3069/20=153.45 also holds. No independent scalar charge premise
is required. The old low-geometry hypothesis and all original3/5/7/11/13
physical heights remain as in(SH25). This supplies another exact head
input for later primes; it does not prove an unrestricted tail continuation.

`verify_saturated_whole_cost.py` replays the separate
`saturated_whole_cost_certificate.json`. The existing(SH18) and(SH24)
certificates are hash-bound prerequisites. This new replay owns only the
810 whole-cost observations, exact tables, full geometric and multiplier
tails, and the strict final criterion. Run it with `python3 -I -O`.
All conclusions here are ordinary mathematics with exact arithmetic,
not new Lean declarations or a solution of unrestricted#7.

<a id="actual-seven-digit-positions-at-arbitrary357-heights"></a>
### Actual seven-digit positions at arbitrary357 heights

Fix the following eleven distinct low forbidden modulus/residue pairs:

```
(3,0), (9,4), (5,0), (15,11), (45,37), (7,0),
(21,8), (35,9), (63,59), (105,74), (315,89).
```

Their actual complement Ω in Z/315Z has75points. The certificate lists these points in increasing order and assigns each a nonnegative integer weight with total N=1000000007. Let μ be this probability law. No deleted point is filled, no digit is moved, and the weights need not be constant within an old45 fibre.

For arbitrary finite nonnegative n3,n5,n7, lift μ independently and uniformly in the additional prime-power digits to period Q=3^(2+n3)5^(1+n5)7^(1+n7). Call this law λ. Above the eleven fixed low classes, allow any forbidden family with at most one original residue class for each distinct divisor of Q that does not divide315. Let F be the complement of precisely these actual higher forbidden classes. The conclusion concerns ν=λ(.|F). It does not assume that ν has unchanged low marginals or is an ambient uniform law.

When this law is used before additional primes, Q includes the full
3/5/7 part of the original common period, including heights appearing
only in moduli with later prime factors.

For a complete test family consisting of one arbitrary class C_m modulo every divisor m of Q, including C_1=the whole space, write L=Σ_(m|Q)1_Cm. The certificate and the argument below give

    sup_test E_ν L² ≤ 105976769844774468812903/2920804491373837228125
                    < 3849/106.                         (PG1)

This is a result for the specified low family; it does not assert a bound for every other low315 configuration or settle unrestricted Erdős #7. All-height validity follows from the analytic estimates below. The finite verifier recomputes their coefficients and the two low geometry bounds.

<a id="saturated-common-layout-reduction-and-the-full-geometric-tail"></a>
#### Saturated common-layout reduction and the full geometric tail

Put h=(2,1,1). Each original exponent vector a has the unique saturated projection d=Π_p p^min(a_p,h_p), together with its extra exponents a_p−h_p where these are positive. These extra exponents remain part of the original modulus label. Equal projected d never identify different original moduli.

Let Z3,Z5,Z7 be independent auxiliary geometric variables with

    Pr(Z_p=k)=(p−1)/p^(k+1),  k≥0.

For d|315 set w_d(z)=Π_(p:v_p(d)=h_p)(1+z_p). Define the genuine low-layout maximum

    F_μ(z)=max_(one cylinder C_d modulo each d|315)
                E_μ (Σ_d w_d(z)1_Cd)².

The standard saturated-prefix argument gives E_λL²≤E_Z F_μ(Z). Indeed, conditionally on the low point, higher-prefix intersections are bounded by nested-prefix intersections p^−max(e,f); centering the added coordinates realizes this dominating kernel. At a fixed geometric height, the projected cylinders belonging to one d average to a point of their convex hull. Convexity of the square bounds that average by an extreme layout with one cylinder per d. Finite physical heights are truncated versions; completing labels and auxiliary heights only increases these nonnegative bounds. This centering is solely a moment bound under λ and does not alter the actual deletion event F.

Let m_d=max_a μ(a mod d) and P(z)=Σ_(d,e|315)w_d(z)w_e(z)m_lcm(d,e). For each fixed low layout, its weighted-square increment from z=0 is at most P(z)−P(0), because every weight product increment is nonnegative and μ(C_d∩C_e)≤m_lcm(d,e). Therefore

    F_μ(z) ≤ F_μ(0)+P(z)−P(0).

Let H(z) be any valid upper bound for F_μ(z), let B=[0,8]×[0,5]×[0,4], and let β=Pr(Z∈B). Using H inside B and H(0) outside gives

    E_λL² ≤ U_B
      := (1−β)H(0)+Σ_(z∈B)Pr(Z=z)H(z)+Σ_d η_out(d)m_d.

Here η_out(d) is the coefficient of m_d in E[1_(Z∉B)(P(Z)−P(0))]. All coefficients are nonnegative. The full expectation of each pair weight product is the product of the one-prime factors1 (neither exponent saturated), p/(p−1) (exactly one saturated), and p(p+1)/(p−1)² (both saturated). Subtract1 and subtract the finite-box contribution to obtain η_out exactly. No tail is discarded. In particular, this argument does not require P(0)−H(0)≥0 or monotonicity of a relaxed deficit.

<a id="pure7-anchored-upper-bound"></a>
#### Pure7 anchored upper bound

Identify Ω with its actual pairs (x,y), where x is an old45 point and y∈{1,…,6} its7digit. Write R_x=Σ_y μ_(x,y) and v_x=max_y μ_(x,y). Put C=(1,3,5,9,15,45), b=(1,1,1+z5,1+z3,1+z5,(1+z3)(1+z5)), and u=1+z7.

Let A and B range independently over all complete old45 layouts with weights b, including their unit labels. Then a valid upper bound is

    H_pure7(z)=max_(A,B,j) Σ_x [
        R_x A_x²
        +v_x(2u A_x(B_x−1)+u²(B_x−1)²)
        +μ_(x,j)(2u A_x+u²(2B_x−1)) ].

To prove it, fix a genuine low315 layout. Its non-seven part is A. Keep the actual global digit j of its pure7 label. Let B−1 be the sum of the other five high-label old cylinders. Bound every low/high term not using the pure7 label, and every high/high term not using it, by the fibre maximum v_x. Terms involving the pure7 label have mass at most μ_(x,j). Expanding the square gives the displayed expression. Maximizing over actual old layouts preserves validity.

There are4480 complete old layouts and280 after omitting the45singleton. Let s=(1+z3)(1+z5). For fixed base A,B and j, adding s at singleton rows i,k gives an A-only gain a_i, B-only gain b_k, and an additional nonnegative cross gain2u v_i s² only when i=k. Hence the exact best singleton gain is

    max(max_i a_i+max_k b_k, max_i(a_i+b_i+2u v_i s²)).

If the independent maxima occur at the same row, the coincident term dominates them; if they occur at different rows, the independent sum is realized. This explains the verifier's280² base-pair calculation without losing any of the4480² full-layout maxima. The six digits used are the actual surviving digits; the excluded digit0 has zero mass and cannot improve a nonnegative maximum.

<a id="fixed-low-layout-digit-partition-upper-bound"></a>
#### Fixed-low-layout digit partition upper bound

Keep a single complete old low layout A and write its load as a_A(x). For each high label7e, e∈C, and actual digit y define

    R_e^A(y)=max_(old cylinder D modulo e)
        Σ_(x∈D) μ_(x,y)[u²b_e²+2ub_e a_A(x)],

    M_(c,y)=max_(old cylinder D modulo c) Σ_(x∈D) μ_(x,y),

    J_(e,f)(y)=2u²b_e b_f M_(lcm(e,f),y),   e<f.

The diagonal and all cross terms with the common low A use one common old cylinder inside R_e^A(y). For two high labels on the same digit, their old intersection is empty or a cylinder modulo their lcm, so J bounds their pair contribution. Labels on different digits have zero intersection. Only this high/high old-cylinder compatibility is relaxed.

For a subset T of the six high labels put

    H_y^A(T)=Σ_(e∈T)R_e^A(y)+Σ_(e<f in T)J_(e,f)(y).

Partition the six labels among the six surviving digits. The subset recurrence

    D_y(S)=max_(T⊆S)[D_(y−1)(S\T)+H_y^A(T)]

computes the exact maximum of this relaxation. Initialize D_1(S)=H_1^A(S), and permit empty subsets at all digits. Digit0 has no mass; assigning a label from it to a surviving digit cannot decrease the relaxed nonnegative objective. Thus

    H_DP(z)=max_A [Σ_(x,y)μ_(x,y)a_A(x)² + D_6(C)]

is a valid upper bound for F_μ(z). The verifier evaluates all4480 A with64 subset states. The employed bound is H(z)=min(H_pure7(z),H_DP(z)) at the one fixed law μ. This minimum is a pointwise upper bound; no convexity or optimization property is claimed for the minimum.

<a id="actual-grouped-deletion-bound-for-the-same-law"></a>
#### Actual grouped deletion bound for the same law

Use the selected one-extra-prime blocks

    E3={9,45}, E5={5,15,45,35}, E7={7,21,35,63,105,315}.

For p∈{3,5,7}, the block with low projection d∈Ep includes the original moduli d p^e, e≥1. The summed conditional prefix mass is α_p=1/(p−1). The three selected blocks use independent added prime coordinates conditionally on the low point. Their true union is bounded by the maximum over their low cylinders of

    G_group(μ)=max E_μ[1−Π_p(1−α_p A_p)],

where A_p is the count of the selected low cylinders for p. The bounds |E3|≤2, |E5|≤4, |E7|≤6 ensure that each factor is nonnegative. For the original labels at different e, take their geometric convex averages, padding absent exponents by zero. The displayed expression is affine separately in each such average and increasing in each group count within these ranges. Maximizing selects one low cylinder for each projected label, which proves this upper bound without merging original labels or changing F.

Set γ_d=Π_(p:v_p(d)=h_p)p/(p−1)−1 and ρ_d=γ_d−Σ_(p:d∈Ep)α_p. All ρ_d are nonnegative. Every unselected original higher label is bounded by the ordinary union bound, giving

    λ(F) ≥ q := 1−G_group(μ)−Σ_d ρ_d m_d.

The verifier maximizes G_group exactly on the actual75points. To describe its elimination, write A for the two E3 indicators, B for the three old E5 indicators at5,15,45, I for the extra35indicator, and C for the six E7 indicators. The pointwise numerator of the union with denominator48 is

    24A+12B−6AB+6(2−A)I+(2−A)(4−B−I)C.

For each A,B,I choice the six E7 cylinders maximize independently, since their coefficients are nonnegative. The verifier enumerates all A,B,I choices, computes these six maxima, and independently checks the final witness against the product-union formula point by point. All caps and this union maximum use the same integer weights as both numerator bounds.

<a id="exact-values-and-conditioning"></a>
#### Exact values and conditioning

The standalone verifier reproduces

    q = 25428074957/48000000336 > 0,
    U_B = 54284750870997693017389/2756768194297377225000.

Since C_1 is the whole space, L≥1. Thus L²−1≥0, and conditioning the actual higher surviving event gives

    E_ν L² ≤ 1+(E_λ L²−1)/λ(F) ≤ 1+(U_B−1)/q
            = 105976769844774468812903/2920804491373837228125.

Its difference below3849/106 is the positive rational

    8638883751805796885407/309605276085626746181250.

`verify_point_geometry.py` reads `point_geometry_certificate.json`, reconstructs the actual carrier, checks all weights and arithmetic bounds, recomputes both integer geometry maxima at every one of270depths, recomputes all actual cylinder caps and the grouped union maximum, and performs the geometric-tail and final comparisons with exact rational arithmetic. The largest common bound on intermediate square sums is213444001494108, below2^63. The verifier needs Python3 and NumPy; it imports no optimizer or scratch module. This is a finite computational certificate combined with the ordinary all-height proof above, not a Lean kernel verification.

<a id="complete-low315-carrier-classification-for-actual-digit-bounds"></a>
### Complete low315 carrier classification for actual digit bounds

Fix one of the six existing canonical old45 survivor sets S. The fixed old forbidden classes are modulo3,9,5,15,45. The pure7 forbidden digit is normalized to0. The five mixed labels are7d with d=(3,5,9,15,45), with one class per original modulus. Missing or low-redundant labels may be represented by a class on digit0. This note classifies their low surviving carriers. It does not evaluate the new moment bound on all carriers, prove a universal numerical target, or replace the existing justification for reducing old45 families to these six shapes.

<a id="labelled-digits203-patterns-with-the-pure-digit-distinguished"></a>
#### Labelled digits:203 patterns, with the pure digit distinguished

Fix the five old residue choices a_d modulo d. Each mixed label chooses a digit t_d∈Z/7Z independently by CRT. Include the distinguished pure label with t_0=0. Two such assignments are equivalent under one common permutation of the six nonzero7digits if and only if the six labelled objects {0,3,5,9,15,45} have the same equality partition by their digit.

The forward direction preserves equality and the zero block. Conversely, map the nonzero digits attached to corresponding blocks to one another, then extend the resulting partial bijection to the unused nonzero digits. Since there are only five mixed labels, no partition needs more than six total blocks. Every partition of six labelled objects is realizable. Therefore the exact labelled digit-orbit count is Bell(6)=203, not203 entire carrier cases on S.

The numbers of patterns with k=1,…,6 total blocks are1,31,90,65,15,1. A pattern with k blocks has6!/(7−k)! concrete digit assignments when t_0=0. Their sum is7^5=16807. The classifier independently normalizes all16807 tuples and recovers precisely the203 restricted-growth strings.

If all mixed digits are required nonzero, the pure label is a singleton and the count becomes Bell(5)=52. The existing code uses52 partitions together with the option that each old cylinder is empty. Moving every label whose digit is0 into that empty-cylinder option gives the same low carrier. Conversely, an empty-cylinder label can be placed at digit0 with any old residue. Thus the current52-partition construction covers all actual low carriers, including pure-digit coincidences. It does not preserve the full description of redundant original labels, which is unnecessary when the only required input is their complement.

Before taking effects on S, the five old residue choices number3·5·9·15·45=91125. Hence a direct labelled enumeration at one fixed S has91125·203=18498375 digit orbits. Many have identical carrier effects. Replacing old residues by their distinct masks on S gives12960 old-mask choices for each17point shape and12240 for each16point shape. The resulting203-pattern products over six shapes contain15346800 entries; the equivalent52-plus-empty enumeration contains3931200 entries. These are labelled enumeration counts, not distinct carrier counts.

<a id="exact-carrier-state-and-what-the-deletion-vector-forgets"></a>
#### Exact carrier state and what the deletion vector forgets

For each surviving digit y∈{1,…,6}, let

    U_y = union of (S∩{x≡a_d mod d}) over labels whose t_d=y.

The carrier is exactly Ω={(x,y): x∈S\U_y, y∈{1,…,6}}. Represent it by the sorted multiset of its nonempty masks U_y; repeated masks retain their multiplicity. The number of omitted empty masks is6 minus the multiset length. At most five masks are nonempty, so there is a globally unused nonzero digit.

Two carriers on the same fixed S are equivalent under one common7digit permutation fixing0 if and only if their mask multisets are equal. One direction is immediate. For the other, match equal nonempty masks with their multiplicities and match the remaining empty masks; these matches define a single permutation of the six digits. This is a statement about carriers; different original labelled forbidden families may have the same carrier and need not be equivalent as labelled families.

The existing deletion vector is only

    b(x)=#{y:x∈U_y},    r(x)=6−b(x).

It forgets which old points are deleted together at a common digit. Its161375 states are therefore insufficient as the input to an arbitrary75point weighting or to an oracle retaining actual digit positions. The richer state above preserves exactly the information these methods need. It can be realized by assigning the sorted masks to digits1,…,k and treating the remaining digits as empty-deletion columns.

Completeness has a small successive-label recursion. Start with the empty multiset. For each of the five original labels, choose any of its old-cylinder masks, including the empty one. An empty mask leaves the state unchanged. A nonempty mask either occupies a fresh digit, appending that mask, or uses an existing digit, replacing one U by U∪C. Sort the resulting multiset and deduplicate. The inductive alternatives cover exactly every assignment of the labels seen so far. Since there are only five labels and six available nonzero digits, a fresh digit always exists when needed. The resulting states agree in count and projected b digest with the existing two-enumeration certificate.

<a id="allowed-common-crt-coordinate-maps"></a>
#### Allowed common CRT coordinate maps

A7digit permutation must be common to every old point x. Independent permutations in separate old45 fibres generally send a single cylinder modulo7d to a union of cylinders and are not allowed in this equivalence.

Every common permutation of the7roots fixing0 extends to every finite7power by permuting the first digit and leaving all later digits unchanged. It sends every prefix cylinder to a prefix cylinder of the same depth and preserves uniform suffix measure. Likewise, any old ternary rooted-tree permutation preserving the mod3 and mod9 cylinder families, and any common permutation of the five5roots, extends to arbitrary finite additional heights. Their coordinatewise CRT product preserves every original modulus label and sends its residue class to another single class of that same modulus. No primality label, projected cofactor label, or original high exponent is merged.

For the six normalized old carriers, the surviving mod9 rows are (1,7) in the short ternary root and (2,5,8) in the long root. The surviving mod5 columns are(1,2,3,4). Candidate old coordinate maps form

    S_{ {1,7} } × S_{ {2,5,8} } × S_{ {1,2,3,4} },

of size2!·3!·4!=288. Keep exactly those maps preserving S. They preserve each old cofactor-cylinder family d∈{3,5,9,15,45}; the classifier checks this for every map. The short and long roots cannot be interchanged in a map preserving S, because they have different numbers of surviving mod9 rows. The excluded root0 and deleted child4 carry no old points; the listed maps extend to the full rooted tree by fixing them. Thus these maps are allowed global coordinate changes, not arbitrary permutations of S.

Act with each such old map on every mask U_y, then sort the masks. The combined old-coordinate and common7digit quotient is complete for this stated group. Transport an actual law along the corresponding bijection of Ω, and extend the coordinate map to the additional physical digits. Every cylinder cap, all selected original deletion blocks, complete test-family moment, and resulting actual conditional law is transported coherently. Consequently one exact feasible certificate on each carrier orbit would suffice for this finite classification, provided its analytic all-height estimates are valid. Reusing a law after a coordinate map means pushing forward every point weight and every actual event together.

<a id="measured-classification"></a>
#### Measured classification

`verify_seven_digit_classification.py` regenerates the mask states by the successive-label recursion, verifies the exact existing b-set hashes, checks each old map preserves all five cylinder families, and enumerates the combined orbits. It performs no LP or moment sweep. The result file is `seven_digit_classification_certificate.json`. The only external input is the canonical adjacent `actual_deletion_profile_certificate.json`; the classifier reads its six old geometries, checks their exact original classes and complements, and binds the used input fields by SHA-256. It imports no other program, optimizer, or policy cache.

| Old45 shape | b vectors | Digit-union carriers | Old maps | Carrier orbits | b orbits |
|---|---:|---:|---:|---:|---:|
| root1, same root / other column |27679|165141|12|31833|5281|
| root1, other root / same column |28939|168517|24|15451|2829|
| root1, other root / other column |28735|168695|8|40281|7082|
| root2, same root / other column |25813|157010|8|36152|6063|
| root2, other root / same column |25238|152235|36|12692|2268|
| root2, other root / other column |24971|153997|12|34160|5718|
| Total |161375|965595| |170569|29241|

Some b vectors have 37 distinct digit-union states even before old-coordinate symmetries. The old-coordinate quotient leaves170569 exact carrier cases; it is the relevant complete finite domain for applying the new actual-point geometry language.

A concrete loss-of-information witness on the first17point shape is retained in the result: the same b has union multiset(66576,103278) and union multiset(8,65828,104018), where bit i refers to the listed ith old point. These use respectively two and three nonempty digit masks. No common digit permutation or old-coordinate bijection can change that number, so the carriers are inequivalent even under the combined allowed group, despite having exactly the same b.

<a id="what-a-complete-next-step-would-require"></a>
#### What a complete next step would require

Use a carrier representative, not one arbitrary realization of b. Expand its masks to the actual315points, choose and certify a law on that actual support, and evaluate the pure7 bound, fixed-low digit-partition bound, all caps, actual grouped deletion bound, and full geometric tail on that one law. Coordinate symmetries then transport the certificate to its orbit. Existing bounds that depend only on b can settle all richer states above a certified b without reevaluation; unresolved b states must retain the mask multiset before using the new digit-sensitive bounds.

The present result certifies the finite coverage and equivalence statement and the measured state counts. It does not show that all 170569 carrier orbits meet 3849/106.


<a id="reproduction-and-verification-boundary"></a>
#### Reproduction and verification boundary

Place the new classifier and result certificate beside the existing canonical `actual_deletion_profile_certificate.json`, then run:

```sh
python3 -I -O verify_seven_digit_classification.py
```

Alternatively pass the canonical input path through `--source-certificate` and the result path through `--check`. The program uses only the Python standard library, with unbounded integer arithmetic and explicit guards unaffected by optimization. It checks raw types on all consumed integer geometry fields, pins the six canonical shapes and their original old classes, reconstructs all carrier states, checks the old maps form a group preserving every cofactor-cylinder family, checks disjoint orbit coverage, and compares the complete deterministic result. It records hashes of all reconstructed state sets and orbit-representative sets without storing the large sets. It also verifies the displayed two-carrier witness and the exact203 digit-orbit sizes against all16807 digit tuples. The results are finite arithmetic certificates with the ordinary equivalence and all-height transport proofs above; no Lean kernel verification or universal numerical moment bound is claimed.
