# A common matching-polynomial source admits arbitrary edge endpoints

There is one positive complete continuation gate for every edge-endpoint
pattern under the following retained head conditions. The directed exact
bound is

    gamma=482417875025047259/65752554559609241600 > 7/1000.       (ME1)

This treats the endpoint-pattern frontier following Report617 without
enumerating its 1296*1540^4 endpoint configurations. Each edge's twelve
retained labels still share one pair of first roots, but different edges
incident to a prime may use different roots, including roots with different
star roles or unmarked roots. All central star and pair phases and all
permitted higher lifts remain arbitrary and fixed once globally.

The complete reference ten-prime head has Haar survivor mass

    (2673/138320) gamma
      =1289502979941951323307/9094893346685150298112000
      >1/7100.                                                (ME2)

The same source admits Report616's entire outside network, leaving
extendible head Haar mass greater than 1/11000. The larger arbitrary
three-parent network fee in Reports619/620 is not paid by this smaller
gate. The endpoint scope is wider than Report617; its mass margin is
smaller. These are ordinary proofs and exact finite arithmetic, not new
Lean verification or a resolution of unrestricted Erdos #7.

## 1. Exact family and retained restrictions

Keep Report617's reference head P0={3,5,7,11,13,17,19}, followed by
P1={23,29,31}. Original numerical moduli are pairwise distinct, and every
original phase is fixed once for the whole family. Pure3/pure5 originals
are a subset of the FA1 inventory

    2mod3, 7mod9, 4mod27, 13mod81, 40mod243, 121mod729;
    4mod5, 2mod25,

with no additional pure3/pure5 original. The central15 slot has phase0;
an absent slot may be imposed as an auxiliary deletion.

At each q in Q={7,11,13,17,19}, let f_q be its actual forbidden first
pure root, or an auxiliary forbidden root when that slot is absent.
Choose five live roots u_(q,1),...,u_(q,5), different from f_q;
these five roots may coincide.
The outside first roots of 3q,5q,15q,9q,25q are respectively these five
roots. The square stars 3q^2 and5q^2 have arbitrary lifts of u_(q,1) and
u_(q,2). All central components are arbitrary. Every higher pure-q
original is arbitrary at its own distinct numerical label and finite
height. Missing retained slots may be added as auxiliary deletions.

For each edge e={q,r}, its twelve retained labels are

    3^a5^b q^i r^j,
    (a,b) in{0,1}^2, (i,j) in{(1,1),(2,1),(1,2)}.

They all project to one endpoint root d_(q,r) at q and one endpoint root
d_(r,q) at r. These endpoint choices may differ between different edges
at q. Their higher outside lifts and central phases may differ arbitrarily
between labels. Endpoints may be any live roots. An endpoint equal to the
pure forbidden root makes its whole edge source-null; replacing that
edge by an auxiliary live-root rectangle is a valid sufficient reduction.
Different first roots among the twelve labels of one edge are NOT covered.

Every other mixed P0-original must have maximum exponent at least3,
central3/5 exponents at most1, or at least five prime divisors. The35
star and120 pair slots are retained once and removed from the remaining
loss inventory. Originals touching23,29 or31 are arbitrary. The complete
remaining-original L and weighted future-query W arrays are exactly the
published Report604 arrays also used by Report617, with no query labels
or heights removed. No arbitrary-ten-head prime transfer is asserted.

## 2. Construct one actual conditional survivor source

Use the actual root-balanced pure-q survivor law rho_q. Its live first
roots have equal mass r_q=1/(q-1), its square cylinders have mass at most
alpha_q=1/[q(q-2)], and all of its higher-prefix caps hold on this same
law. First fix the auxiliary star padding described in section3, and use
that same padded actual family throughout the source construction. At a
fixed central mod9/mod25 leaf, the union bound gives actual
star-survivor mass at least

    Z_q=1-r(R1+C1+P+L9+L25)
          -alpha[(1-R1)R2+(1-C1)C2].

The first five terms pay for the five linear-star root events. A square
event needs its own payment only when the corresponding linear star is
inactive, because its first root is the same. Collisions among the five
linear roots only make this union bound more conservative. Thin the whole
actual star survivor by one constant factor to mass Z_q, obtaining xi_q.
This is possible because Z_q is positive by the box bound below. It gives
xi_q<=rho_q, so every root has mass at most r_q and every higher-prefix cap
continues to hold. No rootwise distinctness is used. Square stars must still
project to their corresponding 3q and5q roots; independently chosen square
endpoints are not covered by this deduction.
Its normalized product nu_c=product_q xi_q/Z_q is a genuine product law.

For edge{q,r}, impose the entire first-root rectangle

    E_qr={x_q=d_(q,r), x_r=d_(r,q)}.

It contains all twelve retained originals on that edge, whether or not its
unconditional qr slot was originally present. Every root mass in xi_q is
at most r_q. With beta_qr=r_q r_r, therefore

    nu_c(E_qr)<=u_qr(c)=beta_qr/(Z_q Z_r).                    (ME3)

The ten rectangle events have ordinary shared-coordinate dependency graph
L(K5). Their endpoint equalities and conflicts may be arbitrary; no special
incidence pattern, resampling oracle or independence of adjacent edges is
assumed.

## 3. A strict Shearer region for every actual and comparison vector

After the valid auxiliary padding from Report617, R2 is the other live
ternary row from R1, C2 differs from C1, and P is a live unmasked root
point. Thus the entire actual central-leaf vector is

    Z_real=1-r(I_R+I_C1+I_P+I_L+I_M)-alpha(1-I_R+I_C2).

Define an aligned whole vector

    Zhat(C)=1-r(I_R+I_C+I_P+I_L+I_M)-alpha(1-I_R+I_C).        (ME4)

Then, with the same other roles held fixed,

    Z_real=[r/(r+alpha)]Zhat(C1)
                 +[alpha/(r+alpha)]Zhat(C2).               (ME5)

For both the actual vectors and all aligned corners,

    zmin_q=1-5r_q-alpha_q <= Z_q <= zmax_q=1-alpha_q.

Every zmin is positive, with zmin_7=29/210. Let
pmax_qr=beta_qr/(zmin_q zmin_r). For any subset A of the ten edges,
independent sets in L(K5) are matchings of size at most2, and

    S_A(u)=1-sum_(e in A)u_e
                 +sum_(e,f in A, disjoint)u_e u_f.         (ME6)

The exact rational values satisfy

    S_all(pmax)=9982817138470/32441035304113 >0,
    max_e sum_(f disjoint e)pmax_f=6264863/13910285 <1.

The latter gives a negative coordinate derivative throughout0<=u<=pmax.
Every induced polynomial therefore decreases when its available coordinates
increase, and zeroing omitted coordinates can only increase it. Hence all
1024 induced polynomials are strictly positive throughout this box. They
are also independently enumerated at pmax. This is a uniform strict region,
including every path segment between the mean and any comparison corner.

For a vertex subset S define the unnormalized matching polynomial

    H(S;Z)=product_(q in S)Z_q
      -sum_(e subset S)beta_e product_(q in S\e)Z_q
      +sum_(e,f disjoint, e union f subset S)
                       beta_e beta_f product_(q in S\(e union f))Z_q.

Write H_T=H(Q\T;Z). Each H_T is positive on the entire Z box and

    d H(S;Z)/dZ_q = H(S\{q};Z), q in S.                      (ME7)

Thus it is increasing in every remaining Z coordinate on that box.

## 4. The same law gives every mass and full-height query grid

Let F_c avoid all ten actual auxiliary rectangles. Ordinary conditional
Shearer/Scott-Sokal avoidance, as in
[Report597](597-a-common-pair-survivor-law-closes-the-outside-square-slice.md),
gives

    nu_c(F_c)>=S_all(u)>0,
    mu_c=nu_c(.|F_c),
    mu_c(A)<=nu_c(A) S_(edges outside T)(u)/S_all(u)          (ME8)

for any outside query cylinder A with coordinate support T. One proof of
the last inequality adjoins an independent rare coin and the event
A intersect{coin=1}; its nonneighbors are precisely the old edges outside
T. The strict inequalities above permit a sufficiently small positive coin
probability, and conditional avoidance followed by cancellation gives ME8.
The coin does not change mu_c, which is the same for all queries.

Now define one actual submeasure

    zeta_c=(product_q Z_q) S_all(u) mu_c.

ME8 and the avoidance lower bound show

    zeta_c<=product_q xi_q,
    zeta_c(1)=H_empty(c),
    zeta_c(A)<=[product_(q in T) cap_q(A_q)] H_T(c).           (ME9)

Indeed xi_q<=rho_q implies nu_c(A)<=product_(q in T)cap_q(A_q)/Z_q.
All queried-coordinate denominators cancel. This proves the query bound
for arbitrary finite heights using the original pure-prefix caps.

Mix zeta_c with the fixed FA1 central source and the central15 mask. The
result is one submeasure zeta<=rho supported on every retained star and
pair original. Its central dependence is only through the mod9/mod25 leaf,
so all sixteen inherited central selector menus remain valid. Restricting
this same measure by every remaining original only decreases its raw
query masses. The complete L/W gate is therefore

    K(H)=(1-c)sum_b mu_b H_empty(b)
         -sum_j [(1-c)L_j+cW_j]
                          max_(s in menu_j)sum_b s_b H_(T_j)(b),
    c=1084133/201247200.                                    (ME10)

It lower-bounds eta(1)-c Gamma(eta) for the resulting actual complete-core
survivor eta. No response in ME9 or ME10 chooses a new source for a query.

The EP1 incidence distinction in Report617 remains real: the unthinned
rectangle-avoidance mass can differ between endpoint patterns. The present
H_empty is the exact mass of a deliberately scaled conditional submeasure,
not a claim that those actual raw avoidance counts coincide. For each
fixed original family there is one such supported source and simultaneous
query bounds; sources for different original families need not be equal.

## 5. Convex comparison removes actual central-square column choices

H_T is affine in each whole Z_q vector when the other four are fixed.
K is concave in its response grid because its mass is linear and its
subtracted selector maxima have nonnegative coefficients. Therefore ME5,
applied successively at the five primes, transfers any uniform lower bound
for aligned corners to the actual source already constructed in ME9.
Aligned corners need not themselves describe rootwise actual submeasures;
only their scalar Z box and response comparison are used.

There are5320 aligned templates per prime: two rows, four columns, seven
live root points, five ternary leaves and nineteen quinary leaves. Their
uniform mean at every positive unmasked central leaf is

    zbar_q=1-(3047/2660)r_q-(3/4)alpha_q.                    (ME11)

The complete source permutation group, template-pair orbit representatives
and all sixteen selector menus are the same as Report617. It has317920
ordered pair representatives covering5320^2 template pairs.

## 6. Signed pair bounds retain all orders of interaction

For fixed five templates put delta_q=Z_q-zbar_q and
Z_q(t)=zbar_q+t delta_q. Taylor's integral identity and ME7 give exactly

    H=Hbar+sum_q D_q
                  +sum_(q<r) Q_(T,qr) delta_q delta_r,
    D_q=1_(q notin T) Hbar_(T union{q}) delta_q,
    Q_(T,qr)=2 integral_0^1 (1-t)
                           H(Q\(T union{q,r});Z(t))dt,      (ME12)

with Q=0 when T meets{q,r}. This identity includes all interactions of
orders two through five. No higher-order error is discarded.

By positivity and monotonicity on the strict box, rational lower and upper
bounds L_(T,qr)<=Q_(T,qr)<=U_(T,qr) follow by replacing the remaining
endpoint Z coordinates with zmin and zmax while retaining zbar at t=0.
The remaining polynomial has at most three vertices, so the integrals are
finite exact rational sums. The producer expands affine products; an
independent check uses Bernstein-product integration.

Allocate Hbar/10+(D_q+D_r)/4 to edge qr. With v=delta_q delta_r, its
mass lower grid uses L v_+ + U v_-, and its query upper grids use
U v_+ + L v_-. These are signed comparison grids, not separate probability
laws. Nonnegative selector weights and the superadditivity of K give

    K(H)>=sum_(q<r) k_lower(q,r).                            (ME13)

Minimize each pair contribution over every template pair with prescribed
central columns. Then minimize the sum over the4^5 shared column choices.
Different pair-table minimizers need not be jointly attainable: they are
lower bounds for one coherent five-template assignment. Their relaxation
cannot increase the claimed lower bound.

## 7. Complete directed certificate

Local lower/upper grids are rounded at2^23 and gate coefficients at2^27;
the common central denominator is58400. Negative mass terms use the upper
gain coefficient and negative query screens use the lower debit coefficient.
All local entries lie in[-2,2]. The implementation uses signed64 selector
arithmetic and signed128 budget arithmetic, with explicit bounds checked.

The full scan covers317920 representatives for each of ten prime pairs,
then1024 common-column assignments. It returns ME1. Every remaining
original coefficient and every weighted query coefficient is consumed
from the complete512-entry L/W arrays with their exact source hash. There
is no finite query-height cutoff and no floating optimizer input.

Independent verification reconstructs the rational interval endpoints,
checks generic selector vectors at all160 recorded pair-table witnesses,
and checks the1024-column minimum. The engine provides the full orbit
exhaustion. These finite checks supplement the ordinary source, convexity
and Taylor arguments; none is a Lean proof.

## 8. Exactly which outside network the new margin pays

The actual core law eta remains dominated by the same product pure source.
Its singleton Haar caps are below2 at3, at most25/16 at5, and q/(q-2) at
other core primes; the largest product of two is below10/3. The unchanged
head-only kernels at23,29,31 have conditional original-Haar caps
5/3,20/11,2 and full density multiplier200/33. Thus the same head law has
singleton cap2, pair cap4, and full Haar density bound

    C=138320/2673, alpha=1/C=2673/138320.

This supplies exactly Report616's source conditions. Its early two-head
roots can be preloaded; the head kernels still ignore them, and their
conditional product law given the full head is preserved. Every later
normalized owner row leaves the prior head marginal unchanged. Its complete
same-source fees are bounded by

    fee616=1/780+4/125000+1/65536+2(1/250000+1/1600)
          =20665363/7987200000.                            (ME14)

This covers one fixed tuple per owner, either the previous two-parent type
or a three-parent type with at least two outside parents, together with
that report's declared disjoint ordinary private interfaces. Network size,
width and depth are arbitrary finite quantities; original heights remain
arbitrary finite and all phases remain globally fixed.

The new raw gate after those deletions is positive. Its exact head lower
bound is

    alpha(gamma-fee616)
      =1356495098958953106676083/14779201688363369234432000000
      >1/11000.                                           (ME15)

Even the simpler gamma>7/1000 gives a lower bound greater than1/12000.
The actual network and private witnesses glue exactly as in Report616;
this is an extension-domain lower bound on head configurations, not a
claim that every head point or every intermediate fibre survives.

Reports619/620 permit other three-parent types by paying a larger complete
fee, about0.0265, which exceeds the present gamma. Those whole-network
conclusions do not follow from this result. Raising later-owner thresholds
or developing a sharper gate would require new estimates. The arbitrary
endpoint progress is not combined with an unpaid network expansion.


## Retained exact certificate

The [producer](../../frontier/cover-geometry/matching_endpoint_certificate.py),
[integer kernel](../../frontier/cover-geometry/matching_endpoint_certificate.cpp)
and [data](../../frontier/cover-geometry/matching_endpoint_certificate.json)
retain the complete coefficient pin, strict Shearer box, exact integrated
intervals, source orbit coverage, ten common-column tables and their
shared minimum. The proof above supplies the common-source and unbounded
height statements. No finite sample or optimizer output is an input.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/matching_endpoint_certificate.py
