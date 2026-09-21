# 339e. Uniform transport for both actual-source squares

This concerns the actual irredundant family F_N constructed in
[339](339-irredundant-source-seven-labels-bound-the-actual-surplus.md),
with every original exclusion through N and period Q=3^N5^N7^N. It
extends the two complete F12 maxima in
[339b](339b-the-actual-near-j-source-and-the-unit-refund.md).
The plain Schur result in
[339d](339d-the-complete-plain-source-square-at-every-height.md)
retains its separate site/pair LP conclusion for N>=12.

Let R_N be the surviving set and let H_Q be normalized Haar probability.
Write rho=1_{R_N}H_Q and rho_r=r(x3 mod9)rho, where the row weights on
(0,3,1,4,7) are (11/8,5/4,1,1,1). Normalize each by its own total mass
to obtain nu and nu_r. The surviving point(4,4,4) makes both masses
positive. A complete layout retains one auxiliary residue for every
numerical divisor of Q, including the unit once. Its load is L.

**Theorem.** For every integer N>=4, the complete common-center layout

    L4=sum_{d|Q} 1_{x=4 mod d}

attains both Gamma_Q(nu)=max_L integral L^2 dnu and Gamma_Q(nu_r).
It is the unique maximizing layout inside the simultaneous compressed
class, for either law. The exact values below tend respectively to
1829/72 and671791/29142.

This is an ordinary exact certificate for this actual source family.
It does not prove weighted pair-LP exactness, uniqueness before
compression, arbitrary-source domination, later-prime closure or
unrestricted Erdős #7. There is no new Lean declaration.

## Actual cylinders and the root envelope

The source-preserving compression in339b moves every positive five and
seven test to its nested clean residue4. It retains the following
ternary choices without moving any original forbidden AP:

| Category | a=1 | a=2 | a>=3 |
|---|---|---|---|
| A | root0 | 0 mod9 | 18 mod3^a |
| B | root0 | 3 mod9 | 3 mod3^a |
| C | root1 | 4 mod9 | 4 mod3^a |

A and B coincide only at depth1. Source positivity and ancestor
compatibility are preserved. Row4 dominates rows1 and7 in the remaining
mask; path18 removes the pure-three loss in row0, and row3 is flat at
deeper ternary depths. These comparisons hold for both specified laws.

Set

    x=3^-N, y=5^-N, z=7^-N,
    t=1/18-x/2, eta=1/18+x/2,
    q=(1-y)/4, s=(1-z)/6, u=1-s,
    R1=1/3-(5/6-x/2)q=1/3-(7/9+t)q.

Work initially with the unnormalized weighted restriction rho_r.
For a>=2 the actual canonical-cylinder mass is

    M_c(a,j,k)=r_c H_c(a) F_c(j) G_c(k),             (UC1)

where r_A=11/8,r_B=5/4,r_C=1, and

    H_A(2)=eta, H_A(a)=3^-a for a>=3,
    H_B(a)=H_C(a)=3^-a,
    F_A(0)=F_B(0)=1-q, F_C(0)=1-2q,
    F_c(j)=5^-j for j>0,
    G_A(0)=u-1/7, G_B(0)=u-2/7, G_C(0)=u,
    G_c(k)=7^-k for k>0.

The shallow moments retain the full surviving rows:

    M_A(1,j,k)=M_B(1,j,k)=M_A(2,j,k)+M_B(2,j,k),
    M_C(1,0,k)=R1 G_C(k),
    M_C(1,j,k)=(1/3)5^-j G_C(k) for j>0,
    M(0,j,k)=M_A(1,j,k)+M_C(1,j,k).                 (UC2)

These are actual-mask identities. On rowA, the deeper pure-seven
exclusions lie inside the original37 exclusion at seven root1; the
remaining forbidden seven width is s+1/7. On rowB, the original97
exclusion also absorbs the deeper3*7 exclusions, giving width s+2/7.
The mixed35 restrictions on ternary root1 give the displayed R1.

The maximum root0 pair coefficient at maximum ternary depth1 is the
whole root0 moment, at depth2 it is categoryB, and at depth>=3 it is A.
For depth2 and N>=4,

    (r_A eta)/(r_B/9)<=11/18,
    G_A(k)/G_B(k)<=29/23,
    M_A(2,j,k)/M_B(2,j,k)<=319/414<1.                (UC3)

At deeper depths A dominates B because r_A>r_B, their five factors
agree and G_A>=G_B. These separate pair maxima supply an upper envelope;
they are not claimed to be jointly attainable.

## The anchored cut and transport lemma

Fix the one auxiliary test h=(2,0,0), the modulus9 label, to category
b in {A,B,C}. This fixes a test choice and never conditions the source.
The variable vertices and fixed load are

    V={(a,j,k):1<=a<=N,0<=j,k<=N}\{h},
    B0=sum_{0<=j,k<=N} I_(0,j,k).

The inventory remains (N+1)^2+[N(N+1)^2-1]+1=(N+1)^3.
For v in V put

    U_v^b(c)=M_c(v)+2 sum_{0<=l,m<=N} M_c(v∨(0,l,m))
                   +2 integral I_v^c I_h^b d rho_r,
    U_v^0=max(U_v^b(A),U_v^b(B)), U_v^1=U_v^b(C),
    K0(v,w)=max(M_A(v∨w),M_B(v∨w)),
    K1(v,w)=M_C(v∨w), W(v,w)=K0(v,w)+K1(v,w),
    d_v=U_v^0-U_v^1+sum_{w in V,w!=v}(K0(v,w)-K1(v,w)). (UC4)

The anchor intersection is the actual compatible cylinder, or zero.
At depth1 compatibility means the same root and uses the anchor's
depth2 category; at depth>=2 it means the same category. The anchor
term is added before taking the unary maximum. Diagonals occur once
and all distinct fixed/anchor cross terms occur twice.

Let S be the variable labels assigned root0, and let B_b be the actual
squared integral with anchor b and all variables C. Expanding the
binary upper relaxation, keeping one shared root choice per label, gives

    integral L^2 d rho_r
      <=B_b+sum_{v in S}d_v-sum_{v in S,w outside S}W(v,w). (UC5)

**Transport lemma.** If f is antisymmetric, |f(v,w)|<=W(v,w), and
d_v<=div f(v)+h_v with h_v>=0, then

    sum_{v in S}d_v-sum_{v in S,w outside S}W(v,w)
      <=sum_{v in S}h_v<=sum_{v in V}h_v.            (UC6)

Indeed, internal transport cancels when divergences are summed over S;
every outward transport is at most its cut-edge capacity. No optimizer
or assertion that a flow is maximal is used.

## A fixed transport on the original vertices

The following11 types are ordered as written; + means every positive
exponent through N:

    0:(1,0,0)  1:(1,0,+)  2:(1,+,0)  3:(1,+,+)
    4:(2,0,+)  5:(2,+,0)  6:(2,+,+)
    7:(>=3,0,0)  8:(>=3,0,+)  9:(>=3,+,0)  10:(>=3,+,+).

The omitted(2,0,0) is exactly the anchor. The arrays TH, HA and HB in
[source_uniform_cut.py](../../frontier/source-budgets/source_uniform_cut.py)
give every certificate coefficient as an integer divided by10000.
TH contains65 used entries with absolute value at most1 and one unused
zero at(0,0), whose type contains just one vertex.

For different types i<j define f(v,w)=TH[i,j]W(v,w) when v is in i and
w is in j, and use antisymmetry in the reverse direction. Within a type,

    f(v,w)=TH[i,i]W(v,w) sign_lex(v-w),

where lexicographic order uses the full triples(a,j,k). Thus every
original edge satisfies its capacity bound. A type selects a coefficient;
its vertices remain independent and may lie on different cut sides.

Write g_v=3^-a5^-j7^-k. The certificate establishes in anchor branch C

    div f(v)-d_v >=(1691/120000)g_v.                (UC7)

For branches A and B, split each active range into its first exponent
and complete remaining tail: a=3/a>=4, j=1/j>=2 and k=1/k>=2. This
gives35 subtypes, ordered by the11 types and then the lexicographic bits
for active coordinates a,j,k. HA and HB specify nonnegative allowances
h_v=H_b(subtype)g_v for which

    d_v<=div f(v)+h_v.                              (UC8)

Summing the allowances over all infinite tails, not just through N, gives

    sum h_v^A=5965019/25200000,
    sum h_v^B=58975639/226800000.                    (UC9)

The factors for a>=4,j>=2,k>=2 are respectively1/54,1/20,1/42;
the first-exponent factors are1/27,1/5,1/7. Consequently(UC9) bounds
every actual finite-N allowance sum without omitting high powers.

## Finite exact obligations cover all heights and indices

At a variable vertex use shifted indices A=a-3 for a>=3, J=j-1 for
j>0 and K=k-1 for k>0. The active endpoint variables are
E3=3^(a-N), E5=5^(j-N), E7=7^(k-N). The exact normalized positive
partner sums and their lower-minus-upper versions are

    three: A+1+(1-E3)/2,  A-(1-E3)/2,
    five:  J+1+(1-E5)/4,  J-(1-E5)/4,
    seven: K+1+(1-E7)/6,  K-(1-E7)/6.               (UC10)

For example, the five sum is
sum_{l=1}^N 5^-max(j,l)/5^-j=j+(1-E5)/4. For a shallow target, the
deep ternary partner sum is instead3^a(1/18-x/2). Zero-depth factors
come directly from(UC1)-(UC2).

To obtain the within-type divergence, split partners at the first
coordinate differing from v. The ternary lower-minus-upper factor is
multiplied by full five/seven sums; the equal-ternary five difference
is multiplied by the full seven sum; the equal-ternary/five seven
difference supplies the last term. The diagonal transport is zero.
This gives the finite lexicographic expression `lex` in the verifier.

The diagonal envelope difference also occurs in the exact unary
difference. Including it in `rowdiff` cancels it from the unary,
leaving twice the fixed-a0 cross difference and the full row difference.
The actual anchor adjustment is then made for each candidate before
the maximum. Thus the verifier's `residual` is exactly

    (div f(v)-candidate_d_v)/g_v.                   (UC11)

For branch C the root0 unary envelope in(UC3) is used. For A/B both
candidate categories are checked. The source-to-graph verification
below independently reconstructs these quantities from actual cylinders.

Every expression in(UC11) is separately affine in the nine variables
A,J,K,E3,E5,E7,x,y,z. This follows by inserting(UC1)-(UC2) and(UC10):
each coordinate contributes one full-sum or signed-sum factor, and
source factors and anchor corrections involve each source variable at
most once. In particular finite differences at0/1 extract all
coefficients in the free shifted indices; there are no unexamined
higher-degree terms. A separate symbolic degree audit expands all55
type/branch/candidate expressions and verifies this property.

For N>=4 the bounded source box is

    0<=x<=1/81, 0<=y<=1/625, 0<=z<=1/2401.          (UC12)

In branch C every active shift is nonnegative and each active E lies
in[0,1]. In A/B, the first-exponent cases have shift0 and respectively
E3<=1/3, E5<=1/125, E7<=1/343. On the remaining tails a shift is1+U
with U>=0, and E lies in[0,1]. These boxes contain every actual tuple;
enlarging them is a coefficient comparison, not a change of source law.

At each source/endpoint corner the checker takes the finite differences
in every subset of free indices, adding the prescribed allowance to
the constant term for A/B. All resulting coefficients are nonnegative.
Multiaffine interpolation extends their signs over each bounded box;
nonnegative powers of U then extend the inequalities over all free
indices. This proves(UC7)-(UC8) for every integer N>=4.

| Anchor | Coefficient checks | Zero coefficients | Least positive | Least constant |
|---|---:|---:|---:|---:|
| A |6256|0|561/40000|9001/640000|
| B |6256|0|47039/3360000|47039/3360000|
| C |1192|0|561/40000|1691/120000|

These13704 exact inequalities, the degree argument and the complete
tail sums together establish the unbounded result. Finite-height graph
checks alone do not do so.

## Anchor losses, strict maxima and transfer to the plain law

Let J_r=integral L4^2 d rho_r. Define c_A=1/7,c_B=2/7 and
R_A=(11/8)eta,R_B=5/36. Directly removing the centered anchor and
adding the actual root0 anchor gives

    J_r-B_b=(2/3+2t)(1-q)-(1/9)(1-2q)u
             -R_b[(1-q)(u-c_b)+2(1-c_b)].           (UC13)

For the centered anchor, integral L4 I_h^C d rho_r=(1/3+t)(1-q).
The shallow ternary contributions total1/3, deeper ones total t, and
the complete five and seven stacks sum to1-q and1. For a root0 anchor,
only B0 intersects it, giving integral L4 I_h^b d rho_r=R_b(1-c_b).
Combining these two cross sums with the two anchor diagonals proves
(UC13) in the same actual measure.

Expression(UC13) is separately affine in x,y,z. Its eight corners in
(UC12) give

    J_r-B_A>=350909/1037232,
    J_r-B_B>=282449/1037232,                         (UC14)

with both minima at(x,y,z)=(1/81,0,1/2401). Subtracting the full
allowances in(UC9), then applying(UC5)-(UC8), yields

    anchor A: integral L^2 d rho_r<=J_r-2634720449/25930800000,
    anchor B: integral L^2 d rho_r<=J_r-955030823/77792400000,
    anchor C: integral L^2 d rho_r
                <=J_r-(1691/120000)sum_{v in S}g_v.  (UC15)

The first two gaps are uniform unnormalized weighted gaps. The last
is relative to the changed-label masses; it does not give an absolute
N-independent gap between all distinct layouts. Every noncentered
compressed layout loses strictly. This proves compressed uniqueness
and, by simultaneous compression, the full weighted maximum.

For any compressed L, on surviving root0 one has L>=L4=B0; on root1
one has L<=L4. The weighted law increases only root0 weights, leaving
root1 weights equal to1. Therefore the same actual difference satisfies

    integral(L^2-L4^2)d rho<=integral(L^2-L4^2)d rho_r<=0. (UC16)

Strictness transfers for every noncentered compressed layout. Apply
the valid plain compression to arbitrary layouts, then divide each
law by its own positive normalization. This proves the plain theorem
without identifying the two normalized laws.

## Exact values and limiting constants

For either law choose(r_A,r_B)=(1,1) or(11/8,5/4), and set

    T3=2-(N+2)3^-N,
    T5=7/8-((4N+7)/8)5^-N,
    T7=5/9-((3N+5)/9)7^-N.

These are the exact sums sum_{h=1}^N(2h+1)p^-h for p=3,5,7.
The normalization and centered numerator are

    Z_r=r_A eta(1-q)(u-1/7)+(r_B/9)(1-q)(u-2/7)+R1 u,
    J_r=r_A eta(1-q+T5)(u-1/7+T7)
        +(r_B/9)(1-q+T5)(u-2/7+T7)
        +4(R1+T5/3)(u+T7)
        +(T3-1)(1-2q+T5)(u+T7),
    Gamma_Q(nu_r)=J_r/Z_r, N>=4.                   (UC17)

Exactly(2a+1)(2j+1)(2k+1) ordered centered pairs have maximum depths
(a,j,k). Summing their actual nested-cylinder masses gives(UC17),
including the unit and all its cross terms. At N12 it reproduces

    plain:2036574313467845778288943/80172464522644795549722,
    weighted:16622960794401007994531582/721107129061336405998171.

As N tends to infinity, x,y,z tend to0 and(T3,T5,T7) to(2,7/8,5/9).
The normalizations tend to5/28 and1619/8064, both positive. Thus

    lim Gamma_Q(nu)=1829/72,
    lim Gamma_Q(nu_r)=671791/29142.                 (UC18)

## Reusable exact verification and scope

The standard-library checker keeps all65 transport coefficients and
both35-entry allowance arrays. It verifies the coefficient inequalities
and infinite allowance totals. Independently of its residual formulas,
it reconstructs actual pair masses, candidate unaries, capacities,
antisymmetric edge transports and anchor losses using the existing
actual-source API:

| Height | Variables | Fixed a0 labels | Anchor | Complete labels | Checked vertices | Directed edges | Residual equalities |
|---|---:|---:|---:|---:|---:|---:|---:|
|4|99|25|1|125|99|9702|495|
|12|2027|169|1|2197|45|91170|225|

Every N4 row is checked. The45 N12 vertices cover all11 types, first
and last indices, and interior representatives; each uses the entire
2027-vertex partner inventory. The source API's original-AP audit is
retained in339b. Exact centered values at N4,5,12,24 for both laws are
also compared with the complete actual-source pair-maximum histogram.

The existing sharpness producer invokes the full standard-library
check and retains its small exact result in `uniform_source_squares`.
Standalone invocations are

    python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_uniform_cut.py --check
    python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_uniform_cut.py --check-degrees

The second is an optional independent symbolic audit using SymPy;
it verifies all55 residual degree bounds and both anchor degree bounds.
It was checked with SymPy1.14.0. The canonical rational checker needs
only the standard library. Both paths use explicit exceptions, active
under optimization.

The certificate proves exact maxima for the specified two actual laws.
It provides no weighted categorical pair-LP certificate and does not
extend339d's plain LP statement below N12. Types are never graph
contractions. Transport to guarded, killed or differently generated
source laws requires further same-object comparisons; no arbitrary
inventory or later-prime survival conclusion follows from(UC17).
