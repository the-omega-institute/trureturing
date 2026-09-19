[Index](../marked_head_profile.md) · [Actual endpoints](50-sharp-source-survival-endpoints.md) · [Common deleted measure](57-common-deleted-measure-coupling.md)

# A joint linear source-deletion bound at the off-diagonal endpoint

Let actual finite original-label families approach source vertex404,
normalized survivor mass S=D=3/20, and shallow carrier mixture(0,1).
For every independently labelled original357 linear test A, with unit
term1, the actual surviving-load numerator satisfies

    limsup integral_survivor A <=1157/1800.            (1)

The statement is uniform over the original test residues, which can
change with the family. It concerns source and deletion together.
For the live linear direction40 in profile49, whose actual cost is
f(v)=v and whose barrier is6, it gives

    liminf [6*S-integral_survivor A] >=463/1800.

The old margin at this endpoint and carrier is4507/24300. The new
absolute bound improves that margin by3487/48600. No separate source
correction is subtracted from the old margin; all deletion credits
below are evaluated against the same actual source.

This is an endpoint and approaching-sequence theorem, not a bound
on every finite family, a quantitative neighborhood estimate, or a
new global K certificate. The proof is ordinary mathematics, not
a Lean result. A finite family below disproves an unqualified
extension of the constant1157/1800 away from the endpoint.

## 1. Saturation supplies one actual deleted measure

Use raw35 source Lambda, pure3 source eta, pure7-normalized measure,
and actual deleted marginal delta from profile57. The five surviving
ternary cells, their roots, and their masses at vertex404 are

    cells=( [0]9,[3]9,[1]9,[4]9,[7]9 ),
    ROOT=(0,0,1,1,1),
    eta=(1/18,1/9,1/9,1/9,1/9),
    n=(1/24,1/12,1/36,1/24,1/18),
    d=(3/4,3/4,1/4,1/2,1/2),
    h0=1/6, h1=1/3, h=1/2, s=1/4.

The raw source has pure5 union mass1/4, effective alpha deletion1/4
on root1, effective beta deletion1/4 on cell2, and actual additional
late35 deletion1/72 on cell3. Every other alpha, beta, and late
entry is zero. These are parameters of actual original labels.

For a nonunit original old35 cofactor3^a*5^b the complete source
caps are

| Cofactor | Raw Lambda cylinder cap | Sum over that category |
| --- | ---: | ---: |
| 3 | 1/8 | 1/8 |
| 9 | 1/12 | 1/12 |
| 3^a, a>=3 | (3/4)*3^(-a) | 1/24 |
| 5^b, b>=1 | h*5^(-b) | 1/8 |
| 3*5^b, b>=1 | h1*5^(-b) | 1/12 |
| 9*5^b, b>=1 | max(eta)*5^(-b) | 1/36 |
| 3^a*5^b, a>=3,b>=1 | 3^(-a)*5^(-b) | 1/72 |

The sum is1/2. Including the unit source mass gives a complete
raw35 linear bound of3/4. Each positive-seven depth has normalized
cap u_e=6/(5*7^e), with sum_e u_e=1/5.

For the actual forbidden cofactors C_i define

    V(dx)=sum_i u_(e_i)*1_(C_i)(x)*Lambda(dx).

Profile57 gives delta<=V and (V-delta)(1)<=S-D. At S=D, equality
holds as measures: delta=V. Moreover the cap sum is exactly
s-D=1/10, so every nonnegative gap in the complete cap comparison
is zero. In particular every cofactor with a positive cap is
present and attains its own old35 cap; neither missing labels nor
overlap nor a normalized seven-cap loss can remain.

The carrier condition means every cofactor3*7^e uses root0 and
every cofactor9*7^e uses cell1. The first is material because the
two source root masses both equal1/8; cell1 uniquely maximizes n.

## 2. The first five-adic level is forced

Write P_b,A_b,B_b for the five-coordinate cylinders of the actual
source labels5^b,3*5^b,9*5^b. The effective budgets force all A_b
onto root1 and all B_b onto cell2. Since the three complete raw
budgets1/4+1/4+1/4 are fully used in the effective union on cell2,
all these five-coordinate cylinders are mutually disjoint, including
across depths and families. This is the zero-deficit case of the
shallow-budget argument in profile50.

In particular P=P_1, A=A_1, B=B_1 are three distinct full mod5
slots. Here B denotes the beta first cylinder, on cell2. It does
not denote the alpha cylinder on root1.

A saturated forbidden cofactor5 has source mass h/5=1/10. Its
mod5 slot H is therefore completely source-free relative to eta.
It cannot equal P,A, or B. Every deeper P_b,A_b,B_b, b>=2, must
avoid H and the three first cylinders. Hence all lie in the one
remaining mod5 slot Q, each family with total five mass1/20.
The slot Q has positive source loss, so H is the unique completely
source-free first slot. All cofactor5 labels, at every seven depth,
must therefore use H.

Similarly, a saturated cofactor15 must use root1: root0's pure3
mass h0 is strictly smaller than h1. On root1 every first slot
other than H has positive source loss: P,A are removed there, B
loses cell2, and Q contains the positive pure5 and alpha tails.
Thus all cofactor15 labels use root1 times H.

More generally every saturated cofactor5^b is globally source-free
relative to eta. Every saturated cofactor3*5^b uses root1 and is
source-free there. Such a five cylinder is also globally source-free:
the only five-dependent source deletion outside root1 is pure5,
and a pure5 intersection would already cause loss inside root1.
Consequently all those complete virtual-deletion families contribute,
in cell l, exactly

    cofactor5^b, all b,e:       eta_l/20,
    cofactor3*5^b, all b,e:     1_(ROOT(l)=1)*eta_l/20.   (2)

No agreement between their deeper five residues is required.

### The late b=1 budget lies in the beta first slot

Every source label3^a*5^b, a>=3,b>=1, attains its full additional
raw budget, all inside cell3. In particular a b=1 label cannot
use P or A, already removed on cell3. It cannot use H, which has
zero source loss. It cannot use Q: the pure5 and alpha tails have
positive five mass inside Q, so a full mod5 Q rectangle would lose
part of its raw area before the late deletion. Thus every b=1
late source label uses B, the beta first slot. This is permitted
because cell3 differs from beta's cell2.

Their full mass is

    sum_(a>=3)3^(-a)/5=1/90.

Let x be actual additional late deletion inside cell3 times B.
All other late deletion lies in cell3 times Q. Therefore

    1/90<=x<=1/72,
    late(cell3 times Q)=1/72-x.                       (3)

This uses the actual extra deletion; no already deleted alpha
area is counted a second time.

## 3. Four uniform surviving-cylinder estimates

Let mu=Lambda-delta be the actual surviving old-coordinate marginal.
The four selected complete forbidden-cofactor families give

    delta >=(1/5)*(1_root0+1_cell1+1_H+1_(root1 times H))*Lambda. (4)

This is an inequality of measures on the common source. The family
5, all seven depths, is distinct from family15; both contributions
are valid because at saturation delta=V.

For a test cylinder of modulus3 or9 we use, in addition to the
root0 and cell1 families, all the positive-five families in(2).
This gives

    mu(cell_l)<=n_l*(1-(1_root0+1_(l=1))/5)
                      -(1+1_root1)*eta_l/20.

The five right-hand sides and their root sums are

    cells: (11/360,2/45,1/60,11/360,2/45),
    roots: (3/40,11/120).

Thus every independently chosen original test label satisfies

    modulus3: surviving mass<=11/120,
    modulus9: surviving mass<=2/45.                   (5)

For labels5 and15 retain the stronger slot geometry. Before late
deletion the exact cell-slot masses, divided by eta_l, are

| Cell | P | A | B | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0,1 | 0 | 1/5 | 1/5 | 3/20 | 1/5 |
| 2 | 0 | 0 | 0 | 1/20 | 1/5 |
| 3,4 | 0 | 0 | 1/5 | 1/10 | 1/5 |

Subtract x from the cell3,B entry and1/72-x from cell3,Q.
The row sums are exactly n. Applying(4) entrywise multiplies each
entry by

    1-(1_root0+1_(l=1)+1_(slot=H)+1_(root1 and slot=H))/5.

For x throughout(3), the resulting complete slot bounds are

    (P,A,B,Q,H)<=(0,1/45,1/18,2/45,1/18),

and the root0 and root1 slot bounds are respectively

    root0: (0,1/45,1/45,1/60,7/450),
    root1: (0,0,1/30,1/36,1/25).

Every entry is affine in x, so checking the two endpoints of(3)
proves these tables for the whole interval. They yield

    modulus5:  surviving mass<=1/18,
    modulus15: surviving mass<=1/25.                  (6)

The test residues in(5) and(6) are arbitrary and can be different
for every modulus. Credits used to bound different test cylinders
can be added because their sum is precisely the linear test load;
they are not repeated payments on one occurrence of that load.

## 4. The complete original357 numerator

The four old source caps and new surviving caps are

| Original test label | Old cap | New cap | Loss |
| --- | ---: | ---: | ---: |
| 3 | 1/8 | 11/120 | 1/30 |
| 9 | 1/12 | 2/45 | 7/180 |
| 5 | 1/10 | 1/18 | 2/45 |
| 15 | 1/15 | 1/25 | 2/75 |

Their total loss is43/300. Two complete test tails improve as well.
For any pure3 test cylinder T of depth a>=3 inside cell l, source
deletion gives Lambda(T)<=d_l*eta(T). The source-free cofactor
families in(2) have, on every such T, virtual mass
(1+1_root1)*eta(T)/20. Together with the root0 and cell1 cofactors,

    mu(T)<=[d_l*(1-(1_root0+1_(l=1))/5)
                      -(1+1_root1)/20]*eta(T).

The five coefficients are(11/20,2/5,3/20,2/5,2/5). Since
eta(T)<=3^(-a), every test of depth a>=3 has mass at most
(11/20)*3^(-a), compared with the old(3/4)*3^(-a). The complete
additional loss is(1/5)*sum_(a>=3)3^(-a)=1/90.

For a pure5 test cylinder F of depth b>=2, retaining just the
root0 and cell1 deletion families gives

    mu(F)<=sum_l(1-(1_root0+1_(l=1))/5)*Lambda(cell_l times F)
          <=[h-(h0+eta1)/5]*5^(-b)=(4/9)*5^(-b).

This improves the old(1/2)*5^(-b) by a complete total1/360. These
two test tails are disjoint from each other and from the four
shallow test labels. Their additional loss is1/72.

All other nonunit zero-seven labels retain their old source caps.
The unit label contributes the actual survivor mass S. Thus

    integral_survivor A0<=S+1/2-43/300-1/72.

Without these last two tail refinements the four shallow labels
alone would already give the intermediate full357 bound197/300.

For a positive-seven test label with independently chosen cylinder
C35 times K_e, dropping mixed-seven deletion gives

    survivor_mass(C35 times K_e)<=u_e*Lambda(C35).

The bound holds label by label and does not require a common K_e
among the old-coordinate cofactors at one depth. Summing all a,b
including the old-coordinate unit, then all e>=1, gives the complete
positive-seven contribution at most(1/5)*(3/4)=3/20. Therefore

    integral_survivor A<=S+1/2-43/300-1/72+3/20
                       =1157/1800 at S=3/20.        (7)

This is an absolute source-deletion bound. Compared with profile49,

    6*(3/20)-1157/1800=463/1800,
    463/1800-4507/24300=3487/48600.

The checked profile49 coefficient of this direction is positive,
94212612766226/1174116234095805. Its positive endpoint gain alone
does not authorize changing the global consumer: the neighborhood
estimate and the other source/carrier cases have not been supplied.

## 5. Approaching finite families and complete tails

No finite family is assumed to attain an infinite geometric budget.
To prove(1), suppose a sequence with the stated parameter and
carrier limits violates its claimed upper limit. Each individual
original source or test label has finitely many residue choices,
plus absence. A diagonal subsequence makes every fixed label
eventually constant. Pure3, raw35 and pure7 forbidden unions have
uniform geometric tail bounds obtained by summing reciprocal
moduli; their indicators therefore converge in L1. The same is
true of the full357 forbidden union. Pure7 normalization is bounded
away from zero by5/6.

Source parameters and actual surviving masses pass to the limiting
label family. The carrier mixture is a convergent positive cap sum;
concentration on(0,1) makes each fixed shallow carrier use that pair
in the limit. Linear test tails are uniformly integrable here:
the contribution of labels outside any finite exponent box is
bounded by(6/5) times the corresponding sum of reciprocal357
moduli, which tends to zero. Finite test sums are bounded functions,
so their integrals converge by the L1 convergence of the source.
Consequently the complete test integrals converge as well.

The limiting countable family satisfies exact endpoint saturation
and all hypotheses used in sections1–4. It would contradict(7).
This proves the sequence statement for arbitrary changing test
residues, with all exponent tails retained. It supplies no explicit
error as a function of distance from the endpoint.

## 6. Independent arithmetic checks and a finite-scope counterexample

[The standard-library checker](../frontier/endpoint_linear_numerator.py)
reconstructs both endpoint matrices, the four cap improvements, the
complete geometric sums, and the live profile49 direction and old
margin from its hash-pinned logical certificate. Its comparisons use
exact rational arithmetic and remain active under Python -O.

It also constructs the actual finite sources of profile50 at
heights3 and4 and computes the supremum over all independently
labelled original357 linear tests on each fixed source. This is
not a truncated test search. For a source periodic in3^N and5^N,
the mass of a finer cylinder scales exactly with its additional
depth. The complete test tails are therefore included by multiplying
the a=N boundary by3/2 and the b=N boundary by5/4. Independent test
labels can attain their separate cylinder maxima simultaneously.

For these source families, write

    u_N=(5+7^(-N))/6,
    kappa_N=(1-7^(-N))/(5+7^(-N)).

If g_N is the number of active old carrier groups, the true
old-coordinate surviving measure is

    (1-kappa_N*g_N)*Lambda_N.

All positive-seven test labels can use the unused first-seven slot4. Thus their total
optimal contribution is exactly the raw35 all-test norm divided
by6*u_N. This also includes every positive-seven test depth.

The exact certified full357 suprema are30957413/46332000 at N=3
and37645409/60030000 at N=4, respectively0.66816483208... and
0.62710992837.... The former is strictly larger than
1157/1800, so it is a genuine counterexample to claiming(7) for all
finite sources without the endpoint qualification. These fixed-source
suprema do not determine the general endpoint optimum.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_linear_numerator.py --check
```

The checker is read-only unless `--output PATH` is supplied. The
[certificate](../certificates/source_norms/endpoint_linear_numerator.json)
stores the exact rational outputs. The arbitrary-family geometry,
saturation argument, and passage to limits are the ordinary proof
above; the finite checks do not replace them.
