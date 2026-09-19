[Index](../marked_head_profile.md) · [Actual source budgets](48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Common deletion](57-common-deleted-measure-coupling.md) · [Identity comparison](66-explicit-linear-endpoint-neighborhood.md) · [Entire controlling face](72-a-linear-gap-on-the-entire-controlling-beta-face.md)

# An explicit neighborhood of both controlling beta faces

The strict identity-cost improvement of72 extends to an explicit
neighborhood of the entire source face398,410,422, with carrier(1,1).
The distance below allows unrestricted variation within its beta
triangle. For every independently labelled original357 test A,

    integral_survivor A
      <=S+233/450+34*tau+608*epsilon+3*kappa+2*sqrt(epsilon)
      <=133/200+36*tau+609*epsilon+3*kappa+2*sqrt(epsilon), (FN1)

provided tau<=1/1000 and epsilon<=1/10000. The actual signed margin
therefore obeys

    6*S-integral_survivor A
      >=131/600-42*tau-608*epsilon-3*kappa-2*sqrt(epsilon). (FN2)

For the original49 identity direction40, with the same barrier6,

    sum_c pi_c*m40(theta;c)
      <=9257/48600+12*tau+kappa/2.                      (FN3)

Consequently the improvement over that inherited margin is at least

    677/24300-54*tau-608*epsilon-(7/2)*kappa-2*sqrt(epsilon). (FN4)

On the nonzero box

    tau<=1/10000, epsilon<=1/100000000, kappa<=1/10000, (FN5)

(FN4) is at least66533407/3037500000>1/50. All statements transport
to the second controlling face616,628,640 and carrier(1,0) by the
root0-cell exchange of72.

This is an ordinary finite-neighborhood theorem, with complete
exponent tails and arbitrary original residues. It does not by itself
update the global K certificate, and has no Lean verification claim.

## 1. Distance to the full face and actual mass slack

Use the effective9 actual source variables of48: eta,n,d,z,alpha,beta,
late, raw source Lambda and normalized surviving marginal mu. Put

    deltaP=z-3/4,
    deltaA=1/4-alpha1,
    deltaB=1/4-(beta2+beta3+beta4),
    deltaL=1/72-late0,
    delta_s=deltaP+deltaA+deltaB.

All four deltas are nonnegative. The beta deletion terms are actual
additional deletion in their respective ternary cells, not a single
five-coordinate union across different cells.

For beta*=(beta2*,beta3*,beta4*) in the closed simplex

    beta_i*>=0, beta2*+beta3*+beta4*=1/4,

define the face data

    eta*=(1/18,1/9,1/9,1/9,1/9),
    d*=(3/4,3/4,1/2-beta2*,1/2-beta3*,1/2-beta4*),
    n*=(1/36,1/12,d2*/9,d3*/9,d4*/9).

Set

    tau=min_beta* [||eta-eta*||_1+||n-n*||_1+||d-d*||_1]
                   +delta_s+deltaL,
    epsilon=S-D, kappa=1-pi_(1,1).                    (FN6)

The minimum is attained because the simplex is compact and the
objective is continuous. Fix any minimizer for the estimates below;
no choice of a distinguished beta vertex is required. In particular
tau does not count movement within the face as an error.

The original complete cap formula gives |C-37/72|<=3*tau and
|s-1/4|<=tau, hence

    |D-53/360|<=8*tau/5,
    S>=53/360-8*tau/5+epsilon.                         (FN7)

As in57 and66, the original-label virtual deleted measure V satisfies

    epsilon=sum_i u_(e_i)*(cap_i-Lambda(C_i))+(V-delta)(1).

Each summand is nonnegative. Thus all selected cofactor deficiencies
and the final V-to-delta transfer can be paid by epsilon. This includes
absent labels, seven-coordinate cap loss and overlapping deletions.

## 2. One beta label controls the shallow slots near the entire face

Assume tau<=1/1000 and epsilon<=1/10000. The source labels pure5 at
b=1, root1-alpha at b=1 and a root1-beta at b=1 must be present:
otherwise the corresponding missing additional budget is at least1/5,
larger than delta_s. Write P,A,B for their first five-coordinate slots,
and L in{2,3,4} for the cell of that beta label. They are distinct;
a coincidence would similarly lose a first-label budget1/5.

The individual beta b=1 deficit is at most deltaB. This observation
will be used on cell L only. Other beta labels may lie in different
cells and may overlap its five-coordinate projection without an
assumption of global beta disjointness.

The first forbidden cofactor5 at seven depth1 is also present. Its
absence would cost (6/35)*(h/5)>epsilon. Let H be its first slot and

    ell=h/5-Lambda(H)<=35*epsilon/6.                   (FN8)

The uniform face guards give etaL>=1/10, h1-h0>=1/9, h>=1/2 and
h1<=1/3. Source losses in P,A,B are at least h/5,h1/5,etaL/5, each
larger than ell. Hence H differs from P,A,B. Denote the remaining
first slot by Q.

To quantify source mass in Q, assign the pure5 and root1-alpha union
to its original labels, putting P1,A1 first. Their assigned pieces
are disjoint in the five coordinate. The total nonnegative difference
between raw capacities and assigned masses is deltaP+deltaA. Each
deep family has raw mass1/20, so its assigned mass is at least
1/20-deltaP-deltaA; the two together have at least
1/10-deltaP-deltaA. All their deeper pieces avoid P and A.

The union of their assigned pieces inside B has mass at most deltaB:
it is a subset of the part removed before the original first-beta
label contributes on cell L, and that one label's additional deficit
pays this entire intersection. Their total assigned mass in H is at
most ell/etaL, since on cell L it contributes that amount times etaL
to the source loss ell. Therefore

    each deep family has Q mass >=1/20-delta_s-ell/etaL,
    their combined Q mass >=1/10-delta_s-ell/etaL.      (FN9)

Only the beta b=1 label was used in(FN9). No nesting, common residue
or single beta cell is required for the other labels. In particular
the resulting source-slot upper table is profile72's table for cell L,
with a common additional Q coefficient

    beta_err=2*delta_s+ell/etaL<=2*tau+60*epsilon.      (FN10)

All deeper beta deletions and late source deletions may be discarded
for this upper bound. The table then holds on every ternary subset
of each cell, because the retained P/alpha pieces have the same
five sections throughout their root. The full slot table differs
from its reference eta* upper table in total positive mass by at most

    ||eta-eta*||_1+h*beta_err<=3*tau+60*epsilon.        (FN11)

## 3. Selected forbidden labels and the two first-five test caps

Every forbidden cofactor5 not in H has a source-cap loss at least
one of h/5,h1/5,etaL/5 or h*(1/20-delta_s-ell/etaL). All are at
least1/100 under the guards. For cofactor15, a wrong root loses at
least(h1-h0)/5; on root1 a wrong first slot loses at least h1/5,
etaL/5, or h1*(1/10-delta_s-ell/etaL). These too are at least1/100.
Missing labels have their whole positive cap as loss. Thus each of
these two forbidden families has total bad seven-cap weight at most
100*epsilon.

The cofactor3 and9 labels have correct carrier weight at least
(1-kappa)/5. Keeping these four original families and then transferring
V to the actual deleted measure gives the same positive-measure bound
as66, with root1 replacing root0:

    mu<=w*Lambda+nu, nu(1)<=201*epsilon+2*kappa/5,
    w=1-(1_root1+1_cell1+1_H+1_(root1 intersect H))/5.  (FN12)

Profile72 verifies the reference column and root-column maxima for
all three possibilities L. Combining(FN11),(FN12) gives the two caps
with errors at most3*tau+261*epsilon+2*kappa/5. We use the conservative
common errors

    mu(test5)<=29/450+14*tau+300*epsilon+kappa,
    mu(test15)<=8/225+14*tau+300*epsilon+kappa.          (FN13)

The test residues are arbitrary. The slots P,A,B,Q,H describe the
source geometry; they do not impose the test residue choices.

## 4. All remaining original-test tails

The complete forbidden families5^b and3*5^b yield, for any ternary
event T, exactly the deficit argument66(N10), now with carrier(1,1):

    mu(T)<=Lambda(T)-(1-kappa)/5*
                  [Lambda(T intersect root1)+Lambda(T intersect cell1)]
                 -[eta(T)+eta(T intersect root1)]/20+4*epsilon. (FN14)

For wrongly rooted3*5^b labels, the desired root1 mass is at most
h1/(h1-h0)<=3 times the original label's cap deficiency. All sums
over b and seven depth are complete. Original labels are not moved
between roots in this argument.

The reference roots, cell maximum and deep pure3 coefficient from72
are31/360,11/180 and7/10. Their changes are bounded by2*tau for the
first two, tau for the deep coefficient, and2*kappa/5 for the carrier.
Consequently

    mu(test3)<=31/360+2*tau+4*epsilon+2*kappa/5,
    mu(test9)<=11/180+2*tau+4*epsilon+2*kappa/5,
    sum_(a>=3)mu(test3^a)<=7/180+tau/18+kappa/45+R3(epsilon),
    R3(epsilon)=sum_(a>=3)min(4*epsilon,(1/20)*3^-a).  (FN15)

The minimum in the last line uses the unchanged source cap
(3/4+tau)*3^-a as a second upper bound; the reference improvement
is1/20 per unit ternary cylinder.

For pure5 tests at b>=2, retain only the shallow root1/cell1
forbidden families. The endpoint weighted full-product coefficient
is37/90; the unchanged product coefficient is h*=1/2. Therefore

    sum_(b>=2)mu(test5^b)<=37/1800+tau/20+kappa/50+R5(epsilon),
    R5(epsilon)=sum_(b>=2)min(epsilon,(4/45)*5^-b).    (FN16)

Each R is an exactly computable finite constant segment followed by
a complete geometric tail. Both vanish at epsilon=0 and satisfy
R3(epsilon)<=sqrt(epsilon), R5(epsilon)<=sqrt(epsilon): use
min(x,y)<=sqrt(x*y), the complete geometric sums, and respectively
sqrt(1/5)<1 and sqrt(4/45)<1. The relevant sums
sum_(a>=3)3^(-a/2) and sum_(b>=2)5^(-b/2) are each less than1.

The remaining inherited sums are

    3*5^b,b>=2: 1/60+tau/20,
    9*5^b,b>=1: 1/36+tau/4,
    3^a*5^b,a>=3,b>=1: 1/72,
    positive-seven: (s+C)/5<=11/72+4*tau/5.

Together with the unit S, the baseline is S+233/450. The complete
error coefficients are at most34,608,3 on tau,epsilon,kappa.
This proves the first line of(FN1), with the sharper R3+R5 if desired.
Equation(FN7) gives the second line and the signed margin(FN2).
No error independent of a or b is summed over an infinite tail.

## 5. Comparison to the live49 margin over the full face

Fix the minimizing beta* in(FN6), and use profile72's one fixed
old layout b=(2,3,1,1,1), c=(1,2,2,2,2). Its face margin is exactly
9257/48600 for every beta*. The actual old margin is the minimum
over layouts, so it is bounded above by this layout evaluated at
the current source.

The uniform layout estimates established in66 apply without requiring
the reference point to be a vertex. The source term changes by at
most4*tau, the charged cofactor term by2*tau, and6*s by6*tau.
Hence this one layout proves

    m40(theta;(1,1))<=9257/48600+12*tau.

The same whole-carrier oscillation bound112/225<1/2 used in66 is
uniform on the feasible source domain. The correct carrier has weight
1-kappa, proving(FN3). Subtracting(FN3) from(FN2) proves(FN4).
At the corner of(FN5) the subtracted error is74451/12500000, giving
the exact strict lower bound in the opening statement. Monotonicity
in all three deviations proves the result throughout the box.

The compatible exchange of the two root0 cells transports every
source label, test label and complete cap to the other controlling
face. Under that exchange use late1, the transported eta*,n*,d*,
and kappa=1-pi_(1,0). Thus both full faces have the same constants.

## 6. Exact checks and an actual nonempty neighborhood

The [checker](../frontier/endpoint_k_face_neighborhood.py) verifies the
positive assigned Q masses and all bad-carrier lower gaps at the
worst guard corner, the complete test inventory and both geometric
tails, the original comparison constants, and the strict box gain.
The [certificate](../certificates/source_norms/endpoint_k_face_neighborhood.json)
pins the exact face result72 and the inherited identity-cost formulas.

Profile48's explicit finite398 family enters(FN5). The checker uses
its complete closed formulas, evaluates tau at the particular face
vertex398 as an upper bound on the minimized tau, and finds a witness
at height15. It independently compares the source, survivor and cap
masses at height3 with the original-label CRT-union constructor.
No huge period is enumerated at height15, and no claim of realizability
of every point of the relaxed face is made.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_k_face_neighborhood.py --check
```

Checks use the Python standard library and remain enabled under `-O`.
Default execution is read-only; only `--output PATH` writes. The
ordinary assigned-budget proof carries the all-family quantifiers.
Combining this local gain with a global concentration or interpolation
argument is a separate consumer obligation.
