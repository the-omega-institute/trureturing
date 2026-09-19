[Index](../marked_head_profile.md) · [Endpoint bound](59-endpoint-linear-source-deletion-bound.md) · [Common deleted measure](57-common-deleted-measure-coupling.md)

# An explicit neighborhood of the off-diagonal linear endpoint

This is an ordinary mathematical bound for arbitrary finite original-label
families in the effective9 branch of profiles48--59. It is not Lean verified
and is not a new global K certificate. All test residues remain independent.

Let Lambda, eta, n, d, S and D be the actual source data and normalized
survivor mass of profiles48 and57. Use cell roots (0,0,1,1,1), and set

    eta*=(1/18,1/9,1/9,1/9,1/9),
    n*  =(1/24,1/12,1/36,1/24,1/18),
    d*  =(3/4,3/4,1/4,1/2,1/2).

These are vertex404; s*=1/4 and D*=3/20. Define nonnegative deviations

    delta_s=(z-3/4)+(1/4-alpha1)+(1/4-beta2),
    delta_L=1/72-late3,
    tau=||eta-eta*||_1+||n-n*||_1+||d-d*||_1+delta_s+delta_L,
    epsilon=S-D.

The shallow carrier distribution pi is the actual distribution of the
cofactor3/cofactor9 carrier pair, weighted by 5*u_e at seven depth e,
where u_e=6/(5*7^e). Absent labels give the empty carrier. Thus sum pi=1,
including the infinite absent-label tail. Put A=(root0,cell1) and

    kappa=1-pi_A.

For every original357 linear test Z, with unit term1 and independently
chosen residue for each modulus, if

    tau<=1/1000, epsilon<=1/10000,                 (N1)

then

    integral_survivor Z
      <=S+887/1800+34*tau+608*epsilon+3*kappa+2*sqrt(epsilon)
      <=1157/1800+36*tau+609*epsilon+3*kappa+2*sqrt(epsilon). (N2)

Both lines remain valid with the sharper R3(epsilon)+R5(epsilon)
from (N12)--(N13) in place of 2*sqrt(epsilon). Those two tails have
exact finite-segment-plus-geometric formulas for every positive
epsilon and can be used directly by a later quantitative consumer.

Here epsilon>=0 follows from the inherited mass cap. No limitation on
the finite exponent heights is imposed. The same estimates hold for
complete countable label families whenever the actual measures are
defined, by the nonnegative complete geometric bounds below.

For the actual live49 direction40, f(v)=v and barrier6, (N2) implies

    6*S-integral_survivor Z
      >=463/1800-42*tau-608*epsilon-3*kappa-2*sqrt(epsilon). (N3)

Let m40(theta;c) denote exactly the old conditional margin function
defined in profile49. On the nonzero neighborhood

    tau<=1/1000, epsilon<=1/1000000, kappa<=1/1000, (N4)

the right side of (N3) exceeds sum_c pi_c*m40(theta;c) by more than1/100.
This is a strict quantitative improvement of that one inherited linear
direction. It does not assert an improvement of every other direction,
of the whole numerator, or of a global worst-case comparison.

The carrier deviation is material: the two source root masses tie at
vertex404. Source parameters and epsilon alone do not select root0.

## 1. Every discarded capacity is paid by epsilon

Let delta be the actual old-coordinate deleted measure and

    V=sum_i u_(e_i)*1_(C_i)*Lambda

the complete virtual deleted measure over present nonunit old35
cofactors at positive-seven depths. Write cap_i for the inherited
individual old35 cap. Include absent labels with Lambda(C_i)=0.
Profile57 gives a nonnegative decomposition

    epsilon=sum_i u_(e_i)*(cap_i-Lambda(C_i))+(V-delta)(1).

Thus every selected group of weighted individual cap deficiencies is
at most epsilon, and 0<=V-delta has mass at most epsilon. For every
event E, delta(E)>=V(E)-epsilon. Missing labels, loss of seven cap,
and deleted-union overlap have not been omitted; the latter two are
inside V-delta.

On (N1), eta2>=1/10, h1-h0>=1/9, h>=1/2, h<=1, and
h1/(h1-h0)<=3. Here h_r is the eta mass of root r and h=h0+h1.
The inherited width simplex gives h1<=1/3 and root1 maximal.

## 2. Two source budgets force the five first slots

Write P_b,A_b,B_b for pure5, root1 alpha and cell2 beta source labels,
as five-coordinate cylinders; a misplaced or absent label contributes
zero effective mass to cell2. Partition the effective shallow union
in cell2 among these labels. Its measure is3/4-delta_s, whereas the
sum of all raw label capacities is3/4. Therefore the sum of all
nonnegative missing, overlap and mislocation deficits is delta_s.

Since delta_s<1/25, the labels P1,A1,B1,P2 are present, properly
located, and have four distinct depth1 parents except that P2 itself
is a depth2 cylinder. Indeed a missing or misplaced first label loses
1/5; omitting P2 loses1/25. Any coincidence between P2's parent and
one of the three first slots loses at least1/25. Write P,A,B for
the three full first slots.

The forbidden cofactor5 at seven depth1 must be present: its missing
weighted cap would be (6/35)*(h/5)>epsilon. Let H be its depth1 slot,
and put

    ell=h/5-Lambda(H)<=35*epsilon/6.              (N5)

The three slots P,A,B have respective losses at least h/5,h1/5,eta2/5,
each larger than ell. Also H cannot contain P2, which would give loss
at least h/25>ell. Hence H is the fifth first slot and Q, the parent
of P2, is the unique slot left after P,A,B,H.

Every forbidden cofactor5 outside H has cap deficiency at least1/100:
the four lower bounds are h/5,h1/5,eta2/5,h/25. For cofactor15, a
wrong ternary root has loss at least (h1-h0)/5; on root1 every slot
other than H has loss at least one of h1/5,eta2/5,h1/25. Missing
labels also lose at least1/100. Consequently the total seven-cap
weight of bad or missing cofactor5 labels is at most100*epsilon;
the same holds separately for cofactor15.

The correct shallow cofactor3 and cofactor9 carrier weights are each
at least(1-kappa)/5. For any old-coordinate event E, retaining these
four distinct forbidden families and then transferring V to delta
gives

    mu(E)<=integral_E w dLambda+201*epsilon+2*kappa/5,
    w=1-(1_root0+1_cell1+1_H+1_(root1 intersect H))/5,       (N6)

where mu=Lambda-delta is the surviving marginal. The error uses
Lambda(E)<=1. It will be used only for the two tests5 and15; it is
not summed over an infinite list of tests.

## 3. A quantitative version of the endpoint source-slot table

Order P1,A1,B1 first when assigning the effective shallow union in
cell2 to its labels. Every assigned depth>=2 piece therefore avoids
P,A,B. Each of the three deep families has raw budget1/20 and loses
at most delta_s from its assigned budget. The total shallow assigned
mass in H is at most ell/eta2, since its deletion on cell2 alone
contributes eta2 times that mass to ell. Hence in Q the assigned
deep budget of each family is at least

    1/20-delta_s-ell/eta2.

More generally any subcollection of the three families loses at
most delta_s+ell/eta2 in total, because both deficits were total
deficits. These assigned sets are pairwise disjoint. The pure5
pieces are also present on cells0,1, and the pure5 and root1-alpha
pieces are present on cells3,4. Before late deletion, the actual
cell-slot masses consequently have the following entrywise upper
table, divided by the current eta_l:

    cell       P    A      B       Q                 H
    0,1        0    1/5    1/5     3/20+beta_err      1/5
    2          0    0      0       1/20+beta_err      1/5
    3,4        0    0      1/5     1/10+beta_err      1/5

where beta_err=2*delta_s+ell/eta2 is a conservative common error.
Other source deletions only lower entries in this upper table.

Partition actual additional late deletion in cell3 among its original
labels, with assigned q_(a,b)<=c_(a,b)=3^-a*5^-b. Then

    sum_(a>=3,b>=1)(c_(a,b)-q_(a,b))=delta_L.

The full b=1 raw budget is1/90. A b=1 label outside cell3 contributes
zero. Within cell3 the slots P,A are already deleted, and a label in
Q loses at least1/5 of its raw budget to P2. The total additional
late deletion in H is at most ell. Therefore, if x is additional
late deletion on cell3 times B,

    1/90-5*delta_L-ell<=x<=1/72.                 (N7)

For the lower bound, split b=1 labels into those assigned to B,
those in H, and the remaining labels. In the remaining group,
c<=5*(c-q); the H group's total raw budget is at most ell plus
its assigned deficits. Subtracting the B group's own deficits
from its raw budget gives the lower bound in (N7). This counts
all missing and infinite-tail labels as well as overlaps. The
remaining late deletion in Q is
at least1/72-delta_L-x-ell.

Put x'=max(x,1/90). Then x' belongs to[1/90,1/72] and
0<=x'-x<=5*delta_L+ell. Compare the actual source-slot matrix with
profile59's exact endpoint matrix at x'. The sum of positive
entrywise errors is at most

    ||eta-eta*||_1+h*beta_err+delta_L+ell+(x'-x)
      <=9*tau+70*epsilon
      <=14*tau+76*epsilon.                      (N8)

The first term bounds all raw table changes from eta, whose row
coefficient sums are at most1. The Q correction costs h*beta_err;
late-Q uncertainty costs delta_L+ell. Replacing x by x' increases
only the B upper-entry error by x'-x. In the last inequality use
eta2>=1/10, h<=1 and (N5). In particular this comparison does not
assume that the non-endpoint source is identical to an endpoint
source or that its late labels are disjoint.

The multiplier w in (N6) is between0 and1. Profile59's endpoint
column and root-column maxima are1/18 and1/25 for every x' in that
interval. Combining (N6) and (N8), for arbitrary test residues,

    mu(test5) <=1/18+14*tau+300*epsilon+kappa,
    mu(test15)<=1/25+14*tau+300*epsilon+kappa.    (N9)

## 4. Complete positive-five deletion and arbitrary ternary tests

Let epsilon0 and epsilon1 be the total weighted cap deficiencies
of all forbidden cofactors5^b and3*5^b, respectively, b>=1,e>=1.
Then epsilon0+epsilon1<=epsilon.

For the first family, the difference between the full product mass
eta(T)*5^-b and Lambda on any ternary set T times the actual five
cylinder is at most its global cap deficiency. Missing labels use
their entire cap. Thus its virtual deletion on any T is at least

    eta(T)/20-epsilon0.

For the second family, correctly rooted labels have the same
argument on root1. A wrong-root label loses at least
(h1-h0)*5^-b from its cap, whereas the desired mass on any subset
of root1 is at most h1*5^-b. The ratio is at most3 on (N1).
Including missing labels, this family's virtual deletion on T is
therefore at least eta(T intersect root1)/20-3*epsilon1. This is
a label-by-label comparison for any fixed T; the actual wrong-root
label is not moved to root1.

Together with the shallow cofactor3/cofactor9 families and the
V-to-delta transfer, this proves

    mu(T)<=Lambda(T)-(1-kappa)/5*
                [Lambda(T intersect root0)+Lambda(T intersect cell1)]
              -[eta(T)+eta(T intersect root1)]/20+4*epsilon. (N10)

Every b and e has been summed, using sum_b5^-b=1/4 and sum_e u_e=1/5.
The labels in different families keep their original independent
residues. There is no product assumption on the actual survivor.

Applying (N10) to the two ternary roots and five cells, and using
their endpoint table from profile59, gives

    mu(test3)<=11/120+2*tau+4*epsilon+2*kappa/5,
    mu(test9)<=2/45+2*tau+4*epsilon+2*kappa/5.    (N11)

For a pure3 test cylinder of depth a>=3 in cell l, use
Lambda(T)<=d_l*eta(T) and eta(T)<=3^-a. The relevant coefficients
remain nonnegative on (N1), and their endpoint maximum is11/20, so

    mu(T)<= (11/20+tau+2*kappa/5)*3^-a+4*epsilon.

The unchanged source cap also gives mu(T)<=(3/4+tau)*3^-a. Taking
the better of the two and summing every a>=3 yields

    sum_(a>=3)mu(test3^a)
      <=11/360+tau/18+kappa/45+R3(epsilon),
    R3(epsilon)=sum_(a>=3)min(4*epsilon,(1/5)*3^-a)
      <=sqrt(epsilon).                          (N12)

For pure5 test cylinders of depth b>=2, retain just the shallow
cofactor3 and cofactor9 deletion in V. Their surviving coefficient
is h-(1-kappa)*(h0+eta1)/5, whose endpoint value is4/9 and whose
increase is at most tau+2*kappa/5. The unchanged cap is h*5^-b.
Thus

    sum_(b>=2)mu(test5^b)
      <=1/45+tau/20+kappa/50+R5(epsilon),
    R5(epsilon)=sum_(b>=2)min(epsilon,(1/18)*5^-b)
      <=sqrt(epsilon).                          (N13)

These are complete tails. For epsilon>0 each R is an exactly
summable finite constant segment followed by a geometric tail.
Alternatively min(x,y)<=sqrt(x*y) bounds R3 by
sqrt(4*epsilon/5)*sum_(a>=3)3^(-a/2) and R5 by
sqrt(epsilon/18)*sum_(b>=2)5^(-b/2); each coefficient of
sqrt(epsilon) is less than1. At epsilon=0 both tails are0.

## 5. Sum the disjoint test categories

The other zero-seven tests retain these complete inherited caps:

    a=1,b>=2: h1/20 <=1/60+tau/20,
    a=2,b>=1: max(eta)/4 <=1/36+tau/4,
    a>=3,b>=1: 1/72.

The unit test contributes S. Positive-seven test labels contribute
at most(s+C(theta))/5, without identifying their seven residues:
each separate label has survivor mass at most u_e*Lambda(C35).
Here

    C(theta)=R(n)+max(n)+max(d)/18+(h+h1+max(eta))/4+1/72.

On the original feasible parameter domain, |C-1/2|<=3*tau and
|s-1/4|<=tau. Hence the positive-seven part is at most3/20+4*tau/5,
and |D-3/20|=|s-C/5-3/20|<=8*tau/5.

Summing (N9), (N11)--(N13) and the remaining categories gives
baseline887/1800 in addition to S. The error coefficients are at
most34 for tau,608 for epsilon and3 for kappa. This proves the
first line of (N2). Substitution S=D+epsilon proves its second line;
using S>=3/20-8*tau/5 in 6*S-(N2 first line) proves (N3).

## 6. Compare with the actual old49 margin throughout a neighborhood

The identity cost is f(v)=v, not v-1. The complete centered source
cost is psi(v)=v-1. On the inherited feasible domain, for independent
layouts b,c in BASES the exact fixed-layout source envelope is

    U(theta;b,c)=6*s/5+C(theta)/5+sum_l n_l*(b_l-1)+max(d)/18
             +(1/5)*sum_l eta_l*c_l
             +(1/20)*max_t sum_l eta_l*t_l+1/72.  (N14)

This follows directly by summing the linear source's complete
geometric tails: its centered-five correction is0, its complete
positive-five expression is one fifth of the retained first layout
plus one twentieth of the maximal layout plus1/72, and the
independent positive-seven complement is6*s/5+C/5. It is also
checked against the current full49 implementation.

Set N=||n-n*||_1, E=||eta-eta*||_1, F=||d-d*||_1. Since
1<=b_l,c_l<=3, (N14) gives the uniform bound

    |Delta U|<=(18/5)*N+(1/15)*F+(9/10)*E<=4*tau.

For k_l=6-b_l, a_l=k_l*n_l-c_l*eta_l/5, the old conditional
cofactor expression is A_carr(a)+T, with T exactly as in profile47.
Its root/cell part uses each coordinate at most twice; the two
deep coefficients sum to1/18, and 3<=k_l<=5. Thus

    |Delta (A_carr+T)/5|
      <=2*N+F/18+(99/100)*E<=2*tau.

Taking the finite maximum over layouts preserves these uniform
Lipschitz bounds, and |Delta(6*s)|<=6*tau. Therefore

    |m40(theta;A)-4507/24300|<=12*tau.            (N15)

For any feasible theta, 0<=n_l<=eta_l<=1/9, so
-1/15<=a_l<=5/9. Every carrier sum has at most four terms with
multiplicity, whence A_carr(a) lies in[-4/15,20/9]. Consequently

    |m40(theta;carr)-m40(theta;A)|<=112/225<1/2,
    sum_c pi_c*m40(theta;c)<=4507/24300+12*tau+kappa/2. (N16)

Subtract (N16) from (N3). The guaranteed improvement is at least

    3487/48600-54*tau-608*epsilon-(7/2)*kappa-2*sqrt(epsilon). (N17)

At the corner of (N4) the subtracted error is exactly15027/250000;
the remaining positive gap is707189/60750000>1/100. Monotonicity
in the three deviations proves the strict claim throughout (N4).
The actual finite families approaching vertex404 and carrier A
from profile50 eventually enter this neighborhood; no new existence
assumption about an actual family was introduced.

This converts the endpoint result into an explicit local inequality.
Integrating it into a uniform global comparison still requires a
proof that accounts for all other parameter/carrier/slack regions;
evaluating only this neighborhood does not supply that proof.

## 7. Exact arithmetic and construction checks

The [checker](../frontier/endpoint_linear_neighborhood.py) reconstructs
the [certificate](../certificates/source_norms/endpoint_linear_neighborhood.json)
with `python3 -I -O .../endpoint_linear_neighborhood.py --check`.
It checks the cap tables and error coefficients, two independent
complete min-geometric-tail evaluations, 400 fixed-layout identity
source expressions and72 inherited conditional margins. It also
rechecks two actual finite original-label constructions, including
one complete CRT union, against their closed source formulas.

The closed formulas put the height11 construction inside (N4), with
1727 distinct original nonunit modulus labels; the large complete
period at height11 is not enumerated. The arbitrary-label geometry
and all-height validity come from the ordinary proof above, not
from these finite checks. Neither Lean verification nor a complete
global comparison is claimed.
