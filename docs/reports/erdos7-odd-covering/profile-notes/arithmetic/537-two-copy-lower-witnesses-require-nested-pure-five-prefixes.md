# Two-copy lower witnesses require nested pure-5 prefixes

For a finite actual family on Q={5,7,11,13,17,19}, with at most two
fixed original classes at each nonunit numerical modulus, let V be its
complete survivor and define

    q_d(nu)=max_a nu([a]_d),
    R_Q(nu)=sum_(nonunit Q-smooth d) q_d(nu).

The query sum includes every height and one maximum per numerical label.
Original multiplicity affects deletion costs, not the number of queries.
If R_Q(nu)>=r>257/51 for every probability supported on V, then its pure-5
classes must have the following geometry: both modulus-25 originals lie
inside one surviving mod-5 root P; both modulus-125 originals lie inside
one live mod-25 cell C; and C lies inside P. The other two surviving
mod-5 roots each retain pure-survivor Haar mass at least49/250.

These are ordinary mathematical deductions and exact rational checks.
They refine the actual-family necessary conditions in
[report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md),
not its universal bound on the remaining nested case. They do not solve
unrestricted Erdős#7. In particular, the two-copy Q interface is distinct
from the seven-prime G interface of report534; the extra transport
conditions in [report536](536-ternary-conditioning-preserves-a-joint-query-and-entropy-boundary.md)
cannot be omitted when connecting them.

## Keep the actual pure survivors and all higher original depths

Write H for product Haar probability. Report348 NC proves that a strict
all-laws lower witness has exactly two original pure cylinders at each
of5,25,125 and7,49. The six displayed5-power cylinders are pairwise
disjoint within that coordinate. Hence two mod-5 roots are deleted,
leaving three roots. Let S5 and S7 be the complete actual pure-prime
survivors, with every higher original still present. The entire possible
pure-5 deletion above depth3 has mass at most

    sum_(e>=4)2/5^e=1/250.                         (NP1)

Overlap can only reduce this deletion. Also H7(S7)>=2/3. Use normalized
Haar rho7 on S7, so q_(7^e)(rho7)<=3/(2*7^e) and R7(rho7)<=1/4.

The constructions below each choose one actual rho5 on all of S5,
independently of the later queries. Start from the single probability
rho5 tensor rho7. Remove the actual mixed5^a7^b originals once and then
apply the four actual11,13,17,19 kernels of report348 once. There is no
intermediate normalization. All original phases remain globally fixed.
Only the final surviving subprobability is normalized.

## A comparison depending on the first two 5-adic levels

Suppose the chosen rho5 obeys simultaneous bounds

    q_5(rho5)<=q1, q_25(rho5)<=q2,
    q_(5^e)(rho5)<=K/5^e for e>=3,
    0<=K/125<=q2<=q1<=1.

Then R5(rho5)<=q1+q2+K/100. The actual initial mixed deletion is at
most2*R5(rho5)*R7(rho7), so the initial mass is at least

    a0=1-(q1+q2+K/100)/2.                          (NP2)

The conditional convex comparison cited in report348 CP4 and used there
with exponent-dependent caps in RC2 gives the auxiliary factor

    Pr(N5=1)=1-q1,
    Pr(N5=2)=q1-q2,
    Pr(N5=3)=q2-K/125,
    Pr(N5=n)=4K/5^n for n>=4,
    E N5=1+q1+q2+K/100.

For7 use Pr(N7=1)=11/14, Pr(N7=n)=9/7^n for n>=2 and E N7=5/4.
The comparison factors are independent; the actual survivor law is
preserved by its conditional kernels and is not assumed independent.

The four later stages use

    (q,t_q,C_q)=(11,2,5/3),(13,2,3/2),(17,4,2),(19,4,9/5).

For the auxiliary product M of the preceding factors, its stage loss is
at most[2/(q-1-2t_q)]E(M-t_q)_+. After that stage append the factor with
Pr(N_q=1)=1-C_q/q, Pr(N_q=n)=C_q*(q-1)/q^n for n>=2 and mean
1+C_q/(q-1). Define

    alpha=a0-sum_(four stages)[2/(q-1-2t_q)]E(M_old-t_q)_+,
    Phi=E(M_final-3)_+.

The full means retain the infinite tails. Only product atoms1,2,3 need
explicit convolution, since

    E(M-t)_+=E M-t+sum_(m<t)(t-m)Pr(M=m).          (NP3)

The same actual final subprobability lambda satisfies lambda(1)>=alpha
and lambda(L-1)<=2*lambda(1)+Phi for every finite complete query L.
When alpha>0, normalizing this one lambda yields

    R_Q(nu)<=2+Phi/alpha.                         (NP4)

Countable query completion follows from the finite first moments and
monotone convergence. No original or query height cutoff is imposed.

The exact convolution is affine in(q1,q2,K). With coefficient order
(constant,q1,q2,K), it gives

    alpha coefficients = (453101833983971/491495438353920, -35365645456019/32766362556928, -614089/339456, -3155821/169728000),
    Phi coefficients   = (6704874615181/20853247134720, 25234196718989/20853247134720, 6704249/4299776, 2079/102400).

For T=257/51 put gap=(T-2)*alpha-Phi. The three geometrically constructed
inputs below have alpha>0 and gap>0. Their exact paired values are:

    Separated modulus-25 roots:
      (q1,q2,K)=(1/3, 2/21, 50/21),
      alpha=339671304653243/982990876707840,
      Phi=115325650801759/125119482808320,
      gap=1550057836318121593/12065230020712028160,
      2+Phi/alpha=3433952691451381579/735728045878924338.

    Separated modulus-125 cells:
      (q1,q2,K)=(40/103, 8/103, 250/103),
      alpha=1528798555834581/4821336204805120,
      Phi=196755332039291/204560424273920,
      gap=110128877501532471/59177080577778042880,
      2+Phi/alpha=5555770599937749911/1103792557312567482.

    Common modulus-125 cell outside P:
      (q1,q2,K)=(14/37, 3/37, 100/37),
      alpha=5756722437366853/18185331219095040,
      Phi=741240614045003/771570143984640,
      gap=936539976329900629/669620266149517562880,
      2+Phi/alpha=20926398728761551783/4156353599778867866.

Their respective query bounds are approximately4.6674212172,
5.0333466765 and5.0347975037, all strictly below257/51. The comparisons
use their own matched numerator and denominator under one actual law.

## The modulus-25 classes must share a mod-5 root

Suppose they lie in different surviving roots. In any surviving root r,
there is at most one25-class, at most two125-classes and higher pure
mass at most1/250. Therefore its complete pure-survivor mass satisfies

    s_r>=1/5-1/25-2/125-1/250=7/50.

Give each of the three roots probability1/3 and use normalized Haar on
its actual survivor. This rho5 has q1=1/3 and every depth-e cylinder
for e>=2 has mass at most1/[3*(7/50)*5^e]. It therefore satisfies the
first input(q1,q2,K)=(1/3,2/21,50/21). Its density on each live root is
1/(3s_r)>=5/3, and it has full support on S5.

The first row of(NP4) contradicts the strict all-laws lower premise.
Thus both25-classes lie in one surviving mod-5 root P.

## The modulus-125 classes must share a live mod-25 cell

There are now thirteen live mod-25 cells: three in P and five in each
other surviving root. The125-classes lie in live cells by NC disjointness.
Suppose they lie in different cells. Before higher pure deletion, those
two cells each retain4/125, and the other eleven each retain1/25.

Let t_j be each cell's COMPLETE actual pure-survivor mass, tau=4/125,
a_j=min(t_j,tau) and A=sum_j a_j. All t_j are positive. If delta_j is
the effective higher pure deletion in cell j, then
min(t_j,tau)>=tau-delta_j. Since sum_j delta_j<=1/250,

    A>=13*(4/125)-1/250=103/250.

Give cell j probability a_j/A and use normalized Haar on its actual
survivor. Every root contains at most five live cells, so

    q1<=5*tau/A<=40/103,
    q2<=tau/A<=8/103,
    density in cell j=a_j/(A*t_j)<=250/103.

These are the second input's simultaneous all-depth bounds. The law
has full support on S5. Since t_j<=1/25 and A<=52/125, its density is
at least(4/5)/(52/125)=25/13>1 everywhere on S5.

The second row of(NP4) contradicts the lower premise. Hence both125
originals lie in one live25-cell C.

## The common cell must lie inside P

Suppose C lies in one of the other two surviving roots. Its complete
pure-survivor mass is at least1/25-2/125-1/250=1/50. Every other live
cell has mass at least1/25-1/250=9/250.

Give C weight2/37. In the other five-cell root give one arbitrary cell
weight2/37. Give each of the remaining eleven cells weight3/37. Within
each cell use normalized Haar on its actual survivor. The weights sum
to one. Root probabilities are14/37,14/37,9/37; every cell has mass at
most3/37. The largest possible density is bounded by

    (2/37)/(1/50)=100/37

in C. Every other cell has density at most(3/37)/(9/250)<100/37. This
proves the third simultaneous input(q1,q2,K)=(14/37,3/37,100/37).
Its density is at least(2/37)/(1/25)=50/37>1 throughout S5.

The third row of(NP4) contradicts the lower premise. Thus C lies in P.
All three constructions have positive density on the complete pure
survivor; rho7 and each actual later row also have density at least1
on their survivors. Therefore their final laws have full actual support.

In this remaining geometry the listed pure deletion in P is2/25+2/125,
and all higher pure deletion is at most1/250. Consequently

    1/10<=H5(S5 intersect P)<=13/125,
    H5(S5 intersect r)>=49/250 for either other surviving root. (NP5)

The nested objects here are the containing prefixes P and C. The six
forbidden5-power cylinders themselves remain pairwise disjoint.
These are necessary conditions, not a lower witness or a proof of the
query target on the remaining nested layout.

## Exact disjoint mixed packing prevents a uniform overlap rebate

[Report538](538-near-maximal-mixed-packing-preserves-the-anchor-query-hinge.md)
also rules out a rebate obtained only by removing the mixed union from
the maximal old-query hinge: a transposed packing leaves every maximizing
anchor query untouched and removes only load1. This does not show that
the later actual fibre-loss bounds are sharp.

The nested layout does not force the mixed5^a7^b originals to overlap.
At finite pure heights H5,H7 choose, for p=5,7,

    p^(e-1) mod p^e and2*p^(e-1) mod p^e,  1<=e<=Hp.

Their least-significant-digit-first prefixes are0^(e-1)1 and0^(e-1)2.
For H5>=3, the25-classes share root0 mod5, the125-classes share cell
0 mod25, and roots3,4 mod5 have no pure deletion.

For each1<=a<=A and1<=b<=B choose two fixed CRT originals at5^a7^b:

    (3*5^(a-1) mod5^a, 3*7^(b-1) mod7^b),
    (4*5^(a-1) mod5^a, 3*7^(b-1) mod7^b).

The5-prefixes0^(a-1)3 and0^(a-1)4 are pairwise disjoint. At a fixed
5-prefix the7-prefixes0^(b-1)3 are pairwise disjoint. Every mixed
rectangle avoids every pure original. Thus the actual mixed union is
pairwise disjoint and entirely inside the complete pure survivor, with
exact raw Haar mass

    (1/12)*(1-5^(-A))*(1-7^(-B)).                  (NP6)

This tends to1/12. The pure survivor masses are
w5=(1+5^(-H5))/2 and w7=(2+7^(-H7))/3. Under their normalized product
Haar law the mixed union has mass(NP6)/(w5*w7), tending to1/4 as all
four heights increase.

At H5=H7=A=B=4 the raw mass is4992/60025 and the normalized mass is
124800/501113. The pure deficits are1/1250 and1/7203. As all heights
increase these deficits tend to zero, so they eventually lie in NC's
strict joint deficit region. Adding one nonzero arbitrarily deep pure
class at each of11,13,17,19 gives an actual six-prime input with the
same5/7 geometry and a surviving all-zero point. This embedding does
not assert an all-laws lower witness.

At the terminal envelope(q1,q2,K)=(2/5,2/25,2), the new ratio(NP4)
equals the retained PA bound

    B_star=28165018706892770299/5469152872511772242>257/51.

If the later PA loss and query ledger is held fixed, repairing its
terminal gap only by a smaller RAW mixed union charge would require
saving at least

    6168733163201163811/1650097635185615616000

from1/12. Formula(NP6) rules out any height-uniform positive saving
based only on two-copy multiplicity, the forced nested pure tree, the
two lightly deleted roots or mandatory rectangle overlap. For every
fixed mixed inventory in this construction its union bound is exact.

This does not exclude changing the initial probability, retaining actual
query phases, or a joint inequality in which near-disjoint mixed packing
pays an offsetting later loss or query cost. Such a coupled estimate, or
another construction on the remaining nested layout, is still needed.

## Exact arithmetic scope

The [consumer](../../frontier/cover-geometry/two_copy_nested_prefix.py)
reads the pinned [PA input](../../frontier/cover-geometry/two_copy_pure_anchor.json).
Its [result](../../frontier/cover-geometry/two_copy_nested_prefix.json)
retains the affine coefficients, one shared low-atom convolution, all
three matched positive-mass and query comparisons, and the fixed packing
arithmetic. All59 checks passed. Infinite tails are included analytically
through the full first moments; no finite original-height enumeration
or constant-cap grid is used to prove the arbitrary-height statements.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_copy_nested_prefix.py
```
