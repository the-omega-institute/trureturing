# A mixed divisibility chain has a moment bound; overlapping chains do not factor

An irredundant chain of mixed numerical labels admits a precise extension of report534's one-prime moment. Its cofactor dilutes the moment by its actual cylinder mass. The extension uses the same entropy law G from report530. It cannot be multiplied into an overlapping pure-chain estimate: an explicit irredundant family with only one pure chain and one mixed chain has unbounded joint exponential moments. A twelve-label instance supplies this failure even when all displayed query phases are the unique maximizing phases of one law in G.

The statements are ordinary mathematics and fixed rational checks. They do not settle the remaining shallow-mixed query sum below51863873/25500000 or unrestricted Erdős#7.

Use P={3,5,7,11,13,17,19}, product Haar probability H, alpha=7235955529/6075000000000, Lambda=1/alpha, A=212731/110592 and T=565/51. The entropy class and complete numerical query sums are those of [report534](534-one-entropy-budget-controls-every-pure-prime-chain.md).

## A sharp moment bound for an irredundant numerical divisibility chain

Let3<=d1<...<ds be odd P-smooth numerical labels, with d_i dividing d_(i+1). Suppose the original cylinders C_i at these numerical labels belong to an irredundant actual core. They are pairwise disjoint: if two meet, divisibility forces the finer cylinder to be contained in the coarser one, contradicting irredundancy of the finer original.

For arbitrary query cylinders A_i at the same labels, define f=sum_i1_Ai. Expanding exp(f) and using the disjoint originals gives

    integral_(outside union C_i)exp(f)dH
       <=1+sum_(i=1 to s)[(e-1)*e^(i-1)-1]/d_i,
    e=exp(1).                                      (MC1)

Indeed every nonempty query intersection whose largest index is i has mass at most1/d_i. Its expansion coefficients sum to(e-1)*e^(i-1). On the removed original union the exponential is at least1, and its disjoint mass is sum_i1/d_i.

The bound is sharp for a full chain. Set all A_i=[0]_(d_i). Set C1=[1]_(d1), and for i>=2 set C_i=[2+d_(i-1)]_(d_i). The originals are pairwise disjoint: modulo a smaller d_i each later original is2, whereas its own earlier original is2+d_(i-1). All originals lie outside the query root0 modulo d1, using roots1 and2. Thus every intersection upper bound and every removed unit contribution is attained.

## Fixed cofactor: a mixed extension of the pure moment

Fix p in P and an odd P-smooth integer m>=1 coprime to p. Consider occupied labels m*p^j for j in E subset{1,...,n}, excluding any inadmissible unit label. For m>1 these are mixed labels. Define M_(p,n) as in report534:

    M_(p,n)=sum_(k=0 to n-1)(p-1)*e^k/p^(k+1)
              +e^n/p^n-sum_(j=1 to n)p^(-j).

The same expansion, and the monotonic numerical completion of missing depths, give

    integral_(outside this original chain)
           exp(sum_(j in E)1_Aj)dH
      <=1+(M_(p,n)-1)/m.                          (MC2)

The1/m factor belongs to the complete cofactor cylinder, including its actual phase. It is not a claim that arbitrary p-fibre projections are disjoint. The full-depth case is sharp by(MC1), or by fixing the cofactor root of every query and original and using report534's disjoint p-adic red comb outside the blue p-root0.

Since e<p, the infinite-depth uniform limit is finite:

    M_(p,infinity)=(p-1)/(p-e)-1/(p-1),
    B_(m,p)=1+(M_(p,infinity)-1)/m.                 (MC3)

Every finite occupied depth inventory, at any heights, satisfies the same bound B_(m,p). This does not say that the infinite limit improves a particular finite-prefix-plus-tail numerical choice.

## What this pays under one law in G

Let M0 be the actual irredundant core, U its complete survivor, and G the nonempty class

    nu supported on U, nu<=Lambda H,
    R_unused(nu)+D_H(nu)<=log Lambda.

Choose the query cylinder at each selected mixed-chain label to maximize q_d(nu), all under this one nu. Since U avoids the selected chain, the restricted-U entropy inequality and(MC2) yield

    R_unused(nu)+sum_(selected chain labels d)q_d(nu)
       <=log Lambda+log[1+(M_(p,n)-1)/m].           (MC4)

One may use B_(m,p) instead for a finite chain at arbitrary heights. This holds for every nu in G. Other occupied labels are not paid by(MC4).

If selected chains have pairwise disjoint prime supports, the corresponding functions and forbidden sets depend on disjoint Haar coordinates. Their moments can then be multiplied before applying the entropy inequality, paying their sum of query costs with one entropy cancellation. Pure-chain blocks on coordinates outside these supports can be included in the same product. All unpaid occupied labels remain explicit.

Overlapping prime supports do not satisfy this factorization hypothesis. Adding separate instances of(MC4) gives two copies of log Lambda and R_unused; it does not yield the estimate with one copy of that budget. The counterexample below shows that even a pure3 chain and one5-times-3 chain cannot be multiplied as if their boundary data were independent.

[Report540](540-pivot-layer-multiplicities-control-one-entropy-budget.md) gives a different sufficient composition: retain each mixed query's multiplicity in its pivot-prime layer, bound each conditional moment uniformly and integrate in reverse pivot order. It cancels one entropy budget without asserting independence of the overlapping query blocks. Keeping the full nonconstant conditional weights needs another weighted estimate.

## An actual two-chain family at arbitrary height

For every n>=1 use the2n distinct odd labels

    3^j and5*3^j,       1<=j<=n.

Define the pure originals

    C1=[1]_3,
    C_j=[2+3^(j-1)]_(3^j),       j>=2.

Define mixed originals D_j by one globally fixed CRT phase each:

    D1: x=2 mod3 and x=0 mod5,
    D_j: x=3^(j-1) mod3^j and x=0 mod5,   j>=2.

Each class has a private integer. Resolve the3-coordinate modulo3^n. For C1 use its root1 and choose the5-root1. For C_j, j>=2, use the complete3-residue2+3^(j-1) and5-root1. For D1 use complete3-residue2 and5-root0. For D_j, j>=2, use complete3-residue3^(j-1) and5-root0. The comb residues exclude every competing class; CRT realizes these conditions as integers. Thus the entire family is an irredundant actual core.

The pure originals are disjoint and have total mass sum_(j=1 to n)3^(-j). D1 meets the pure union precisely on the5-root0 parts of the C_j with j>=2. The remaining D_j are disjoint, lie in3-root0, and meet no pure original. Their additional masses cancel that D1 overlap, leaving total additional mixed mass1/15. Therefore the complete actual survivor has

    h_n=H(U_n)=1-sum_(j=1 to n)3^(-j)-1/15
               =13/30+1/(2*3^n).                  (MC5)

All non3/non5 coordinates remain free.

Query phase0 at every occupied label. The cylinder[0]_(5*3^n) lies in U_n and has load2n. Hence

    integral_(U_n)exp(sum_all_2n_queries1_A)dH
       >=e^(2n)/(5*3^n).                          (MC6)

This diverges as n increases, since e^2>4>3.

By contrast each chain separately has a uniform finite moment bound. The exponential series gives e>8/3. Bounding the tail from degree4 by(1/24) times sum_(k>=0)4^(-k)=1/18 gives e<49/18<11/4. Therefore

    M_(3,infinity)<15/2,
    B_(5,3)<23/10,
    M_(3,infinity)*B_(5,3)<69/4.                   (MC7)

At n=8 all16 original labels are at most32805<10^9, while

    e^16/(5*3^8)>(8/3)^16/(5*3^8)>100.            (MC8)

Thus a numerical factorization failure already occurs entirely below the shallow cutoff; it is not caused only by arbitrarily deep labels.

This family itself has an inexpensive common law. Its normalized survivor Haar law rho_n satisfies

    R_P(rho_n)<=A/h_n<(39/20)/(13/30)=9/2<T,
    D_H(rho_n)=log(1/h_n)<log(30/13)<1.

Its density is less than30/13<Lambda, and

    R_unused(rho_n)+D_H(rho_n)<11/2<6<log Lambda.

So rho_n lies in G. Here log Lambda>6 follows from Lambda>800>3^6>e^6. The huge moment does not refute the query target. Phase0 need not be a maximizing phase for rho_n; the next fixed instance addresses that additional constraint.

## A fixed G-law whose maximizing phases exhibit the same failure

Take n=6, N=5*3^6=3645 and h=h_6. Let mu be normalized Haar on[0]_N, which is contained in U_6, and define

    nu=(9/10)*rho_6+(1/10)*mu.                     (MC9)

Its density is at most

    (9/10)*(30/13)+(1/10)*3645=9531/26<800<Lambda.

The occupied reciprocal sum is

    lambda=(6/5)*sum_(j=1 to6)3^(-j)=728/1215>59/100.

Therefore

    R_unused(rho_6)<(39/20-59/100)/(13/30)=204/65.

For mu, the complete query generating factors are15/2 on the3-coordinate,9/4 on the5-coordinate, and(8/15)*(A+1) on all other coordinates. Thus

    R_P(mu)=9*(A+1)-1=9*A+8.

Every one of the12 occupied labels has q_d(mu)=1, so

    R_unused(mu)=9*A-4<271/20.

Convexity of query maxima and relative entropy gives

    R_unused(nu)<(9/10)*(204/65)+(1/10)*(271/20),
    D_H(nu)<(9/10)*1+(1/10)*9=9/5,

where log3645<9 follows from exp(9)>(8/3)^9>3645. Consequently

    R_unused(nu)+D_H(nu)<15547/2600<6<log Lambda.    (MC10)

The mixture is therefore one valid member of the same class G and has full actual survivor support through its rho component.

For either occupied label d=3^j or d=5*3^j, the all-zero cylinder avoids all pure originals and all mixed originals of depth at most j. Its only deletions are the deeper mixed comb cylinders, so

    H(U_6 intersect[0]_d)
       =1/d-(1/5)*sum_(ell=j+1 to6)3^(-ell).

For every nonzero phase b modulo d, mu([b]_d)=0 and rho_6([b]_d)<=1/(d*h). It follows that

    nu([0]_d)-nu([b]_d)
       >=1/10-(9/(50*h))*sum_(ell=j+1 to6)3^(-ell)
        >1/10-9/130=2/65>0.                       (MC11)

Here the future reciprocal sum is at most1/6 and h>13/30. Phase0 is thus the unique maximizing phase at every occupied label under this same nu.

Nevertheless its associated Haar exponential moment satisfies

    integral_(U_6)exp(sum_all_12_maximizing_queries1_A)dH
       >=e^12/3645>(8/3)^12/3645>69/4.             (MC12)

This exceeds the product of the two separate chain ceilings in(MC7), even with irredundancy, actual shallow labels, simultaneous maximizing phases, full survivor support and membership in G all enforced.

## What is constructive and what remains unresolved

The positive result is a mixed-chain moment with its complete cofactor reference and a one-law entropy consumer. Prime-support disjointness is a sufficient condition for multiplying such blocks. The actual two-chain family proves that sharing a prime can invalidate that multiplication, including at the actual maximizing phases of a law in G. Neither global irredundancy nor separate sharp chain bounds remove the missing joint relation.

Even before multiplication, global irredundancy need not pass to projected pure disjointness. The actual originals0 mod15 and0 mod63 have private integers15 and63. On the common cofactor fibre x5=0 mod5 and x7=0 mod7, their3-adic restrictions are nested0 mod3 and0 mod9. The globally fixed query phases10 mod15 and28 mod63 restrict to1 mod3 and1 mod9. Their exact restricted moment is(3+2e+e^2)/9, whereas the incorrectly applied disjoint-red bound M_(3,2) is(2+2e+e^2)/9. The excess1/9 is the twice-subtracted red intersection. This example changes the cofactor between5 and7; it does not contradict the fixed-m hypothesis in(MC2).

The remaining target is still to find one nu in G with total shallow mixed occupied core query sum below51863873/25500000, or to develop another valid route. These counterexamples concern proposed moment compressions, not existence of such a law. They do not exclude joint phase-aware estimates, conditional measures or other retained interactions between overlapping supports.

The [fixed rational consumer](../../frontier/cover-geometry/mixed_chain_moments.py) and its [result](../../frontier/cover-geometry/mixed_chain_moments.json) verify the displayed n6/n8 comparisons and entropy margins; all20 checks passed. The general cylinder, irredundancy and maximizing-phase statements are proved above. These scalar checks do not enumerate a CRT period or establish an arbitrary-height theorem by enumeration.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_chain_moments.py
```
