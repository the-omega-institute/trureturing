[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Two incidence cycles with arbitrary original support sizes

## Statement and scope

Let a finite family of congruence classes have pairwise distinct odd
numerical moduli greater than one. Form the bipartite graph on its actual
primes and its distinct nonsingleton original prime supports, with edges
for membership. Suppose every connected component has cycle rank at most
two (edges minus vertices plus one for a connected component). Then the
family does not cover the integers.

There is a full survivor probability bounded by K times original full
CRT Haar, with K depending only on the finite incidence graph and actual
prime set, not the original exponent heights or residues. Hence the full
Haar survivor proportion is at least 1/K. The existing density-to-BBMST
restart supplies a computable unrestricted large-prime cutoff for each
fixed such head, uniformly in its exponents and residues.

This is an ordinary mathematical deduction, not a Lean theorem or a
resolution of unrestricted Erdős #7. It extends the incidence-forest and
incidence-pseudoforest constructions of
[Chapter 48](48-incidence-forests-with-arbitrary-original-heights.md) and
[Chapter 49](49-incidence-pseudoforests-with-arbitrary-original-heights.md). The proof
below treats a connected component of cycle rank exactly two; components
of smaller cycle rank use those previous constructions. It neither
changes their statements nor assumes their original sources were global
survivor marginals. Public-literature priority has not been established.

## 1. Retain both small primes and the full cyclic core

For a connected component of cycle rank two, iteratively remove leaves
to obtain its nonempty connected 2-core. Every removed component is a
tree attached at one vertex. If 3 occurs, retain its path to the 2-core.
Also retain 5 and its path to the already retained graph if 5 occurs.
Let R be this connected retained incidence graph, K its prime vertices,
and E_core its support vertices. If 3 does not occur, retaining just the
2-core suffices; the separate bound in Section 4 applies.

Leaf deletion preserves connectedness of every nonempty remaining
graph, so the 2-core is connected even for a barbell: the path between
its cycles remains. A component outside the 2-core cannot contain a
cycle or meet it twice, since either would leave another cycle in the
2-core. It is therefore a singly attached tree. Adding the paths to
3 and 5 takes place in these trees, creates no new cycle, and creates
no terminal vertex other than the selected primes. If a path first
meets a support vertex, every retained incident prime is kept in C_E.

All retained support vertices have degree at least two. The only
possible leaves of R are the prime vertices 3 and 5. R still has cycle
rank two, so the exact Euler excess identity is

    sum_{v in R}(degree_R(v)-2) = 2.                    (B1)

This identity includes support vertices. A branch at a support vertex
is not replaced by a branch at a prime. It covers the theta,
figure-eight and barbell shapes, their subdivisions, and paths from
3 and 5 meeting either kind of vertex.

For each core support E write C_E=E intersection K for its retained
prime set and T_E=E minus K for its direct private child primes.
Every C_E has at least two elements. All unretained components are
hanging incidence trees, and their complete prime interiors are disjoint.
If 3 occurs, every unretained prime is at least 7: prime 5 has either
been retained or does not belong to this component at all.

Keep every original exponent vector and residue in its own original
support group. Pure-power labels remain at their actual prime vertices.

## 2. Actual domains, unchanged inventory, and one common law

Prune all noncore support groups by Chapter 48's original-exponent
construction. A support with parent q and child set T uses

    c_T = product_{r in T}1/(r-1),
    D_T = product_{r in T}(r-3),
    w_i = product_{r in T}r^{-b_(i,r)},
    L_E(x_q) = sum_i w_i 1_{actual parent cylinder_i}(x_q).

Numerical distinctness gives sum_{i:a_i=a}w_i <= c_T at every original
parent exponent. Deleting B_E={L_E >= (D_T-1/4)c_T} costs at most

    H_q(B_E) <= 4 q^{-(D_T-1)}/[3(q-1)].

Outside B_E, the actual simultaneously allowed child tuple set has
original child Haar mass greater than c_T/4. No independently chosen
marginal witnesses are substituted for that tuple set.

Deleting original pure powers and these exceptional sets gives actual
domains S_q. For every q>=5 they obey

    H_q(S_q) >= d_q
      := 1-1/(q-1)-4q/[3(q-1)(q^2-1)].              (B2)

At 3 the distinct representative-child sum omits prime 5. This is true
both when 5 is retained and when 5 is absent from the component. Removing
that term from the forest estimate gives

    H_3(S_3) >= 1/4 + (2/3)3^{-1} = 17/36.          (B3)

Set b_3=18/17 and b_q=1/[(q-1)d_q] for q>=5. The sum of positive-exponent
cylinder caps at q under H_q(.|S_q) is at most b_q. The existing exact
square estimate is

    S := sum_{q>=5 prime} b_q^2 < 1/4,               (B4)

with b_5=18/49, b_7=36/173, b_11=90/799 and b_13=126/1373.
The sequence b_q decreases. All b_q for q>=5 are less than one.

Use exactly one actual core probability

    rho = product_{q in K} H_q(.|S_q).

For a support with T_E empty, let B_E be its actual bad union on C_E.
For a support with private primes use the original retained-match load
and the same threshold (D_T-1/4)c_T. Chapter 49's full original inventory
gives

    rho(B_E) <= v_E product_{q in C_E} b_q,
    v_E = 1                         if T_E is empty,
    v_E = 1/(D_(T_E)-1/4)            otherwise.     (B5)

Outside B_E its actual entire private tuple has allowed Haar volume
more than c_T/4. All core fees refer to rho before any conditioning.

When 3 occurs, nonempty T_E contains only primes at least 7, and hence

    v_E <= 4/15 if T_E is nonempty.                 (B6)

This private-support factor is retained. Distinct supports that induce
the same retained pair are not treated as repeated pure pairs.

## 3. Account for supports containing 3 before bounding the rest

Assume 3 occurs. Write B=18/17 and let d be its degree in R. For a
support E containing 3 define its adjusted charge

    A_E := v_E B product_{q in C_E minus {3}} b_q
                  - (1/2)sum_{q in C_E minus {3}}b_q^2. (B7)

The subtracted squares pay for incidences at those same prime vertices;
they are not separate credits from incompatible distributions.
For supports not containing 3,

    v_E product_{q in C_E}b_q <= (1/2)sum_{q in C_E}b_q^2.

Indeed v_E<=1, choose any two retained primes, drop the remaining
factors (all at most one), and use 2xy<=x^2+y^2. Summing all groups
therefore gives the single-source bound

    rho(union_E B_E)
       <= (1/2)sum_{q in K minus {3}}degree_R(q)b_q^2
                    + sum_{E containing 3} A_E.     (B8)

We now bound the adjusted charges without discarding support identity.
Put f(x)=Bx-x^2/2. It increases on 0<=x<=b_5 because B>b_5.

If the complete original support is E={3,q}, then A_E=f(b_q).
There is at most one such support vertex for each q. Many original
numerical moduli may belong to it, but their entire exponent inventory
has already been paid in (B5).

If C_E={3,q} and T_E is nonempty, (B6) and completing a square give

    A_E <= (24/85)b_q-b_q^2/2
         <= (1/2)(24/85)^2 = 288/7225.              (B9)

If C_E contains at least two primes q,r other than 3, drop other
product factors and keep the full negative square term. Then

    A_E <= B b_q b_r -(b_q^2+b_r^2)/2
         <= (B-1)(b_q^2+b_r^2)/2
         <= (b_5^2+b_7^2)/34.                     (B10)

The possible additional negative squares only improve this bound.
Both (B9) and (B10) are strictly smaller than

    f(b_17) = 12134448/176591393.                   (B11)

Consequently, whenever d<=5, the sum of the d adjusted root charges
is at most the sum of the first d entries of

    f(b_5), f(b_7), f(b_11), f(b_13), f(b_17).      (B12)

To see this, the pure-pair entries have distinct prime labels and are
bounded in descending order by the corresponding first entries. Every
remaining entry is at most the fifth entry, so can fill any unoccupied
one of the first d positions. This retains the discount for every
repeated projected pair and every higher-rank retained support.

## 4. Euler excess closes every two-cycle shape

Let s=sum_{E in E_core}(degree_R(E)-2)>=0.

**Prime 5 is not a leaf (including when it is absent).** Every retained
prime other than 3 has degree at least two. Equation (B1) gives

    sum_{q in K minus {3}}(degree_R(q)-2)=4-d-s>=0.

Thus 1<=d<=4. Since b_q<=b_5, equations (B4), (B8) and (B12) imply

    rho(union_E B_E)
      < 1/4 + ((4-d)/2)b_5^2 + sum_{j=1}^d f(b_(p_j)), (B13)

where p_1,...,p_5 are 5,7,11,13,17. The right side increases for
integer d from 1 to 4: each difference is f(b_(p_(d+1)))-b_5^2/2>0.
At d=4 it is exactly

    337636291352823447913/345922643206101994564
      < 49/50.                                      (B14)

**Prime 5 is a leaf.** Its contribution to the degree excess is -1;
every other retained prime besides 3 has degree at least two. Hence

    sum_{q in K minus {3,5}}(degree_R(q)-2)=5-d-s>=0.

Now 1<=d<=5, all primes in this sum are at least 7, and

    rho(union_E B_E)
      < 1/4-b_5^2/2 + ((5-d)/2)b_7^2
                           + sum_{j=1}^d f(b_(p_j)). (B15)

This increases for integer d from 1 to 5 because the differences are
f(b_(p_(d+1)))-b_7^2/2>0. At d=5 it is exactly

    3511740635399181789573718321/3593350672588678665890305156
      < 49/50.                                      (B16)

The checks of the differences and the endpoint comparisons use exact
rational arithmetic; the inequalities are independent of the number
of degree-two subdivisions, original heights or support ranks.

**Prime 3 absent.** Retain only the 2-core. All retained vertices have
degree at least two, and (B1) gives total prime excess at most two.
Here (B5) has v_E<=1 even if an unretained prime is 5. The square bound
alone yields

    rho(union_E B_E)
       <= (1/2)sum_{q in K}degree_R(q)b_q^2
       < 1/4+b_5^2 < 49/50.                         (B17)

These cases exhaust the connected cycle-rank-two graph. No bound on
an ordinary prime co-occurrence degree was assumed, and no retained
hyperedge was converted into a different constraint. Thus always

    rho(all core supports simultaneously extend) > 1/50. (B18)

## 5. Full original law, density, and continuation

Condition rho once on avoiding all core B_E. Then generate every private
tuple uniformly on its actual allowed set and descend all noncore
forest kernels. Different generated interiors are disjoint, so the
resulting law nu avoids every original class simultaneously.

Let m=|K| and h be the total number of nonsingleton support vertices
in this connected component. Every retained domain has Haar mass at
least 1/4. The core conditioning costs at most 50; each support that
introduces new primes costs at most 4 product_{r introduced}(r-1).
Each unretained prime is introduced exactly once, whence

    nu <= K_2 H,
    K_2 = 50*4^{m+h} product_{r not in K}(r-1).      (B19)

This full-history conditional-kernel bound implies full original
Haar survival at least 1/K_2. Component laws multiply, using Chapters
48 and 49 for components of cycle rank zero or one.

For a fixed head graph and prime set, use Chapter 48, Section 6, with
this complete joint density. Uniformly lift to every later-required
old height and all unused odd primes through p_k, and put

    kappa=K product_{odd p<=p_k}(1+(3p-1)/(p-1)^2).

The original-label moment expansion satisfies BBMST hypothesis (20)
with initial survivor mass one. A computable k has
kappa<=k(log k+loglog k-3)^2 because the product is O((log k)^4).
The BBMST continuation then permits arbitrary additional distinct
original classes with largest prime greater than p_k. The cutoff may
be large; no small cutoff or uniform bound as the head grows is claimed.

## Exact scalar and original-family verification

The companion
[incidence_bicyclic.py](../frontier/cover-geometry/incidence_bicyclic.py)
checks every scalar comparison with Fraction,
including all ten degree cases, the two degree-monotonicity comparisons,
and both non-pure-pair bounds against f(b_17). It uses explicit exceptions
that remain active under Python optimization. Its literal regressions
reconstruct the incidence graph, leaf-prune the actual 2-core, add the
specified small-prime paths, check Euler excess and possible leaves,
and build each original domain, exceptional set and allowed tuple set.
It then enumerates the actual full CRT law and checks normalization,
original avoidance and the complete density bound.

| Fixture | Period | Original classes | Full original survivors | Actual core loss | Maximum generated density | Density cap |
| --- | ---: | ---: | ---: | --- | --- | ---: |
| Theta: three distinct supports with retained pair 3,5 | 15015 | 8 | 5040 | 1/8 | 143/48 | 36864000 |
| Path from 3 meets a branched support, with 5 a leaf | 15015 | 9 | 4893 | 289/1920 | 715/233 | 13107200 |
| Figure-eight with degree-five prime 3 and leaf 5 | 255255 | 13 | 67351 | 24809/92160 | 255255/67351 | 3355443200 |
| Theta without prime 3 | 85085 | 8 | 44160 | 1/24 | 17017/8832 | 98304000 |
| Barbell with private child coordinates | 255255 | 11 | 78912 | 23/160 | 85085/26304 | 1258291200 |

Every generated probability has exact total mass one. The first fixture
keeps one complete support {3,5} and two larger distinct supports whose
retained part is that same pair; their private factors are charged
separately. The second retains a core support with four prime coordinates,
including the path's first support-node contact. The third realizes the
maximal possible retained degree five at 3. The last keeps the bridge
between the two cycles inside the connected 2-core.

These finite checks do not prove the unbounded theorem or the analytic
tail. The arbitrary-rank and all-height assertions rest on the preceding
original-inventory inequalities, graph identity and actual tuple kernels;
the analytic continuation retains Chapter 48's explicit BBMST premises.

The [retained exact output](../certificates/source_norms/cover-geometry/incidence_bicyclic.json)
is reproduced from the repository root by

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/incidence_bicyclic.py --check
```
