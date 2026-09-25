# Arbitrary central pure phases support sharper same-source networks

The two head interfaces of [Report624](624-arbitrary-central-pure-phases-admit-two-complete-boundary-gates.md)
admit the following complete network extensions. Set V=2^115.

| Head interface | Outside owner and parent scope | Ordinary interfaces | Extendible head Haar mass |
| --- | --- | --- | --- |
| Root-one | At each37<=v<V, one fixed union of at most three smaller head/network parents; at v>=V, any fixed finite union of smaller head/network parents | Exactly Report619's declared ordinary extension domains and disjoint private interiors | >1/5000 |
| Matching | Every added owner v>=V; any fixed finite union of smaller head/network parents | Only pure owner powers and the declared mixed owner inventories; no additional private or Type I blocks | >1/62000 |

The full finite survivor densities are respectively greater than
1/(5000 Q_off) and1/(62000 Q_off), where Q_off is the product of the
actual outside resolving prime powers. Network size, width, depth and
all exponent heights are arbitrary finite quantities. Each original
numerical modulus is distinct and has one globally fixed residue; each
non-head original is assigned once to its owner or to a declared ordinary
block. Parents are head primes or earlier declared owners, not undeclared
private-interior coordinates. Several descriptions at one owner must
fit the one fixed union allowed in the table.

The literal head primes remain{3,5,7,11,13,17,19,23,29,31}. Both branches
allow arbitrary central pure3/pure5 phases and heights. The first retains
Report624's root-one outside layout and mixed-label inventory. The second
retains its matching interface, including one endpoint pair shared by the
twelve labels of each retained edge and both square-to-linear root anchors;
linear-star roots may coincide. These are ordinary mathematical results
and exact rational certificates, not new Lean verification or a resolution
of unrestricted Erdős #7.

Sections1--5 establish a sharper all-three-parent base, with head bound
>1/4943. Sections6--7 then admit unbounded parent unions above the same
uniform V, paying the complete prime tail on the same actual law. The
second branch uses only those large owners; it does not inherit an unpaid
small-owner network from the first branch.

## 1. Recover the joint head caps from the actual construction

The core survivor of Report624 is dominated by one actual normalized product pure-source law. Its seven coordinate Haar caps are

```
c3=2, c5=4/3,
cq=q/(q-2) for q=7,11,13,17,19.
```

The head-only normalized continuation kernels at 23,29,31 have conditional caps

```
c23=5/3, c29=20/11, c31=2.
```

Restrict the resulting full head submeasure to its actual head-good set and call it `mu`. Report624's gate gives

```
mu(1) >= gamma_root = 534185412720319/23749451159961600,
mu <= C H_P, C=110656/2673, alpha=1/C=2673/110656.
```

For **every** subset `J` of head coordinates and cylinder depths `j_p>=1`,

```
mu(intersection_(p in J) [a_p]_(p^j_p))
 <= product_(p in J) c_p p^(-j_p).                 (ST1)
```

Proof: remove the good-set restriction for an upper bound, then integrate the 31,29,23 kernels in reverse sampling order. At queried coordinates pay the conditional cap; unqueried normalized kernels integrate to one. On the seven-prime core use domination by the normalized product pure law and integrate unqueried factors. Restriction and all original deletions can only reduce these masses. In particular ST1 is not obtained by multiplying singleton marginals and uses the same source as `gamma_root`.

## 2. A stronger outside invariant closes the sharper parent comparison

Sample this complete head first, then all outside owners in increasing numerical prime order. At owner `v`, the inherited actual ordinary extension domain has Haar mass at least `1-2/(v-1)` and already accounts for pure owner powers. Selecting at most `N` nonunit parent-exponent patterns and deleting all corresponding actual owner cylinders costs at most `N/(v-1)`. This is valid at every prior history: each pattern has at most one actual numerical original at each owner height and `sum_(h>=1) v^(-h)=1/(v-1)`.

Thus the remaining domain has mass at least `D/(v-1)`, where

```
D=v-3-N.
```

Use the normalized half-threshold row on this domain. If its remaining forbidden fraction is `t`, the row has bad probability `(2t-1)_+<=t^2`, is normalized even at `t=1`, and has Haar density at most `2(v-1)/D`. Enforce

```
D>=10  =>  2(v-1)/D <= (v-1)/5 < v/5.             (ST2)
```

The complete cubical-tail rows below instead have cap at most 4, also at most `v/5`. All rows are normalized at every complete prior history. They therefore form one joint submeasure `Pi`, preserve the head marginal and every earlier event mass, and require no intermediate surviving fibre.

Order the actual parents `u1<u2<u3` and use reference roles

```
(p1,p2,p3)=(3,5,7), (d1,d2,d3)=(2,4/3,7/5).
```

Every actual head parent `u>=p_i` satisfies

```
c_u/u <= d_i/p_i,
(d1/p1,d2/p2,d3/p3)=(2/3,4/15,1/5).              (ST3)
```

For role 1 this follows from the listed ten caps; for role 2 the prime 3 is unavailable and the largest permitted ratio is `(4/3)/5`; for role 3 the primes 3 and 5 are unavailable and the largest ratio is `(7/5)/7`. The continuation ratios `(5/3)/23`, `(20/11)/29` and `2/31` all lie below `1/5`. Every outside parent has ratio at most `1/5` by ST2, which suffices in every role. Since `u_i>=p_i`, for any positive depth `j`,

```
c_(u_i) u_i^(-j)
 <= (d_i/p_i) u_i^(1-j)
 <= d_i p_i^(-j).                                 (ST4)
```

The old cap `u/4` alone would not prove ST4 in role 3, whose required ratio is `1/5`. This is why the new row condition `D>=10` is part of the construction, rather than an after-the-fact numerical substitution.

Integrate queried outside parents in reverse actual sampling order, then use ST1 on all queried head parents together. Zero depths cost one. For two exponent patterns `x,y`, any intersection of their actual parent cylinders is empty or a prefix cylinder of maximum depth at each coordinate. This remains true when their phases came from different owner heights. The resulting **joint** bound is

```
k(x,y)=product_i [1,                             max(x_i,y_i)=0;
                 d_i p_i^(-max(x_i,y_i)),        otherwise]. (ST5)
```

No additional factor 2,4,8 or full-head density is paid here. For fewer than three parents, put zero exponents in missing reference slots. Any nonphysical selected pattern has no actual deletion and costs zero; the number of actual selected patterns remains at most `N`. The actual remaining pattern set embeds in the full reference complement, which is a valid positive overestimate.

## 3. One complete moment pays every owner height

Let `S_N` consist of the unit pattern and the first `N` nonunit patterns in increasing reference order `3^i5^j7^k`. Define

```
M(N)=sum_(x notin S_N,y notin S_N) k(x,y).
```

Only actual numerical labels are deleted; reference ordering does not replace a numerical modulus or its phase. For every remaining pattern the owner-height weights `w_h=(v-1)v^(-h)` sum to one. The actual forbidden fraction is bounded by `1/D` times the sum of its parent indicators averaged with these weights. Apply ST5 to every pair of indicators, retaining all cross terms, then the half-threshold inequality gives

```
Pi(owner-v violation) <= M(N)/D^2.                (ST6)
```

All infinite sums are convergent positive upper bounds for arbitrary finite inventories. Distinctness of numerical originals supplies the at-most-one coefficient for each `(parent pattern, owner height)`.

The complete one-coordinate factors and rows are

```
T_i=1+d_i[3/(p_i-1)+2/(p_i-1)^2],
row_i(e)=1+d_i/(p_i-1)                         if e=0,
         d_i p_i^(-e)[e+1+1/(p_i-1)]          if e>0.
```

The product moment is `product_i T_i`. The exact complement formula is

```
M(N)=product_i T_i
     -2 sum_(x in S_N) product_i row_i(x_i)
     +sum_(x,y in S_N) k(x,y).                    (ST7)
```

For each of all 152 primes `37<=v<971`, minimize `M(N)/(v-3-N)^2` over `0<=N<=v-13`, so `D>=10`. The stored finite table gives an exact fee sum approximately `0.014047689021246493`. All chosen rows have `D>=19`, though the proof and allowed search use the simpler invariant `D>=10`.

## 4. The complete infinite prime tail

For each odd prime `v>=971`, choose `n>=7` with

```
2n^3+3 <= v <= 2(n+1)^3+1.
```

Select the nonunit cube `[0,n)^3`. Then `N=n^3-1`, `D=v-n^3-2>=n^3+1`, and the row Haar cap is at most 4, which is below `v/5`. The intervals cover all odd primes in this range; their gaps are single even integers.

Put

```
A_i(n)=d_i p_i(p_i+1) p_i^(-n)/(p_i-1)^2,
B_i(n)=d_i p_i^(1-n)[n+1+2/(p_i-1)]/(p_i-1).
```

Here `A_i` sums the kernel with both exponents at least `n`, and `B_i` with one at least `n`. Choose a coordinate outside the cube for each of the two patterns, allowing overcounting. Then

```
M_cube(n) <= sum_i A_i(n) product_(j!=i) T_j
          +2 sum_(i<j) B_i(n)B_j(n)T_k
          <24*3^(-n).                              (ST8)
```

At `n=7`, the displayed majorant times `3^7` equals `8040996178/337640625 <24`. Its scaled diagonal ratios are `3/p_i<=1`. Its scaled cross ratios are at most `3/(p_i p_j)*((n+2)/(n+1))^2<1` for every `n>=7`. Thus the bound is uniform at all subsequent depths.

Each interval contains at most `6(n+1)^2` integers. Replacing primes by all integers, using `D>=n^3`, and overcounting the whole first interval that starts below 971 gives the complete tail

```
W_tail <= 6*24*(8/7)^2*7^(-4)*sum_(n>=7)3^(-n)
        =512/9529569.
```

Hence the sum for **all** possible outside owners satisfies

```
W3 <= W_finite+512/9529569
   <1411/100000.                                  (ST9)
```

Its exact stored value is approximately `0.01410141652980433`. This is a complete infinite-prime estimate, uniformly covering every finite network, not a finite search cutoff.

## 5. One common budget and the actual extension

The inherited ordinary Type I single-head blocker Haar sum is at most `2^(-17)`. ST1 has singleton caps at most 2, so its charge on this same `Pi` is at most `1/65536`. Owner ordinary extension domains have already been charged in ST2. No early-root or two-parent fee is added separately: ST6 covers every owner once, including roots and all parent types.

Thus

```
Pi(all head, owner and ordinary tests pass)
 >= gamma_root-W3-1/65536 >0.
```

Using the exact finite fee and tail, the remaining raw lower bound is approximately `0.008375861840092202`; multiplication by `alpha` gives an exact rational lower bound approximately `0.0002023268390197229`, strictly greater than `1/4943`. The full exact fractions are in the certificate. A shorter independently checked estimate is

```
gamma_root >449/20000,
alpha*(449/20000-1411/100000-1/65536)>1/5000.         (ST10)
```

The full head density bound converts good joint mass to head Haar mass. Every actual good network assignment lies in all its ordinary extension domains. The declared disjoint interiors and separate ordinary components can be filled simultaneously, as in Report619; no undeclared crossing is permitted. Counting one actual outside extension for each extendible head class and applying CRT yields the full-density statement.

## 6. Arbitrarily many parents above one uniform owner threshold

The actual finite rows have new conditional caps. They cannot be replaced
coordinatewise by Report621's old caps: eighteen of the new finite caps
are larger. Use the actual cap c_p from ST1 on each head coordinate and
c_p=2(p-1)/D_p from the new finite row at each37<=p<971. Above971 use4.
Define

    T_p(c)=1+c[3/(p-1)+2/(p-1)^2],
    A_new=product_(odd prime p<971) T_p(c_p)(1-1/p)^12.

The exact162-factor product satisfies

    0<A_new<3/1000,
    A_new approximately0.0011070274704615278.            (ST11)

At each actual owner v>=V select no nonunit pattern in advance (N=0).
Its actual ordinary domain already avoids the pure powers and has Haar
mass at least(v-3)/(v-1). The normalized half-threshold row is defined
at every prior history, including dead fibres, and gives

    dK_v/dH_v <=2(v-1)/(v-3)<4<v/5,
    bad probability=(2t-1)_+<=t^2.                       (ST12)

Use the new finite/cubical three-parent rows for owners below V and
ST12 for owners at or above V, all in increasing prime order after the
one actual head. ST12 preserves the stronger conditional invariant used
in ST4. The old three-parent estimates therefore hold for the actual
small owners on this new joint law. No owner uses two rows.

For any fixed parent union A_v at a large owner, reverse actual sampling
and ST1 give the simultaneous prefix bound product c_p p^(-j_p). If two
prefixes use the same coordinate, their intersection is empty or a single
prefix at the maximum depth, and the cap is paid once. Expanding the
square of the full cofactor sum and summing all owner heights gives

    Pi(owner-v violation)
      <= product_(p in A_v)T_p(c_p)/(v-3)^2.             (ST13)

The owner-height weights(v-1)v^(-h) sum to one. This retains all cross
terms and all finite actual heights and phases. An absent parent can be
padded by a factor T_p>1; this is a numerical overestimate, not an added
coordinate or a different probability law.

The elementary Euler bound and dyadic summation in
[Report621](621-one-uniform-owner-threshold-removes-the-parent-count-bound.md),
UT11--UT21, use only the actual finite correction bound ST11 and c_p<=4
from971 onward. They apply here and give, for K>=109,

    sum_(v prime, v>=2^K) Pi(owner-v violation)
      <(15/1000)[4(K+2)]^12 2^(-K)=E_K.

In particular

    E_115=19740202146111572828188083
                /495176015714152109959649689600.        (ST14)

This is the entire infinite prime tail. Its derivation uses
product_(3<=p<=2^k)(1-1/p)^(-1)<=4(k+1),
T_p(4)<=(1-1/p)^(-12), and the successive dyadic ratio
(1/2)(112/111)^12<3/5. No finite prime cutoff is substituted for it.

Conservatively pay the full W3 of ST9 for the actual small owners, even
though W3 also included hypothetical three-parent rows at larger primes.
Then pay ST14 for the actual new large rows and the one ordinary Type I
fee. The same-law good mass is bounded below by

    gamma_root-W3-1/65536-E_115>0.

The exact projected lower bound is approximately0.00020136386186086602.
The shorter strict estimate is

    alpha*(449/20000-1411/100000-1/65536-E_115)>1/5000.  (ST15)

This proves the first row of the opening table. All actual owner values
lie in their declared ordinary extension domains, and the inherited
private-interior disjointness gives simultaneous filling and CRT gluing.
The ordinary-interface restrictions have not disappeared.

## 7. The matching head also supports an arbitrary-parent large-owner network

For the matching interface use its own supported head submeasure and gate

    gamma_match=135228904182589/189995609279692800.

It is dominated by the same product pure-source caps before the23/29/31
kernels. Reverse integration gives ST1 with the same ten actual c_p,
and its full density is still C=110656/2673. This concerns one actual
matching-family source; no root-one law is substituted for it.

All added owners now satisfy v>=V. At each owner, remove its actual pure
powers; their total Haar cost is at most1/(v-1), so the weaker convenient
remaining-domain bound(v-3)/(v-1) is valid. There are no added private or
Type I blocks in this branch. Every other non-head original belongs once
to its owner's fixed mixed inventory

    (product_(p in A_v)p^e_p)v^h,
    sum_p e_p>0, h>=1.

Use the normalized N=0 rows of ST12. The same complete cofactor moment
and tail ST13--ST14 apply. All small outside coordinates are absent here;
their T_p factors from ST11 are only positive numerical padding. This
imports neither their actual rows nor their fees into the matching law.

The good joint mass is strictly greater than gamma_match-E_115. Its
head projection therefore has Haar mass strictly greater than

    alpha*(gamma_match-E_115)
      =9361130188259343013584115491
         /576781023103844377680999958446080
      >1/62000.                                        (ST16)

Counting at least one actual outside extension for every extendible head
assignment gives full density>1/(62000 Q_off). Small outside owners and
additional private blocks are not covered by this second branch.

## Exact certificate and independent formula

The [producer](../../frontier/cover-geometry/arbitrary_pure_network_extensions.py)
and [data](../../frontier/cover-geometry/arbitrary_pure_network_extensions.json)
retain all971 complete reference moments, all152 finite rows, the complete
cubical tail, all162 actual Euler factors and both large-owner budgets.
The current source data and both head producer/kernel hashes are checked.
The standard-library computation passes1461 checks, including the stronger
v/5 invariant and both strict final projection bounds.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_pure_network_extensions.py

A separate implementation imports no producer and checks the selected
moments by a positive-layer formula. In coordinate(p,d), let L have weights

    Pr(L=0)=1-d/p,
    Pr(L=l)=d(p-1)/p^(l+1), l>=1.

Then Pr(L>=m)=1 at m=0 and d/p^m at m>=1. The product kernel ST5 is the
probability that the three independent L coordinates dominate both queried
exponent patterns. Tonelli expresses M(N) as the expectation of the squared
number of unselected lattice points in0<=x_i<=L_i. Counting selected points
by prefix sums and integrating the remaining polynomial tails exactly
checks all78 actually selected moments, all152 rows and121210 positive
integration cells. These239 checks agree with the complement-sum formula.
A separate exact162-factor computation verifies ST11 and ST15; the
same-source and gluing arguments are the ordinary proof above.

The restrictions still requiring removal are the respective head labels
and endpoint relations, small-owner parent unions, and declared ordinary
interfaces. Arbitrary parent count in the complete large-prime tail does
not remove any of those remaining conditions.
