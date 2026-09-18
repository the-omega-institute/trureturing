[Index](../marked_head_profile.md) · [Previous](02-survivor-weighted-full-convex-comparison.md) · [Next](04-the-weighted-upper-quantile-lemma.md)

<a id="arbitrary-height-transfer-for-matching-kernels"></a>
## Arbitrary-height transfer for matching kernels

Let Q be the old period, q and r new distinct primes coprime to Q, and
H,J≥1 finite. Let μ be a probability on the complete old survivors.
For every complete old test load A suppose

    Eμ A ≤ M,       Eμ A² ≤ G.

The first bound can be M=1+R_old (the sum of old nonunit cylinder maxima
plus one), or any sharper validated common first-moment bound. It can
always be tightened to min(M,sqrt(G)); since A≥1, G≥1.

Suppose each old point x has a first-q/r-digit law ρ_x avoiding all actual
classes whose new exponents are at most one. Assume these laws share
row, column and atom caps R,C,a and a common diagonal quadratic bound
whose coefficient sum is F. A valid improvement of the complete low
square may also be retained:

    Γ_(Qqr)(μρ_x) ≤ C0 := FG−η,       η≥0, C0≥1.                 (HT1)

Extend this single probability law uniformly in the additional H−1
q-digits and J−1 r-digits. Write

    u_q = Σ_(t=1)^(H−1) q^(−t),
    v_q = Σ_(t=1)^(H−1) (2t−1)q^(−t),
    w_q = 4u_q+v_q,

and similarly for r. Empty sums are zero. Define

    Λ=M[(R+a)u_q+(C+a)u_r+a u_q u_r],                           (HT2)
    E=(R+3a)w_q+(C+3a)w_r+a w_q w_r.                         (HT3)

For every distinct-original-modulus family with old factors dividing Q
and new exponents bounded by H,J, provided its low classes are already
avoided and Λ<1, the uniformly lifted law gives positive mass to the
complete survivor set. Conditioning that same law on all actual high
class exclusions yields

    Γ_(Q q^H r^J)(μ_final)
      ≤ [C0+EG−Λ]/[1−Λ]
      = [(F+E)G−η−Λ]/[1−Λ].                                  (HT4)

No nonempty lift over every old x is required; the final old marginal
can change. The actual high classes can overlap and can have repeated
new prefixes. Original modulus labels, not projected distinctness, are
used throughout.

<a id="proof-of-the-bad-mass-bound"></a>
### Proof of the bad-mass bound

At x a prescribed q-prefix of depth b≥1 has mass at most R q^(−(b−1));
an r-prefix has the analogous cap, and a prescribed positive-depth pair
has mass at most a q^(−(b−1))r^(−(c−1)). This follows from uniformity only
in the higher digits, without any independence hypothesis on ρ_x.

For each fixed new exponent pair, the actual old cofactors d occur at
most once because the original moduli d q^b r^c are distinct. Their
active old indicators form a partial complete old test load, so their
mean is at most M. Sum the prefix caps for b≥2,c=0; b=0,c≥2; and b,c≥1
with at least one exponent≥2. The sums are respectively

    R u_q, C u_r, a(u_q+u_r+u_q u_r).

The union bound proves that the actual deleted high mass β is at most Λ.
This argument includes the pure high prime-power classes (d=1) and does
not assume disjoint forbidden classes.

<a id="proof-of-the-full-square-bound"></a>
### Proof of the full-square bound

Group a complete fine test layout by its new exponent pair e=(b,c).
The sum A_e(x) of the old cofactor indicators is one complete old load.
For any e,e′, after expanding their two grouped fine loads, every new
prefix intersection is either empty or has the cap at exponent pair
max(e,e′). Therefore its integrated contribution is at most

    κ_(max(e,e′)) Eμ[A_e A_e′] ≤ κ_(max(e,e′)) G.

The last inequality is Cauchy–Schwarz; no independence between old
layouts is used. Keep the four low groups b,c∈{0,1} together and apply
(HT1) to them, instead of replacing their intersections by separate caps.
All remaining pairs have at least one maximum exponent at least two.

There are 2b+1 ordered pairs of exponents in {0,…,H} whose maximum is b.
Thus Σ_(b=1)^H(2b+1)q^(−(b−1))=3+w_q. Summing all the high pairs gives

    Rw_q+Cw_r+a[(3+w_q)(3+w_r)−9]=E.

Consequently the square of every fine layout has integral at most C0+EG.
Every complete fine load is at least one, so deleting high mass β saves
at least β from that integral. After conditioning,

    E_final L² ≤ (C0+EG−β)/(1−β)
                ≤ (C0+EG−Λ)/(1−Λ),

because C0+EG≥1. This is the repository's existing minimum-load deletion
saving/N9, reused on the present law, and proves (HT4).

<a id="matching-row-column-and-atom-caps"></a>
### Matching row, column and atom caps

For m,n≥3, 0≤K<min(m,n), and 0≤ε≤1/(9C_K), put

    S=m+n, V=mn−K, H0=K(S−K−1),
    C_K=max(S+2K−1,2m,2n), D=V+H0ε, c=1/D,
    R=c(n+Kε), C=c(m+Kε),
    a=(1+ε)c if K≥1, and a=c if K=0,
    F=1+c[3(S+3)+6Kε].

These are global caps, not just values at selected cells. An affected
row has mass c(n−1)(1+ε), smaller than R by
c[1−(n−K−1)ε]>0; columns are analogous. Every positive atom is c or a.

They apply to fixed-K matching grids and moving matching fibres with
common m,n. If the true matching size is k_x≤K, the denominator D_j
decreases with j and the row/column numerators increase. Hence the K
caps also apply when each fibre keeps its actual k_x and uses MT7–MT9.
In particular retain either

    η=Eμ[F_K−F_(k_x)],

or its validated lower bound γ(K−M)_+, with the same first-moment M
bounding the actual cross-class activation load. This saving is not
discarded by the high extension.

<a id="exact-criterion-for-preserving-the-ε-improvement"></a>
### Exact criterion for preserving the ε improvement

Take a fixed positive matching size k, η=0, and keep the same low
support, old law and uniform higher-digit rule when comparing ε=0 to
ε>0. Let V=mn−k,H0=k(S−k−1), and put

    N0=V+3(S+3)+(n+3)w_q+(m+3)w_r+w_qw_r,
    N1=H0+6k+(k+3)(w_q+w_r)+w_qw_r,
    L0=(n+1)u_q+(m+1)u_r+u_qu_r,
    HT1=(k+1)(u_q+u_r)+u_qu_r.

The conditioned bound is the linear fractional expression

    B(ε)=[GN0−ML0+ε(GN1−ML1)]
          /[V−ML0+ε(H0−ML1)].                                (HT6)

Its ε derivative has constant sign wherever the denominator is positive.
In particular it strictly improves at every positive permitted ε iff

    Δ=(GN0−ML0)(H0−ML1)−(GN1−ML1)(V−ML0)>0.                 (HT7)

This is a checkable symbolic condition, not a consequence of F alone
decreasing: the larger positive atom cap can increase high error terms.
The exact gain is

    B(0)−B(ε)= εΔ / [(V−ML0)(V+εH0−M(L0+εL1))].             (HT8)

<a id="all-finite-heights-for-the-1113-ten-by-twelve-one-hole-grid"></a>
### All finite heights for the 11/13 ten-by-twelve one-hole grid

For q=11,r=13,m=10,n=12,k=1 the permitted interval is
0≤ε≤1/216. The improvement is strict for every positive ε in this
interval, every pair of finite heights, and every old first-moment
bound M≤40 (with G≥1 and the stated valid old bounds).

Here 0≤u_q≤1/10,0≤u_r≤1/12 and
0≤w_q≤13/25,0≤w_r≤31/72. Define δb=H0N0−VN1 and
δt=VL1−H0L0. Direct simplification gives

    δb=786−176w_q−216w_r−99w_qw_r ≥115863/200,
    δt=−22u_q+18u_r+99u_qu_r ≤3/2.

The latter maximum is at a corner of the indicated rectangle, since
the expression is bilinear. Also

    L0≤89/40, HT1≤3/8, N0≤186859/900.

The survival denominator is at least

    V+εH0−M(L0+εL1) ≥30+5ε>0.

The derivative is negative exactly when

    G δb(1−ML0/V) > (GN0/V−1)M δt.

If δt≤0 this is immediate, because N0/V≥1. If δt>0, divide by G,
use G≥1, and bound the left side below and the right side above.
Their strict positive margin is at least

    (115863/200)(30/119)
      −(186859/(900·119))·40·(3/2)=295331/7140>0.

This proves the all-finite-height statement; the finitely many regression
calculations are not its proof.

<a id="arithmetic-consumer-and-exact-uniform-in-height-bound"></a>
### Arithmetic consumer and exact uniform-in-height bound

Use the repository's sharp supported 315 law, G=1131/86,M=271/86,
and a first-digit 10×12 one-hole grid. Uniform infinite geometric sums
majorize every finite height, and the conditioned bound is increasing
in each u and w on its valid domain. They give

    ε=0:       Γ_final ≤140529901/5778615,
    ε=1/216:   Γ_final ≤6074954672/249830373,

with exact difference

    1271130847931/481224513624465>0.

At ε=1/216 the high deleted-mass bound is
5213769/88490560<1. These values are approximately 24.31895895 and
24.31631750, with gain 0.00264145. They are upper bounds, not asserted
exact Γ values.

One actual consumer is the eleven-class sharp 315 family together with
(11,0),(13,0),(143,1), already constructed in the repository. Adjoin
arbitrarily many distinct actual moduli d·11^a·13^b with d|315 and
a≥2 or b≥2, up to any finite heights, and arbitrary residues. The bound
gives a supported complete survivor probability for every such extension.
It does not say that an arbitrary odd family has this low support shape.
The next result combines this head bound with a full convex comparator and a tail certificate under an explicit low-grid hypothesis.

The matching common diagonal, the sharp 315 law, and the existing minimum-load deletion saving are reused directly. The quantitative step retains the complete low square and charges only higher exponent pairs to prefix caps. The adjacent verifier checks the exact displayed constants, ordered-pair identity and 64 finite-height regressions; the universal statements follow from the ordinary argument above. No new Lean wrapper is added.

<a id="a-matching-1113-head-with-arbitrary-heights-and-unrestricted-tails"></a>
## A matching 11/13 head with arbitrary heights and unrestricted tails

**Theorem.** Let a finite family have distinct odd nonunit moduli. Suppose
the full 3/5/7 part of every modulus divides 315, including those moduli
having later prime factors. Choose the canonical old 315 survivor law μ
constructed above. At each x in its support suppose there is a rectangle
A_x×B_x of 10 first 11-digits and 12 first 13-digits, with at most one cell
removed, which avoids all actual head classes whose 11/13 exponents are
both at most one. The row sets, column sets and hole may depend on x.
Then the family does not cover the integers. The 11/13 heights and the
number, heights and interactions of all tail primes at least 17 are
unrestricted.

Pad a missing hole by one virtual hole and use the matching law with
ε=1/216. Extend its higher 11/13 digits uniformly, at their full heights
in the original family, padding an absent coordinate to height one.
Condition on avoiding all actual head classes
having an 11 or 13 exponent at least two. The height theorem gives a single
supported head probability ν with

    Γ(ν)≤J0=6074954672/249830373,
    higher deleted mass≤b=5213769/88490560<1.                 (MH1)

All original labels d·11^a·13^b remain distinct; no assumption about
distinct projected moduli or disjoint high classes is made.

<a id="a-full-comparator-for-the-same-supported-law"></a>
### A full comparator for the same supported law

For comparison, let τ sample x from μ, then sample independently given x
from the uniform laws on A_x and B_x, with uniform higher digits. The
matching atom cap is amax=217/25724, so its density relative to τ before
high-class conditioning is at most 120 amax. Afterwards,

    dν/dτ≤1/ell,
    ell=(1−b)/(120amax)=83276791/89577600.                    (MH2)

This remains true when entire old fibres are killed; ν may have a
different old marginal. The reference law τ is only a comparison law
and need not avoid the matching hole or high classes.

Under τ every positive-depth p-prefix, conditional on the full earlier
history, has mass at most c_p p^(−e), where c11=11/10,c13=13/12. Indeed
the first digit is uniform on 10 or 12 choices and all higher digits are
uniform. The sets may depend on x: their cardinalities give constants
independent of x, and B_x does not depend on the sampled 11-coordinate.

Let independent auxiliary variables N11,N13, independent also of the
published eight-atom old comparator X, have laws

    Pr(Np=1)=1−c_p/p,
    Pr(Np=k)=c_p(p−1)/p^k,  k≥2.

The existing conditional comparison C1 applies successively to 13 and 11.
Keeping the complete old load for each exponent tuple and applying
Jensen after comparison gives, for every complete head test load L and
nonnegative increasing convex h,

    Eτ h(L)≤E h(Y),        Y=X N11 N13.                     (MH3)

For fixed auxiliary values n11,n13 the compared load is a sum of
n=n11n13 complete old loads A_i. Its expectation is bounded by
n^(−1)Σ_i Eμ h(nA_i)≤E h(nX). This explains both the product comparator
and why moving first-digit sets do not require independence of old
test loads. Infinite auxiliary heights majorize every finite physical
height by adding nonnegative completed labels.

For every real z, density domination and (MH3), applied to (h(.)−z)_+,
give

    Eν h(L)≤z+ell^(−1)E(h(Y)−z)_+.                          (MH4)

The exact reference mean and first two masses are

    EY=1574239/412800,
    Pr(Y=1)=6391/92880,       Pr(Y=2)=807835/2173392.

They imply

    Pr(Y>2)=3040019/5433480<ell<86489/92880=Pr(Y≥2).

Let Z be the upper ell-quantile of Y, splitting its atom at 2:

    Pr(Z=2)=1837670057/4615287417,
    Pr(Z=z)=Pr(Y=z)/ell for integer z>2,
    EZ=2+[EY−2+Pr(Y=1)]/ell=3016548085/749491119.             (MH5)

Taking z=h(2) in (MH4) proves Eν h(L)≤E h(Z) for every layout and every
such h. Thus (MH1) and (MH5) bound the same actual supported probability.
The direct square J0 is used separately; it need not equal E[Z²].

<a id="exact-continuation"></a>
### Exact continuation

Use Z in AP2 and J0 in AP5. For any subsequent independent auxiliary
product N, the step charge is bounded by E(ZN−T)_+/s. Its exact
positive-part identity uses the mean and only finitely many low states:

    E(W−t)_+=EW−t+Σ_(d≤t)(t−d)Pr(W=d),       W=ZN.

Here EW is the mean of a fully specified comparator, not an unknown
maximum actual head mean. Thus the caution following AP7 does not
invalidate this calculation. The retained directed-arithmetic
certificate processes 258 primes from 17 through 1693, with global prime
index 264, and gives

    survivor mass≥240819191260897231/10^18,
    Γ_stop≤1169229336100810112644/240819191260897231
           <4856<4868
           <264(log264+loglog264−3)^2.                      (MH6)

The last logarithmic inequality is certified by positive rational
atanh-series lower bounds. In particular, log 264 > 55759/10000 and
log log 264 > 17184/10000 give the shorter lower bound
60855341217/12500000 > 4868. AP6 and the dossier’s T1–T6 transfer into
BBMST Theorem 6.1 therefore continue through every later prime.
The new head construction is supplied here. If the original family ends earlier, the
already positive prefix mass suffices. Finite CRT supplies an integer
outside all original classes, proving the theorem.

The low-fibre hypothesis is the boundary of this result: the argument
does not establish a 10×12 single-hole rectangle for every arbitrary
old head assignment. Higher 3/5/7 exponents also remain outside the
theorem. This is an ordinary proof with an exact arithmetic certificate,
not an unrestricted solution of Erdős #7 or end-to-end Lean verification.

The fixed schedule and its 258 charges are retained in `matching_height_tail17` in the adjacent certificate. The verifier reuses the existing directed convolution and logarithm routines. It retains 384 low states, bounds all omitted states through the full exact mean, and rounds upwards on a grid of 10^-18. Independent arithmetic at scale 10^-24 gives charge < 0.759181, second moment < 1170 and Γ < 4856. These are finite arithmetic certificates for the ordinary proof, not a claim that the selected schedule is optimal.

<a id="arbitrary-point-holes-and-a-common-diagonal"></a>
## Arbitrary point holes and a common diagonal

<a id="statement"></a>
### Statement

Let m,n>=3, let E be an arbitrary set of k holes in an m by n grid, and
assume k<mn. Write d_i and e_j for the row and column degrees of E. Set

```
C0 = max(m+n+1, 2(m−1), 2(n−1), 4),
0 <= epsilon <= 1/(9 k C0)                 (k>0),
w_ij = 1+epsilon(d_i+e_j)                  ((i,j) outside E),
H = k(m+n)−sum_i d_i^2−sum_j e_j^2,
Z = mn−k+epsilon H,
rho(i,j)=w_ij/Z.
```

For k=0 use the uniform full-grid law. The following diagonal dominates
every independently chosen row/column/single-cell Gram matrix of rho:

```
lambda_E = (1+(m+n+1+2k epsilon)/Z,
            2(n+1+k epsilon)/Z,
            2(m+1+k epsilon)/Z,
            4/Z).                                        (AH1)
```

Thus, for all real four-vectors A and every test row i, column j and cell z,

```
E_rho (A0+A1*1[row=i]+A2*1[column=j]+A3*1[cell=z])^2
    <= sum_g lambda_E[g] A_g^2.                          (AH2)
```

Now fix K>=1 and choose one epsilon<=1/(9 K C0). If K<mn and

```
D_K=mn−K+epsilon K(m+n−K−1)>0,
```

then every arbitrary hole pattern with 0<=k<=K admits the same diagonal

```
lambda_K = (1+(m+n+1+2K epsilon)/D_K,
            2(n+1+K epsilon)/D_K,
            2(m+1+K epsilon)/D_K,
            4/D_K).                                      (AH3)
```

The row, column and point probabilities of this same law satisfy

```
R_k=(n+k epsilon)/D_k,
C_k=(m+k epsilon)/D_k,
a_k=(1+k epsilon)/D_k,                                    (AH4)
```

where D_k=mn−k+epsilon k(m+n−k−1). These bounds are continuous at k=0.
All three increase with k, so the K-bounds work in every fibre. No extra
row/column deletion or matching hypothesis is used.

<a id="proof-of-the-new-gram-estimate"></a>
### Proof of the new Gram estimate

Use unnormalized matrices. For selected row i, column j and surviving
cell z, let r=n−d_i, c=m−e_j, u=1[(i,j) survives],
v=1[z lies in row i], and t=1[z lies in column j]. At epsilon=0 the Gram is

```
M0 = [[mn−k,r,c,1], [r,r,u,v], [c,u,c,t], [1,v,t,1]].
```

The unnormalized diagonal from (AH1) is initially
`(mn−k+m+n+1,2(n+1),2(m+1),4)`. Its difference D0 from M0 is a
nonnegative weighted graph Laplacian plus diagonal slacks

```
(d_i+e_j, 2+2d_i−u−v, 2+2e_j−u−t, 2−v−t).               (AH5)
```

All slacks are nonnegative integers. They all vanish precisely when
d_i=e_j=0 and z=(i,j). In that exceptional case both axes and their
intersection are untouched by holes.

In every other case D0 >= I/9. Here is a proof including fully missing
rows or columns, so k<min(m,n) is unnecessary. If r,c>=1, the graph
contains the unit star 01,02,03 and some vertex has a unit diagonal
anchor. Expressing four coordinates through the anchor and the three
star differences gives a matrix with squared Frobenius norm at most 9.
Thus `sum x_g^2 <= 9(x_anchor^2+sum_{a=1}^3(x0−xa)^2)`.

If r=0 then d_i=n. The center slack is at least n>=3 and the vertex-1
slack is at least 2n+2. Use two units of each slack and
`2x0^2+2x1^2 >= (x0−x1)^2` to restore the missing star edge 01.
The analogous construction restores 02 if c=0. If either edge was
missing, the remaining center slack is at least
`n*1[r=0]+m*1[c=0]−2(1[r=0]+1[c=0]) >=1`.
The full star and its center anchor therefore remain, giving the same
I/9 bound. All other edge and diagonal terms are nonnegative.

Write h=d_{z_row}+e_{z_column}, and let r',c' be the derivatives of the
selected raw row/column masses. Let u'=d_i+e_j if (i,j) survives and 0
otherwise. On a surviving cell, its row-incident and column-incident
hole sets are disjoint, so h<=k and u'<=k. Moreover

```
0<=r'<=k(n−1),    0<=c'<=k(m−1).
```

For a row with a hole this follows by summing at most n−1 cell
derivatives bounded by k. A row without holes has r'=sum e_j=k.
The column statement is identical. The difference matrix is affine:

```
D(epsilon)=D0+epsilon Delta,
Delta = [[2k, −r', −c', −h],
         [−r',2k−r',−u',−hv],
         [−c',−u',2k−c',−ht],
         [−h,−hv,−ht,−h]].                                (AH6)
```

Its absolute row sums are bounded respectively by

```
k(m+n+1), 2k(n−1), 2k(m−1), 4k.
```

For the second bound, use
`|2k−r'|+r'+u'+hv <= max(2k,2r'−2k)+2k
                    <= max(4k,2r') <=2k(n−1)`.
Symmetry and `2|xy|<=x^2+y^2` imply
`|x^T Delta x|<=k C0 ||x||^2`. Hence the nonexceptional matrices satisfy
`D(epsilon)>=(1/9−epsilon k C0)I>=0`.

In the exceptional case r'=c'=k and h=u'=0. Then Delta is itself the
nonnegative star Laplacian with weight k on 01 and 02. Thus D remains
positive semidefinite there too. This proves (AH1)–(AH2).

A test cell outside the survivor support has zero indicator. Its Gram
inequality follows by taking the upper-left principal submatrix for any
surviving test cell, together with the nonnegative fourth diagonal.
Test rows or columns outside chosen axis sets are likewise zero blocks.

<a id="the-graph-identity-and-common-coefficients"></a>
### The graph identity and common coefficients

Summing cell derivatives gives exactly H above. If t(E) counts unordered
pairs of holes sharing neither row nor column, then

```
sum_i d_i^2+sum_j e_j^2 = k^2+k−2t(E),
H = k(m+n−k−1)+2t(E).                                    (AH7)
```

Indeed each pair of distinct holes shares at most one endpoint. It is
counted twice in the sum of degree squares when it shares an endpoint,
and zero times otherwise. Thus H>=k(m+n−k−1), and Z>=D_k.
Replacing Z by D_k in the positive fractions of (AH1) only increases
the diagonal. Also

```
D_j−D_(j+1)=1−epsilon(m+n−2j−2)>0,
```

since epsilon(m+n−2)<1. Positive numerators in all four coordinates
increase with j. Therefore their D_j-envelopes are coordinatewise
increasing, and D_K>0 ensures every earlier denominator positive.
This proves the shared vector (AH3) for all patterns with at most K holes.

Within this particular degree-weight certificate, for fixed m,n,k,epsilon,
all four coordinates improve as t(E) increases. Stars have t=0 and
matchings have t=binomial(k,2), when these patterns fit. This is an
ordering of these sufficient certificates, not an assertion about the
true minimax laws or all possible certificates.

<a id="same-law-probability-caps-and-arithmetic-use"></a>
### Same-law probability caps and arithmetic use

The selected raw row derivative has the exact expression

```
r'_i = d_i(n−d_i)+k−sum_{j:(i,j) in E} e_j
      <= k+d_i(n−d_i−1).
```

Consequently, since epsilon(n−2)<=1,

```
raw row mass = n−d_i+epsilon r'_i <= n+k epsilon.
```

The same argument gives raw column mass <=m+k epsilon. The disjoint
incident-hole observation above gives every raw point mass <=1+k epsilon.
Normalize by Z>=D_k to obtain (AH4). This point cap is different from
the old indicator-weight matching law's 1+epsilon cap.

Let an arbitrary old law mu index varying row/column sets and arbitrary
hole patterns E_x, always of size at most K and with the same m,n.
Use the conditional law rho_x above in each fibre. The old marginal is
exactly preserved. Apply (AH2) with the four old complete block loads,
then integrate using the common diagonal (AH3), to obtain

```
Gamma_new <= F_K Gamma_old,
F_K = sum lambda_K = 1+3(m+n+3+2K epsilon)/D_K.             (AH8)
```

The existing convex-concentration reduction allows each block's residue
choices to vary independently by original cofactor. Actual original
labels must remain distinct. This argument neither assumes independent
old coordinates nor mixes different selected old laws. The caps (AH4)
hold for the very same conditional laws and can be used in the existing
full-height extension and weighted-profile arguments.

One may retain the actual k(x) envelope. Since every complete old block
load includes the unit cofactor and hence is at least 1, subtraction gives

```
Gamma_new <= F_K Gamma_old − E_mu[F_K−F_(k(x))].           (AH9)
```

This is the same valid unit-load rebate as in the matching case, now for
arbitrary point-hole geometry. Any sharper use of H or t(E) must retain
the same-law weighted old-load bookkeeping.

<a id="concrete-m10n12k12-boundary"></a>
### Concrete m=10,n=12,K=12 boundary

For the coarse common envelope, compare with the uniform-count factor
`F0_K=1+3(m+n+3)/(mn−K)`. Exact algebra gives

```
F0_K−F_K = 3K epsilon B_K / [(mn−K)D_K],
B_K=m^2+n^2+(2−K)(m+n)−K−3.
```

For m=10,n=12 this is B_K=285−23K. Thus the envelope is strictly better
for every integer 1<=K<=12 and epsilon>0; at K=12, B_K=9. Choosing the
conservative epsilon=1/(207 K) gives

```
epsilon=1/2484,
D_12=2485/23,
F_12=12632/7455,
R_12=1/9,
C_12=2071/22365,
a_12=208/22365.
```

The strict gain over the uniform-count factor 61/36 is exactly 1/89460.
All 12 point exclusions are allowed in arbitrary positions, including
an entirely removed row. The strict-improvement cutoff 12 belongs to
this sufficient envelope; PSD validity itself extends further whenever
the stated support and D_K positivity conditions hold.

The adjacent verifier checks 11 exact polynomial identities and four
nonnegative-coefficient certificates for these formulas. The graph-counting
and anchored-star arguments above prove the all-pattern statement. The
matching theorem, weighted-rectangle concentration and established SDP
framework are reused; the degree-weight construction supplies the new estimate.

`D5.S3.Arith.Congruence.ArbitraryHoleGram.degree_reweighted_grid_second_moment_le`
in [ArbitraryHoleGram.lean](../../../../D5/S3/Arith/Congruence/ArbitraryHoleGram.lean)
formalizes the unnormalized weighted grid inequality for arbitrary finite
row and column carriers of cardinality at least three, arbitrary hole
relations, and the stated nonnegative small perturbation. Its proof derives
the incidence budgets and both Gram cases from the relation. Normalization,
the denominator lower bound, integration with arithmetic head laws, and
the tail continuation remain ordinary proof obligations. The later
zero-perturbation extension to axes of size one or two is also supplied by
an ordinary Laplacian proof, not by this Lean declaration. No
literature-priority claim is made.

<a id="mean-hole-count-and-the-complete-comparison-profile"></a>
## Mean hole count and the complete comparison profile

This result combines the degree-weighted point-hole kernel with the
repository's existing weighted conditional comparison, old 315 convex
profile, and high-digit lift. Its improvement comes from retaining the
correlation between hole count and old test loads. Replacing a supremum
density by its average while keeping the original comparator would not
be justified.

<a id="kernel-inputs-and-one-actual-law"></a>
### Kernel inputs and one actual law

Use one old probability μ with common complete-load comparator X,
EX=M=271/86 and Γ(μ)≤G=1131/86. Above every old point x suppose there is
a 10×12 rectangle of first 11/13 digits. Its row and column sets may move
with x. Delete k(x) arbitrary cells, where 0≤k(x)≤K≤12, and suppose the
remaining cells avoid all actual classes with both new exponents at
most one. No matching assumption is made.

Use the degree-weighted kernel on that punctured rectangle, with one
common 0≤ε≤1/(207K). A surviving cell (i,j) receives unnormalized weight
1+ε(d_i+e_j), where d_i,e_j are the row/column hole degrees. The kernel
construction gives the following common bounds at hole count j:

    D_j=120−j+εj(21−j),
    R_j=(12+jε)/D_j,       C_j=(10+jε)/D_j,
    a_j=(1+jε)/D_j,        d_j=120a_j,
    F_j=1+(75+6jε)/D_j.                                      (VH1)

Here R,C,a are row, column and atom caps; d is the density cap relative
to the full uniform 10×12 rectangle. F is the sum of the common diagonal
quadratic coefficients

    1+(23+2jε)/D_j, 2(13+jε)/D_j, 2(11+jε)/D_j, 4/D_j.

The proof of this degree-weighted kernel, including wholly deleted rows
or columns, is a separate input. Its actual normalization may exceed
D_j; all displayed quantities are upper bounds, which is sufficient.

Uniformly lift all additional 11/13 digits to their full finite original
heights. Denote this probability by ν0. After deleting all actual high
classes, condition once, producing ν. All bounds below refer to these
same two laws, without choosing a new law for each test load.

Suppose in addition

    Eμ k≤M.                                                   (VH2)

For actual point holes from distinct original mixed moduli 11·13·d,
d|315, this follows because their activation count is bounded by one
complete old load. There are only 12 old divisor labels, so K=12 applies
automatically. Repeated forbidden cells reduce k. Virtual added holes
must not be counted under (VH2) without a separate justification.
