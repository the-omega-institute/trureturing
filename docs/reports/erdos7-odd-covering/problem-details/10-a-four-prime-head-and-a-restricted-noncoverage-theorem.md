[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](09-quantitative-extension-of-the-old-prime-powers.md) · [Next](11-current-bounds-and-comparisons.md)

<a id="a-four-prime-head-and-a-restricted-noncoverage-theorem"></a>
### A four-prime head and a restricted noncoverage theorem

**Theorem.** A finite family of residue classes with distinct odd moduli
greater than one cannot cover the integers if every prime divisor of every
modulus belongs to

\[
 \{3,5,7,11\}\ \cup\ \{p:\ p\text{ prime},\ p\ge67\}.
 \tag{P1}
\]

There is no bound on the exponents, the number of large prime divisors, or the
number of prime divisors of a single modulus. Equivalently, any hypothetical
distinct odd covering must use a modulus divisible by at least one of the
primes from 13 through 61. This is a restricted theorem, not the full conjecture.

The head estimate used to prove it is the following uniform statement.
For any finite distinct-modulus family supported on `{3,5,7,11}`, its complete
survivor set is nonempty, and the uniform survivor probability satisfies

\[
 \boxed{\Gamma\le C_4:=\frac{4939031}{47730}<103.478546.}
 \tag{P2}
\]

**Cylinder profiles.** Fix a finite family and restrict it to each prime
subset `S`. Let `μ_S` be the uniform probability on its complete survivor set,
when nonempty. A profile `c_S(T)>0`, `T⊆S`, with `c_S(∅)=1`, bounds every
cylinder supported on `T` by

\[
 \mu_S(x\equiv a\pmod{\prod_{p\in T}p^{e_p}})
 \le\frac{c_S(T)}{\prod_{p\in T}p^{e_p}}\qquad(e_p\ge1).
\]

Projection to sub-divisors yields the stronger envelope, for nonnegative
exponent vectors `e`,

\[
 u_c(e)=\min_{T\subseteq\operatorname{supp}(e)}
           \frac{c(T)}{\prod_{p\in T}p^{e_p}},\qquad
 R(c)=\sum_{e\ne0}u_c(e),\qquad
 K(c)=\sum_e\left(\prod_p(2e_p+1)\right)u_c(e).
 \tag{P3}
\]

These are sums over all finite nonnegative exponent vectors, providing bounds
uniform in the finite height of the given family. They imply
`∑_{1<d|Q} max_a μ_S(a mod d)≤R(c)` and `Γ_Q(μ_S)≤K(c)`.
For the latter, expand a squared layout load. Compatible pairs intersect in
one cylinder modulo their least common multiple; incompatible pairs contribute
zero. For each prime, `2e+1` ordered exponent pairs have maximum `e`.
No independence of `μ_S` is used.

**Construction of profiles.** Start with `c_∅(∅)=1`, `R(c_∅)=0`.
For a prime `p`, the set `X_p` avoiding the pure `p`-power classes has uniform
density at least `(p−2)/(p−1)`. Indeed the sum of the reciprocals of distinct
positive powers of `p` is at most `1/(p−1)`. Its uniform law `ρ_p` therefore
has cylinder caps `C_p p^{−e}`, where `C_p=(p−1)/(p−2)`.

Suppose profiles and nonempty survivors have been established for `A=S\{p}`.
Start with `ν=μ_A×ρ_p`. Every remaining forbidden class has modulus `dp^e`
with `d>1` supported on `A`. There is at most one class for each pair `(d,e)`,
so their total `ν`-mass is at most

\[
 b_{A,p}=\frac{R(c_A)}{p-2}.
\]

If `b_{A,p}<1`, condition on avoiding these remaining classes. The result is
uniform on the complete survivor set for `S`, and has the valid profile

\[
 c^{(p)}_S(T)=\frac{c_A(T\setminus\{p\})}{1-b_{A,p}}
       \begin{cases}C_p,&p\in T,\\1,&p\notin T,\end{cases}
 \qquad T\ne\varnothing.
 \tag{P4}
\]

Every admissible choice of last prime produces **the same** uniform probability
on complete survivors. Thus take `c_S(T)=min_p c^{(p)}_S(T)` separately for
each support, over last primes with `b_{A,p}<1`. This is not a minimum over
different measures. The marginal on `A` is reweighted by its actual conditional
survival fraction; a completely killed fibre receives mass zero. No preservation
of each old fibre is assumed.

Applying (P3)–(P4) to all subsets of `{3,5,7,11}` gives

\[
 R(c_{\{3,5,7,11\}})=\frac{1514}{145},\qquad
 K(c_{\{3,5,7,11\}})=\frac{3885}{29}.
 \tag{P5}
\]

The last-prime deletion bounds for `p=3,5,7,11` are respectively
`34/39`, `215/261`, `137/195`, `77/135`, all strictly below one.
The complete resulting profile is:

| `T` | `c(T)` | `T` | `c(T)` |
|---|---:|---|---:|
| ∅ | 1 | {3,5} | 540/29 |
| {3} | 378/29 | {3,7} | 468/29 |
| {5} | 216/29 | {3,11} | 420/29 |
| {7} | 117/29 | {5,7} | 288/29 |
| {11} | 75/29 | {5,11} | 240/29 |
| {7,11} | 180/29 | {3,5,7} | 648/29 |
| {3,5,11} | 600/29 | {3,7,11} | 540/29 |
| {5,7,11} | 360/29 | {3,5,7,11} | 720/29 |

**Exact evaluation of the infinite sums.** For each prime choose `L_p≥0`
satisfying

\[
 p^{L_p+1}\ge\max_{T\subseteq S\setminus\{p\}}
                         \frac{c(T\cup\{p\})}{c(T)}.
\]

If `e_p>L_p`, including `p` in a candidate support in (P3) cannot increase
its value. Thus a minimizing support can include all such tail coordinates.
Partition each exponent into the individual values `0,…,L_p` and one tail
state `e_p>L_p`. For a cell with tail coordinates `J` and positive bounded
coordinates `I`, its envelope is exactly

\[
 \left(\prod_{p\in J}p^{-e_p}\right)
 \min_{T\subseteq I}\frac{c(J\cup T)}{\prod_{p\in T}p^{e_p}}.
\]

Sum the tail coordinates with the exact identities

\[
 \sum_{e>L}p^{-e}=\frac{1}{p^L(p-1)},\qquad
 \sum_{e>L}(2e+1)p^{-e}
   =\frac{(2L+3)(p-1)+2}{p^L(p-1)^2}.
\]

For the displayed four-prime profile the cutoffs are `(2,1,0,0)`, so only
48 cells are needed. The same construction evaluates each predecessor profile
exactly. The [profile verifier](../elementary-checks/verify_uniform_head_profile.py)
checks the rational recurrence, existence of an admissible normalization at
every nonempty subset, (P5), and its strict comparison to the tail seed.
It uses Python 3.9+ standard-library arithmetic and no residue enumeration:

```sh
python3 docs/reports/erdos7-odd-covering/elementary-checks/verify_uniform_head_profile.py
```

For an independent arithmetic bound, summing (P3) on the box `0≤e_p≤6`
and bounding the complement by the raw support coefficients and exact geometric
tails gives `K<134`, consistent with (P5). The cutoff-cell calculation retains
the sharper exact value. These finite calculations certify the numerical
parameters; the profile induction proves their validity for every residue
assignment and every finite height.

**Refinement using a surviving ternary fibre.** For a two-prime family on
`3^H q^J`, with prime `q≥5`, the same uniform complete-survivor law satisfies

\[
 \mu(x\equiv a\pmod3)\le\frac{2(q-2)}{3q-8}.
 \tag{P6}
\]

To prove this, let `Y` avoid the pure `q`-power classes and write
`z=|Y|/q^J≥1−y`, where `y=1/(q−1)≤1/4`. If the target ternary root
is excluded by the modulus-3 class its mass is zero. Otherwise another root
`r mod 3` is also not excluded by that class. Inside `r`, pure powers
`3^h`, `h≥2`, remove a fraction at most `1/2` of the ternary coordinate.
Classes of modulus `3q^j` remove at most `y` of the `q` coordinate.
These conditions concern separate coordinates, leaving relative density
at least `(z−y)/2`. The remaining mixed classes, of modulus `3^h q^j`
with `h≥2`, have total relative density at most `y/2`. Thus complete
survivors in `r` have relative density at least `z/2−y>0`.

The target root has relative survivor density at most `z`, so its normalized
mass is at most `z/(3z/2−y)`. This expression decreases with `z`, and
substituting `z≥1−y` proves (P6). Missing moduli only improve the estimates.
In particular the `{3,5}` bound is `6/7`; it uses actual survival in another
root, with no assumption that every fibre survives.

For each support `T` containing 3, augment `c(T)` with a coefficient `b(T)`
meaning

\[
 \mu\left(x\equiv a\pmod{3^{e_3}\prod_{q\in T\setminus\{3\}}q^{e_q}}\right)
 \le\frac{b(T)}{3\prod_{q\in T\setminus\{3\}}q^{e_q}}
 \qquad(e_3\ge1).
 \tag{P7}
\]

This follows by projection to exponent one of the ternary coordinate.
The envelope is now the minimum of all projected `c` and `b` bounds.
When adjoining a prime other than 3, propagate both coefficients by (P4),
using the refined predecessor `R`; when adjoining 3, the new `b` candidate
equals the new `c` candidate. Take minima across admissible orders for both
families. At each two-prime subset `{3,q}`, additionally replace `b({3})`
by its minimum with `6(q−2)/(3q−8)`, as justified by (P6).
Every bound concerns the same uniform complete-survivor law.

The finite-cell evaluation above still applies. For a nonternary coordinate
also require `p^{L_p+1}≥b(T∪{p})/b(T)` for supports containing 3 and
omitting `p`. Require `L_3≥1` and
`3^{L_3+1}≥3c(T)/b(T)` for every support containing 3. Above that
ternary cutoff, the full-exponent `c` term dominates its `b` counterpart;
the remaining tails factor geometrically as before. The resulting exact
envelope sums are

| Prime support | `R` | `K`, an upper bound on `Γ` |
|---|---:|---:|
| {3,5} | 33/14 | 429/28 |
| {3,5,7} | 36903/7585 | 336438/7585 |
| {3,5,7,11} | 7621078040639947/773234757691590 | 47039764798810808/386617378845795 |

The last row gives a uniform head bound; the joint budget below strengthens
it first to (B6), then the shared-density argument to (P2).
Its cutoffs remain `(2,1,0,0)`.
The [refined profile verifier](../elementary-checks/verify_refined_head_profile.py)
checks this recurrence with exact rational arithmetic and an independent
finite-box sum with a geometric bound on the complement. The simpler
support-only estimate (P5) remains valid. Neither calculation enumerates
residue assignments; universality follows from the two profile inductions
and the root-fibre argument.

**Joint deletion budget for the two ternary roots.** Individual cylinder
bounds can be strengthened by bounding their entire weighted sum with the
same family's deletion budget. For a `{3,q}` family let `X,Y` avoid the
pure powers and put

\[
 x=|X|/3^H\ge\tfrac12,\quad z=|Y|/q^J\ge1-y,\quad
 y=\frac1{q-1},\quad a_q=\frac{3q-1}{(q-1)^2},\quad
 s=|S|/(3^Hq^J)\ge xz-y/2>0.
\]

Write `M(a,b)` for the maximum mass of a cylinder modulo `3^a q^b`.
Counting its intersection with `X×Y` gives
`M(a,0)≤z/(3^a s)`, `M(0,b)≤x/(q^b s)` and
`M(a,b)≤1/(3^a q^b s)` for positive exponents. Retain the actual root
maximum `ρ=M(1,0)` separately. Summing all other exponents geometrically
bounds the finite nonunit cylinder sum `R_μ` and the finite weighted
cylinder sum `K_μ` by

\[
 R_\mu\le\rho+\frac{z/6+xy+y/2}{s},\qquad
 K_\mu\le1+3\rho+\frac{z+a_qx+2a_q}{s}.
 \tag{P9}
\]

As before `Γ(μ)≤K_μ`. These sums are over the actual finite divisors;
infinite geometric sums only supply upper bounds.

Suppose first that the pure modulus-3 class is present. Of the other two
roots designate one attaining `ρ` as the target. Let `w,v` be their
relative pure-ternary survivor densities. Since the higher pure powers
have total density at most `1/6` in the full ternary period,

\[
 \tfrac12\le w,v\le1,\quad w+v\ge\tfrac32,\quad x=(w+v)/3.
\]

Let `α,β` be the densities **inside `Y`**, measured against the full
`q` period, of the unions forbidden by first-level mixed moduli `3q^b`
in the two roots. Distinct moduli imply `α,β≥0` and `α+β≤y`.
Let `t_1,t_2` be the actual additional full-period densities removed from
the remaining sets by mixed moduli with ternary exponent at least two.
Then `t_1,t_2≥0` and `t_1+t_2≤y/6`. The actual complete root densities are
exactly

\[
 n=w(z-\alpha)/3-t_1,\quad m=v(z-\beta)/3-t_2,
 \qquad s=n+m,\quad\rho=n/(n+m).
\]

Thus (P9) has numerators `n+C_R` and `3n+C_K`, where
`C_R=z/6+xy+y/2>0` and `C_K=z+a_qx+2a_q>0`; the second fraction has
an additional constant one. Move all `t_1` to the other root. This keeps
the denominator fixed and increases `n`. Next increase the other-root
deletion to `y/6`, keeping the numerators fixed and decreasing the
denominator. Both changes increase the bounds. This is a relaxation of
the actual budgets, with no claim that the altered parameters describe
another residue family. All denominators remain positive: throughout the
allowed region the resulting roots satisfy

\[
 n=w(z-\alpha)/3\ge(1-2y)/6>0,\qquad
 m=v(z-\beta)/3-y/6\ge(1-3y)/6>0.
\]

It remains to maximize the two fractions at these relaxed `n,m`.
With the other variables fixed, each is a ratio of affine functions of
`(α,β)`, then of `(w,v)`, then of `z`, with positive denominator.
The maxima therefore occur among the eighteen choices

\[
 (\alpha,\beta)\in\{(0,0),(y,0),(0,y)\},\quad
 (w,v)\in\{(1/2,1),(1,1/2),(1,1)\},\quad z\in\{1-y,1\}.
 \tag{P10}
\]

For completeness, if affine `N,D` have `D>0` and
`u=∑_i θ_i u_i` is a convex combination of vertices, then
`N(u)/D(u)=∑_i[θ_i D(u_i)/D(u)] [N(u_i)/D(u_i)]`.
These are nonnegative weights summing to one, which proves each vertex
reduction. Applying it successively proves (P10) without a numerical
optimization assumption.

If the modulus-3 class is absent, `x≥5/6`. The unsplit estimates instead give

\[
 R_\mu\le\frac{z/2+xy+y/2}{xz-y/2},\qquad
 K_\mu\le1+\frac{2z+a_qx+2a_q}{xz-y/2}.
 \tag{P11}
\]

Both decrease in `x` and `z`, so use `x=5/6,z=1−y`.
For example, the derivative numerators of the first fraction are
`−(y²+z²+zy)/2` and `−y/4−x²y−xy/2`; those of the second are
`−a_qy/2−2z²−2a_qz` and `−y−a_qx²−2a_qx`, all strictly negative.
The resulting bounds are below those of (P10):

| `q` | Uniform `R_μ` bound | Uniform `K_μ` bound | Bounds if modulus 3 is absent |
|---:|---:|---:|---:|
| 5 | 13/6 | 59/4 | 17/12, 215/24 |
| 7 | 21/13 | 29/3 | 23/22, 208/33 |
| 11 | 33/25 | 29/4 | 5/6, 73/15 |

For `q=5`, both maxima in (P10) occur at
`w=1,v=1/2,z=3/4,α=1/4,β=0`, giving `n=1/6,m=1/12`.
The same eighteen exact evaluations give the other rows.

These are bounds for entire sums of the **same** uniform survivor law.
In the profile recurrence use the smaller of its envelope bound and this
joint `R_μ` bound for the next deletion cost `R/(p−2)`. Retain the
individual `c,b` inequalities and similarly take the smaller valid
whole-`K_μ` bound. The new `R` need not equal the sum of the old envelope.
This strengthened induction gives

\[
 R_{\{3,5,7\}}\le\frac{9937}{2142},\quad
 K_{\{3,5,7\}}\le\frac{179315}{4284},\qquad
 R_{\{3,5,7,11\}}\le\frac{1200449891}{129232735},\quad
 K_{\{3,5,7,11\}}\le\frac{28643873521}{258465470}.
\]

This is an intermediate head estimate. The refined profile verifier checks
the eighteen vertices, the absent-modulus branch, this induction and
continuation from this intermediate seed. Its independent finite-box
calculation brackets that profile envelope. The stronger bounds (B6) and (P2) use
the nine-cell and coupled-density arguments below and their separate verifier.

**Joint budgets for the five surviving modulo-9 cells.** Retain the notation
\(x,z,y,a_q,s,M\) of (P9). Suppose first that the family has a pure
modulus-3 class and a pure modulus-9 class outside that forbidden root.
Exactly five modulo-9 cells remain. Label their roots
\(r(j)=(0,0,1,1,1)\), for \(j=1,\ldots,5\). Let \(w_j\) be the relative
density in cell \(j\) remaining after all pure ternary exclusions. Since
the pure powers \(3^a\), \(a\ge3\), have total ambient density at most
\(1/18\),

\[
 \tfrac12\le w_j\le1,\qquad
 \sum_j(1-w_j)\le\tfrac12,\qquad x=\tfrac19\sum_jw_j\ge\tfrac12.
\]

Let \(Y\) be the pure \(q\)-power survivor set, of density \(z\).
For each good root \(r\), let \(A_r\) be the union of its \(q\)-coordinate
exclusions from moduli \(3q^b\), and let
\(\alpha_r=|A_r\cap Y|/q^J\). For each good modulo-9 cell \(j\), let
\(B_j\) be the union from moduli \(9q^b\), and define the **additional**
removed density
\(\beta_j=|B_j\cap(Y\setminus A_{r(j)})|/q^J\).
Thus the remaining \(q\)-coordinate density in cell \(j\) is exactly
\(z-\alpha_{r(j)}-\beta_j\), and distinct moduli give the shared budgets

\[
 \alpha_r,\beta_j\ge0,\qquad \alpha_0+\alpha_1\le y,\qquad
 \sum_j\beta_j\le y.
\]

Let \(t_j\) be the actual additional ambient density deleted in cell \(j\)
by mixed classes with ternary exponent at least three. Then
\(t_j\ge0\) and \(\sum_jt_j\le y/18\). The complete cell densities are
therefore exactly

\[
 n_j=\frac{w_j(z-\alpha_{r(j)}-\beta_j)}9-t_j,\qquad
 s=\sum_jn_j.
\]

All variables describe the same residue family. In particular the budgets
are shared among cells. Put
\(N_1=\max_r\sum_{j:r(j)=r}n_j\) and \(N_2=\max_jn_j\).
These maxima may occur in different roots. Keeping both actual maxima
and using the ordinary caps only at higher ternary exponents gives

\[
 R_\mu\le\frac{N_1+N_2+z/18+xy+y/2}{s},\qquad
 K_\mu\le1+\frac{3N_1+5N_2+4z/9+a_qx+2a_q}{s}.
 \tag{P12}
\]

Here \(\sum_{a\ge3}3^{-a}=1/18\) and
\(\sum_{a\ge3}(2a+1)3^{-a}=4/9\); the pure-\(q\) and mixed terms are
the same geometric sums as in (P9). This bounds the entire cylinder sums
and hence also \(\Gamma\le K_\mu\).

The relaxed parameter region given by these budgets contains every actual
family. It has nonnegative cells and a uniformly positive denominator:

\[
 n_j\ge\frac{z-3y}{18}\ge\frac{1-4y}{18}\ge0,\qquad
 s\ge xz-\frac y2\ge\frac12-y\ge\frac14.
\]

For the second inequality, first-level mixed deletion is at most \(y/3\),
second-level deletion at most \(y/9\), and the remaining deletion at most
\(y/18\). Their sum is \(y/2\). A cell can be empty when \(q=5\); the
proof never conditions on that cell.

For a fixed target root and target modulo-9 cell, the expressions in (P12)
are linear-fractional separately in the five parameter groups
\((1-w_j)_j\), \(\alpha\), \(\beta\), \(t\), and \(z\), with positive
denominator throughout. The vertex identity used for (P10) therefore
applies successively to each group. Taking maxima over target roots and
cells commutes with taking parameter maxima. The budget simplexes have
respectively \(6,3,6,6\) vertices, and \(z\in[1-y,1]\) has two endpoints,
giving exactly \(6\cdot3\cdot6\cdot6\cdot2=1296\) rational evaluations.

The missing-class cases require a separate bound. If modulus 3 is absent,
\(x\ge5/6\). If it is present but modulus 9 is absent or its class is
contained in the forbidden root, only powers with exponent at least three
can remove more pure ternary mass, so \(x\ge2/3-1/18=11/18\).
Both cases are covered by (P11) with \(x=11/18,z=1-y\), since those
fractions decrease in \(x,z\). The exact bounds are:

| \(q\) | \(R_\mu\) from (P12) | \(K_\mu\) from (P12) | Missing or ineffective pure classes: \(R_\mu,K_\mu\) |
|---:|---:|---:|---:|
| 5 | 15/7 | 173/12 | 47/24, 593/48 |
| 7 | 21/13 | 19/2 | 65/46, 574/69 |
| 11 | 33/25 | 181/25 | 101/90, 1411/225 |

The missing-class bounds are smaller in every row. This also handles
finite heights below two. In the recurrence, retain every individual
\(c,b\) bound and use the smaller of the profile sum and the appropriate
whole-sum bound for the next deletion cost. No identity between the new
\(R_\mu\) bound and the old envelope sum is asserted.

**A sharper mixed-head mass under the pure-survivor product.** For every
finite original family on arbitrary powers of 3, 5 and 7, let \(P_0\)
be the product of uniform laws on its actual pure-prime-power survivors.
The union of its mixed-head classes satisfies
\[
 P_0(B_{\mathrm{mixed},357})\le\frac{82}{135}<\frac23.
 \tag{CM1}
\]
This is the same unconditioned head law as in (PH1)--(PH4). Its tail
conditional cylinder caps and complete-layout second-moment majorant
therefore remain valid. The displayed PH numerical certificates retain
their already sufficient input \(2/3\).

To prove (CM1), let \(x,z\) be the ambient pure survivor densities for
3 and 5, and let \(s,R_{35}\) be the density and uniform nonunit cylinder
sum of the complete actual \(\{3,5\}\)-survivors. The pure-7 cylinder sum
is at most \(1/5\). The probability \(\lambda\) under \(P_0\) of avoiding
all mixed-head classes consequently obeys
\[
 \lambda\ge\frac{s}{xz}\left(1-\frac{R_{35}}5\right).
\]
When both low pure ternary exclusions are effective, use the five cells
of (P12), with root labels \((0,0,1,1,1)\). Their shared budgets specialize to
\[
 \sum_j(1-w_j)\le\tfrac12,\quad
 \sum_r\alpha_r\le\tfrac14,\quad\sum_j\beta_j\le\tfrac14,\quad
 \sum_jt_j\le\tfrac1{72},\qquad \tfrac34\le z\le1,
\]
where all deficits and deletions are nonnegative. Retain the actual
quantities \(x=\sum_jw_j/9\),
\(n_j=w_j(z-\alpha_{r(j)}-\beta_j)/9-t_j\), and \(s=\sum_jn_j\).
The positivity bounds for (P12) give \(n_j\ge0\) and \(s\ge1/4\).
Writing \(N_1=\max_r\sum_{r(j)=r}n_j\), \(N_2=\max_jn_j\), (P12) gives
\[
 sR_{35}\le T:=N_1+N_2+z/18+x/4+1/8,\qquad
 \lambda\ge\frac{s-T/5}{xz}\ge\frac{53}{135}.           \tag{CM2}
\]
For fixed target root and cell, the last quotient has separately affine
numerator and positive denominator in the five groups
\(1-w,\alpha,\beta,t,z\). The denominator-weighted vertex identity used
for (P10) applies successively. Minimizing over target root and cell
produces the two maxima in \(T\); the parameter region therefore reduces
to \(6\cdot3\cdot6\cdot6\cdot2=1296\) rational vertices.
Their exact minimum is \(53/135\), attained in this relaxation at
\[
 1-w=(1/2,0,0,0,0),\quad \alpha=(0,1/4),\quad
 \beta=(0,1/4,0,0,0),\quad t=(1/72,0,0,0,0),\quad z=3/4.
\]
Here \(x=1/2\), \(n=(1/36,1/18,1/18,1/18,1/18)\),
\(s=1/4\), and \(T=37/72\). Attainment by an actual residue family is
not asserted.

If modulus 3 is absent, \(x\ge5/6\); if its class is present but the
pure modulus-9 class is absent or contained in the forbidden root,
\(x\ge11/18\). These cases include physical heights below two.
The unsplit bounds \(s\ge xz-1/8\) and
\(sR_{35}\le z/2+x/4+1/8\) give
\[
 \lambda\ge\frac{xz-1/8-(z/2+x/4+1/8)/5}{xz}.
\]
This expression increases in \(x,z\). At \(z=3/4\), the two lower
values of \(x\) give \(43/75\) and \(73/165\), both above \(53/135\).
This proves (CM2) in every case, and hence (CM1). The existing
[verifier](../verify_star_block_obstruction.py)
records the exact vertex minimum and both missing-class branches under
**head_mixed_mass_improvement** in its
[certificate](../certificates/star_block_obstruction_certificate.json).

**Sharpness of (CM1) for actual pure-survivor product laws.** The constant
\(82/135\) is the supremum over actual finite \(\{3,5,7\}\)-families under
the prescribed law \(P_0\). The following construction realizes every
prime-7 union bound as an equality and approaches that supremum. This is
an ordinary mathematical result; the finite residue checks below are not
an end-to-end Lean proof.

Fix \(H\ge3\) and \(K,L\ge1\). First assign one class to every nonunit
divisor of \(3^H5^K\). The pure ternary classes are
\[
 0\pmod3,\qquad4\pmod9,\qquad
 3^{a-1}-8\pmod{3^a}\quad(3\le a\le H),
\]
and the pure quinary class at depth \(b\) is
\(5^{b-1}-1\pmod{5^b}\). For each \(1\le b\le K\), choose the mixed
classes by these CRT coordinates:

| Modulus | Ternary residue | Quinary residue |
|---|---:|---:|
| \(3\cdot5^b\) | \(2\pmod3\) | \(2\cdot5^{b-1}-1\pmod{5^b}\) |
| \(9\cdot5^b\) | \(2\pmod9\) | \(3\cdot5^{b-1}-1\pmod{5^b}\) |
| \(3^a5^b,\ 3\le a\le H\) | \(2\cdot3^{a-1}-8\pmod{3^a}\) | \(2\cdot5^{b-1}-1\pmod{5^b}\) |

Put
\[
 A=\sum_{a=3}^H3^{-a}=\frac{1-3^{-(H-2)}}{18},\qquad
 r=\sum_{b=1}^K5^{-b}=\frac{1-5^{-K}}4,\qquad
 x=\frac59-A,\quad z=1-r.
\]
Inside the cell \(1\pmod9\), the higher pure ternary classes and the
higher mixed ternary coordinates are the disjoint suffix exits
\(2^k0\) and \(2^k1\), respectively, in least-significant-digit order.
The pure, first mixed, and second mixed quinary coordinates are likewise
the mutually disjoint exits \(4^k0,4^k1,4^k2\). Thus \(x,z\) are exactly
the pure survivor densities. The complete pair-survivor set \(S\) has
the following ambient masses in cells \((1,7,2,5,8)\pmod9\):
\[
 \left(\frac z9-A,\ \frac z9,\ \frac{1-3r}9,
             \frac{1-2r}9,\ \frac{1-2r}9\right),\qquad
 s=\frac{|S|}{3^H5^K}=x-r.                            \tag{CM3}
\]
The largest root and cell masses are
\(N_1=(3-7r)/9\) and \(N_2=z/9\). Indeed, the long root exceeds the
short root by \((1-5r)/9+A\ge1/108\); the clean cell \(7\pmod9\)
is the largest cell.

Write \(C_{a,b}\) for the largest ambient mass of \(S\) in a cylinder
modulo \(3^a5^b\). Every maximum is exactly
\[
 \begin{aligned}
 C_{1,0}&=N_1,& C_{2,0}&=N_2,&
 C_{a,0}&=z3^{-a}&& (a\ge3),\\
 C_{0,b}&=x5^{-b}&& (b\ge1),&
 C_{a,b}&=3^{-a}5^{-b}&& (a,b\ge1).
 \end{aligned}                                      \tag{CM4}
\]
For pure ternary depths at least two, use cylinders in the clean cell
\(7\pmod9\). For pure quinary depths use the clean exits \(4^k3\),
which avoid all three earlier quinary exit families. Their product with
the long ternary root, or with the clean short cell, supplies full mixed
cylinders. These choices may differ between divisors, as the definition
of \(R_{35}\) permits; no common cylinder centre is asserted. Since
\(\sum_{a=1}^H3^{-a}=4/9+A=1-x\), (CM4) gives
\[
 T_{H,K}:=sR_{35}
   =N_1+N_2+zA+xr+(1-x)r
   =\frac{4+r}{9}+(1-r)A.                           \tag{CM5}
\]
In particular, \(s\to1/4\) and \(T_{H,K}\to37/72\).

To attain the subsequent prime-7 deletion bound, choose a maximizing
old cylinder for every \(d=3^a5^b>1\). Its ternary coordinate, when
present, is
\[
 g_1=2\pmod3,\qquad g_2=7\pmod9,\qquad
 g_a=3^{a-1}-2\pmod{3^a}\quad(a\ge3),
\]
and its quinary coordinate is \(f_b=4\cdot5^{b-1}-1\pmod{5^b}\).
The higher \(g_a\) are pairwise disjoint exits inside \(7\pmod9\);
the \(f_b\) are pairwise disjoint clean quinary exits. Partition these
old cylinders into five colours:

| Exponents of \(d\) | Colour |
|---|---:|
| \(b=0,\ a=1,2\) | 1 |
| \(b=0,\ a\ge3\) | 2 |
| \(a=0,\ b\ge1\) | 3 |
| \(a=1,2,\ b\ge1\) | 4 |
| \(a\ge3,\ b\ge1\) | 5 |

Within each colour the old cylinders are pairwise disjoint. Assign
the pure class \(7^{e-1}-1\pmod{7^e}\) for \(1\le e\le L\).
For each old divisor \(d>1\) of colour \(j\), assign to \(d7^e\)
the chosen old cylinder and the septenary coordinate
\[
 (j+1)7^{e-1}-1\pmod{7^e}.                           \tag{CM6}
\]
These are the suffix exits \(6^k j\), while the pure exclusions are
\(6^k0\). Distinct pairs \((j,e)\) have disjoint septenary cylinders;
for equal \((j,e)\), the old cylinders are disjoint. Consequently all
mixed classes ending at 7 are pairwise disjoint and avoid the pure
septenary exclusions. Each \(d7^e\) is a new original modulus, so its
old residue is allowed to differ from the residue assigned to \(d\).
The resulting family contains exactly one class for every nonunit
divisor of \(3^H5^K7^L\).

Let \(r_7=\sum_{e=1}^L7^{-e}=(1-7^{-L})/6\) and \(z_7=1-r_7\).
By disjointness, the mixed prime-7 classes remove exactly ambient mass
\(r_7T_{H,K}\) from \(S\) times the pure-7 survivors. Therefore the
complete actual survivor probability under \(P_0\) is exactly
\[
 \lambda_{H,K,L}
 =\frac{s z_7-r_7T_{H,K}}{xz z_7}
 =\frac{s-T_{H,K}r_7/z_7}{xz}
 \longrightarrow\frac{53}{135}.                    \tag{CM7}
\]
Together with (CM1), this proves that the actual mixed-head mass has
supremum \(82/135\). Thus imposing actual residue compatibility on
(CM2), or requiring overlap among the final prime-7 classes, cannot
uniformly reduce this constant for the prescribed pure-survivor product
law. Other choices of the head law are outside this sharpness statement.

**Exact ambient uncovered-density infimum.** Every finite distinct family
supported on \(\{3,5,7\}\) leaves ordinary uniform density strictly
greater than \(53/432\). Indeed, the product of its three actual pure
survivor densities is strictly greater than
\((1/2)(3/4)(5/6)=5/16\), because each finite geometric exclusion sum is
strictly below its infinite sum. Multiplying by (CM1)'s conditional
survivor bound \(53/135\) proves the claim. For the constructed families,
the exact ambient survivor density is
\[
 s z_7-r_7T_{H,K}
 \longrightarrow\frac14\frac56-\frac16\frac{37}{72}
 =\frac{53}{432}.                                   \tag{CM8}
\]
Thus \(53/432\) is the exact infimum over all such finite families.
The earlier pair recurrence \(\lambda\ge(4/7)\theta_{35}\ge8/21\)
implies only the smaller ambient bound \(5/42\).

The existing verifier records **cm1_actual_head_sharpness** through its
canonical certificate writer. It enumerates nine pair-head families,
checks all 126 divisor-cylinder maxima and the disjoint colour classes,
then enumerates eight complete three-prime families with
\(H=3,4\), \(K,L=1,2\). Direct CRT residue checks confirm the exact
prime-7 deletion and (CM7). The all-height construction and its limiting
sharpness are proved above.

**Exact finite densities for the two 5040 odd heads and all ternary heights.**
Among distinct nonunit divisors of \(315\), the minimum number of uncovered
residues in one period is **74**. Among distinct nonunit divisors of
\(3^H\cdot35\), for every \(H\ge3\), that minimum is
\[
 58\cdot3^{H-2}+17.                                  \tag{CM9}
\]
In particular, the minimum at \(945\) is **191**. These are minima over
all residue assignments and all subsets of the indicated divisor sets;
the constructions attaining them use every nonunit divisor once.
The corresponding sharp mixed-head probabilities under the actual
pure-survivor product are \(23/60\) at 315 and \(145/336\) at 945.
These improve the earlier (FC1)--(FC2) bounds without changing the
already valid tail certificates.

For the lower bounds, retain the actual five-cell parameters from (CM2),
but put
\[
 A=\sum_{a=3}^H3^{-a},\quad u=4/9+A,\qquad
 \sum_j(1-w_j)\le9A,\quad \sum_r\alpha_r\le1/5,\quad
 \sum_j\beta_j\le1/5,\quad\sum_jt_j\le A/5,
 \quad4/5\le z\le1.
\]
The same actual identities give \(x=\sum_jw_j/9\),
\(n_j=w_j(z-\alpha_{r(j)}-\beta_j)/9-t_j\) and
\(s=\sum_jn_j\). Since there is at most one pure septenary class,
its normalized cylinder mass is at most \(1/6\). The complete
\(\{3,5\}\) cylinder sum consequently gives
\[
 T=N_1+N_2+zA+x/5+u/5,\qquad
 \lambda\ge\frac{s-T/6}{xz}.                         \tag{CM10}
\]
Here \(N_1,N_2\) are the actual largest root and cell masses, as before.
The relaxed cells stay positive: \(n_j\ge1/90\), and \(x\ge1/2\),
\(z\ge4/5\). For each fixed \(A\), the denominator-weighted vertex
identity reduces the inequality to the same budget-simplex vertices.
At \(H=2\), the deficit and late-deletion budgets are zero, leaving
36 distinct vertices. Their exact minimum is \(37/60\).
