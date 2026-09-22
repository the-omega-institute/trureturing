[Index](../../marked_head_profile.md) · [Common-law construction](402-one-common-law-with-a-universal-row-compatible-bound.md) · [Minimum-source structure](403-root-structure-of-sharp-minimum-sources.md)

# A sharper common law and its witness-choice boundary

Every source satisfying the six pairwise ternary-tree conditions and
the full five-ary projection condition admits one actual probability
whose squared-load bound for all independently phased original
divisor labels is strictly below

\[
\frac{309}{50}=6.18.
\tag{SC1}
\]

The probability uses the full-tree and pair-tree witnesses of report
402, with full-tree weight `3/5`. This improves the universal ceiling
`168/25` from that report. The new ceiling is sharp in the limit over
arbitrary permitted witness choices for this fixed mixture. It still
exceeds six by `9/50` and does not prove the desired finite comparison
`Gamma_(1,K)<=2t_K` or resolve unrestricted Erdős #7.

A separate pair of actual witness families shows that no fixed mixing
coefficient makes this arbitrary-witness construction uniformly bounded
by six. This is a restriction on the construction's guarantee, not a
lower bound on the minimum over all probabilities supported on a source.
The proofs and exact research checks here are not Lean-certified.

## One supported law and its row-sensitive caps

Let `K>=0`, and let `R` be a subset of
`{1,2,3,4} times Z/7^K`. Digits are read from lowest to highest.
Assume every pair of row fibres contains a complete ternary tree of
depth `K`, and the full projection contains a complete five-ary tree
of depth `K`. A complete tree selects exactly its stated number of
children at every selected nonleaf. Three active rows are permitted.

Choose any such five-tree and label each of its leaves by an available
source row. Its uniform labelled law is `mu`; put
`beta_r=mu(row r)`. For each pair `{r,s}`, choose and label any actual
ternary-tree witness, giving its uniform law `eta_rs`. Set

\[
\omega=\sum_{r<s}\frac{1-\beta_r-\beta_s}{3}\eta_{rs},
\qquad \nu=\frac35\mu+\frac25\omega.
\tag{SC2}
\]

The pair weights are nonnegative and sum to one. Thus SC2 is one
probability on the original source, chosen before the adversarial
phases. No conditional or separately optimized laws are substituted.

Identify a point `(r,y)` with its CRT residue modulo `5*7^K`. Let

\[
\Gamma_{1,K}(\nu)=
\max_{(a_d)_{d\mid5\cdot7^K}}
\mathbb E_\nu\left(\sum_{d\mid5\cdot7^K}
\mathbf1_{x\equiv a_d\pmod d}\right)^2.
\tag{SC3}
\]

Every original divisor label, including divisor one, is retained;
all its phase choices are independent. For depth `j`, write

\[
f_j=5^{-j},\quad q_j=3^{-j},\quad
m_j=\frac35f_j+\frac25q_j,\quad
c_j(b)=\frac35\min(b,f_j)+\frac4{15}(1-b)q_j.
\tag{SC4}
\]

The tree laws and the omitted-row mixture give simultaneously, for
every literal depth-`j` prefix `P`,

\[
\nu(P)\le m_j,\qquad
\nu(\{r\}\times P)\le c_j(\beta_r).
\tag{SC5}
\]

Indeed `mu(P)<=f_j`, `mu(row r intersect P)<=min(beta_r,f_j)`,
and `omega(row r intersect P)<=(2/3)(1-beta_r)q_j`, as proved
in GM4–GM7 of report 402. In particular the new depth-zero cap is
`c_0(b)=4/15+b/3`; it is not the constant `2/5` of the old mixture.

## Bounding every independent row sequence

Write `r_j` for the row of mixed divisor `5*7^j`, and let
`n_j` count the earlier occurrences of that row. The expansion of
the square, retaining zero mixed/mixed intersections between different
rows, gives the following upper bound from GM23 of report 402:

\[
\mathcal F_K(\beta,\mathbf r)=\sum_{j=0}^K(2j+1)m_j
+\sum_{j=0}^K\left[
(2j+3+2n_j)c_j(\beta_{r_j})
+2\sum_{i<j}c_j(\beta_{r_i})\right].
\tag{SC6}
\]

The coefficients count all ordered pure/pure, pure/mixed and
mixed/mixed terms. Incompatible seven-adic prefixes may remove terms,
which only lowers this bound. A mixed phase in absent row zero gives
zero load on the source and can be replaced by an actual-row phase
without decreasing the load. Thus it suffices to bound SC6 over four
actual rows and all probability vectors `beta`.

Put `u_j=max_(0<=b<=1)c_j(b)` and `v_j=c_j(1/5)`. For `j>=1`,

\[
u_j=\frac35f_j+\frac4{15}(1-f_j)q_j,\qquad
v_j=\frac35f_j+\frac{16}{75}q_j.
\tag{SC7}
\]

For depth zero, `u_0=3/5` and `v_0=1/3`.

### Constant words

A constant word through depth `N` has row contribution
`sum_(j=0)^N(6j+3)c_j(b)`, a concave piecewise linear function.
For `N>=2` its right derivative at `b=1/5` is

\[
1-\frac45\bigl(S_N(1/3)-1\bigr)
\le-\frac{11}{45}<0,
\qquad S_N(z)=\sum_{j=0}^N(2j+1)z^j.
\]

The left derivative is

\[
1+\frac{27}{5}-\frac45\bigl(S_N(1/3)-1\bigr)
\ge\frac{24}{5}>0.
\]

Consequently `b=1/5` uniquely maximizes every constant word with
`N>=2`. Its full value is

\[
A_N=\frac{12}{5}S_N(1/5)+\frac{26}{25}S_N(1/3)-\frac{36}{25}
=\frac{309}{50}-\frac{3(4N+7)}{2\,5^{N+1}}
-\frac{26(N+2)}{25\,3^N}<\frac{309}{50}.
\tag{SC8}
\]

For depths zero and one, the constant-word maxima instead occur at
`b=1` and equal `14/5` and `116/25`. Both are below SC1.

### The first row change occurs at depth at least three

Suppose the first row change occurs at `h>=3`. The prefix through
`h-1` is bounded by its constant-word optimum. At depth `h`, the
total row-cap coefficient is `4h+3`, losing `2h` against the
constant coefficient `6h+3`. At every later depth `j`, the previous
rows are not all equal, so the total coefficient is at most `6j+1`.

Denote the corresponding caps for the old `2/5` mixture by
`u_j^old,v_j^old`. At all positive depths,

\[
u_j=\frac23u_j^{\rm old}+\frac13f_j,\qquad
v_j=\frac23v_j^{\rm old}+\frac13f_j.
\]

If `D_(h,K)` denotes the first-change excess over the constant
profile, the coefficient losses therefore give

\[
D_{h,K}^{\rm new}
=\frac23D_{h,K}^{\rm old}
-\frac{2h}{3}5^{-h}-\frac23\sum_{j=h+1}^K5^{-j}<0.
\tag{SC9}
\]

Here RA4–RA7 of report 402 prove `D_(h,K)^old<0` at every such
height: the omitted tail terms are positive and their infinite upper
bound is

\[
\frac{8-2h}{25}3^{-h}-\frac{4h+1}{5}5^{-h}
-\frac{434h+346}{245}15^{-h}<0.
\]

Thus every word whose first change is at least three has value
strictly below `A_K`. This argument uses no finite height cutoff.

### The first row change occurs at depth one or two

Normalize the names of the first four rows by order of first
appearance, starting with zero. Exactly the following thirteen
prefixes have their first change at depth one or two. The table gives
the exact maximum of SC6 through depth three, one maximizing `beta`
in these normalized coordinates, and a common supporting slope `s`.

| Prefix | Maximum | `beta` | `s` |
| --- | ---: | --- | ---: |
| `0010` | `291698/50625` | `(1/5,1/25,0,19/25)` | `0` |
| `0011` | `292907/50625` | `(24/25,1/25,0,0)` | `17/405` |
| `0012` | `97196/16875` | `(119/125,1/25,1/125,0)` | `17/405` |
| `0100` | `285313/50625` | `(4/5,1/5,0,0)` | `133/405` |
| `0101` | `287927/50625` | `(4/5,1/5,0,0)` | `37/81` |
| `0102` | `57464/10125` | `(99/125,1/5,1/125,0)` | `37/81` |
| `0110` | `293327/50625` | `(4/5,1/5,0,0)` | `257/405` |
| `0111` | `297913/50625` | `(4/5,1/5,0,0)` | `301/405` |
| `0112` | `295904/50625` | `(99/125,1/5,1/125,0)` | `301/405` |
| `0120` | `289052/50625` | `(19/25,1/5,1/25,0)` | `257/405` |
| `0121` | `292132/50625` | `(19/25,1/5,1/25,0)` | `301/405` |
| `0122` | `293012/50625` | `(19/25,1/5,1/25,0)` | `301/405` |
| `0123` | `291409/50625` | `(94/125,1/5,1/25,1/125)` | `301/405` |

These values have exact concave-supergradient certificates. To state
the certificate explicitly, let `w_(r,j)` be the coefficient of
`c_j(beta_r)` in SC6, and set `g_r(b)=sum_j w_(r,j)c_j(b)`.
At a proposed maximizing coordinate `b`, its left and right slopes are

\[
\begin{aligned}
\ell_r(b)&=\frac35\sum_{j:b\le f_j}w_{r,j}
-\frac4{15}\sum_jw_{r,j}q_j,\\
d_r(b)&=\frac35\sum_{j:b<f_j}w_{r,j}
-\frac4{15}\sum_jw_{r,j}q_j.
\end{aligned}
\tag{SC10}
\]

Every row in the table satisfies `d_r(beta_r)<=s<=ell_r(beta_r)`
for interior coordinates; at zero only the lower inequality is
needed, and at one only the upper inequality is needed. Concavity
therefore gives `g_r(x)<=g_r(beta_r)+s(x-beta_r)` on `[0,1]`.
Summing and using `sum_r x_r=sum_r beta_r=1` proves each global
simplex maximum. This certifies the table without assuming that a
finite search captures all possible real row distributions.

At every later depth `j>=4`, a nonconstant word contributes at most
`(2j+1)m_j+(6j+1)u_j`. Its infinite tail is

\[
\sum_{j=4}^{\infty}\left[(2j+1)m_j+(6j+1)u_j\right]
=\frac{633557}{2480625}.
\tag{SC11}
\]

For example each summand equals
`(3/5)(8j+2)5^-j+((12j+6)/15+(24j+4)/15)3^-j`
`-(24j+4)15^-j/15`, so SC11 follows directly from geometric
and differentiated geometric sums. Adding the largest table entry
gives the uniform early-change ceiling

\[
\frac{297913}{50625}+\frac{633557}{2480625}
=\frac{564122}{91875}
=\frac{309}{50}-\frac{7331}{183750}<\frac{309}{50}.
\tag{SC12}
\]

Short nonconstant words at heights one or two can be extended through
depth three; every added term in SC6 is nonnegative. They satisfy
the same bound. Constant words, late changes and early changes
exhaust all words, proving SC1 at every finite height.

## Actual witnesses attain the limiting ceiling

For every `K>=1`, use full digit trees
`F={0,1,2,3,4}^K` and `T={0,1,2}^K`. Label the uniform full-tree
law `mu` by row one on root child zero and row two elsewhere.
Then `beta=(1/5,4/5,0,0)`. Use `T` for every pair witness, labelled
as follows: `eta_12,eta_13,eta_14` lie in row one;
`eta_23,eta_24` lie in row two; `eta_34` lies in row three.

Take the actual source to be the union of these labelled supports.
All required trees are present. An unused row-four point can be added
if four active rows are required. The mixture becomes

\[
\omega=\frac8{15}\operatorname{Unif}(\{1\}\times T)
+\frac2{15}\operatorname{Unif}(\{2\}\times T)
+\frac13\operatorname{Unif}(\{3\}\times T).
\]

Select every pure phase to be the zero prefix, and every mixed phase
to have row one and that same seven-adic prefix. These are literal
allowed choices for every original divisor. At every positive depth
they simultaneously attain `m_j` and `v_j`; at depth zero the row
mass is `1/3`. Hence the actual squared-load expectation is `A_K`
from SC8, and tends to `309/50`.

Together with SC1, this proves sharpness of the limiting universal
ceiling for arbitrary permitted witness choices in SC2. It does not
assert `Gamma_(1,K)=A_K` for each finite `K`, or optimality among all
probabilities on the source.

## Exact reusable checks

The standard-library program
[three_fifths_tree_common_law.py](../../frontier/cover-geometry/three_fifths_tree_common_law.py)
constructs SC2 on a supplied source and independently checks the
component witnesses, support, mixture identity and all literal prefix
caps. A caller may also supply other valid full/pair witnesses.
`profile_bound` evaluates SC6, and `certify_profile_maximum` checks
the exact common-supergradient certificate SC10. `sharpness_source`
constructs the actual aligned witnesses and evaluates all original
divisor indicators.

Its no-argument self-check, run with `python3 -I -S -B -O`, passes
13 early-prefix certificates, nine actual source controls, five actual
sharpness controls through height five, and eleven malformed or
nonoptimal certificate controls. The finite sharpness expectations
are `112/25`, `1246/225`, `100268/16875`, `514006/84375`, and
`23341096/3796875`. Its `--stdin` mode accepts an exact JSON object
with `height` and `source`; validation remains active under `-O`.
The all-height conclusion comes from the preceding proof, not from
the finite control heights.

## Actual witness choices obstruct every fixed mixture coefficient

Now allow `nu_lambda=lambda*mu+(1-lambda)*omega` with
`0<=lambda<=1`, keeping the same component construction. The
sharpness family just given has actual layout expectation

\[
A_K(\lambda)=4\lambda S_K(1/5)
+\frac{13}{5}(1-\lambda)S_K(1/3)-\frac{12}{5}\lambda.
\tag{SC13}
\]

For a second actual family, use the same full tree `F` and six pair
trees `T`, at `K>=5`. Name the rows `a,b,c,d`. Label the pair laws
entirely by `a` for pairs `ab,ac,ad`, by `b` for `bc,bd`, and by `c`
for `cd`. Label `mu` by row `b` precisely on its all-zero depth-five
prefix, and by `a` elsewhere. Thus
`beta_b=1/3125`, `beta_a=3124/3125`, and

\[
\omega=\frac{2\beta_b}{3}\operatorname{Unif}(\{a\}\times T)
+\frac{2\beta_a}{3}\operatorname{Unif}(\{b\}\times T)
+\frac13\operatorname{Unif}(\{c\}\times T).
\tag{SC14}
\]

Again the source is the union of the actual labelled supports.
Choose every pure phase to be the zero prefix. Choose mixed row `a`
at depths zero, one and two, and row `b` thereafter, always with the
zero seven-adic prefix. If `p` counts the active pure labels at a
point, its squared loads in rows `a,b,c` are respectively

\[
(p+\min(p,3))^2,\qquad
(p+\max(p-3,0))^2,\qquad p^2.
\tag{SC15}
\]

Under the uniform digit tree of branching `d`, `p` has mass
`(d-1)/d^p` for `1<=p<=K` and mass `d^-K` at `p=K+1`.
In `mu` the row is `a` for `p<=5` and `b` for `p>=6`.
These finite distributions compute the actual expectations without
any cap relaxation. At height six they give

| Family | `E_mu L^2` | `E_omega L^2` |
| --- | ---: | ---: |
| A | `79672/15625` | `28327/3645` |
| B | `917/125` | `2595983/759375` |

Consequently the two actual affine lower bounds on their respective
layout maxima are

\[
\begin{aligned}
A_6(\lambda)&=\frac{28327}{3645}
-\frac{30440987}{11390625}\lambda,\\
B_6(\lambda)&=\frac{2595983}{759375}
+\frac{2974792}{759375}\lambda.
\end{aligned}
\tag{SC16}
\]

The first line decreases and the second increases. Their intersection
lies in `[0,1]`, at `lambda=49582130/75062867`, proving

\[
\min_{0\le\lambda\le1}\max\{A_6(\lambda),B_6(\lambda)\}
=\frac{1408882511647}{234571459375}
=6+\frac{1453755397}{234571459375}>6.
\tag{SC17}
\]

Thus for every fixed coefficient there is an actual permitted witness
choice at height six with `Gamma_(1,6)>6`. Letting the coefficient
depend only on height does not avoid this obstruction. Both supports
can also be united into a common source, preserving their permitted
witness choices; this does not make every choice on that source bad.

The limiting lines are

\[
A_\infty(\lambda)=\frac{39}{5}-\frac{27}{10}\lambda,
\qquad
B_\infty(\lambda)=\frac{96919}{28125}
+\frac{218857}{56250}\lambda.
\]

Their intersection at `lambda=61228/92683` gives the limiting
two-family barrier `2788059/463415=6+7569/463415`. These bounds
come from actual probabilities and actual layouts. They leave open
optimizing the witnesses, choosing a coefficient from those witnesses,
changing the construction, and the source minimax problem.

The standard-library checker
[actual_witness_mixture_barrier.py](../../frontier/cover-geometry/actual_witness_mixture_barrier.py)
constructs both height-six families and the height-five B family,
checks their actual full/pair witnesses and common laws, evaluates
every original divisor indicator, and independently recomputes the
prefix-count distributions SC15. Its exact checks verify SC16–SC17
under `python3 -I -S -B -O`. At height five it also verifies the
specific obstruction `B_5(2/3)=13701358/2278125>6`.

There is an exact reduction for the worst permitted witness choices
at any fixed literal layout. For a function `g` on `Z/7^K`, define

\[
\mathcal M_b(g)=\max_{T\text{ complete }b\text{-ary tree}}
b^{-K}\sum_{y\in T}g(y).
\]

This maximum uniform-tree average is computed recursively by taking
the mean of the `b` largest child values. It is distinct from the
bottleneck tree rank. Write `c_r(y)=L(r,y)^2` for the literal layout
cost, and set

\[
z_{rs}=\mathcal M_3(\max(c_r,c_s)),\qquad
w_i=\frac13\sum_{\substack{r<s\\r,s\ne i}}z_{rs}.
\]

Then the maximum actual expectation over all permitted labelled
full/pair witnesses, allowing their union as the actual source, is

\[
\mathcal M_5\!\left(\max_r
\left[\lambda c_r+(1-\lambda)w_r\right]\right).
\tag{SC18}
\]

For fixed `mu`, each pair-law coefficient is nonnegative. Each pair
law can therefore independently attain `z_rs`, by choosing its tree
and an endpoint row at each leaf. Its combined contribution is then
`sum_i beta_i w_i`. Maximizing the resulting full-tree expectation
first over leaf labels and then over the five-tree proves SC18.
All maxima exist on the finite carrier; the union of their labelled
supports is one admissible source. This is a worst-witness reduction,
with no minimization over source laws or exchange of minimax orders.
The two explicit families above need only direct evaluation.
