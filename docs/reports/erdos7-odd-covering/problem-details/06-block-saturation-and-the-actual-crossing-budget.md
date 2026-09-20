[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](05-unrestricted-axis-deletions-a-complete-head-bound.md) · [Next](17-odd-cactus-noncoverage.md)

<a id="block-saturation-and-the-actual-crossing-budget"></a>
### Block saturation and the actual crossing budget

Let `D` be a finite set of distinct odd moduli greater than one, with actual
residues `a_d`, and let `N=lcm(D)=QT`, where `gcd(Q,T)=1`. Use the actual
head survivors `R_Q`, obtained by removing exactly the classes with `d|Q`,
and suppose a probability `mu` supported on `R_Q` is given. Partition the
primes of `T` into arbitrary finite nonempty blocks `B`, and set
`T_B=prod_(q in B) q^(v_q(N))`. Empty tail support is allowed: all block
sums are then empty. Write `d=m_d t_d` with `m_d|Q`, `t_d|T`, and put
`h_d(x)=1[x=a_d mod m_d]` (identically one when `m_d=1`).

A tail class is local to `B` when `t_d>1` and its entire prime support
lies in `B`; otherwise it is crossing if it meets two or more blocks.
For each head point, let `U_B(x)` be the union of the actual local tail
cylinders whose head incidence is one. All original labels are retained:
different head labels can have the same projected tail modulus. Define

\[
 \alpha_B(x)=\frac{|U_B(x)|}{T_B},\qquad
 A_B=\mathbb E_\mu\alpha_B^2.
\]

For a crossing class put `t_(d,B)=gcd(t_d,T_B)` and, when this is greater
than one, define the remaining cylinder fraction

\[
 r_{B,d}(x)=\frac{|\{y\bmod T_B:y\equiv a_d\pmod{t_{d,B}}\}
                    \setminus U_B(x)|}{T_B}
 \le\frac1{t_{d,B}}.
\]

For thresholds `0<delta_B<1`, set

\[
 E=\sum_B\frac{A_B}{\delta_B^2},\qquad
 J=\sum_{d\text{ crossing}}\mathbb E_\mu
       \left[h_d\prod_{B:t_{d,B}>1}\frac{r_{B,d}}{1-\delta_B}\right].
 \tag{BS1}
\]

**Block criterion.** If `E+J<1`, the system does not cover. A sufficient
upper bound for `J` is

\[
 J_{\rm raw}=\sum_{d\text{ crossing}}
 \frac{\mu(h_d=1)}{t_d\prod_{B:t_{d,B}>1}(1-\delta_B)}.
 \tag{BS2}
\]

If there are no crossing classes, the stronger endpoint bound is

\[
 \mu\{x:\text{the tail fibre at }x\text{ has an uncovered point}\}
 \ge 1-\sum_B A_B.                                      \tag{BS3}
\]

**Proof.** On `G={x:alpha_B(x)<=delta_B for every B}`, every local
complement is nonempty. Markov's inequality and a union bound give
`mu(G)>=1-E`. For a fixed `x in G`, choose the block coordinates
independently and uniformly on their respective local complements.
The conditional probability of a crossing class is exactly

\[
 h_d(x)\prod_{B:t_{d,B}>1}\frac{r_{B,d}(x)}{1-\alpha_B(x)},
\]

and is bounded by its integrand in (BS1). Keep `mu` restricted to `G`
**unnormalized**; the resulting head-and-tail measure has mass at least
`1-E`. Summing the crossing probabilities leaves uncovered mass at least
`1-E-J`. CRT realizes an uncovered residue as an integer. The cylinder
bound and `prod_B t_(d,B)=t_d` prove (BS2).

Without crossing classes, the tail fibre is covered exactly when at least
one block is saturated. If no block is saturated, choose one point in
each complement and use CRT. Since `1[alpha_B=1]<=alpha_B^2`, the union
bound proves (BS3). No assumption on block cardinality was used.

<a id="moment-bounds-preserve-the-original-labels"></a>
#### Moment bounds preserve the original labels

Let `F_B=sum_(d local to B) h_d/t_d`, let `mathcal T_B` be the set of
distinct tail parts occurring locally, and set `W_B=sum_(t in mathcal T_B)1/t`.
The two available moment bounds are

\[
 A_B\le\sum_{d,e\text{ local to }B}
       \frac{\mu(h_dh_e=1)}{t_dt_e},\qquad
 A_B\le\Gamma_Q(\mu)W_B^2.                              \tag{BS4}
\]

The first follows from `alpha_B<=F_B` and retains incompatible head
intersections as zero. For the second, fix a tail part `t`. Distinctness
of the **original** moduli implies at most one class for each head label
`m` with `mt in D`. Completing the missing head labels to a complete test
layout shows that `L_t=sum_(mt in D)h_(mt)` satisfies
`||L_t||_2<=sqrt(Gamma_Q(mu))`. Minkowski applied to
`F_B=sum_t L_t/t` gives (BS4). In particular,

\[
 W_B\le\prod_{q\in B}\sum_{e=0}^{v_q(N)}q^{-e}-1
       <\prod_{q\in B}\left(1+\frac1{q-1}\right)-1.
 \tag{BS5}
\]

This is where the existing reciprocal-divisor Euler product enters the
new criterion. The same divisor coordinates used at 5040 supply `W_B`;
the squared block loads in (BS4) additionally account for the actual head
incidences. No two-prime distinct-modulus theorem is applied to a projected
family with repeated tail moduli. No general tensorization of Gamma is used.

<a id="arbitrary-three-prime-heads-with-sparse-tail-interactions"></a>
#### Arbitrary three-prime heads with sparse tail interactions

The existing common uniform law on the actual complete `{3,5,7}` head
survivors satisfies

\[
 \Gamma_Q(\mu)\le G=\frac{1889}{48},\qquad
 \sum_{m\mid Q}c_\mu(m)\le C=1+\frac{1649}{360}
                         =\frac{2009}{360}.             \tag{BS10}
\]

The Gamma bound is the consequence of (ZG1) displayed after (N9), and the
nonunit cylinder sum is the common-density bound preceding (P14). Both
hold for the same uniform law, arbitrary finite heights, arbitrary actual
head residues, and missing head classes. Unlike the star application,
no particular head assignment is imposed here.

**Degree-two tail theorem.** Distinct odd moduli cannot cover if every
prime factor belongs to `{3,5,7}` or is at least 37, and the actual
interaction graph on primes at least 37 has maximum degree at most two.
There is no exponent bound or bound on the total number of primes.
Arbitrarily long path and cycle components, as well as triangles, are allowed.

To prove this, set `a_q=1/(q-1)`, `S=sum_q a_q^2`, and take singleton
blocks with threshold `delta=2/3`. A tail support must be a clique in the
interaction graph, so it has size at most three. Triangles are pairwise
vertex-disjoint components. The degree bound and `a_q<=1/36` give

\[
 \sum_{\{q,r\}\in\mathcal E}a_qa_r\le S,\qquad
 \sum_{\{q,r,s\}\text{ triangle}}a_qa_ra_s\le\frac{S}{108}.
\]

For the first inequality use `2ab<=a^2+b^2` and count vertex degrees.
For the second, average the three bounds `abc<=(1/36)ab` and use the
same square inequality within each disjoint triangle. For a fixed tail
part `t`, distinct original moduli give
`sum_(d:t_d=t)mu(h_d=1)<=sum_(m|Q)c_mu(m)<=C`. Summing all positive
prime powers on a fixed support then gives the product of its `a_q`.
Consequently (BS1)--(BS2) satisfy

\[
 E+J\le E+J_{\rm raw}
 \le\frac94 GS+C\left(9S+27\frac{S}{108}\right)
 =\frac{403681}{2880}S.                                 \tag{BS11}
\]

The exact prime bound already used above gives

\[
 S<\frac{4976233}{2000000000}
     +\sum_{\substack{37\le q\le73\\q\text{ prime}}}
                 \frac1{(q-1)^2}
  =\frac{469089312556889868097}{72216234108018000000000},
\]

so the right side of (BS11) is less than
`189362442782277858843265057/207982754231091840000000000 < 0.91048 < 1`.
This proves the theorem using (BS1).

**Three-vertex component theorem.** The lower cutoff can instead be 31
if every tail interaction component has at most three vertices. Use each
component as one block; there are no crossing classes. Now `a_q<=1/30`
and (BS5) gives, for each such component,

\[
 W_B\le\frac{2791}{2700}\sum_{q\in B}a_q,\qquad
 W_B^2\le3\left(\frac{2791}{2700}\right)^2
                    \sum_{q\in B}a_q^2.
\]

Indeed the pair terms in the three-variable product sum to at most
`(1/30)sum a_q`, and its triple term to at most
`(1/(3*30^2))sum a_q`. The same coefficient covers smaller components.
Using (BS3)--(BS4) and (BS10), the total loss is strictly below

\[
 3G\left(\frac{2791}{2700}\right)^2
 \left(\frac{4976233}{2000000000}
        +\sum_{\substack{31\le q\le73\\q\text{ prime}}}
                              \frac1{(q-1)^2}\right)
 =\frac{8083223933051729599312138630673}{8423301546359219520000000000000}
 <0.95963<1.                                             \tag{BS12}
\]

Both statements allow a modulus with all three head primes and all three
primes of a tail triangle, hence six distinct prime factors. They allow
arbitrarily many distinct prime factors across the whole family. They are
not direct specializations of the published at-most-three-factors-per-modulus
or at-most-eight-total-primes results, or of (P1)'s cutoff 67. They do not
claim global literature priority.

More generally, for any actual head law with the two bounds `G,C`, a tail
graph of maximum degree `Delta` and `a_q<=a` satisfies the sufficient criterion

\[
 S\left[\frac{G}{\delta^2}
   +C\sum_{k=2}^{\Delta+1}\frac{\binom\Delta{k-1}}{k}
                    \frac{a^{k-2}}{(1-\delta)^k}\right]<1.
 \tag{BS13}
\]

Every tail support is a clique. On a `k`-clique, averaging pairwise products
gives `prod a_q<=a^(k-2)sum a_q^2/k`; each vertex belongs to at most
`binom(Delta,k-1)` such cliques. Grouping original labels as above proves
(BS13), without bounding the number of graph components.

The fixed-constant singleton criterion for degree two cannot reach cutoff
31 merely by changing its common threshold. Let

\[
 L=\frac{2363054-529}{10^9}
       +\sum_{\substack{31\le q\le73\\q\text{ prime}}}\frac1{(q-1)^2}
    <\sum_{q\ge31,\ q\text{ prime}}\frac1{(q-1)^2}.
\]

Exact arithmetic gives `GL>(33/50)^3` and `CL>(17/50)^3`. For every
`0<delta<1`, Hölder's inequality therefore gives
`GL/delta^2+CL/(1-delta)^2 >= ((GL)^(1/3)+(CL)^(1/3))^3 > 1`, even before
the nonnegative triangle term. This limits this scalar certificate with
the constants (BS10); it does not refute noncoverage at cutoff 31 or exclude
estimates retaining the actual graph and residues. All constants in
(BS10)--(BS13) and these strict comparisons are checked by the same fixed
block certificate linked below. The general arguments are ordinary proofs,
not new Lean declarations.

<a id="every-positive-height-star-head-admits-the-required-broad-law"></a>
#### Every positive-height star head admits the required broad law

Take the complete star assignment defined above, now at **arbitrary
positive heights** `H_p>=1` on any set `P` of odd primes at most 73
containing 3. This extends the positive result beyond the heights needed
for the earlier lower-bound refutation; that refutation still uses 31/8.
Let `Q` be the full prime-power part of `N` at primes at most 73, with
support exactly `P`, and suppose the actual classes with `d|Q` are this
star assignment at these full heights. All tail primes are greater than 73.

The same exact survivor decomposition holds, and use only its broad branch

\[
 R_b=C_3\times\prod_{p\in P\setminus\{3\}}D_p,\qquad
 \mu_b=\operatorname{Unif}(R_b).
\]

Its coordinate densities are `s_3=(1-3^(-H_3))/2` and
`s_p=(p-3+2p^(-H_p))/(p-1)` for `p>=5`; all are positive.
For every positive exponent, a coordinate cylinder has mass at most
`p^(-e)/s_p`. Expanding any complete layout square bounds its moment by
`sum_(m|Q) chi(m)c_mu(m)`: each intersection is empty or a cylinder modulo
the lcm, and exactly `2e+1` ordered exponent pairs have maximum `e`.
Factoring these cylinder bounds for the explicitly product law yields

\[
 \Gamma_Q(\mu_b)\le
 \prod_{p\in P}\left(1+s_p^{-1}
                 \sum_{e=1}^{H_p}(2e+1)p^{-e}\right)<K_0<177,
 \quad K_0=5\prod_{\substack{5\le p\le73\\p\text{ prime}}}
                   \frac{p^2-p+2}{(p-3)(p-1)}.           \tag{BS6}
\]

The finite ternary factor is exactly `5-2H_3/(3^(H_3)-1)<5`, since its
weighted sum is `2-(H_3+2)3^(-H_3)`. For the other coordinates use
`sum_(e>=1)(2e+1)p^(-e)=(3p-1)/(p-1)^2` and the lower bound on `s_p`.
All omitted-prime factors exceed one. The unweighted cylinder sum similarly
satisfies

\[
 \sum_{m\mid Q}c_{\mu_b}(m)\le C_0<\frac{73}{10},\qquad
 C_0=2\prod_{\substack{5\le p\le73\\p\text{ prime}}}
                \frac{p-2}{p-3}.                       \tag{BS7}
\]

Here the finite ternary factor is exactly 2. These bounds concern the
specific star law; no bound for arbitrary head assignments is asserted.

<a id="matching-tails-cannot-complete-a-star"></a>
#### Matching tails cannot complete a star

The actual tail interaction graph has the primes greater than 73 dividing
`N` as vertices, and an edge `{q,r}` when an original modulus contains
both. If this graph is a matching, its components are singleton or pair
blocks, and every tail class is local to one block. All residues, exponents,
numbers of tail primes, and head factors within tail moduli remain arbitrary.

Write `a=1/(q-1)`, `b=1/(r-1)`. Since `q,r>=79`, the pair load satisfies
`W_B<=a+b+ab<=(157/156)(a+b)`. Thus
`W_B^2<=2(157/156)^2(a^2+b^2)`, with the same upper coefficient valid for
singletons. The exact prime-tail bound gives

\[
 \sum_{q>73,\ q\text{ prime}}\frac1{(q-1)^2}<\frac1{400},
 \qquad \sum_B A_B<177\cdot2\left(\frac{157}{156}\right)^2\frac1{400}
       =\frac{1454291}{1622400}<\frac9{10}.
\]

By (BS3), more than `168109/1622400>1/10` of the broad-branch head points
have an uncovered tail lift. This proves noncoverage of every such star
extension. The conclusion also survives removal of redundant mixed-zero
head classes, since that leaves the head survivors unchanged. The numerical
proportion refers to head points under `mu_b`, not to uniform density in
the entire period `N`.

<a id="star-forests-arbitrarily-many-centres-of-unbounded-degree"></a>
#### Star forests: arbitrarily many centres of unbounded degree

Let `mu` be any actual head survivor law with `Gamma_Q(mu)<=G`. Suppose
the tail interaction graph is a disjoint union of stars, allowing isolated
vertices and edges. There is no bound on the number of stars or their degrees.
For one component choose its centre `r` and write its leaves as `q`.
For fixed head point `x`, let `alpha_r(x)` be the fraction of the `r` coordinate
covered by actual classes with tail part a pure power of `r`. For fixed
`r` coordinate `y`, let `alpha_q(x,y)` be the covered fraction of the `q`
coordinate from all actual classes with tail support `{q}` or `{r,q}`.
Put `beta_q(x)=Pr_y[alpha_q(x,y)=1]`, where `y` is uniform.

If the whole component is saturated above `x`, every `y` outside the central
pure-power union must saturate at least one leaf fibre. Otherwise choose an
uncovered coordinate for every leaf and apply CRT. Hence
`alpha_r+sum_q beta_q>=1` on saturation, and pointwise

\[
 1[\text{component saturated}]
 \le\frac43\left(\alpha_r^2+\sum_q\beta_q\right),
 \qquad \alpha_r^2+1-\alpha_r
       =(\alpha_r-\tfrac12)^2+\tfrac34.                 \tag{SF1}
\]

Set `a_p=1/(p-1)` and `D_p=1+3a_p+2a_p^2`. The original-label bound (BS4)
gives `E_mu alpha_r^2<=G a_r^2`. For a leaf, regard `Qr^(v_r(N))` as the
head, with the unconditioned law `mu` times uniform `r`. At fixed tail
power `q^e`, every original modulus has a distinct enlarged head label;
repeated projected `q^e` moduli are all retained. The uniform-coordinate
transfer (T1), with `delta=0`, gives enlarged Gamma at most `G D_r`.
Applying (BS4) there yields

\[
 \mathbb E_\mu\beta_q
 \le\mathbb E_{\mu\otimes U_r}\alpha_q^2
 \le G D_r a_q^2.
\]

The tail can cover a head fibre only if one of its components is saturated.
Thus (SF1), summed over the disjoint components, proves

\[
 \mu\{x:\text{an uncovered tail lift exists}\}
 \ge 1-\frac{4G}{3}\sum_{\text{stars}}
       \left(a_r^2+D_r\sum_{q\text{ leaf}}a_q^2\right).
 \tag{SF2}
\]

An isolated vertex satisfies the stronger direct bound `G a_r^2`, so it
also satisfies this estimate. No independence of overlapping deletion
events was assumed. Each star's centre may be chosen freely when its degree
is at most one.

For a uniform lower tail-prime cutoff `q0`, (SF2)'s loss is at most
`(4G/3)(1+3/(q0-1)+2/(q0-1)^2) sum_q 1/(q-1)^2`. Exact constants give:

| Head | Tail primes | Saturated-head mass upper bound |
|---|---|---:|
| Arbitrary `{3,5,7}` head, law (BS10) | `q>=19` | `<0.858311` |
| Complete star head at any positive heights, law (BS6) | `q>73` | `<0.588420` |

Both therefore exclude covering systems with any star-forest tail graph.
The first permits arbitrarily many primes in total and original moduli
with all three head primes and two tail primes. The second applies to the
same star geometry that refutes the universal Gamma73 target.

<a id="arbitrary-forests-a-bound-independent-of-depth-and-degree"></a>
#### Arbitrary forests: a bound independent of depth and degree

The actual tail interaction graph may be any finite forest. Since every
tail support forms a clique, each actual tail modulus then involves at most
two tail primes. There is no bound on the number of vertices, their degrees,
tree depth, or prime-power exponents. Two resulting exclusions are:

| Head | Tail primes | Saturated-head mass upper bound |
|---|---|---:|
| Arbitrary `{3,5,7}` head, law (BS10) | `q>=19` | `<0.965600` |
| Complete star head at any positive heights, law (BS6) | `q>73` | `<0.661972` |

Here is the finite recursive argument, with all probabilities over the
original head law `mu`. Root every tail tree independently of the head point
`x`. Write `Y_v=Z/v^(v_v(N))Z` for a prime coordinate and `U_v` for its
uniform law. Assign every class with tail support `{v}` to `v`, and every
class with tail support `{p,v}`, where `p` is the parent, to its child `v`.
A root receives original moduli `m v^e`, where `m|Q,e>=1`; a nonroot receives
original moduli `m p^f v^e`, where `m|Q,f>=0,e>=1`. Every actual tail class
is assigned exactly once. Original moduli, including their full head labels,
remain distinct labels; repeated projected tail moduli are never deleted.

For fixed `x` and parent value `z`, let `F_v(x,z)` be the union of the actual
forbidden `v` cylinders from the classes assigned to `v` whose head and
parent conditions hold. Put `alpha_v(x,z)=U_v(F_v(x,z))`. Give a root a
one-point parent space, so the same notation covers all vertices. Define

\[
 \epsilon_v(x)=\mathbb E_{z\sim U_{p(v)}}\alpha_v(x,z)^2,
 \qquad
 s_v=\sum_{e=1}^{H_v}v^{-e},\quad
 \kappa_v=1+\sum_{e=1}^{H_v}(2e+1)v^{-e}.
 \tag{AF1}
\]

For a root `epsilon_v=alpha_v^2`. These are actual union fractions, not raw
sums of cylinder measures. Let `V` be the set of head points having an
uncovered tail lift. The general forest bound is

\[
 \mu(V)\ge1-\frac32\sum_v\mathbb E_\mu\epsilon_v
 \ge1-\frac{3G}{2}\left(\sum_{v\text{ root}}s_v^2+
       \sum_{v\text{ nonroot}}\kappa_{p(v)}s_v^2\right).
 \tag{AF2}
\]

**Exact subtree messages.** Fix `x`. Define `B_v` as the set of parent
values for which no assignment to the entire subtree rooted at `v` avoids
all classes assigned to that subtree, including its incoming parent edge.
Write `beta_v=U_(p(v))(B_v)` and `c_v=sum_(w child of v) beta_w`. For a root,
`beta_v` is zero or one; it is one exactly when that component is saturated.
These sets have the exact finite recursion

\[
 z\in B_v\quad\Longleftrightarrow\quad
 F_v(x,z)\ \cup\!\bigcup_{w\text{ child of }v}B_w=Y_v.
 \tag{AF3}
\]

Indeed a `v` value outside the union violates none of its assigned classes
and has an avoiding extension in each child subtree. Those extensions can
be combined because different child subtrees have disjoint tail coordinates
and no classes connecting them. The child sets depend on `x` and the `v`
coordinate, not on the parent value `z`; no probabilistic independence of
the sets is assumed. This proves (AF3) by induction on finite subtree height.
For every `z in B_v`, the union bound gives `1<=alpha_v(x,z)+c_v`, hence

\[
 \epsilon_v\ge\beta_v(1-c_v)_+^2.                     \tag{AF4}
\]

**A potential that cancels along every tree.** Set `Phi(t)=t-t^3/3` for
`0<=t<=1`. For `b,b_i in [0,1]` and `c=sum_i b_i`,

\[
 \Phi(b)\le b(1-c)_+^2+\sum_i\Phi(b_i).               \tag{AF5}
\]

If `c>=1`, then `sum Phi(b_i)>=2c/3>=2/3>=Phi(b)`. These bounds follow
from `Phi(t)>=2t/3` and `2/3-Phi(t)=(1-t)^2(t+2)/3` for `t in [0,1]`.
If `0<=c<=1`, then `sum b_i^3<=c^3`, so `sum Phi(b_i)>=Phi(c)`.
When `b<=c`, monotonicity of `Phi` on `[0,1]` proves (AF5). When `c<=b`,
use the exact identity

\[
 b(1-c)^2+\Phi(c)-\Phi(b)
 =c(1-b)^2+\frac{(b-c)^3}{3}\ge0.                    \tag{AF6}
\]

This proves (AF5). Applying it to `beta_v` and its child messages, then using
(AF4), gives `Phi(beta_v)<=epsilon_v+sum_(w child) Phi(beta_w)`.
Summation over a tree cancels every nonroot potential exactly once:

\[
 \sum_{v\text{ in tree}}\epsilon_v
 \ge\Phi(\beta_{\rm root})
 =\tfrac23\,1[\text{tree saturated}].                 \tag{AF7}
\]

A tail lift exists exactly when every component has an avoiding assignment.
Consequently `1[x not in V]<=(3/2) sum_v epsilon_v`, which proves the first
inequality in (AF2). No fibres are discarded or conditioned on, and there
is no factor accumulating with depth, degree, or component size.

**Moment bound retaining the original labels.** For a root, (T2) gives
`E_mu epsilon_v<=G s_v^2`. For a nonroot `v` with parent `p`, test its actual
assigned family over the enlarged head `Q p^(H_p)` with law `mu times U_p`.
At fixed positive `v` exponent `e`, the old divisor `m p^f` determines the
original modulus `m p^f v^e`; there is at most one original class for that
old divisor. Thus (T2) applies without assuming distinct projected `v^e`
moduli. The unconditioned transfer (T1), with `delta=0`, gives

\[
 \mathbb E_\mu\epsilon_v
 \le\Gamma_{Qp^{H_p}}(\mu\otimes U_p)s_v^2
 \le G\kappa_p s_v^2.                                \tag{AF8}
\]

The coefficient retains both pure and incoming-edge classes: among
nonnegative parent exponent pairs there are `2e+1` pairs with maximum `e`.
The uniform parent law is only the testing law for this moment estimate.
It is not asserted to survive the parent's classes; their effect is already
present in the exact subtree recursion. This proves the second inequality
in (AF2).

For a tail cutoff `q0`, put `a0=1/(q0-1)`,
`kappa0=1+3a0+2a0^2`, and let `S` bound `sum_(q>=q0 prime)1/(q-1)^2`.
Since `s_v<=1/(v-1)` and `kappa_v<=kappa0`, (AF2) yields the sufficient
condition `(3/2) G kappa0 S<1`. It also retains the stronger individual-parent
and root coefficients when a concrete forest is known.

For arbitrary `{3,5,7}` heads, take `q0=19`, `G=1889/48`, and
`kappa0=95/81`. The sharper prime-square estimate (GS1) gives

\[
 S_{19}=\frac{2400198237}{10^{12}}+
       \sum_{\substack{19\le p\le73\\p\text{ prime}}}\frac1{(p-1)^2},
 \qquad
 \frac32G\kappa_0S_{19}
 =\frac{6024840902671133365942778501}
        {6239482626932755200000000000}
 <0.965600<1.                                          \tag{AF9}
\]

For a complete star head, take `q0=79`, `G=177`, `kappa0=1580/1521`, and
`S=2400198237/10^12`. The exact loss is

\[
 \frac32G\kappa_0S=\frac{11187323982657}{16900000000000}
 <0.661972<1.                                         \tag{AF10}
\]

Thus more than `5712676017343/16900000000000>0.338028` of its broad-branch
head points admit an uncovered tail lift. In particular, any full star
completion must contain a cycle in its actual tail interaction graph.
This proportion concerns head points, not uniform density in the full
period. These are arbitrary-finite-forest proofs; the adjacent exact
certificate verifies their scalar constants, not a bounded enumeration of
tree shapes. Proof provenance: the Nyx oracle supplied the exact-message
energy reduction; the cubic potential above is the present refinement.
These are ordinary mathematical proofs, not complete Lean formalizations
of the forest criterion.

The reusable construction in
[ExactForestMessages.exact_forest_message_feasibility](../../../../D5/S3/Arith/Congruence/ExactForestMessages.lean)
formalizes the exact residual-set equations and the equivalence between a
simultaneous avoiding assignment and nonempty root residuals, for arbitrary
finite forests and finite domains. Its two well-founded recursions construct
messages from leaves upward and assignments from roots downward. The scoped
kernel build and source-bound report use only `propext`, `Classical.choice`,
and `Quot.sound`. The congruence embedding, cubic potential, and moment
estimates (AF2) remain outside that Lean theorem.

[ForestConstraintEnergy.unsatisfiable_forest_square_energy](../../../../D5/S3/Arith/Congruence/ForestConstraintEnergy.lean)
also formalizes the actual-constraint energy estimate (AF7). Each vertex may
carry any fixed normalized nonnegative weights. From the original unary and
binary forbidden relations and unsatisfiability, it derives the bound
`sum epsilon_v>=2/3`, using the exact messages, weighted union estimates,
the cubic potential, and cancellation over the forest. It does not assume
the local energy inequalities. Its scoped build and source-bound report
have the same standard axiom closure. The CRT embedding, prime-coordinate
moment bounds, and arithmetic noncoverage consequences remain separate.

<a id="full-fibre-blocking-and-exact-hanging-tree-elimination"></a>
#### Full-fibre blocking and exact hanging-tree elimination

The original prime-prefix structure gives a quantitative refinement of
the exact forest messages above. Let D be a finite set of distinct odd
nonunit moduli, with one arbitrary actual class A_d per modulus. Work at
the original period Q=lcm D, with full coordinates X_p=Z/p^{h_p}Z and
their uniform Haar marginals H_p. Join p,q when pq divides an original
label. No divisor closure or normalization of residues is assumed.

For an edge pq, let E_pq consist of the exponent pairs (a,b) for which
the original label p^a q^b is present. If V_q is a nonempty feasible
set of full q-words, write delta_q=H_q(V_q). For a full p-word x let
C_pq(x) be the union of the actual q-prefixes of exactly those edge
classes whose p-prefix matches x. The full-fibre blocker is

    B_(q->p)={x in X_p : V_q is contained in C_pq(x)}.

For an integer r>=1 set

    L_pq(r)=sum_((a,b) in E_pq, a<r) q^(-b),
    T_pq(r)=sum_((a,b) in E_pq, a>=r) p^(-a)q^(-b).

Whenever delta_q>L_pq(r),

    H_p(B_(q->p)) <= T_pq(r)/(delta_q-L_pq(r)).              (PB1)

Indeed, at a blocked p-word the shallow classes cover at most L_pq(r)
of the q-coordinate. The sum of active deep q-prefix measures must
therefore be at least delta_q-L_pq(r). Its H_p-expectation is exactly
T_pq(r), since each actual p^a-prefix has measure p^(-a). Integrating
this pointwise inequality proves PB1. Merely meeting V_q does not
satisfy the full-fibre hypothesis.

Distinct numerical labels permit at most one class per exponent pair.
Consequently

    L_pq(r) <= (r-1)/(q-1),
    T_pq(r) <= p^(1-r)/((p-1)(q-1)).                         (PB2)

These geometric sums bound the finite original labels; they do not
introduce new labels or replace their residues. If q>=5 and delta_q>=1/2,
choose r=(q-1)/2. Then delta_q-L_pq(r)>=1/(q-1), giving

    H_p(B_(q->p)) <= p^((3-q)/2)/(p-1).                     (PB3)

For a leaf q, its feasible set only avoids pure q-powers, so
delta_q>=1-1/(q-1). The choice r=q-2 instead gives
`H_p(B_(q->p))<=p^(3-q)/(p-1)`.

Retain a connected set of prime vertices C such that every removed
component is a tree attached at exactly one retained vertex, every
removed prime is at least 5, and every label meeting a removed vertex
is a pure power or an edge label. Root the removed trees toward C.
For a removed q, its exact descendant-feasible domain is

    V_q=X_q minus (all original pure-q classes
                    union all B_(r->q) for children r).     (PB4)

Define the same domain at each retained p using only its removed-tree
children. This recursion is exact: once the parent word is fixed,
different descendant trees have disjoint coordinates and no class
joining them. Their avoiding extensions can be chosen simultaneously.
It is the same existential mechanism as AF3, now retaining a separate
prefix-depth estimate for the incoming edge.

Induction from the leaves, PB3 and the distinct child primes give

    delta_p >= d_p:=1-1/(p-1)-1/(p-1)^2.                    (PB5)

To see the induction, if every child r has delta_r>=1/2, the lost measure
is at most `1/(p-1)+(1/(p-1))*sum_r p^((3-r)/2)`. Overcount the distinct
children by all odd integers at least 5; their sum is at most 1/(p-1).
Every removed p>=5 therefore has delta_p>=11/16>1/2, closing the induction.
At a retained p=3 the same calculation gives delta_3>=1/4.

If 3 is retained, its retained neighbors are absent from its child sum.
Subtracting their terms from that same geometric upper bound gives

    delta_3 >= 1/4 + (1/2) sum_(q in N_C(3)) 3^((3-q)/2).   (PB6)

The exact projection of the global uncovered set onto C is

    (product_(p in C) V_p) minus
       (all actual mixed classes supported entirely in C). (PB7)

For tree components alone the same induction applies after rooting at
the least prime. This recovers their noncoverage; that exclusion was
already supplied by the preceding forest-energy and original-label
moment bounds. PB1--PB6 provide the additional coordinate-domain estimates
used below, rather than a claim of a new independent forest exclusion.

<a id="arbitrary-odd-pseudoforests-are-noncovering"></a>
#### Arbitrary odd pseudoforests are noncovering

**Statement.** If every connected component of the original
prime-interaction graph has at most one cycle, no choice of the actual
classes A_d covers all integers. The number of vertices, degrees, all
finite prime-power heights and all residues are unrestricted. In
particular, the statement retains three-prime labels on a triangular
cycle. This is an ordinary mathematical proof, not a Lean-certified
noncoverage theorem or a literature-priority claim.

The existence conclusion already follows from
[Schroeder, Theorem 1.1](../../../../Library/Arith/schroeder2026noncoverage.md):
every modulus here has at most three distinct prime factors, since its
support is a clique in a pseudoforest. The cited source has the repository
audit described in that reference. The independent argument below supplies
the specified retained-domain reserve, coordinate bounds and exact extension
weights; it does not add a new noncoverage case beyond that theorem.

Different components use disjoint CRT coordinates, so their avoiding
assignments combine. Tree components were treated above. For a connected
component with one cycle, retain the cycle and, if 3 occurs off it, the
unique path from 3 to the cycle. Call the resulting graph C. All removed
vertices are at least 5 and form singly attached trees. A label with
three support primes creates a triangle, so it must lie on the unique
cycle. Larger supports and mixed labels crossing removed branches are
impossible. Thus PB4--PB7 apply with every original label accounted for.

On the actual nonempty set V=product V_p use one common probability law

    nu_C=product_(p in C) H_p( . | V_p).                     (UC1)

It is H_C conditioned on the product set V, not the marginal of H_Q
conditioned on globally surviving the removed classes. Each original
p^a-prefix has nu_C-marginal at most p^(-a)/delta_p. Put
`b_p=1/((p-1)delta_p)`. Summing the actual distinct exponent tuples
and applying the union bound yields

    nu_C(union of mixed core classes)
      <= sum_(pq edge of C) b_p b_q
          + 1[cycle is a triangle on r,s,t] b_r b_s b_t.     (UC2)

Both sides use the same actual domains and the same law. The extra
term bounds all original three-prime labels at every finite height;
it is not discarded or absorbed into binary labels.

For primes p>=5, PB5 gives

    b_p <= w_p:=(p-1)/((p-1)^2-(p-1)-1),
    w_5=4/11, w_7=6/29, w_11=10/89, w_13=12/131.

The function w_p decreases for p>=5. A self-contained square budget is

    sum_(p>=5 prime) w_p^2 <1/4.                            (UC3)

For real p>=15, d_p>=181/196. Bound the remaining primes by all odd
integers 15+2k, k>=0, and use the decreasing function (14+2t)^(-2):

    sum_(k>=0) (14+2k)^(-2)
      <=1/196+integral_0^infinity (14+2t)^(-2)dt
       =1/196+1/28.

The four small primes plus this tail give

    sum_(p>=5 prime) w_p^2
      <= (4/11)^2+(6/29)^2+(10/89)^2+(12/131)^2
           +(196/181)^2*(1/196+1/28)
       =110535026441982184/453169967387358001 <1/4.

For any graph on primes at least 5 with maximum degree at most a positive Delta,
`sum_edges b_p b_q <= (1/2) sum_p degree(p)b_p^2 <Delta/8`.
This follows from 2xy<=x^2+y^2 and UC3; edge violation events need
not be independent.

**3 on the cycle.** Now C is precisely that cycle. Let its two neighbors
of 3 be q<r. The edges away from 3 have maximum degree two and total
budget less than 1/4. It suffices to bound
`b_3(b_q+b_r+b_q b_r)<7/10`: this includes the actual triple term
if the cycle is triangular, and is still an upper bound otherwise.
PB6 gives the exhaustive cases

| Neighbors | Bound on b_3 | Bound on b_3(b_q+b_r+b_q b_r) |
|---|---:|---:|
| q=5, r=7 | 18/17 | 3708/5423 <7/10 |
| q=5, r>=11 | 6/5 | 276/445 <7/10 |
| q>=7, r>=11 | 2 | 1768/2581 <7/10 |

For the first row, PB6 gives delta_3>=17/36; the second uses
delta_3>=5/12 and the third delta_3>=1/4. Monotonicity of w supplies
the other factors. Thus the complete budget in UC2 is less than

    7/10+1/4=19/20.                                        (UC4)

**3 off the cycle.** Retaining its path makes 3 a degree-one endpoint
of C. If its neighbor is 5, PB6 bounds its incident edge by 24/55;
if the neighbor is at least 7, the bound is 12/29<24/55.
After deleting 3 the remaining core has maximum degree at most three,
so its edge sum is less than 3/8. Any triangle avoids 3 and its triple
term is at most w_5^3=64/1331. Consequently

    total budget <24/55+3/8+64/1331
                  =45757/53240 <19/20.                     (UC5)

No monotonicity of prime labels along the path is assumed.

**3 absent.** The core is a cycle on primes at least 5, giving total
budget less than `1/4+64/1331<19/20`. The triple term is only needed
for a triangle; keeping it in the bound is harmless.

In all cases nu_C gives more than 1/20 mass to avoiding every actual
mixed core class. PB7 supplies simultaneous extensions into the removed
trees, and CRT gives an original uncovered residue. Componentwise CRT
then proves the stated pseudoforest noncoverage result.

The 1/20 is a retained-coordinate probability, not a uniform lower bound
for full original Haar survival. For a connected cyclic component with
original period Q it implies only the period-dependent bound

    H_Q(global avoidance) > product_(p in C)|V_p|/(20Q)>0,   (UC6)

because every good core tuple has at least one extension. More exactly,
let W_p(x_p) count the jointly avoiding assignments of all trees attached
at p, including their original labels meeting p, and set it to zero when
a pure p-class holds. If G_C is the core
set avoiding all remaining mixed classes, the full survivor count is

    sum_(x in G_C) product_(p in C) W_p(x_p).                (UC7)

Here `W_p(x_p)>0` precisely on V_p. These nonconstant weights cannot be
omitted when transporting densities or overlap costs.

A minimum-cardinality distinct odd whole cover, if one exists, therefore
has a connected prime graph with at least two independent cycles. Indeed,
if its graph had multiple components, a zero product of their finite
avoidance probabilities would give a covering proper subfamily. Neither
this consequence nor UC6 excludes general cores with multiple cycles.

The [exact control program](../frontier/cover-geometry/cyclic_core_extension_controls.py)
and [data](../frontier/cover-geometry/cyclic_core_extension_controls.json)
retain literal original labels and residues, the full-coordinate tree
domains, extension counts, core compatibility and original-Haar counts.
Their finite examples check the implementation and constants; the
unbounded graph and height claim follows from PB1--UC7. The existing
[feedback-vertex estimates](18-four-vertex-blocks-and-cycle-breaking-vertices.md#a-bounded-number-of-cycle-breaking-vertices-in-each-component) retain their stated head and tail-cutoff
hypotheses and are not being quoted as this all-odd specialization.
