# Cross-pair Haar rectangle charges have no uniform excess bound

The fixed-pair account of [Report 840](840-two-cut-rectangle-multiplicity-charges-the-actual-cover-excess.md)
cannot be extended to all selected prime pairs merely by integrating
against full Haar measure. Under its local covered/private-fibre
hypotheses, no universal constant bounds the sum of the rectangle masses
by that constant times the original covering excess. This remains false
when every original is irredundant, and even when every modulus is
squarefree.

Two finite constructions establish these statements. The first has an
exact ratio greater than $2n/7$, using one tag prime at different
heights. The second has squarefree moduli and ratio tending to infinity,
using disjoint finite pools of tag primes. All phases are fixed once by
CRT. All probabilities below are under the full original-period Haar
law, including every tag coordinate.

The squarefree families also have covered fraction tending to one.
Neither a fixed additive hole-mass penalty nor a fixed multiple of the
logarithm of inverse hole mass repairs the proposed bound: the rectangle
sum grows quadratically, while excess and logarithmic hole cost grow
at most linearly in the construction parameter.

Both families have explicit global holes. They refute the proposed
extension under Report 840's local premises; they do not refute a bound
with the additional hypothesis of whole coverage, nor Erdős #7. These
are ordinary proofs, not Lean verification or a claim of literature
priority.

## 1. The precise extension being tested

For one actual finite original family $C_i=[a_i]_{d_i}$, write

$$
L=\sum_i\mathbf1_{C_i},\qquad
\mathcal E=\mu((L-1)_+),
\tag{AP1}
$$

where $\mu$ is uniform on its full period. Select some original targets,
with at most one prime pair $\{p_t,q_t\}$ per target. Each pair must
satisfy Report 840's global numerical condition: every other original
is deficient at one of the target's two selected prime heights.

Define $R_t$ exactly as there: retain all full coordinates outside the
pair, retain the lower selected digits, and select only boundary fibres
that are entirely covered and contain an actual private point of $C_t$.
Within those fibres take the rectangle outside both target root digits.
All tests use the same original carrier, family and probability law.

For one fixed pair Report 840 proves

$$
\sum_t\mathbf1_{R_t}\le(L-1)_+.
\tag{AP2}
$$

The proposed extension asks for a constant $C<\infty$, independent of
the number of primes, original labels and heights, such that

$$
\sum_t\mu(R_t)\le C\mathcal E
\tag{AP3}
$$

for targets whose pairs may differ. The earlier pointwise cross-pair
control did not settle AP3: collisions elsewhere in the full period
could still pay an integrated account. The constructions below include
all such collisions.

## 2. One tag prime and an exact unbounded ratio

Fix $n\ge1$, and choose distinct primes

$$
P=\{p_1,\ldots,p_n\},\qquad p_i>\max(5,4n).
$$

Use the additional primes $3,5$. Put

$$
D=\prod_i p_i,\qquad A=\prod_i(p_i-1),\qquad K=A+2,
\qquad N=3D5^K.
\tag{AP4}
$$

Let $V=\prod_i(\mathbb Z/p_i\mathbb Z\setminus\{1\})$, so
$|V|=A$. Choose any bijection $j:V\to\{1,\ldots,A\}$.
The following are literal original congruence classes on $N$:

* For each $v\in V$, a supplier $S_v$ with $P$-coordinates $v$
  and tag coordinate $0\bmod5^{j(v)}$. Its modulus is $D5^{j(v)}$.
* A supplier $B_0$ with $3$-coordinate $0$ and tag
  $0\bmod5^{K-1}$, of modulus $3\cdot5^{K-1}$.
* A supplier $B_2$ with $3$-coordinate $2$ and tag
  $0\bmod5^K$, of modulus $3\cdot5^K$.
* For each $i$, a target $C_i$ with coordinates $1\bmod3$,
  $1\bmod p_i$, and $0\bmod5^K$, of modulus $3p_i5^K$.

CRT assigns one residue to each displayed modulus. Every modulus is odd
and greater than one. They are distinct: the $S_v$ have different
5-heights; the two $B$ labels have no $P$ factor; and the targets
have different single $P$ factors and a factor 3 absent from every
$S_v$. This includes $n=1$.

Choose the pair $\{p_i,3\}$ for target $C_i$. Every $S_v$ omits 3,
each $B$ omits $p_i$, and every other target omits $p_i$. Thus
global numerical admissibility holds against every original, not only
the active ones on a selected fibre.

### 2.1 Actual covered/private fibres

The canonical boundary for $C_i$ has period

$$
b_i=5^K\prod_{j\ne i}p_j.
\tag{AP5}
$$

A fibre can contain a private target point only if its tag is zero
modulo $5^K$. If some fixed $p_j$-coordinate with $j\ne i$ is 1,
then $C_j$ covers the entire part of $C_i$ in that fibre, so there is
no private target point.

Conversely, suppose the tag is zero modulo $5^K$ and every fixed
$p_j$-coordinate, $j\ne i$, differs from 1. The entire free
$p_i\times3$ fibre is covered:

* $3$-coordinate 0 or 2 is covered by its $B$ supplier;
* at $3$-coordinate 1 and $p_i\ne1$, the unique full $P$-pattern
  $v\in V$ supplies $S_v$, which is active on this tag fibre;
* the remaining root $(p_i,3)=(1,1)$ is covered only by $C_i$.

This also verifies its private point within that same fibre. Hence all
the complementary rectangles are exactly the same set:

$$
R_i=R=\{x_{p_j}\ne1\ (\forall j),\ x_3\ne1,
                  \ x_5=0\bmod5^K\}.
\tag{AP6}
$$

Write

$$
a=\prod_i(1-1/p_i),\qquad s=\sum_i1/p_i<1/4.
\tag{AP7}
$$

Under full Haar, AP6 gives

$$
\sum_i\mu(R_i)=\frac{2n}{3}a5^{-K}.
\tag{AP8}
$$

The factor $5^{-K}$ is retained; no conditional fibre probability is
substituted for the full mass.

### 2.2 Exact global excess, including shallower tag layers

Let $L_S,L_B,L_C$ denote the three groups' loads. The $S_v$ are
pairwise disjoint because their full $P$-patterns differ. The two
$B$ suppliers are disjoint at 3. A target misses every $S_v$ at its
$p_i$-coordinate and misses each $B$ at 3. Therefore, pointwise,

$$
(L-1)_+=L_S L_B+(L_C-1)_+.
\tag{AP9}
$$

On the tag-zero fibre of height $K-1$, all $S_v$ are already active.
Thus the $S/B_0$ intersection has mass $a5^{-(K-1)}/3$.
The $S/B_2$ intersection has mass $a5^{-K}/3$. The former contributes
five times the latter; discarding that shallower-tag payment would give
an incorrect account. The total supplier excess is

$$
\mu(L_S L_B)=\frac{6a}{3}5^{-K}.
\tag{AP10}
$$

On $x_3=1,x_5=0\bmod5^K$, the target load is
$Z=\sum_i\mathbf1_{\{x_{p_i}=1\}}$. Its mean is $s$, and
$\Pr(Z>0)=1-a$. Since $(Z-1)_+=Z-\mathbf1_{Z>0}$,

$$
\mu((L_C-1)_+)=\frac{s-1+a}{3}5^{-K}.
\tag{AP11}
$$

Combining AP9--AP11 accounts for every original intersection and gives

$$
\mathcal E=\frac{7a+s-1}{3}5^{-K},\qquad
\frac{\sum_i\mu(R_i)}{\mathcal E}
   =\frac{2na}{7a+s-1}>\frac{2n}{7}.
\tag{AP12}
$$

The denominator is positive because $s\ge1-a$ and $a>0$; it is
strictly smaller than $7a$ because $s<1$. For any proposed constant
$C$, choosing $n>7C/2$ refutes AP3.

### 2.3 Irredundancy and the global hole

Every original has an actual private CRT point on this same carrier:

* For $S_v$, take $P=v$, $x_3=1$, $x_5=0\bmod5^K$.
* For $B_0$ or $B_2$, take its 3-coordinate, all $P$-coordinates
  equal to 1, and $x_5=0\bmod5^K$.
* For $C_i$, take $x_{p_i}=1$, all other $P$-coordinates zero,
  $x_3=1$, and $x_5=0\bmod5^K$.

The CRT point with all $P$-coordinates zero, $x_3=1$, and $x_5=1$
misses every original. Thus the family is irredundant on its union and
is a global noncover. Its very large but finite number of labels and
tag height are legitimate for the tested unbounded interface; no
efficient enumeration claim is made.

## 3. A squarefree construction

The failure is not confined to high prime powers. Fix $n\ge4$.
Choose disjoint sets $P,Q$, each containing $n$ odd primes exceeding
$n^2$, with every chosen prime at most

$$
R=2^{2n}\,2n^2.
\tag{AP13}
$$

For example, successive applications of Bertrand's postulate give
$2n$ distinct primes in successive doubling intervals above $2n^2$
and below this endpoint. Put

$$
a_P=\prod_{p\in P}(1-1/p),\quad
a_Q=\prod_{q\in Q}(1-1/q),\quad
\lambda=\log(4R).
\tag{AP14}
$$

The union bound gives $a_Pa_Q\ge1-2/n\ge1/2$.

For every pair $(p,q)\in P\times Q$, include the target
$C_{p,q}=\{x_p=x_q=1\}$, with modulus $pq$.

For each full non-1 pattern $v\in\prod_{p\in P}(\mathbb F_p\setminus \{1\})$, choose a finite nonempty pool $T_v$ of new tag primes.
Do the same for every non-1 pattern on $Q$. All pools are disjoint
and avoid $P\cup Q$. Choose them with

$$
\lambda\le\sum_{\ell\in T_v}\frac1\ell<\lambda+1.
\tag{AP15}
$$

There are finitely many patterns. Divergence of the sum of prime
reciprocals after removal of any finite set permits choosing the pools
successively, stopping at the first crossing of $\lambda$. A final
increment is less than 1. All tag primes can be required to exceed $R$.

For each $P$-pattern $v$ and each $\ell\in T_v$, include one
supplier specifying $P=v$ and $x_\ell=0$, with modulus
$\ell\prod_{p\in P}p$. Include the analogous $Q$-suppliers.
Every original modulus is odd, squarefree and greater than one.
Every supplier uses its own tag prime, so numerical moduli are distinct
within and between both sides and from the targets. They also form a
divisibility antichain: supplier tags are unique, and every target uses
one prime from each side, whereas each supplier uses primes from only
one side together with its private tag.

The complete period includes every tag prime. A pattern is called active
when at least one tag in its assigned pool has coordinate zero. Full
product Haar, AP15, and $1-u\le e^{-u}$ imply

$$
\Pr(v\text{ inactive})
 =\prod_{\ell\in T_v}(1-1/\ell)
 \le e^{-\lambda}=\frac1{4R}.
\tag{AP16}
$$

No phases are chosen after observing tags. The original classes were
fixed before this probability calculation.

### 3.1 Actual rectangle mass

Select the pair $\{p,q\}$ for target $C_{p,q}$. Other targets omit
at least one of these primes; every $P$-supplier omits $q$, and
every $Q$-supplier omits $p$. This is the required global numerical
admissibility. Every cut height is one.

Fix all other core coordinates to non-1 values, and fix every tag.
If all $p-1$ relevant non-1 $P$-patterns and all $q-1$ relevant
non-1 $Q$-patterns are active, the entire $p\times q$ fibre is
covered: $P$-suppliers cover its $p\ne1$ rows, $Q$-suppliers
cover its $q\ne1$ columns, and the target alone covers $(1,1)$.
That root is private because all other core coordinates differ from 1.

For each fixed full core assignment having no coordinate 1, the union
bound and AP16 give probability at least

$$
1-\frac{p+q-2}{4R}\ge\frac12
\tag{AP17}
$$

that all these patterns are active. Independence between the pattern
activation events is not needed for this lower bound. The core and tag
coordinates are independent under the declared full Haar law.
Every resulting point belongs to the actual complementary rectangle,
so

$$
\mu(R_{p,q})\ge\frac12a_Pa_Q\ge\frac14,
\qquad \sum_{p,q}\mu(R_{p,q})\ge\frac{n^2}{4}.
\tag{AP18}
$$

All tag assignments not satisfying the sufficient event remain in the
global probability space. AP18 does not condition away their cost.

### 3.2 Global cost and private points

All the supplier multiplicities, including cases where several tags
activate the same pattern, are paid in the global first moment:

$$
\begin{aligned}
\mathcal E\le\mu(L)
&\le (a_P+a_Q)(\lambda+1)
       +\left(\sum_{p\in P}\frac1p\right)
        \left(\sum_{q\in Q}\frac1q\right)\\
&\le2(\lambda+1)+\frac1{n^2}.
\end{aligned}
\tag{AP19}
$$

Thus AP18--AP19 yield

$$
\frac{\sum_{p,q}\mu(R_{p,q})}{\mathcal E}
\ge\frac{n^2}{4[2(\log(4R)+1)+1/n^2]}
\longrightarrow\infty.
\tag{AP20}
$$

The denominator is positive: activating relevant patterns on both sides
gives a positive-measure intersection of two suppliers. Since
$\log(4R)=2n\log2+\log(8n^2)$, the bound in AP19 grows only linearly
in $n$, up to the displayed logarithmic term.

All originals again have explicit private points. For a $P$-supplier,
use its $P$-pattern, set every $Q$-coordinate to 1, set its own tag
to zero and every other tag to 1. This excludes the $Q$-suppliers,
all targets, and every other $P$-supplier. Reverse the sides for a
$Q$-supplier. For target $C_{p,q}$, make exactly those two core
coordinates 1, all other core coordinates zero, and every tag 1.
Finally, all core coordinates zero and all tags 1 give a global hole.

The primes, pools and original phases are all finite and fixed. This is
a squarefree irredundant noncover, not a random covering family.

### 3.3 Near coverage and the logarithmic cost of the hole

Let $A_S$ be the event that every core coordinate on side $S\in\{P,Q\}$
differs from 1. Its mass is $a_S$. For a non-1 pattern $v$ on that
side, define its actual tag-pool failure probability and total inactive
pattern mass by

$$
f_S(v)=\prod_{\ell\in T_v}(1-1/\ell),\qquad
h_S=\sum_{v\in A_S}\mu_S(\{v\})f_S(v),\qquad
\varepsilon=e^{-\lambda}=\frac1{4R}.
\tag{AP21}
$$

Here $\mu_S$ is uniform on the full core coordinates on side $S$;
the complete tag contribution is already in $f_S(v)$. AP16 gives
$0<h_S\le a_S\varepsilon$.

If both core sides have a coordinate equal to 1, a target covers the
point. If exactly one side has all coordinates different from 1, only
its matching supplier pool can cover. If both sides have all coordinates
different from 1, either matching pool can cover. These cases are
disjoint. The $P$ core and all its tag pools are independent of the
$Q$ core and all its tag pools under the original full Haar law. Hence
the exact global hole mass is

$$
H:=\mu(L=0)
 =(1-a_Q)h_P+(1-a_P)h_Q+h_Ph_Q.
\tag{AP22}
$$

At a fixed core point, the conditional hole probability is zero,
at most $\varepsilon$, or at most $\varepsilon^2$. Also
$1-a_S\le1/n$. The explicit hole from Section 3.2 has positive mass
on this finite full period, so

$$
0<H\le\varepsilon,\qquad
H\le\frac{2\varepsilon}{n}+\varepsilon^2.
\tag{AP23}
$$

Thus these same odd, squarefree, distinct and irredundant families
cover a fraction tending to one. In particular, no fixed finite
$C,C_0\ge0$ can bound $\sum_{p,q}\mu(R_{p,q})$ by
$C\mathcal E+C_0H$: AP18 is quadratic in $n$, AP19 is at most
linear, and AP23 tends to zero.

A logarithmic hole penalty also fails, but this requires a lower bound
on $H$. Every tag prime exceeds $R$. Using
$\log(1-u)\ge-u/(1-u)$ and AP15 gives, for every actual pattern,

$$
\log f_S(v)
 \ge-\frac{\sum_{\ell\in T_v}1/\ell}{1-1/R}
 \ge-\frac{\lambda+1}{1-1/R}.
\tag{AP24}
$$

Put $\beta=\exp[-(\lambda+1)/(1-1/R)]$. Then
$h_S\ge a_S\beta$, so AP22 and $a_Pa_Q\ge1/2$ imply

$$
H\ge h_Ph_Q\ge\tfrac12\beta^2,\qquad
\log(1/H)\le\log2+\frac{2(\lambda+1)}{1-1/R}.
\tag{AP25}
$$

All logarithms are natural. For $n\ge4$, the inequalities
$\log2\le1$ and $\log n\le n/2$ give
$\lambda=2n\log2+\log8+2\log n\le3n+3\le4n$.
Using $R\ge2$ in AP25 and AP19 yields the explicit bounds

$$
\mathcal E\le9n,\qquad \log(1/H)\le18n.
\tag{AP26}
$$

Consequently, for any fixed finite $C,D\ge0$, choosing $n\ge4$ with
$n>36C+72D$ gives

$$
\sum_{p,q}\mu(R_{p,q})\ge\frac{n^2}{4}
 >(9C+18D)n
 \ge C\mathcal E+D\log(1/H).
\tag{AP27}
$$

The many tag variables introduce no omitted mass: their complete
effect is in AP21 and its reciprocal-prime bound AP24. Every instance
still has $H>0$. AP27 does not address a theorem restricted to exact
whole coverage or a family-dependent penalty; it rules out this fixed
scalar correction under the stated local hypotheses.

## 4. Consequence for the shared budget

The common-pair theorem remains valid. The counterexamples show that
letting each target choose its own pair needs a genuinely additional
account, even after replacing pointwise comparison by full Haar
integration. Numerical distinctness, oddness, irredundancy and
squarefreeness do not supply a support-independent constant in AP3.
An arbitrarily high covered fraction and the two scalar hole penalties
in Section 3.3 do not supply one either.

This does not exclude weights that depend on the chosen prime pair or
the actual source, a jointly allocated subset of targets, another
quantity on the right, or a theorem using whole coverage essentially.
The unweighted Haar obstruction already prevents deriving an arbitrary
same-law weighted extension from Report 840's local premises alone.
The original unrestricted covering problem is unchanged.

## 5. Exact finite controls and evidence scope

The [standalone checker](../../../frontier/moments-survival/all_pair_haar_rectangle_excess.py)
and [exact output](../../../frontier/moments-survival/all_pair_haar_rectangle_excess.json)
test only the two declared single-tag cases $P=(7)$ and $P=(11,13)$.
They construct every original as a numerical CRT residue and modulus,
verify global pair admissibility, and check an actual private witness
for every original and an actual global hole.

The full period is not enumerated. All tag conditions are zero
congruences, so membership depends only on the truncated 5-valuation.
The nonzero stratum at depth $j<K$ has full tag probability
$4/5^{j+1}$; the zero stratum has probability $5^{-K}$.
Every complete core residue is tested in each stratum, using numerical
congruence membership and an independent coordinate comparison.
Covered/private boundary predicates and their rectangles are computed
from those actual memberships before comparison with AP6.

| Cut-prime set $P$ | Original classes | Compressed states | Numerical membership comparisons | Exact ratio in AP12 |
| --- | ---: | ---: | ---: | ---: |
| $(7)$ | 9 | 189 | 1,701 | $1/3$ |
| $(11,13)$ | 124 | 52,767 | 6,543,108 | $480/721$ |

The exact full-Haar excess calculation includes the shallower
$K-1$ tag contribution. These small controls check the implementation
and mass formulas; their ratios are below one and do not independently
establish unboundedness. AP12 proves that claim for arbitrary $n$.
The squarefree family and its hole bounds are supported by
AP13--AP27's symbolic proof;
no enumeration of its tag pools is claimed.

The program uses only the Python standard library and explicit output
paths. Its checks raise exceptions and remain active under -O.

~~~sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/moments-survival/all_pair_haar_rectangle_excess.py --output /tmp/e7_all_pair_haar_rectangle_excess.json
~~~
