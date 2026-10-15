# AURIC FIB-ATOM: separator completeness, shared-edge synchronization and missing joint coordinates

**Convention 40.0 (The common-copy separator setting).**
The graphs, occupancy arrays and attainable histograms are those of
[§39 of the preceding volume](AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS_CONTINUATION.md).
All shared vertices retain their identities across branches, and every
ordinary degree counts one common set of rows.

## 40. The missing joint coordinate and the cost of inconsistent separator laws

**Definition 40.1 (The three-position separator observation).**
For $H=P_3$ with edges $1-2$ and $2-3$, order its five patterns as
$\varnothing,\{1\},\{2\},\{3\},\{1,3\}$. Write

$$
X=c_1=h_{\{1\}}+h_{\{1,3\}},\qquad
Z=c_2=h_{\{2\}},\qquad
Y=c_3=h_{\{3\}}+h_{\{1,3\}},\qquad K=h_{\{1,3\}}.
\tag{40.1}
$$

For fixed local totals on a branch extending this separator, let
$\mathcal K_a$ be the set of all $K$ attainable by its local
realizations. A boundary law is a probability vector $p$ indexed
by $\operatorname{Ind}(H)$; it records a complete separator pattern,
not just its individual vertex means. Write $\kappa(p)=p_{\{1,3\}}$.
For an array with $m>0$, its empirical law has $\kappa=K/m$.

**Theorem 40.2 (An exact information profile for the common-copy seam).**
The separator observation of §39 has the following three properties.
For $P_3$, nonnegative integer data $(m,X,Z,Y)$ determine precisely
the histogram family

$$
h=(m-X-Y-Z+K,\ X-K,\ Z,\ Y-K,\ K),
\qquad
\max(0,X+Y+Z-m)\le K\le\min(X,Y),
\tag{40.2}
$$

where $K$ ranges over integers. If the interval is empty there is
no separator realization. Given equal $(m,X,Z,Y)$, prescribed
histograms agree if and only if their $K$ values agree; for total
fibres the exact global criterion is instead
$\bigcap_a\mathcal K_a\ne\varnothing$.

For an arbitrary finite separator $H$ with $q$ vertices and
$D_H=|\operatorname{Ind}(H)|$, normalization and the $q$ vertex
means have rank $q+1$. Exactly $D_H-q-1$ further independent
linear statistics are necessary and sufficient to recover every
real probability law on its legal patterns. They may be chosen as

$$
\mu_T=\sum_{I\supseteq T}p_I,
\qquad T\in\operatorname{Ind}(H),\quad |T|\ge2.
\tag{40.3}
$$

Finally, let $P$ and $Q$ be fixed full probability laws on the
independent sets of two branches, with separator laws $p$ and $q'$.
Among couplings of these full branch laws, the least probability
that their two separator patterns disagree is

$$
\operatorname{TV}(p,q')
=\frac12\sum_{J\in\operatorname{Ind}(H)}|p_J-q'_J|.
\tag{40.4}
$$

For $P_3$, write $\kappa_P=\kappa(p)$ and
$\kappa_Q=\kappa(q')$. With identical three vertex means,
(40.4) equals $2|\kappa_P-\kappa_Q|$. For two fixed arrays with the same
positive common degree $m$ and the same three totals, the minimum
number of mismatched rows under permutation is
$2|K_P-K_Q|$.

Proof. Solving (40.1) and the normalization equation gives every
entry in (40.2). Requiring all five entries to be nonnegative
gives exactly the displayed interval, since $Z\ge0$ is already
assumed. Conversely any integer in that interval yields a histogram
of $m$ legal separator rows: simply take each pattern its stated
number of times. Extension to a branch with prescribed private
totals can restrict this interval further; that restriction is
exactly what $\mathcal K_a$ records. By (40.2), $K\mapsto h$ is
injective at fixed totals. Substituting it in (39.4) proves the
intersection criterion. No assertion that $\mathcal K_a$ is the
whole separator interval, or even an interval, is needed.

For example, at $m=2$, $(X,Z,Y)=(1,0,1)$, the endpoint values
$K=0,1$ give respectively the arrays
$\{\{1\},\{3\}\}$ and $\{\varnothing,\{1,3\}\}$.
Their means coincide and their histograms differ. If both branches
are just $P_3$ with these totals, each has $\mathcal K_a=\{0,1\}$.
Choosing different endpoint arrays does not obstruct existence:
one can replace a chosen array and align at either common $K$.
In contrast, the private paths of Theorem 39.2, attached at the
nonedge $1,3$ and with occupancy zero at $2$, force the attainable
sets $\{1\}$ and $\{0\}$. This pair does obstruct existence.
At $m=0$ all totals and $K$ are zero; no normalized $\kappa$ is
defined or needed.

For the general rank statement, form the $(q+1)$-by-$D_H$ matrix
whose column at $I$ is $(1,\mathbf1_I)$. The empty-set column is
$(1,0)$, and subtracting it from the singleton columns gives
$(0,e_v)$. These $q+1$ columns are independent, so the rank is
exactly $q+1$ and its real kernel has dimension $D_H-q-1$.
Adding fewer than this many scalar linear statistics leaves a
nonzero kernel vector $v$. Its coordinate sum is zero. Starting
from the uniform strictly positive legal-pattern law $p_*$,
both $p_*+\varepsilon v$ and $p_*-\varepsilon v$ remain probability
laws for sufficiently small $\varepsilon>0$. They have identical
augmented observations and differ. Thus the lower bound applies
to recovery of all real probability laws, including a neighborhood
of a full-support law. A particular face of the probability
simplex can have a smaller fibre dimension.

For attainability of the bound set $\mu_\varnothing=1$ and include
the singleton moments as the already observed means. The inverse
of the complete moment transform is

$$
p_I=\sum_{\substack{T\in\operatorname{Ind}(H)\\T\supseteq I}}
(-1)^{|T|-|I|}\mu_T.
\tag{40.5}
$$

To check it, substitute $\mu_T=\sum_{J\supseteq T}p_J$.
The coefficient of $p_J$ is zero unless $J\supseteq I$; in that
case it is $\sum_{I\subseteq T\subseteq J}(-1)^{|T|-|I|}$.
All intermediate $T$ are legal because $J$ is independent, so
this sum is $(1-1)^{|J\setminus I|}$, equal to one precisely
when $I=J$. For the reverse composition, the coefficient of
$\mu_T$ in $\sum_{I\supseteq B}p_I$ is
$\sum_{B\subseteq I\subseteq T}(-1)^{|T|-|I|}$ when $T\supseteq B$,
and zero otherwise. The displayed sum is $(1-1)^{|T|-|B|}$,
so only $T=B$ remains. In particular taking $B=\varnothing$
gives total mass $\mu_\varnothing$.
Therefore candidate moments specify a probability law exactly
when $\mu_\varnothing=1$ and all inverse coordinates are
nonnegative; those conditions give both total mass one and every
stated moment. The full moment matrix is invertible. Its rows
with $|T|\ge2$ number $D_H-q-1$ and complete the rank.

This is incidence-algebra Möbius inversion on Boolean intervals,
as in Rota, *On the foundations of combinatorial theory I. Theory
of Möbius functions*, §3 [Rota40]. The legal-set poset itself
need not be a Boolean lattice: a union of legal sets can be
illegal. The corresponding path-law suppliers are *Hidden
Relations*, C-28.3.2–C-28.3.3 and C-28.5.1 [Hidden40]; their
support and inversion arguments are used here for a shared
separator. For a clique, $D_H=q+1$ and there are no extra
coordinates. For $P_3$, $D_H=5$, $q=3$, and the sole extra
coordinate is $\mu_{\{1,3\}}=\kappa$. This is a dimension
bound for independent linear observations. It is not a bound
on integer bit encodings, nonlinear injections, storage, or
computational resources.

For (40.4), any boundary coupling $\pi$ has
$\pi(J,J)\le\min(p_J,q'_J)$, so its agreement probability is
at most $M=\sum_J\min(p_J,q'_J)$. Since both masses sum to
one, $1-M=\frac12\sum_J|p_J-q'_J|$. To attain this bound,
put the common mass $\min(p_J,q'_J)$ on each diagonal entry.
The residual nonnegative masses
$r_J=p_J-\min(p_J,q'_J)$ and
$s_J=q'_J-\min(p_J,q'_J)$ have equal total $d=1-M$ and
disjoint supports. If $d>0$, add $r_Js_L/d$ at $(J,L)$;
all this added mass is off diagonal. If $d=0$, the diagonal
already supplies the coupling. This is the finite maximal-coupling
construction, the classical tool also developed for Markov
chains by Griffeath, *A maximal coupling for Markov chains*
[Griffeath40].

It remains to preserve the full original branch laws, not merely
their separator marginals. For every $(J,L)$ having positive
coupling mass, one has $p_J>0$ and $q'_L>0$. Draw a left
independent set conditionally under $P$ given separator $J$,
and a right set conditionally under $Q$ given separator $L$,
independently conditional on that pair. Summing over the other
side gives $P$ and $Q$ back exactly. Zero-probability separator
events receive no coupling mass and require no conditional law.
This extension proves the optimum for the full branch laws.

For arbitrary real $P_3$ laws with equal means, solving the
same linear equations as (40.2) with total mass one gives

$$
p-q'=(\kappa_P-\kappa_Q)(1,-1,0,-1,1).
\tag{40.6}
$$

Its $\ell^1$ norm is $4|\kappa_P-\kappa_Q|$, proving the
factor two in (40.4). In two integer arrays match
$\min(h_J,h'_J)$ rows in each block. All remaining rows can be
paired arbitrarily; their pattern supports are disjoint, so all
are mismatches. Conversely no permutation matches more rows of
pattern $J$ than that minimum. The exact unmatched count is

$$
m-\sum_J\min(h_J,h'_J)
=\frac12\sum_J|h_J-h'_J|=2|K_P-K_Q|.
\tag{40.7}
$$

All match counts are integers, so the optimum is achieved by an
actual permutation, without a rounding step. $\square$

**Proposition 40.3 (Positive mismatch does not define a glued variable).**
When (40.4) is positive, its attaining coupling retains two
different separator variables on the mismatch event. It is a
relaxation of common-source realization, not an actual gluing.
For fixed full laws, zero mismatch is exactly the condition that
the two induced separator laws agree. For total fibres and any
number of branches, (39.4) remains the existence criterion.

Proof. A genuine global independent set has one restriction to
$H$, so the two branch restrictions must agree with probability
one. Positive mismatch contradicts that requirement on an event
of positive mass. When the laws agree, the diagonal construction
and conditional extension above give a common separator and a
legal rowwise union, because there are no cross edges. The
two-branch optimal mismatch formula does not assert a formula
for a many-branch mismatch objective. In particular selecting
one incompatible histogram on each branch cannot disprove the
intersection of their attainable histogram sets. $\square$

[Rota40]: https://doi.org/10.1007/BF00531932
[Hidden40]: AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md
[Griffeath40]: https://doi.org/10.1007/BF00539434

## 41. The retained-edge odd-cycle algebra and its full interior

**Definition 41.1 (Labelled odd cycles with a common edge).**
Fix integers $k\ge2$ and $b\ge1$. Let $G^e_{k,b}$ have shared vertices
$a,b_0$ with the edge $\{a,b_0\}$ retained. For each branch
$\ell=1,\ldots,b$ add $2k-1$ private vertices and a path from
$b_0$ through these vertices to $a$, of $2k$ edges. Together
with the shared edge this is a labelled $C_{2k+1}$, denoted
$C_\ell$. There are no other identifications or cross edges. On each cycle use
cyclic indices $0,1,\ldots,2k$, with $0=a$ and $1=b_0$;
positions $2,\ldots,2k$ are private. Thus
$|V(G^e_{k,b})|=2+b(2k-1)$. The superscript $e$ distinguishes
this graph from the one-common-root graph of §§35–38 [Supplier41].
Set $t=c_a$, $u=c_{b_0}$ and define

$$
\begin{aligned}
\mathcal S^e_{k,b}=\{(m,c)\in\mathbb Z_{\ge0}^{3+b(2k-1)}:
&\ c_v+c_w\le m\quad(\{v,w\}\in E(G^e_{k,b})),\\
&\ \sum_{v\in C_\ell}c_v\le km\quad(1\le\ell\le b)\},\\
\delta_\ell(m,c)&=km-\sum_{v\in C_\ell}c_v,\qquad
R^e_{k,b}=\mathbb C[\mathcal S^e_{k,b}].
\end{aligned}
\tag{41.1}
$$

The degree is $m$, the boundary grading is $(m,t,u)$, and
$X^pX^s=X^{p+s}$. Each shared occupancy is one global coordinate
and occurs once in each local cycle inequality. Let $\mathcal S_k$
denote the single-cycle semigroup of Definition 31.1, extended
to $k=2$ with its same displayed inequalities.

**Theorem 41.2 (Actual edge-compatible rows and the canonical cone).**
Every point of (41.1) is realized by exactly $m$ global independent
sets. Restriction is an additive bijection

$$
\mathcal S^e_{k,b}\ \longleftrightarrow
\{(p_1,\ldots,p_b)\in\mathcal S_k^b:
\deg_{(m,t,u)}p_1=\cdots=\deg_{(m,t,u)}p_b\}.
\tag{41.2}
$$

Its real cone is precisely the real solution cone of (41.1),
its group lattice is $\mathbb Z^{3+b(2k-1)}$, and
$\mathcal S^e_{k,b}$ is the intersection of this cone with that
lattice. The ring is a normal standard graded Cohen–Macaulay
domain of dimension $d=3+b(2k-1)$. Its canonical module is the
interior-monomial ideal with basis the exponents

$$
\mathcal S^{e,\circ}_{k,b}=
\{(m,c)\in\mathcal S^e_{k,b}:c_v\ge1,\ c_v+c_w\le m-1\ (\{v,w\}\in E),
\ \delta_\ell(m,c)\ge1\ (1\le\ell\le b)\}.
\tag{41.3}
$$

Proof. The local integer decomposition supplier is Theorem 28.2
[Supplier41], with the same ordinary degree $m$ and the same
occupancy coordinates. Its short construction explains why the
integral interface, not just a polytope description, is available.
For a single odd cycle, nonnegative integer coordinates satisfying
the edge bounds and $\sum c_i\le km$ decompose by induction on
$m$. At $m=0$ all coordinates vanish. If some coordinate is zero,
delete its vertex; the remaining support is a union of paths.
Two-color each path. On one color occupy the first $c_i$ rows,
and on the other color occupy the last $c_i$ rows, always using
the same row set of size $m$. Each edge bound makes the two
occupied row sets disjoint. Insert the
deleted zero columns to obtain legal cyclic rows.

Otherwise all coordinates are positive. Some edge $i,i+1$ has
sum at most $m-1$, since saturation of every edge would give
$2\sum c_i=(2k+1)m>2km$. The independent set
$\{i+2,i+4,\ldots,i+2k\}$ meets every other edge once and
has size $k$. Subtract its indicator and one from the degree.
Nonnegativity, all new edge bounds and the new total bound hold.
Induction supplies the other $m-1$ rows. This proves the local
integer decomposition for every $k\ge2$, including the five-cycle.

Apply it separately to each $p_\ell$. The retained shared edge
permits just three states, with forced multiplicities

$$
h_{00}=m-t-u,\qquad h_{10}=t,\qquad h_{01}=u;
\qquad 11\text{ is forbidden}.
\tag{41.4}
$$

Reorder each local array into these same three blocks. Rowwise
union then produces independent sets of the actual graph, since
the edge choices agree and there are no additional edges.
This is the complete-separator part of Theorem 39.2 for $H=K_2$.
Conversely a global array restricts to such local arrays and
satisfies (41.1). At $m=0$ the construction is the empty array.
The exponent tuple reconstructs the private coordinates and the
two common coordinates uniquely, proving (41.2). Both maps
commute with addition. Consequently the actual algebra also has
the boundary-diagonal presentation

$$
R^e_{k,b}\simeq
\bigoplus_{m\ge0}\ \bigoplus_{\substack{t,u\ge0\\t+u\le m}}
(R_k)_{(m,t,u)}^{\otimes b},
\tag{41.5}
$$

where multiplication adds the boundary degrees and multiplies
the corresponding local monomials. The monomial-basis bijection
(41.2) proves injectivity and surjectivity of this algebra map.

For the real assertion, the degree-one solution polytope is
bounded: every coordinate is between zero and one, since each
vertex has a neighbor. Every independent-set indicator lies in
it. Multiply a rational point by a common positive denominator
$m$; the integer construction gives $m$ independent sets, whose
average is the original point. Rational points are dense in a
rational polytope and the finite convex hull of indicators is
closed. Thus this polytope is exactly that convex hull. At real
degree zero the edge inequalities force all coordinates to zero,
so homogenizing proves the full real-cone assertion as well.

There are finitely many degree-one indicators and they generate
the entire semigroup by the row construction. The empty-set
indicator gives $(1,0)$; subtracting it from the singleton
indicator at $v$ gives $(0,e_v)$. Hence the group is the full
stated lattice. At degree one choose every occupancy equal to
a positive $\varepsilon$ with $2\varepsilon<1$ and
$(2k+1)\varepsilon<k$. All nonzero defining forms, including
degree, are then strictly positive, so the cone is full
dimensional. It is pointed and rational. Its integral points
are exactly (41.1); in particular if a positive integer multiple
of a lattice point lies in the semigroup, that point itself does.
This proves saturation and normality. The monomial embedding
in $\mathbb C[z_0,(z_v)_v]$ proves the domain assertion, and
degree-one generation proves standard grading.

Strictness of every defining nonzero supporting form characterizes
the interior: an equality forbids an ambient open ball, while
finitely many strict positive margins allow one. This argument
does not assume that the inequality list is an irredundant facet
list. For integral points, strictness gives exactly (41.3), and
the coordinate and edge bounds already imply $m\ge3$.
Addition by any semigroup point preserves those inequalities.

Hochster's theorem now gives Cohen–Macaulayness for this normal
affine monoid ring. The Danilov–Stanley interior formula, in the
full graded form of Barile–Bruns, *$\mathbb Z^r$-graded rings
and their canonical modules*, §5 and Theorem 5.1 [BB41], gives
the asserted canonical ideal. Their monoid is $\mathcal S^e_{k,b}$,
their coefficient field is $\mathbb C$, and their rank $r$ is
$d$; finite generation, the full group, normality, pointedness
and full cone dimension have all been established here. Thus
the canonical interpretation follows from its hypotheses, not
from the later numerical counts.

For the classical gluing correspondence, Matsuda–Ohsugi–Shibata,
Proposition 1.3 [MOS41], treats the union of two graphs along
an induced clique, with edge set their union. Each successive
gluing here has intersection the actual retained $K_2$. Its
three clique-pattern degrees are (41.4), an integral change
of coordinates from $(m,t,u)$. Their toric-fiber-product and
normality result therefore applies to this precise graph.
It is an intermediate supplier; it does not assert the uniform
interior subtraction needed in §42. Deleting the shared edge
would permit a fourth pattern and would change this argument.
$\square$

[Supplier41]: AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS_CONTINUATION.md
[MOS41]: https://arxiv.org/html/1603.01850v1
[BB41]: https://arxiv.org/html/2505.11402v1

## 42. One common removable edge state and every basic interior exponent

**Definition 42.1 (Basic exponents and the local canonical supplier).**
An interior exponent $p$ is basic if there is no nonzero
$s\in\mathcal S^e_{k,b}$ for which $p-s$ is still interior.
For a single cycle use the same definition with $\mathcal S_k$.
Its distinguished exponents are

$$
\nu_j=(2j+1;j\mathbf1),\qquad 1\le j\le k-1.
\tag{42.1}
$$

Their ordinary degree is $2j+1$, and their two endpoint totals
are both $j$. A global tuple whose every restriction is $\nu_j$
is $(2j+1;j\mathbf1_V)$; a general basic global tuple need not
be constant on every branch.

**Theorem 42.2 (Synchronized descent on a retained edge).**
A global interior exponent of $G^e_{k,b}$ is basic if and only
if at least one local restriction equals some $\nu_j$.
Consequently its basic exponents are precisely all tuples of
local interior exponents with common boundary
$(m,t,u)=(2j+1,j,j)$ and at least one entry $\nu_j$, for
$1\le j\le k-1$. These monomials form exactly a minimal
generating set of the canonical module.

Proof. The local classification is the supplier in Theorem 31.3
and §31.2 [Supplier41], also used at the common root in
Theorem 35.4. Its primary source for length $2k+1\ge7$ is
Miyazaki, *Non-Gorenstein locus and almost Gorenstein property
of the Ehrhart ring of the stable set polytope of a cycle graph*,
§4, Lemmas 4.1–4.4 and the argument immediately before
Theorem 4.5 [Miyazaki42]. The exact correspondence is his
$\ell=k$, $\eta(v_i)=c_i$, $\eta(-\infty)=m$,
$\eta_j=\nu_j$ and $R^{(0)}$ equal to the deficit-zero
face algebra. His injection has target $\omega_{R_k}(3)$;
its cokernel is $(\omega_{R_k}/X^{\nu_1}R_k)(3)$.
Thus the translation is by ordinary degree three, not by the
number of shared vertices. Theorem 4.5 itself is the Ulrich
and almost-Gorenstein conclusion; the minimal-generator
classification used here precedes it.

We give the needed local proof in these coordinates, including
$k=2$. Write $\delta=km-\sum_i c_i$ for a local interior
point $p=(m,c)$. If $\delta\ge k-1$, then $p-\nu_1$
has nonnegative coordinates, edge sums at most $m-3$, and
deficit $\delta-(k-1)\ge0$. Its degree is nonnegative because
positivity of two adjacent coordinates and their strict edge
bound give $m\ge3$. Hence $p-\nu_1\in\mathcal S_k$.
Otherwise $1\le\delta\le k-2$; put $j=k-\delta$.
For each vertex $i$, partition the other $2k$ vertices into
the $k$ edges $\{i+1,i+2\},\ldots,\{i+2k-1,i+2k\}$.
Their strict bounds imply

$$
km-\delta=\sum_r c_r\le c_i+k(m-1),
\qquad c_i\ge k-\delta=j.
\tag{42.2}
$$

An edge gives $m\ge2j+1$. Subtracting $\nu_j$ leaves
nonnegative coordinates and degree, valid edge bounds in
degree $m-2j-1$, and deficit zero. Thus every local interior
has the form $\nu_j+s$, $s\in\mathcal S_k$.
Conversely, $\nu_j$ has positive coordinates, edge slacks one
and deficit $k-j\ge1$, so adding any semigroup point preserves
interiority. At $k=2$ only the first case occurs: every local
interior is $\nu_1+\mathcal S_2$. This proves the five-cycle
endpoint directly, without extending the length hypothesis of
Miyazaki's §4.

For local minimality suppose $\nu_j-s$ is interior, with
$s=(q,d)\in\mathcal S_k$. Its edge slacks are one minus
the nonnegative edge slacks of $s$, and must be at least one.
Every slack of $s$ is therefore zero, so
$d_i+d_{i+1}=q$ for every cyclic edge. The odd cycle forces
$d_i=q/2$ for all $i$. Its total inequality gives
$(2k+1)q/2\le kq$, hence $q=0$ and $d=0$.
Thus each $\nu_j$ is basic. The generation already proved
shows that there are no other local basic exponents. For any
nonbasic local $p$, choose $p=\nu_j+s$ with $s\ne0$.
Its residual degree $q=m-2j-1$ is strictly positive, since
a degree-zero semigroup point is zero.

Now retain the endpoint data $(m,t,u)$ throughout this local
decomposition. The residual $q$-row realization has edge
pattern multiplicities

$$
r_{10}=t-j,\qquad r_{01}=u-j,\qquad
r_{00}=q-r_{10}-r_{01}=m-t-u-1.
\tag{42.3}
$$

All are nonnegative integers. The last one is independent
of the chosen $j$. Choose the removed edge state by the rule

$$
\sigma(m,t,u)=
\begin{cases}
00,&m-t-u-1>0,\\
10,&m-t-u-1=0\text{ and }t\ge u,\\
01,&m-t-u-1=0\text{ and }t<u.
\end{cases}
\tag{42.4}
$$

The strict shared-edge bound ensures $m-t-u-1\ge0$, so
these cases exhaust every interior boundary. In the first
case $r_{00}>0$. In the second case
$q=r_{10}+r_{01}>0$ and $r_{10}\ge r_{01}$, so
$r_{10}>0$. In the last case $r_{01}>r_{10}\ge0$.
At $t=u$ in the zero-$00$ case, positivity of $q$ gives
$r_{10}=r_{01}>0$, so the specified $10$ choice still exists.
These implications are valid for every possible local $j$
and every positive residual degree, including degree one.

Local integer decomposition realizes $s$ by exactly $q$ rows.
The chosen state has positive multiplicity, so some legal row
$I_\ell$ has that state. Removing it leaves a semigroup point
$s-(1,\mathbf1_{I_\ell})$, and therefore
$p-(1,\mathbf1_{I_\ell})$ remains interior. If every local
restriction of a global $p$ is nonbasic, apply the same rule
(42.4) to all of them. Their chosen rows agree on both shared
vertices. Their union is a legal global independent set $I$;
the global remainder $p-(1,\mathbf1_I)$ has all restrictions
interior, hence is interior by (41.3). Thus $p$ is not basic.

Conversely suppose $p_\ell=\nu_j$ for some branch. Any nonzero
global semigroup point has positive common degree, and its
restriction to that branch has the same positive degree.
If it could be subtracted from $p$ leaving a global interior,
it could be subtracted from $\nu_j$ leaving a local interior,
contrary to local basicness. This proves the equivalence.
Such an entry fixes the common boundary to $(2j+1,j,j)$;
distinct $j$ cannot occur at that same boundary.

Repeated subtraction when all restrictions are nonbasic lowers
the integer degree. It must terminate, since an interior has
degree at least three. It terminates at one of the stated basic
exponents, proving generation of the entire interior ideal.
The classes of those monomials in
$\omega_{R^e_{k,b}}/R^e_{k,b,+}\omega_{R^e_{k,b}}$ are
linearly independent: a nonbasic exponent is exactly an
interior exponent plus a nonzero semigroup exponent, and
distinct exponent monomials are independent. Hence these
classes form a basis and the asserted generators are minimal
even among arbitrary polynomial generators. $\square$

**Theorem 42.3 (All canonical degrees and their edge-conditioned counts).**
For $1\le j\le k-1$ put

$$
\begin{aligned}
T_q(x,y)&=\mathbf1_{x+y\le q},\qquad 0\le x,y\le q,\\
A_{k,j}&=(T_{2j-2}^{2k})_{j-1,j-1},\\
\mu^e_{k,b,j}&=A_{k,j}^{b}-(A_{k,j}-1)^b.
\end{aligned}
\tag{42.5}
$$

The canonical module has exactly $\mu^e_{k,b,j}$ minimal
generators in degree $2j+1$ and no generators in other degrees.
In particular

$$
\operatorname{type}R^e_{k,b}
=\sum_{j=1}^{k-1}\bigl(A_{k,j}^{b}-(A_{k,j}-1)^b\bigr).
\tag{42.6}
$$

Proof. Consider a local interior with boundary $(2j+1,j,j)$.
The edge sums are at most $2j$. Summing all cyclic edge
bounds gives $\sum_i c_i\le(2k+1)j$, and

$$
(2k+1)j\le k(2j+1)-1\qquad(j\le k-1).
\tag{42.7}
$$

Thus the strict total inequality is automatic. Subtract one
from each coordinate. The new coordinates are nonnegative,
adjacent sums are at most $2j-2$, and both endpoints are
$j-1$. The shared edge already satisfies this bound with
equality. The other route from $b_0$ to $a$ has exactly $2k$
edges and $2k-1$ private vertices. Expanding its transfer
product counts these labelled coordinate vectors once each,
giving $A_{k,j}$ in (42.5). For $j=1$, $T_0=[1]$, so
$A_{k,1}=1$ with the usual one-state matrix convention.

At this boundary the $b$ local choices are independent and
give exactly one global exponent by (41.2), hence $A_{k,j}^b$
tuples. Exactly one local choice is $\nu_j$. The tuples with
none of these entries number $(A_{k,j}-1)^b$. Theorem 42.2
removes precisely them from the basic set, proving the degree
count. Distinct $j$ have distinct degrees. The minimal number
of canonical generators of a Cohen–Macaulay ring is its type,
giving (42.6). At $b=1$ each difference is one, recovering
the single-cycle type $k-1$. At $k=2$ there is only $j=1$,
so every $b\ge1$ has type one and the global interior is
exactly $(3;\mathbf1_V)+\mathcal S^e_{2,b}$. $\square$

**Proposition 42.4 (The seven-cycle counts and a scoped shared-root comparison).**
For shared-edge seven-cycles,

$$
A_{3,1}=1,\qquad A_{3,2}=45,\qquad
\operatorname{type}R^e_{3,b}=1+45^b-44^b.
\tag{42.8}
$$

For two cycles the degree-three generator is unique and the
degree-five generators number $89$, giving type $90$.
The complete comparison with the one-common-vertex family
of Proposition 35.6 [Supplier41] is

| Number $b$ of labelled seven-cycles | One common vertex | One retained common edge |
| ---: | ---: | ---: |
| 1 | 2 | 2 |
| 2 | 202 | 90 |
| 3 | 30302 | 5942 |

Proof. For $j=2$ the matrix and its successive row products are

$$
T_2=\begin{pmatrix}1&1&1\\1&1&0\\1&0&0\end{pmatrix},
\qquad
\begin{aligned}
e_1^{\mathsf T}T_2^0&=(0,1,0),&
e_1^{\mathsf T}T_2^1&=(1,1,0),\\
e_1^{\mathsf T}T_2^2&=(2,2,1),&
e_1^{\mathsf T}T_2^3&=(5,4,2),\\
e_1^{\mathsf T}T_2^4&=(11,9,5),&
e_1^{\mathsf T}T_2^5&=(25,20,11),\\
e_1^{\mathsf T}T_2^6&=(56,45,25),&
e_1^{\mathsf T}T_2^7&=(126,101,56).
\end{aligned}
\tag{42.9}
$$

Each multiplication replaces $(x,y,z)$ with $(x+y+z,x+y,x)$.
The edge case uses six edges with fixed endpoints, hence the
middle entry $45$ at power six. In the common-root case the
closed walk uses all seven edges, hence the middle entry
$101$ at power seven, exactly the supplier in (35.11)–(35.16).
For two branches the basic degree-five tuples are one pair
$(\nu_2,\nu_2)$ and $44$ choices in each of the two labelled
mixed orders. Thus $45^2-44^2=1+44+44=89$.
For three branches the difference is $45^3-44^3=5941$;
including degree three gives $5942$. The shared-root supplier
gives $1+101^2-100^2=202$ and
$1+101^3-100^3=30302$.

An explicit mixed edge tuple pairs $\nu_2$ with
$p=(5;2,2,1,1,1,1,1)$ on the other cycle. The latter is
$\nu_1+(2;1,1,0,0,0,0,0)$, whose remainder is the sum
of the singleton rows $\{a\}$ and $\{b_0\}$.
It is locally reducible and has boundary $(5,2,2)$.
The global tuple is basic because the branch equal to
$\nu_2$ blocks every positive-common-degree subtraction.
This demonstrates why multiplying local types would fail.

The two columns concern different graphs: their vertex counts
are $6b+1$ and $5b+2$ respectively. The numerical comparison
is therefore scoped to these two constructions. It does not
prove a general monotonicity of type or computational complexity
as separator size changes. Nor does clique gluing alone imply
Theorem 42.2 for arbitrary graphs; its proof uses the specific
local generators and the common rule (42.4). $\square$

[Miyazaki42]: https://arxiv.org/html/2205.01409v1

## 43. Endpoint-resolved canonical layers and the entire quotient in each degree

**Definition 43.1 (The legal, interior and exceptional endpoint sectors).**
For a single labelled cycle with endpoints $0,1$, define

$$
\begin{aligned}
L_k(m,t,u)&=\#\{(m,c)\in\mathcal S_k:c_0=t,\ c_1=u\},\\
I_k(m,t,u)&=\#\{(m,c)\in\mathcal S_k^\circ:c_0=t,\ c_1=u\},\\
B_k(m,t,u)&=L_k(m-3,t-1,u-1),\\
E_k(m,t,u)&=I_k(m,t,u)-B_k(m,t,u).
\end{aligned}
\tag{43.1}
$$

All counts are zero for negative degree or inadmissible endpoint
parameters. For $L_k$ this includes $t<0$, $u<0$, or
$t+u>m$; for $I_k$ it includes $t<1$, $u<1$, or
$t+u>m-1$. In degree zero,
$L_k(0,t,u)=\mathbf1_{(t,u)=(0,0)}$ and $I_k(0,t,u)=0$.
The translated $B_k$ always uses the parameters displayed,
so it is zero when its source degree or endpoints are invalid.
The symbol $E_k(m,t,u)$ is an exceptional interior count,
distinct from the one-argument trace error of Definition 32.1
and the root-resolved two-argument count of Definition 36.1.
Set

$$
\nu=(3;\mathbf1_V),\qquad
C^e_{k,b}=\omega_{R^e_{k,b}}/X^\nu R^e_{k,b}.
\tag{43.2}
$$

**Theorem 43.2 (The three slack groups and exact quotient dimensions).**
For nonnegative integer $m,t,u$,

$$
E_k(m,t,u)=
\begin{cases}
\displaystyle\sum_{\substack{2\le j\le k-1\\j\le t,\ j\le u}}
\binom{t-j+k-1}{k-1}\binom{u-j+k-1}{k-1},
 &m\ge t+u+1,\\[2mm]
0,&m<t+u+1.
\end{cases}
\tag{43.3}
$$

For negative parameters use the zero conventions of Definition
43.1. At $k=2$ the sum is empty and $E_2=0$. For the global
edge family, in every degree $m\ge0$,

$$
\begin{aligned}
\dim_{\mathbb C}(\omega_{R^e_{k,b}})_m
 &=\sum_{\substack{t,u\ge0\\t+u\le m}} I_k(m,t,u)^b,\\
\dim_{\mathbb C}(X^\nu R^e_{k,b})_m
 &=\dim_{\mathbb C}(R^e_{k,b})_{m-3}
 =\sum_{\substack{t,u\ge0\\t+u\le m}} B_k(m,t,u)^b,\\
\dim_{\mathbb C}(C^e_{k,b})_m
 &=\sum_{\substack{t,u\ge0\\t+u\le m}}
 \bigl((B_k(m,t,u)+E_k(m,t,u))^b-B_k(m,t,u)^b\bigr).
\end{aligned}
\tag{43.4}
$$

For two labelled branches each summand in the last line is
$2B_k(m,t,u)E_k(m,t,u)+E_k(m,t,u)^2$.

Proof. The local proof in §42 partitions interiors by deficit.
Those of deficit at least $k-1$ are exactly $\nu_1+\mathcal S_k$.
The other interiors have the unique form

$$
p=\nu_j+s_0,\qquad 2\le j\le k-1,\qquad
s_0\in\mathcal S_k^0:=\{s\in\mathcal S_k:\delta(s)=0\}.
\tag{43.5}
$$

Indeed their deficit is $k-j$, fixing $j$, and subtraction
of $\nu_j$ fixes $s_0$. These are precisely the supplied
free face layers of Miyazaki's Lemma 4.4 and (31.13)–(31.14).
They are used here with both adjacent endpoint occupancies
retained; a count resolved at only one root cannot replace this.

For $s_0=(q,d)\in\mathcal S_k^0$ introduce edge slacks
$\alpha_i=q-d_i-d_{i+1}$. The exact inverse coordinates are

$$
q=\sum_{i=0}^{2k}\alpha_i,\qquad
d_i=B_i(\alpha)=\sum_{r=0}^{k-1}\alpha_{i+1+2r},
\qquad \alpha\in\mathbb N^{2k+1}.
\tag{43.6}
$$

Adjacent alternating index sets cover all indices except $i$,
so $d_i+d_{i+1}=q-\alpha_i$. Each slack occurs in exactly
$k$ of the $d_i$, giving $\sum_i d_i=kq$. Conversely,
summing slacks of a face point gives $\sum_i\alpha_i=q$,
and a solution to the cyclic adjacent-sum equations is unique:
a difference alternates sign and returns with opposite sign
around the odd cycle. This proves the additive bijection
(43.6), including nonnegativity and the degree-zero case.
The slack basis vector at $i$ gives the maximum independent
set $\{i+2,i+4,\ldots,i+2k\}$. Thus the face algebra is
polynomial in these $2k+1$ degree-one modes, as in §31.3.

For the actual endpoints $a=0$, $b_0=1$, the groups are
explicitly

$$
\begin{aligned}
d_0&=\alpha_1+\alpha_3+\cdots+\alpha_{2k-1},\\
d_1&=\alpha_2+\alpha_4+\cdots+\alpha_{2k},\\
q-d_0-d_1&=\alpha_0.
\end{aligned}
\tag{43.7}
$$

They partition the indices into groups of sizes $k,k,1$.
The last coordinate is the slack of the retained shared edge;
this partition follows from the adjacent endpoints, not from
an assumption that two arbitrary vertices have disjoint groups.
In (43.5), prescribed $(m,t,u)$ gives

$$
\begin{aligned}
q&=m-2j-1,& d_0&=t-j,& d_1&=u-j,\\
\alpha_0&=m-t-u-1.
\end{aligned}
\tag{43.8}
$$

The three group sums are nonnegative exactly when
$t\ge j$, $u\ge j$, and $m\ge t+u+1$.
Under those conditions their total is $m-2j-1$, so the
residual degree requirement follows automatically. Stars and
bars on the two groups of size $k$ gives the two binomials
in (43.3); the singleton group has one choice of its fixed
value. Distinct $j$ have distinct deficits, so there is no
overlap. This proves the full exceptional count, including
the absence of any additional degree factor. For $k=2$
the direct translation proof in §42 exhausts all interiors.

A global interior is exactly a compatible tuple of local
interiors, by (41.2)–(41.3). At fixed $(m,t,u)$ their number
is $I_k(m,t,u)^b$. The vector $\nu$ has positive occupancies,
all edge slacks one and all cycle deficits $k-1$, so it is
interior. Multiplication by $X^\nu$ is injective in the domain
$R^e_{k,b}$ and shifts the boundary by $(3,1,1)$. A global
interior belongs to its image exactly when every local
restriction belongs to $\nu_1+\mathcal S_k$: after subtraction,
all boundaries are $(m-3,t-1,u-1)$ and (41.2) gives a global
semigroup point. This proves the first two counts in (43.4).
Subtracting monomial bases proves the quotient count. No
splitting of modules is assumed. The two-branch cross terms
count one ordinary and one exceptional sector, in either
labelled order, at the same endpoints. $\square$

**Proposition 43.3 (The full degree-five endpoint table for two seven-cycles).**
For $k=3$, $b=2$, $m=5$, the full table of shared-edge
sectors $t,u\ge0$, $t+u\le5$ is as follows. Every other
integer pair also has all six numerical entries zero.

| $(t,u)$ | $B_3(5,t,u)$ | $E_3(5,t,u)$ | $I_3(5,t,u)$ | $I_3(5,t,u)^2$ | $B_3(5,t,u)^2$ | $I_3(5,t,u)^2-B_3(5,t,u)^2$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| $(0,0)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(0,1)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(0,2)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(0,3)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(0,4)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(0,5)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(1,0)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(1,1)$ | 70 | 0 | 70 | 4900 | 4900 | 0 |
| $(1,2)$ | 56 | 0 | 56 | 3136 | 3136 | 0 |
| $(1,3)$ | 31 | 0 | 31 | 961 | 961 | 0 |
| $(1,4)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(2,0)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(2,1)$ | 56 | 0 | 56 | 3136 | 3136 | 0 |
| $(2,2)$ | 44 | 1 | 45 | 2025 | 1936 | 89 |
| $(2,3)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(3,0)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(3,1)$ | 31 | 0 | 31 | 961 | 961 | 0 |
| $(3,2)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(4,0)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(4,1)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| $(5,0)$ | 0 | 0 | 0 | 0 | 0 | 0 |
| Total | 288 | 1 | 289 | 15119 | 15030 | 89 |

In particular the entire degree-five quotient has dimension
$89$. Here it also equals the number of degree-five basic
generators, whereas quotient dimensions in higher degrees
are not in general new generator counts.

Proof. Positive endpoints and the strict shared-edge inequality
give $t,u\ge1$, $t+u\le4$. These are exactly the six
nonzero rows of the table. Formula (43.3) has only $j=2$ and reduces to

$$
E_3(m,t,u)=\binom{t}{2}\binom{u}{2}
\quad(t,u\ge2,\ m\ge t+u+1),
\tag{43.9}
$$

and zero otherwise. At $m=5$ only $(2,2)$ qualifies, giving
one. For a finite recurrence deriving every ordinary entry,
fix degree $q$ and endpoints $r,s$. If $r,s\ge0$ and
$r+s\le q$, start a path count at vertex $1$ by
$H_0(s,r+s)=1$, all other entries zero. For each of the
$2k-1$ private vertices use

$$
H_{h+1}(w,z+w)=\sum_{\substack{v\ge0\\v+w\le q}}H_h(v,z),
\qquad 0\le w\le q.
\tag{43.10}
$$

The state records the last coordinate and the total occupancy
so far, including both endpoints from the start. Close the
last edge back to vertex $0$ and enforce the total bound:

$$
L_k(q,r,s)=
\sum_{\substack{v+r\le q\\z\le kq}}H_{2k-1}(v,z).
\tag{43.11}
$$

Every labelled coordinate vector determines a unique state
sequence, and conversely each counted sequence specifies
exactly such a vector. This proves the recurrence rather than
assuming that local edge counts enforce the global bound.
At $q=0$ it returns just the zero vector when $r=s=0$.

For the entries needed here there is also a direct transfer
evaluation. The endpoint count ignoring only the total bound
is $(T_2^6)_{r,s}$, provided $r+s\le2$. Direct multiplication
gives

$$
T_2^6=
\begin{pmatrix}
70&56&31\\56&45&25\\31&25&14
\end{pmatrix}.
\tag{43.12}
$$

At degree two, a locally edge-feasible seven-cycle vector
violating the total bound has sum at least seven. Summing
edge bounds gives sum at most seven. Equality forces every
edge sum to be two; oddness then forces every coordinate
to be one. Hence the sole excluded vector has endpoints
$(r,s)=(1,1)$. Removing it gives the complete endpoint
array, with inadmissible pairs assigned zero,

$$
\bigl(L_3(2,r,s)\bigr)_{r,s=0}^{2}
=\begin{pmatrix}70&56&31\\56&44&0\\31&0&0\end{pmatrix}.
\tag{43.13}
$$

Substitute $(q,r,s)=(2,t-1,u-1)$ for the $B$ column;
(43.9) supplies $E$, so $I=B+E$. Squaring and summing at
each common endpoint pair gives

$$
\begin{aligned}
\sum I^2&=70^2+2\cdot56^2+2\cdot31^2+45^2=15119,\\
\sum B^2&=70^2+2\cdot56^2+2\cdot31^2+44^2=15030,\\
\sum(I^2-B^2)&=2\cdot44\cdot1+1^2=89.
\end{aligned}
\tag{43.14}
$$

The sums of the local columns are $288,1,289$; squaring
those sums would discard endpoint compatibility and does
not give the global columns. Formula (43.3) gives no quotient
in degrees below five. Thus all surviving degree-five classes
are minimal, accounting for the $89$ generators of (42.8).
For $k=3$ there are no basic generators beyond degree five
by Theorem 42.3, but the full quotient has higher pieces.
For example the six nonzero ordinary entries in degree six,
in the order $(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)$ up to
endpoint reversal, are respectively $246,216,160,85,189,138$
by (43.10)–(43.11). The exceptional entries occur at
$(2,2),(2,3),(3,2)$ with values $1,3,3$. Consequently

$$
\dim(C^e_{3,2})_6
=(2\cdot189+1)+2(2\cdot138\cdot3+9)=2053.
\tag{43.15}
$$

These are degree-one multiples and their linear combinations
in the quotient, not $2053$ additional canonical generators.
$\square$

## 44. The complete terminal module and the limits of the separator correspondence

**Definition 44.1 (The actual edge-family mode presentation).**
Let $\mathcal B^e_{k,b}=\operatorname{Ind}(G^e_{k,b})$ and use
one variable for every global independent set, including the
empty set. Put

$$
\begin{aligned}
S^e_{k,b}&=\mathbb C[z_I:I\in\mathcal B^e_{k,b}],&
z_I&\longmapsto X^{\gamma_I},&\gamma_I&=(1,\mathbf1_I),\\
D^e_{k,b}&=|\mathcal B^e_{k,b}|,&
\Sigma^e_{k,b}&=\sum_{I\in\mathcal B^e_{k,b}}\gamma_I.
\end{aligned}
\tag{44.1}
$$

The map onto $R^e_{k,b}$ is surjective by Theorem 41.2;
its kernel is the toric ideal of these actual modes.
Ordinary shifts mean $S(-h)_m=S_{m-h}$, with the analogous
convention for full exponent degrees. Write $\mathcal F_i$
for free-resolution modules and $F_n$ for Fibonacci numbers,
where $F_0=0$, $F_1=1$ and $F_{n+2}=F_{n+1}+F_n$.
Let $\mathcal G^e_{k,b,j}$ be the complete set of basic tuples
at boundary $(2j+1,j,j)$ described in Theorem 42.2.

**Theorem 44.2 (Every last shift and multiplicity in the edge presentation).**
For $k\ge2$, $b\ge1$ one has

$$
\begin{aligned}
D^e_{k,b}&=F_{2k+1}^{b}+2F_{2k}^{b},\\
d^e_{k,b}:=\dim R^e_{k,b}&=3+b(2k-1),\\
c^e_{k,b}:=\operatorname{pd}_{S^e_{k,b}}R^e_{k,b}
 &=D^e_{k,b}-d^e_{k,b}.
\end{aligned}
\tag{44.2}
$$

The entire final module of a minimal ordinarily graded free
resolution is

$$
\mathcal F_{c^e_{k,b}}
=\bigoplus_{j=1}^{k-1}
 S^e_{k,b}\bigl(-(D^e_{k,b}-2j-1)\bigr)^{\mu^e_{k,b,j}}.
\tag{44.3}
$$

In the full exponent grading it is

$$
\mathcal F_{c^e_{k,b}}
=\bigoplus_{j=1}^{k-1}\ \bigoplus_{p\in\mathcal G^e_{k,b,j}}
 S^e_{k,b}\bigl(-(\Sigma^e_{k,b}-p)\bigr).
\tag{44.4}
$$

Proof. A path on $r$ vertices has $F_{r+2}$ independent sets.
For $r=0,1$ its counts are one and two; splitting according
to the first vertex's absence or presence gives the Fibonacci
recurrence for $r\ge2$. Classify a global mode by the shared
edge pattern. For $00$, each branch leaves the path on its
$2k-1$ private vertices, with $F_{2k+1}$ choices. For $10$,
the neighbor of $a$ among the private vertices is forced absent,
leaving a path on $2k-2$ vertices with $F_{2k}$ choices.
For $01$ the other private endpoint is forced absent, giving
the same count. The two occupied-endpoint cases are distinct,
and $11$ is forbidden. Independent private choices therefore
give exactly $F_{2k+1}^b+2F_{2k}^b$ modes. The empty global
set occurs in the $00$ case and still contributes a degree-one
variable. The dimension is the full lattice rank proved in
Theorem 41.2.

The polynomial ring has dimension and depth $D^e_{k,b}$ at
its homogeneous maximal ideal $\mathfrak n=(z_I)_I$.
The nonzero finite quotient $R^e_{k,b}$ is Cohen–Macaulay
of depth $d^e_{k,b}$. Hilbert syzygy gives finite projective
dimension over this polynomial ring. After localization at
$\mathfrak n$, the Auslander–Buchsbaum formula applies:
for a nonzero finite module of finite projective dimension
over a Noetherian local ring, ring depth equals projective
dimension plus module depth. This is Stacks, Proposition
10.111.1, tag 090U [AB44]. A minimal graded resolution
localizes to a minimal local resolution, so this formula
gives $c^e_{k,b}$ in (44.2).

Minimal free resolutions may be chosen in the full exponent
grading: homogeneous generator selection applies because
the grading has a positive ordinary coarsening and finite
degree pieces. Every differential has entries in
$\mathfrak n$. The polynomial canonical module is
$\omega_{S^e_{k,b}}=S^e_{k,b}(-\Sigma^e_{k,b})$, since
the top exterior product of its variable differentials has
degree the sum of all variable degrees. Barile–Bruns,
Theorem 4.5(a) [BB41], applies to this regular graded-local
ring and its Cohen–Macaulay residue ring $R^e_{k,b}$.
With $c=c^e_{k,b}$ and $\Sigma=\Sigma^e_{k,b}$, it gives

$$
\operatorname{Ext}^{c}_{S^e_{k,b}}
(R^e_{k,b},S^e_{k,b}(-\Sigma))\simeq\omega_{R^e_{k,b}},
\qquad
\operatorname{Ext}^{i}_{S^e_{k,b}}
(R^e_{k,b},S^e_{k,b}(-\Sigma))=0\quad(i\ne c).
\tag{44.5}
$$

The canonical grading here is the same full-lattice interior
grading supplied by their Theorem 5.1 in Theorem 41.2.
This is the classical canonical-Ext interface used in
§33 and Theorem 38.2 [Supplier41], now applied to the
different global mode set (44.1).

Dualize a minimal resolution into $S^e_{k,b}(-\Sigma)$.
Equation (44.5) makes the reversed dual a resolution of
the canonical module. Its initial module is
$\operatorname{Hom}(\mathcal F_c,S^e_{k,b}(-\Sigma))$.
The incoming dual differential still has all entries in
$\mathfrak n$. Reducing the cokernel modulo $\mathfrak n$
therefore makes this map zero and retains exactly one basis
vector per dual summand. If a summand of $\mathcal F_c$ is
$S^e_{k,b}(-\Theta)$, its dual generator has degree
$\Sigma-\Theta$. By Theorem 42.2 the full canonical minimal
generator degrees are exactly the exponents $p$ in the
sets $\mathcal G^e_{k,b,j}$, each once. Solving
$\Sigma-\Theta=p$ gives every summand of (44.4), with
no cancellations or missing summands. Ordinary degree
coarsening subtracts $2j+1$ from $D^e_{k,b}$ and counts
those exponents by $\mu^e_{k,b,j}$, proving (44.3).
This determines the final module from the actual canonical
module, not from an alternating Hilbert numerator alone.
$\square$

**Proposition 44.3 (The two-seven-cycle terminal module and its full degree sum).**
For the retained-edge graph with $k=3$, $b=2$,

$$
\begin{aligned}
|V|&=12,&D^e_{3,2}&=13^2+2\cdot8^2=297,\\
d^e_{3,2}&=13,&c^e_{3,2}&=297-13=284,\\
\mathcal F_{284}
&=S^e_{3,2}(-294)\oplus S^e_{3,2}(-292)^{89}.
\end{aligned}
\tag{44.6}
$$

The shared coordinates of $\Sigma^e_{3,2}$ are $64,64$;
in private position order $2,3,4,5,6$ on either cycle,
its coordinates are $(89,79,84,79,89)$. Together with
ordinary coordinate $297$, these specify the vector used
in (44.4) for every full shift.

Proof. The Fibonacci values are $F_7=13$, $F_6=8$.
Apply (44.2) and the multiplicities $1,89$ of (42.8).
The ordinary shift subtraction gives $297-3=294$ and
$297-5=292$, and the final rank is $1+89=90$.

For clarity the variable-degree sum can also be evaluated
without an implicit symmetry assumption. Put $A=F_{2k+1}$,
$B=F_{2k}$. Each shared endpoint occurs in exactly $B^b$
modes, those of its occupied shared-edge pattern. At private
position $i\in\{2,\ldots,2k\}$ on a chosen branch,
the contributions from $00,10,01$ respectively are

$$
\begin{aligned}
A^{b-1}F_{i-1}F_{2k-i+1},\qquad
B^{b-1}\begin{cases}F_{i-1}F_{2k-i},&i<2k,\\0,&i=2k,\end{cases}
\qquad
B^{b-1}\begin{cases}0,&i=2,\\F_{i-2}F_{2k-i+1},&i>2.\end{cases}
\end{aligned}
\tag{44.7}
$$

Indeed, requiring a vertex in a path forces its neighbors
absent, leaving two independent subpaths. The Fibonacci
factors count them, and the other $b-1$ branches contribute
the displayed power. In the $10$ case position $2k$ is
forbidden by the occupied endpoint $a$; in the $01$ case
position $2$ is forbidden by $b_0$. The endpoint cases use
$F_1=1$ for an empty remaining side. Substitution gives
$64$ at each shared vertex and the stated five private
coordinates. Each basic exponent in Theorem 42.2 can
therefore be subtracted from this explicitly known $\Sigma$
to give its full terminal degree. $\square$

**Proposition 44.4 (The exact comparison and the information that remains absent).**
The common-edge correspondence identifies one legal separator
histogram both for assembling rows and for synchronizing a
removable row. It does not identify a prescribed row history,
does not give a general clique-sum canonical classification,
and does not give physical or analytic realizations of the
terminal module.

Proof. Assembly uses (41.4), which the clique $K_2$ fixes from
the endpoint totals. Interior descent additionally uses the
local degrees $(2j+1;j,j)$, the invariant residual $00$
count in (42.3), and the common choice (42.4). Theorem 39.2
proves a universal first-moment statement only for existence
over all extensions; it contains no assertion about arbitrary
canonical modules. Likewise (40.3) recovers complete separator
laws by linear statistics, while (40.4) optimizes disagreement
of two fixed laws. These conclusions have different domains
and do not replace one another.

The actual shared-root comparator is Theorems 35.4–35.5,
Proposition 35.6 and Theorem 38.2 with Proposition 38.3
[Supplier41]. Its two-seven-cycle graph has thirteen vertices,
ring dimension fourteen, $505=21^2+8^2$ mode variables,
projective dimension $491$, and complete last module

$$
\mathcal F^{\mathrm{root}}_{491}
=S^{\mathrm{root}}_{3,2}(-502)
 \oplus S^{\mathrm{root}}_{3,2}(-500)^{201}.
\tag{44.8}
$$

The edge graph instead has twelve vertices and (44.6).
These presentations have different polynomial rings and
different shared-boundary conditions. Their types $202$
and $90$ count summands in the final free modules; they
are not dimensions of a common physical state space,
zero-mode counts or Atiyah–Singer indices. A terminal
module and its homological position do not specify all
intermediate Betti numbers or the $284$ or $491$
differential matrices. Theorems 44.2–44.3 specify every
final shift and multiplicity, not those middle matrices.

Even within the edge graph, put zero on both shared vertices
and on every branch except one. The two arrays of degree
two with private rows $\{\{2\},\{4\}\}$ and
$\{\varnothing,\{2,4\}\}$ are legal for every $k\ge2$.
They have the same occupancy vector and the same shared
histogram, yet different unordered row correlations.
Thus even successful common-source realization does not
recover a specified initial array, and it also cannot
recover its order. An interpretation in terms of native
operations would require a map preserving preparation,
allowed transitions and the stated observables. An analytic
index interpretation would require a specified graded
operator, its domain and an appropriate ellipticity or
kernel comparison. None of those structures is part of
Definitions 41.1 or 44.1. The distinct smooth operators
of §§30 and 34 [Supplier41] are not transported to this
graph by agreement of numerical values.

The attribution of the mathematical inputs is correspondingly
specific. Theorem 28.2 supplies integral common-copy cycle
realization; §§31–32 supply the slack/deficit coordinates
and the degree-three translated canonical layers, with
Miyazaki's §4 as their primary classification source.
§§35–38 supply the actual common-root construction and
comparison, including the distinction between canonical
generator counts and entire quotient pieces in §36.
Matsuda–Ohsugi–Shibata's Proposition 1.3 supplies the
clique-sum toric-fiber and normality precedent for the
retained $K_2$. Hochster, Danilov and Stanley supply the
normal-monoid canonical framework in the precise graded
form of Barile–Bruns, Theorems 5.1 and 4.5; Stacks 090U
supplies the stated Auslander–Buchsbaum hypotheses.
Rota's inversion and the finite maximal-coupling method
are intermediate tools in the separator observation, with
the warehouse's legal-pattern moment coordinates in
*Hidden Relations*, C-28.3 and C-28.5 [Hidden40].

The derivation particular to this application is the link
between the attainable-pattern intersection, the explicit
missing separator coordinates, the uniform edge-compatible
descent, the resulting complete basic-tuple counts, and
the endpoint-resolved quotient and terminal modules.
It attributes the classical tools to their sources and
makes no claim of worldwide priority or of a general
canonical theorem for arbitrary clique sums. Every
unbounded-parameter conclusion above follows from its
given proof; finite table entries are evaluations of
the displayed formulas, not a substitute for those proofs.
$\square$

[AB44]: https://stacks.math.columbia.edu/tag/090U

## 追加锚（本行以下为增补区）
