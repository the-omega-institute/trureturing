# Two-cut rectangle multiplicity is paid by actual covering excess

Fix one pair of primes. The complementary rectangles forced by all
globally admissible two-cut targets can be charged simultaneously to
the actual original covering excess. More precisely, if a point lies
in $m$ such rectangles, at least $m+1$ distinct original labels contain
that point. The coefficient is one, independently of all prime heights.

The new joint step interpolates between private witnesses for adjacent
targets in their exponent ordering. Coverage of the same actual fibre
then supplies a label in a prescribed half-open exponent interval.
Those intervals separate the labels and make the charge additive.

This is an ordinary finite CRT proof. It requires global two-cut
admissibility for every selected target, one fixed prime pair, and
private witnesses in the point's own covered fibres. It needs neither
whole coverage nor irredundancy of every original. No Lean verification,
uniform positive query debit, or resolution of Erdős #7 is claimed.

For several prime pairs, Section 7 gives a different joint restriction:
when each prime has one common cut height, the graph of simultaneously
present rectangles must be bipartite. Every finite bipartite pattern can
occur with original load two. The resulting cut inequalities restrict
joint rectangle masses without supplying a uniform all-pair excess
coefficient.

## 1. Original labels and the rectangles being counted

Let

$$
C_i=[a_i]_{d_i},\qquad L(x)=\sum_i\mathbf1_{C_i}(x)
$$

be one finite family of literal original classes with distinct odd
moduli $d_i>1$, on $\Omega=\mathbb Z/N\mathbb Z$, where every $d_i$
divides $N$. Fix distinct primes $p,q\mid N$. Write
$H_p=v_p(N)$ and $H_q=v_q(N)$, and use the literal prime-power CRT
coordinates on $\Omega$ throughout.

Choose a subset $\mathcal T$ of the original labels. For $t\in\mathcal T$
put

$$
\alpha_t=v_p(d_t)\ge1,\qquad \beta_t=v_q(d_t)\ge1,
$$

and assume the **global numerical condition**

$$
\forall i\ne t:\qquad
v_p(d_i)<\alpha_t\quad\text{or}\quad v_q(d_i)<\beta_t.
\tag{RC1}
$$

This is exactly the hitting-set condition for the cut $\{p,q\}$ and
its canonical boundary period

$$
b_t=p^{\alpha_t-1}q^{\beta_t-1}
\prod_{r\mid N,\ r\notin\{p,q\}}r^{v_r(N)}.
\tag{RC2}
$$

Indeed all other prime-power layers are already supplied by $b_t$,
so $d_t\nmid\operatorname{lcm}(b_t,d_i)$ is RC1. It also implies
that $d_t$ is divisibility-maximal among the original moduli. The
condition is imposed on every other original, including originals
inactive on a particular fibre. A phase-dependent safe-fibre condition
alone is not being substituted for it.

Let

$$
\Pi_t=C_t\setminus\bigcup_{i\ne t}C_i
$$

be the actual private region of target $t$. For $x\in\Omega$, let
$F_t(x)$ be its literal $b_t$-fibre. This fixes the first
$\alpha_t-1$ digits at $p$, the first $\beta_t-1$ digits at $q$,
and every full coordinate outside $p,q$.

Let $E_t\subseteq\mathbb Z/b_t\mathbb Z$ consist of those fibres
which are completely covered by the original family and meet $\Pi_t$.
Define

$$
R_t=\left\{x\in\Omega:
\begin{array}{l}
x\bmod b_t\in E_t,\\
x\not\equiv a_t\pmod{p^{\alpha_t}},\\
x\not\equiv a_t\pmod{q^{\beta_t}}
\end{array}\right\}.
\tag{RC3}
$$

On these fibres the previous digits agree with the target, because
the fibre contains a private point of it. Thus RC3 is precisely the
complementary first-digit rectangle of [report 839](839-two-cut-private-fibres-force-query-weighted-overlap-rectangles.md),
with all higher digits retained. In particular $R_t\cap C_t$ is
empty. No original phases are changed, and all private witnesses below
are chosen inside these same actual fibres.

## 2. Pointwise multiplicity bound

For every $x\in\Omega$,

$$
\boxed{\sum_{t\in\mathcal T}\mathbf1_{R_t}(x)
\le (L(x)-1)_+.}
\tag{RC4}
$$

**Exponent ordering.** For two different selected targets, applying
RC1 in both directions shows that neither exponent pair dominates the
other. Their $p$-exponents cannot be equal, nor can their $q$-exponents.
Consequently any selected subfamily has a unique ordering with

$$
\alpha_1<\alpha_2<\cdots<\alpha_m,
\qquad
\beta_1>\beta_2>\cdots>\beta_m.
\tag{RC5}
$$

Fix $x$ and list exactly those $m$ targets for which $x\in R_t$ in
this order. If $m=0$, RC4 is immediate. Assume $m\ge1$. For each
listed target choose

$$
y_j\in\Pi_{t_j}\cap F_{t_j}(x).
\tag{RC6}
$$

The $p$-coordinate of $y_j$ first differs from that of $x$ at digit
$\alpha_j$, and its $q$-coordinate first differs at digit $\beta_j$.
All coordinates outside $p,q$ equal those of $x$.

**Two endpoint labels.** The axis-only classification and forced-strip
result of report 839, Sections 1–2, apply separately to each listed
fibre. At the first target they supply an original containing $x$
whose exponents satisfy

$$
v_p(d_{s_-})<\alpha_1,\qquad v_q(d_{s_-})\ge\beta_1.
\tag{RC7}
$$

At the last target they supply an original containing $x$ with

$$
v_p(d_{s_+})\ge\alpha_m,\qquad v_q(d_{s_+})<\beta_m.
\tag{RC8}
$$

These are actual supplier labels. For example, RC7 can also be seen
directly by replacing only the $p$-coordinate of $x$ with that of
$y_1$. The resulting point lies in the covered first fibre and misses
its target at $q$. Its covering label cannot cover $y_1$, so it must
distinguish their $q$-coordinates, giving $v_q(d_{s_-})\ge\beta_1$.
RC1 gives the $p$-bound. That bound means the label also contains $x$.
The opposite coordinate replacement gives RC8.

**One middle label per adjacent pair.** For $1\le j<m$, use CRT to
form the actual point

$$
w_j^{(p)}=y_{j+1}^{(p)},\qquad
w_j^{(q)}=y_j^{(q)},\qquad
w_j^{(r)}=x^{(r)}\quad(r\ne p,q).
\tag{RC9}
$$

It lies in both $F_{t_j}(x)$ and $F_{t_{j+1}}(x)$: the larger
$p$-prefix comes from $y_{j+1}$ and the larger $q$-prefix from $y_j$.
It misses $C_{t_j}$ at digit $\alpha_j$, since its $p$-coordinate
there agrees with $x$. It misses $C_{t_{j+1}}$ at digit $\beta_{j+1}$,
since its $q$-coordinate there agrees with $x$.

The first of these fibres is covered, so choose an original label
$s_j$ containing $w_j$. It is neither $t_j$ nor $t_{j+1}$. Privacy
therefore says it contains neither $y_j$ nor $y_{j+1}$.

The points $w_j,y_j$ differ only at $p$, with first difference at
digit $\alpha_j$. A congruence class containing one and missing the
other must have $p$-exponent at least $\alpha_j$. Similarly
$w_j,y_{j+1}$ differ only at $q$, first at $\beta_{j+1}$. Hence

$$
v_p(d_{s_j})\ge\alpha_j,\qquad
v_q(d_{s_j})\ge\beta_{j+1}.
$$

Apply RC1 first to target $t_j$ and then to $t_{j+1}$. This gives
the matching strict upper bounds:

$$
\boxed{
\alpha_j\le v_p(d_{s_j})<\alpha_{j+1},\qquad
\beta_{j+1}\le v_q(d_{s_j})<\beta_j.}
\tag{RC10}
$$

The $p$-coordinate of $w_j$ agrees with $x$ through
$\alpha_{j+1}-1$, and its $q$-coordinate agrees through
$\beta_j-1$. All other coordinates already equal those of $x$.
RC10 therefore implies that this **same original** $s_j$ contains $x$.

The $p$-exponents of $s_-,s_1,\ldots,s_{m-1},s_+$ belong to the
disjoint intervals

$$
[0,\alpha_1),\ [\alpha_1,\alpha_2),\ \ldots,\quad
[\alpha_{m-1},\alpha_m),\ [\alpha_m,\infty).
\tag{RC11}
$$

Thus these are $m+1$ distinct original labels, all containing $x$.
It follows that $L(x)\ge m+1$, proving RC4. $\square$

Only coverage of the displayed actual fibres was used. The proof
does not infer a private witness from an owner partition, move a
witness to an unrelated cofactor, or resample any original residue.

## 3. One shared weighted and Haar budget

For any one nonnegative measure $\xi$ on $\Omega$ and any actual
nonnegative payoff $h$, RC4 gives

$$
\boxed{
\sum_{t\in\mathcal T}\int h\mathbf1_{R_t}\,d\xi
\le\int h(L-1)_+\,d\xi.}
\tag{RC12}
$$

In particular $h$ may be a query hinge with its actual simultaneous
phases. No product assumption, independence, coarse measurability, or
change of source law is needed. Different targets can use different
boundary heights; the budget still has no height multiplicity factor.

For full-period Haar $\mu$, put

$$
e_t=\mu\{x:x\bmod b_t\in E_t\}=\frac{|E_t|}{b_t},\qquad
c_{p,q}=\frac{(p-1)(q-1)}{pq}.
$$

Every relevant fibre has the same complementary-first-digit fraction,
so $\mu(R_t)=c_{p,q}e_t$. Consequently

$$
\boxed{
c_{p,q}\sum_{t\in\mathcal T}e_t
\le\int(L-1)_+\,d\mu
=\sum_i\frac1{d_i}-\mu\!\left(\bigcup_iC_i\right).}
\tag{RC13}
$$

Under the additional hypothesis of whole coverage, the last expression
is $\sum_i1/d_i-1$. Every selected essential target then has
$E_t\ne\varnothing$, and thus contributes at least $c_{p,q}/b_t$
to the left side. These positive quantities can shrink with the
boundary periods; RC13 gives no uniform lower bound for their sum.

The scalar floor from private mass is contained in this statement.
On an active fibre the whole selected target has relative Haar mass
$1/(pq)$, so

$$
\mu(\Pi_t\cap\{x:x\bmod b_t\in E_t\})\le e_t/(pq).
$$

Thus RC13 pays at least $(p-1)(q-1)$ times the sum of these actual
private masses. It retains the potentially larger **support of private
fibres**, rather than reducing that support to one private point per
target. The substantive addition is that all these amplifications can
share one excess account for the fixed pair $p,q$.

RC12 is an excess budget, not an equality with a deleted union. A
consumer needing $\int h\mathbf1_W\,d\xi$ still has to identify
the relevant original stage or supplier bucket and control its actual
multiplicity. One cannot add fresh copies of RC12 for different prime
pairs without a further common accounting argument. Nor does existence
of a private fibre force positive $h$-weight or surviving-source mass
on its complementary rectangle.

## 4. The coefficient is sharp at arbitrary multiplicity

Here is one symbolic family showing that RC4 can be an equality with
arbitrarily large $m$. Fix distinct odd primes $p,q,\ell$ and an
integer $m\ge1$. For $t=1,\ldots,m$, take a target of modulus
$p^tq^{m+1-t}$ with CRT phases

$$
x_p\equiv p^{t-1}\pmod{p^t},\qquad
x_q\equiv q^{m-t}\pmod{q^{m+1-t}}.
\tag{RC14}
$$

For each $j=0,\ldots,m$, create a zero supplier with exponent pair
$(j,m-j)$ and phases $(0,0)$. At this same exponent pair also create

- for $j\ge1$, each $p$-branch phase $(c p^{j-1},0)$,
  $c=2,\ldots,p-1$;
- for $j\le m-1$, each $q$-branch phase $(0,c q^{m-j-1})$,
  $c=2,\ldots,q-1$.

Give every supplier its own distinct positive tag exponent $k$ and
the tag phase $0\bmod\ell^k$. A zero exponent at $p$ or $q$ means
that coordinate is unrestricted. All phases define literal CRT
classes. The resulting numerical moduli are odd and distinct:
supplier tags are distinct, the targets have no $\ell$ factor, and
the target exponent pairs differ.

All supplier $p,q$ exponent sums equal $m$, whereas each target sum
is $m+1$. The other targets form a strict exponent antichain. Thus RC1
holds for every target. Let the full tag exponent be $K$, so a common
carrier is $p^m q^m\ell^K$.

In the target $t$'s boundary fibre with all fixed coordinates zero,
the suppliers at $j=t$ cover every next $p$-digit except $1$; those
at $j=t-1$ cover every next $q$-digit except $1$. The target covers
the remaining $1\times1$ first-digit cell. That entire fibre is covered.

The point with full coordinates
$(p^{t-1},q^{m-t},0)$ is private to target $t$. A zero supplier could
contain it only if simultaneously $j\le t-1$ and $j\ge t$, which
is impossible. A branch supplier has a first nonzero digit at least
$2$, whereas both of the displayed first nonzero digits are $1$.
Every other target misses at one of its first prescribed digits.

The origin lies in all $m$ complementary rectangles. Exactly the
$m+1$ zero suppliers contain it; no branch supplier or target does.
Therefore

$$
\sum_t\mathbf1_{R_t}(0)=m=L(0)-1.
\tag{RC15}
$$

This also shows why an absolute bound on rectangle multiplicity,
independent of the original overlap, is unavailable even under RC1.
No irredundancy claim is needed or made for the suppliers. The family
is a noncover: the CRT point with full coordinates $(0,1,1)$ misses
every target at $p$ and every supplier at $\ell$. It supplies no odd
distinct whole cover.

The fixed-pair restriction cannot be dropped from this local theorem.
Take disjoint nonempty sets of odd primes $P,Q$, and for every
$(p,q)\in P\times Q$ take a target with phases $1\bmod p,1\bmod q$.
Take one supplier fixing every $P$-coordinate to zero and one fixing
every $Q$-coordinate to zero. For each $p\in P$ and $c=2,\ldots,p-1$,
add a supplier fixing that coordinate to $c$ and all other
$P$-coordinates to zero; do the same for $Q$. Give all suppliers
distinct positive powers of a new odd tag prime, at phase zero. Targets
have no tag factor. Every target has its own globally admissible
two-prime cut. In the fibre with all other coordinates and the tag zero,
its two axis strip families and its $1\times1$ cell cover the fibre,
and that cell is private to it. At the origin all $|P||Q|$ target
rectangles occur, but only the two zero suppliers contain the point:
$L(0)-1=1$. Numerical moduli are odd and distinct. The tag-one point
with all $P,Q$ coordinates zero is uncovered globally. This symbolic
control uses the same local-coverage premises and shows that different
prime pairs require an additional shared account.

## 5. Reuse and remaining quantitative obligation

[Report 839](839-two-cut-private-fibres-force-query-weighted-overlap-rectangles.md)
supplies the one-target axis classification, actual private fibres,
and complementary rectangles. [Report 838](838-weighted-primitive-overlap-on-admissible-prime-boundaries.md)
supplies the global period/hitting-set criterion. These are reused.

The [Lettl–Sun original-label accounts](../../../../../../Library/Arith/lettlsun2008cosets.md)
already contain common-owner budgets OB1–OB4, joint prime-supplier
rectangles, and the omitted-private and overlap terms of complete
shell columns. Their two-prime demand is integrated over actual
private points under the stated global-top-height premises. RC4
instead counts the enlarged complementary rectangles, with each
target's own pair of heights, and obtains distinct additional labels
from the adjacent exponent intervals RC10. It does not remove any
omitted-private term from those older shell identities.

The exact excess identity in RC13 is also already used in
[report 347](../../321-384/347-original-overlap-leakage-gives-a-uniform-reciprocal-gap.md).
The new step is the pointwise map from rectangle multiplicity to that
same actual excess, not the integration identity or a new source law.
This is a repository proof increment, not an exhaustive literature
novelty claim.

A covering contradiction still requires a lower bound for the
same-law rectangle weights that exceeds an applicable upper excess
budget, or a valid conversion to the required prefix/query debit.
Original irredundancy alone supplies neither the covered-fibre premise
nor a uniform positive rectangle weight. Global whole coverage supplies
the first premise for private fibres, but not the remaining quantitative
gap. Targets whose necessary hitting sets use more than two primes,
and combinations of different selected prime pairs, remain outside
RC4's claimed joint budget.

## 6. Fixed exact controls

The [standard-library checker](../../../frontier/moments-survival/two_cut_rectangle_excess.py)
and [exact output](../../../frontier/moments-survival/two_cut_rectangle_excess.json)
use only $m=1,2,3$ and $(p,q,\ell)=(3,5,7)$ in the sharpness family.
They construct literal original CRT residues, check numerical
distinctness and global cut admissibility, verify each target's
specified private point and the global CRT hole, and enumerate only
the zero-tag conditional grids of sizes $15,225,3375$.

For every target, grouping this actual grid by its lower $p,q$ digits
determines which whole boundary fibres are covered and contain a
private point. The checker then derives $R_t$ from those predicates
and checks RC4 pointwise. It does not infer covered/private status
from the predicted sharpness formula. At the origin the checks give
rectangle multiplicity $m$ and original multiplicity $m+1$.

Under `python3 -I -S -B -O`, the fixed run exits zero with 3,723 checks
over 3,615 conditional grid cells. The conditional sums of rectangle
masses equal the actual excess masses, respectively
$8/15$, $64/225$, and $392/3375$. These are finite controls, not an
all-family or all-height proof. No complete original period is
enumerated, and the different-prime-pair control above is symbolic
only. The general argument remains RC5--RC11.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/moments-survival/two_cut_rectangle_excess.py --output /tmp/e7_two_cut_rectangle_excess.json
```

## 7. Which prime-pair rectangles can coexist

The following uses the same original classes and actual private fibres,
but allows different prime pairs for different targets. Every target
still satisfies RC1 for its own pair. For a point $x$, let $I(x)$ be the
set of original labels containing $x$.

If $x\in R_t$, choose an actual private point
$y_t\in\Pi_t\cap F_t(x)$. For every $i\in I(x)$, one has $i\ne t$
because $x\notin C_t$, and privacy implies $y_t\notin C_i$.
The two points agree outside $p_t,q_t$ and first differ at these primes
at the target's cut heights $\alpha_t,\beta_t$. A label containing
$x$ and missing $y_t$ must distinguish at least one of these two
coordinates. RC1 permits at most one. Therefore every actual active
label satisfies the exact constraint

$$
\boxed{
\mathbf1_{\{v_{p_t}(d_i)\ge\alpha_t\}}
+\mathbf1_{\{v_{q_t}(d_i)\ge\beta_t\}}=1
\quad(x\in R_t,\ i\in I(x)).}
\tag{RC16}
$$

This is a restriction on all the active original labels simultaneously.
No witness or original phase is moved to an unrelated fibre.

### 7.1 Common heights give a bipartite graph and one weighted cut budget

Suppose every prime $p$ has one common cut height $h_p$ across the
selected targets. Let $G$ be the graph whose vertices are these primes
and whose edge $t$ joins $p_t,q_t$. There is at most one target per
edge: two originals reaching the same pair of cut heights would violate
each other's RC1. Let $G_x$ consist of those edges with $x\in R_t$.

If $G_x$ is nonempty, the covered-fibre premise ensures $I(x)$ is
nonempty. Choose any $i\in I(x)$ and put
$S_i=\{p:v_p(d_i)\ge h_p\}$. RC16 says every edge of $G_x$ crosses
the cut $(S_i,S_i^c)$. Thus $G_x$ is bipartite; more precisely its
edge incidence vector is dominated by the cut vector of this same
actual original label.

Write $U_R=\bigcup_tR_t$. For nonnegative edge weights $w_t$, define
the finite weighted maximum cut of the fixed candidate graph by

$$
\operatorname{MC}_G(w)
 =\max_{S\subseteq V(G)}
   \sum_{t:\,|\{p_t,q_t\}\cap S|=1}w_t.
$$

The single label just chosen proves the pointwise inequality

$$
\sum_t w_t\mathbf1_{R_t}(x)
 \le\operatorname{MC}_G(w)\mathbf1_{U_R}(x).
\tag{RC17}
$$

Consequently, under any one nonnegative measure $\xi$ and any one
nonnegative payoff $h$ on the original finite carrier,

$$
\sum_t w_t\int h\mathbf1_{R_t}\,d\xi
 \le\operatorname{MC}_G(w)\int h\mathbf1_{U_R}\,d\xi
 \le\operatorname{MC}_G(w)\int h(L-1)_+\,d\xi.
\tag{RC18}
$$

The last inequality uses the one-target overlap result: every rectangle
point lies in at least two original classes. When the maximum cut is
positive, RC18 also lower-bounds the actual weighted union mass by the
weighted sum of rectangle masses divided by that maximum cut. It does
not identify a particular original deletion bucket.

For an odd cycle $Z$ of $G$, take its edge weights to be one and all
other weights zero. Its maximum cut is $|Z|-1$, so

$$
\sum_{t\in Z}\mathbf1_{R_t}\le |Z|-1,
\qquad
\sum_{t\in Z}\int h\mathbf1_{R_t}\,d\xi
 \le(|Z|-1)\int h\mathbf1_{U_R}\,d\xi.
\tag{RC19}
$$

One may choose $i(x)$ by a single fixed original-label order on $U_R$.
If $0<\int h\mathbf1_{U_R}\,d\xi<\infty$, normalize this same
restricted measure. The normalized rectangle-mass vector then lies in the
downward closure of the convex hull of cuts of $G$. This retains a
common-source mixture; it does not combine independently optimized edge
marginals. The maximum-cut coefficient depends on the graph and weights,
so RC18 is consistent with the unbounded all-pair obstruction of
[Report 842](842-cross-pair-haar-rectangle-charges-have-no-uniform-excess-bound.md).

### 7.2 Every finite bipartite pattern occurs with load two

Conversely let $G=(P,Q,E)$ be any finite nonempty simple bipartite
graph. Assign distinct odd primes to its vertices and a further odd
prime $\ell$ to a tag. For every edge $(p,q)$ include one target
of modulus $pq$ with roots $(1,1)$.

For every complete non-1 pattern on $P$, include one supplier fixing
that pattern and tag $0\bmod\ell^j$, of modulus
$\ell^j\prod_{p\in P}p$. Include the analogous suppliers for every
complete non-1 pattern on $Q$. Assign all suppliers different positive
heights $j$, and let $K$ be their maximum. CRT fixes all phases once.

The numerical moduli are odd, distinct and greater than one. Each
supplier omits the opposite side, and every other target omits at least
one endpoint of any chosen edge. Thus every target satisfies RC1 at
height one. At the full origin, including tag zero, precisely the
all-zero $P$ supplier and the all-zero $Q$ supplier occur: $L(0)=2$.

For each edge, its canonical fibre with all other core coordinates zero
and full tag zero is covered. The $p\ne1$ rows have matching
$P$ suppliers, the $q\ne1$ columns have matching $Q$ suppliers,
and the remaining $(1,1)$ cell has its target. This cell is private:
each other target requires another core coordinate equal to one, and
both supplier groups miss it. Hence every selected rectangle contains
this same origin.

Isolated vertices may be omitted or retained in the side products; a
nonempty edge set ensures both sides are nonempty. This proves the
exact local graph classification for a declared target inventory: a
finite simple edge pattern is simultaneously realizable under the
common-height premises if and only if it is bipartite, with the empty
pattern vacuous. It does not enumerate every possible target cut in
the constructed family. Arbitrarily many
bipartite edges are compatible with load two. The full all-core-zero,
tag-one point is a global hole, so this realization proves no
whole-cover statement.

### 7.3 A sharp triangle with literal original classes

Take core primes $(p,q,r)=(3,5,7)$ and tag prime $11$. Include targets

$$
T_{pq}=[1]_{15},\qquad T_{pr}=[1]_{21},\qquad T_{qr}=[0]_{35}.
\tag{RC20}
$$

Add ten suppliers, each with the indicated core residue and tag
$0\bmod11^k$:

| Core condition | Tag heights $k$, in the displayed residue order |
| --- | --- |
| $p=0,2$ | $1,2$ |
| $q=2,3,4$ | $3,4,5$ |
| $r=2,3,4,5,6$ | $6,7,8,9,10$ |

Their moduli are respectively $p11^k,q11^k,r11^k$. All thirteen
original moduli are distinct and odd, and all targets have globally
admissible pairs at common height one. The full period is
$3\cdot5\cdot7\cdot11^{10}$.

With full tag zero, the targets have private points $(1,1,0)$,
$(1,0,1)$ and $(1,0,0)$ respectively. Their corresponding pair fibres
are covered. For $T_{pq}$, fix $r=0$: the $p$ suppliers cover
$p\ne1$; at $p=1$, $T_{pq}$ covers $q=1$, $T_{qr}$ covers $q=0$,
and the $q$ suppliers cover $q\ge2$. The $T_{pr}$ argument is
symmetric. For $T_{qr}$, fix $p=1$: its target covers $(q,r)=(0,0)$,
$T_{pq}$ covers $q=1$, $T_{pr}$ covers $r=1$, and a supplier covers
every case with $q\ge2$ or $r\ge2$. Each displayed private point
misses every other original.

At the full origin the first two rectangles occur and the third does
not. Exactly the $p=0$ supplier and $T_{qr}$ contain it. Thus

$$
\sum_{t\in\{pq,pr,qr\}}\mathbf1_{R_t}(0)=2,
\qquad L(0)-1=1.
\tag{RC21}
$$

The triangle bound is attained, including RC18 for unit triangle
weights and a point mass at the origin. Its coefficient cannot be
replaced by one under these premises. The point
$(p,q,r,\text{tag})=(0,1,0,1)$ is a global hole. This is a symbolic
CRT control, not an additional run of the checker in Section 6.

### 7.4 Unequal heights and the remaining allocation obligation

For arbitrary target heights, RC16 still holds on threshold vertices
$(p,h)$, one edge for each target's two thresholds. An actual active
label assigns the values $\mathbf1_{v_p(d_i)\ge h}$; these values
are monotone in $h$ along each prime. This threshold graph is bipartite
wherever its rectangles coexist. Identifying different thresholds with
one prime vertex is not justified. RC17--RC19 on the original prime
graph require the stated common-height premise.

RC16 also shows why an unrestricted supplier-matching restatement adds
no capacity. For each present target, the union of its two supplier
sides is all of $I(x)$. If either side is allowed, every target is
adjacent to every active label. After reserving one owner label, this
complete target-to-slot graph has rank
$\min(\#\{t:x\in R_t\},L(x)-1)$.
An allocation that adds arithmetic information must retain an actual
direction, consumer bucket, or additional relation forced by whole
coverage. The graph exclusions and their sharpness do not supply the
uniform positive source/query debit still required for Erdős #7.
