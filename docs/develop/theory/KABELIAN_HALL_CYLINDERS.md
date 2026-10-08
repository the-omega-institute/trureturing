# Four-digit continued-fraction cylinder survivors

## 1. Objects and scope

Let $m=(\sqrt{2}-1)/2$, $M=2(\sqrt{2}-1)$, and $H=[m,M]$.
Let $C_4$ be the irrational numbers in $(0,1)$ whose computed simple
continued-fraction digits all belong to $\{1,2,3,4\}$.
For a generalized continued fraction $g$ with head zero and first $n$ digit
pairs $(1,a_i)$, write $T_{g,n}(z)$ for its standard continuant tail action:

$$
T_{g,n}(z)=\frac{p_n+p_{n-1}z}{q_n+q_{n-1}z}.
$$

Only the first $n$ digits of $g$ matter. No condition is imposed on later digits.
The zero-length action is the identity. These cylinders are closed and include
their endpoints; the terminal coordinate belongs to $H$, not to $[0,1]$.

## 2. Survivor characterization

**Theorem 2.1 (four-digit cylinder survivors).** For every real number $x$,
$x\in C_4$ if and only if for every natural number $n$ there exists a generalized
continued fraction $g$ with head zero, with $a_i\in\{1,2,3,4\}$ for each $i<n$,
and with $x\in T_{g,n}(H)$. The choices of $g$ at different levels need not
initially be compatible.

For recognition, induct on the finite prefix length. If the final coordinate is
$z\in(0,1)$, remove the last digit by replacing it with $1/(a+z)$. The induction
identifies the computed stream at the preceding level. Since the reciprocal
has integer part $a$ and fractional part $z$, the next computed digit is forced.
Thus every surviving cylinder identifies the entire computed prefix. Survival
at every level excludes termination and hence excludes rational numbers.
Conversely, shift the computed integer/fraction stream at each level. Its
fractional tail again has all digits in $\{1,2,3,4\}$, is irrational, and lies
in $(0,1)$. The sharp four-digit hull bound places that tail in $H$; the exact
continuant identity then places $x$ in the corresponding cylinder.

## 3. Source and boundary

This is the bounded-digit survivor step in the elementary Hall construction of
M. Hall, Jr., *On the sum and products of continued fractions*, Ann. of Math.
48 (1947), 966–993, DOI 10.2307/1969389. The surrounding application is the
half-line question of J. Peltomäki and M. A. Whiteland, arXiv:1809.09047v2,
after Theorem 3.15. The cylinder characterization alone does not assert a
sum interval or a Lagrange spectrum identity.

## 追加锚（本行以下为增补区）

## 4. All-denominator approximation control

For an irrational real $x$, let $r_n$ be its ordinary reduced continued-fraction
convergents, with positive denominators $d_n$. Define the approximation coefficients

$$
A_q=\frac{1}{q\,|qx-\operatorname{round}(qx)|},\qquad
B_n=\frac{1}{d_n^2|x-r_n|}.
$$

The value at $q=0$ is immaterial to the upper limits.

**Theorem 4.1 (asymptotic Legendre bound).** In the extended nonnegative reals,

$$
\limsup_{q\to\infty} A_q
\le \max\left(2,\limsup_{n\to\infty} B_n\right).
$$

Fix $c>2$ and a finite convergent-index cutoff $N$. Each distance $|x-r_n|$
for $n<N$ is strictly positive. Induction on $N$ chooses a common denominator
threshold beyond which $1/(cq^2)<|x-r_n|$ for all these convergents.

For any integer numerator $p$ with $1/(q|qx-p|)>c$, put $r=p/q$ in reduced
form, with positive denominator $d\le q$. Then

$$
|x-r|<\frac{1}{cq^2}<\frac{1}{2d^2}.
$$

Legendre's strict theorem identifies $r=r_n$. The chosen threshold excludes
all $n<N$, including repetitions of fixed rational approximants by unreduced
fractions. Reduction also gives

$$
\frac{1}{q|qx-p|}=\frac{1}{q^2|x-r|}
\le\frac{1}{d^2|x-r|}=B_n.
$$

If $b>\max(2,\limsup B_n)$, choose a finite real $c$ strictly between these
values. The convergent coefficients eventually lie below $c$. Apply the preceding
construction with that index cutoff and $p=\operatorname{round}(qx)$: either
$A_q\le c$ already, or it is bounded by a later $B_n<c$. Hence eventually
$A_q<b$, proving the bound. This is the upper-bound step in Perron's formula;
it does not assert the reverse bound or the formula itself.

The Legendre input is the classical strict continued-fraction approximation
theorem used in the continued-fraction proof of the Lagrange spectrum identity
in J. Peltomäki and M. A. Whiteland, arXiv:1809.09047v2, Section 2.

**Theorem 4.2 (reverse approximation bound).** For every irrational real $x$,

$$
\limsup_{n\to\infty} B_n\le\limsup_{q\to\infty} A_q.
$$

For each fixed positive denominator $d$, irrationality makes
$\delta_d=|dx-\operatorname{round}(dx)|/d$ strictly positive.
The nearest-integer property gives $|x-r|\ge\delta_d$ for every rational $r$
of reduced denominator $d$. Induction on a denominator bound $D$, taking a
minimum at each step, gives $\epsilon_D>0$ with
$|x-r|\ge\epsilon_D$ whenever the reduced denominator of $r$ is at most $D$.
The convergence $r_n\to x$ therefore forces $d_n\to\infty$.

Rounding improves the numerator at denominator $d_n$, so
$B_n\le A_{d_n}$. Taking upper limits and using denominator escape proves
the inequality, without assuming beforehand that the computed continuant
coordinates are reduced. Together with Theorem 4.1 this gives
$\max(2,\limsup A_q)=\max(2,\limsup B_n)$. Removing the cutoff still requires
the convergent upper limit to be at least $2$.

## 5. Reduced continuants and the exact Perron coefficient

**Theorem 5.1 (reduced Perron coefficient).** Let $x$ be any irrational real.
Let $r_n$ be its reduced convergent, let $f_n$ be the fractional part at step
$n$ of the continued-fraction floor algorithm, and let $a_1,\ldots,a_n$
be its first $n$ positive partial quotients. Then

$$
\frac{1}{\operatorname{den}(r_n)^2|x-r_n|}
= f_n^{-1}+[0;a_n,\ldots,a_1].
$$

For $n=0$ the reversed tail is zero. No boundedness or periodicity assumption
is imposed. The forward term $f_n^{-1}$ is the next complete quotient.

The integral continuant coordinates are constructed by a strong induction
on the positive-digit recurrence, beginning with $(1,0)$ and $(\lfloor x\rfloor,1)$.
The determinant of consecutive continuants is a power of $-1$. If reduction
of the $n$th continuant fraction extracted an integer common factor $d$,
that same factor would divide this determinant. Positivity of the denominator
makes $d$ positive, so $d=1$. Thus the reduced denominator is the original
continuant denominator. The existing exact convergent-error identity and the
reversed-prefix denominator ratio now give the displayed coefficient.
This is the pointwise identity in Section 3 of the half-line proof associated
with Peltomäki–Whiteland, arXiv:1809.09047v2; it alone does not assert the
upper-limit formula or a Sturmian critical-exponent identity.

**Theorem 5.2 (uniform escape above the Legendre cutoff).** For every
irrational real $x$, the upper limit of its reduced convergent coefficients
is at least $11/5$, and hence strictly exceeds $2$.

Suppose instead that all sufficiently late coefficients are below $11/5$.
Their positive tails first force every late digit to be at most $2$.
At a digit $2$, the preceding denominator ratio and the forward fractional
tail are both at least $1/3$: their adjacent digits are at most $2$, and
all other fractional coordinates lie in $[0,1]$. Its coefficient is therefore
at least $8/3$, a contradiction. Thus all sufficiently late digits are $1$.
Iterating $z\mapsto1/(1+z)$ three times bounds both tails below by $3/5$,
so a later coefficient is at least $1+3/5+3/5=11/5$, again a contradiction.
The argument proves a uniform lower bound, without requiring an exact
calculation of the eventually constant expansion or an upper-limit finiteness
assumption. The bound is sufficient here and is not claimed to be sharp.

## 6. Prefix-dependent Hall feedback digits

**Theorem 6.1 (feedback digit construction).** Let $P_0$ be a finite list of
positive integers bounded by $A$. Let $B$ be a natural number and let $T$ assign
a real value to each finite list, with $6<T(P)\le B$ for every $P$.
There are nested prefixes $P_j$, an infinite positive digit sequence $d$,
strictly increasing center positions $c_j$, and Hall summands $x_j,y_j\in C_4$
such that $P_j$ is precisely the initial segment of $d$ of length $|P_j|$,
$P_0$ is the prescribed seed, and

$$
T(P_j)=d_{c_j}+x_j+y_j,\qquad 5\le d_{c_j}\le B.
$$

If $u_{j,i},v_{j,i}$ are the computed digits of $x_j,y_j$, then

$$
P_{j+1}=P_j\,u_{j,j}\cdots u_{j,0}\,d_{c_j}\,
 v_{j,0}\cdots v_{j,j},\qquad c_j=|P_j|+j+1.
$$

All digits of $d$ are at most $\max(A,4,B)$. Every digit after the seed which
is not at a center is at most four. The summands and their digits are allowed
to depend on the entire current prefix.

**Proof.** For each finite list choose a Hall representation of its target.
The summands lie strictly between zero and one, so its integer part is at least
five and at most $B$. Choose their computed digits and recursively append the
reversed left block, this integer, and the forward right block. Induction gives
prefix nesting, positive bounded digits, and growth by $2(j+1)+1$ at stage $j$.
Each coordinate is therefore present by a finite stage; nesting makes its value
independent of every later choice of stage. This diagonal sequence has all the
prescribed prefixes. The centers strictly increase by the growth formula.
Induction classifies every nonseed coordinate in a finite prefix as either an
earlier center or a digit in one of the two Hall blocks. Taking a stage beyond
any specified coordinate proves the asserted bound at every noncentral
position, including joins. This is the discrete construction in Section 5 of
the half-line proof associated with Peltomäki–Whiteland, arXiv:1809.09047v2.
It does not yet assert convergence of samples or a Perron upper-limit identity.

## 7. Two-sided central block estimate

The continuous feedback construction uses the following estimate for its
reversed and forward blocks. Number the positive continued-fraction digits
from zero. Let $\alpha$ be irrational, let $x,y$ be irrational in $(0,1)$,
and let $L\le n$. Assume

$$
a_{n-1-i}(\alpha)=a_i(x),\qquad
 a_{n+1+i}(\alpha)=a_i(y)\quad(0\le i<L).
$$

If $p_n/q_n$ is the convergent preceding digit $a_n(\alpha)$, then

$$
\left|\frac{1}{q_n^2|\alpha-p_n/q_n|}
       -a_n(\alpha)-x-y\right|
 \le\frac{2}{f_{L+1}^2}.
$$

This is the central estimate in the continuous-target construction of the
half-line proof associated with Peltomäki–Whiteland, arXiv:1809.09047v2.
The finite backward tail may reach the initial seed; it need not be an
infinite continued fraction.

**Proof.** Write $r_j=q_{j-1}/q_j$ and let $s_j$ be the fractional
coordinate in the computed integer/fraction stream of $\alpha$.
The positive-digit recurrences give

$$
r_{j+1}=\frac{1}{a_j+r_j},\qquad
 s_j=\frac{1}{a_j+s_{j+1}},\qquad 0\le r_j\le1,
 \quad 0<s_j<1.
$$

For a common prefix with digits $b_i$, its continuant action satisfies
$T_{i+1}(z)=T_i(1/(b_i+z))$. Induction therefore telescopes any
$L$ consecutive reciprocal recurrences into the same action $T_L$.
Apply this first to $r_{n-i}$ and the fractional coordinates of $x$,
then to $s_{n+1+i}$ and those of $y$. The uniform prefix contraction
bounds each difference by $1/f_{L+1}^2$. Perron's exact convergent
identity is $1/(q_n^2|\alpha-p_n/q_n|)=a_n+s_{n+1}+r_n$.
The triangle inequality adds the two errors. Digits outside the two
common blocks impose no further restriction.

## 8. Continuous feedback with all positions controlled

Let $F:\mathbb R\to\mathbb R$ be continuous, and suppose that
$6<F(z)\le B$ for every $z$, where $B$ is a natural number. Let $P_0$
be a finite list of positive integer digits at most $A$. There is an irrational
$\alpha\in(0,1)$ whose computed continued fraction begins with $P_0$, whose
positive digits are at most $\max(A,4,B)$, and for which

$$
\limsup_{q\to\infty}\frac{1}{q\lVert q\alpha\rVert}=F(\alpha).
$$

**Proof.** For a finite list $P$, let $r(P)$ be its finite continued fraction
$[0;P]$, with $r(\varnothing)=0$. Apply the feedback digit construction of
Section 6 to the target $T(P)=F(r(P))$. Its prefixes grow by $2(j+1)+1$
digits at stage $j$, so their lengths tend to infinity. The positive infinite
digit stream has an irrational value $\alpha$ with precisely those computed
digits. Induction on the continuant recurrence identifies $r(P_j)$ with the
convergent of $\alpha$ at index $|P_j|$. Hence $r(P_j)\to\alpha$ and
$T(P_j)\to F(\alpha)$ by continuity.

At center $c_j=|P_j|+j+1$, the reversed left block and the forward right
block match the first $j+1$ digits of the two chosen Hall summands. Section 7
therefore gives

$$
|H_{c_j}(\alpha)-T(P_j)|\le\frac{2}{f_{j+2}^2}\longrightarrow0.
$$

Thus the central coefficients tend to $F(\alpha)$. Every noncentral digit
after the seed is at most four. Perron's exact coefficient is that digit,
plus the next fractional tail in $(0,1)$, plus the preceding denominator
ratio in $[0,1]$. Every such coefficient is strictly below six.
For any $b>F(\alpha)$, choose $J$ so that all central coefficients with
$j\ge J$ are below $b$. A position beyond both the seed and $c_J$ is either
one of those centers or a noncentral position. Strict center growth excludes
all earlier centers. Since $F(\alpha)>6$, every sufficiently late coefficient
is below $b$. This proves the upper-limit bound for all positions, including
joins. The central subsequence proves the reverse bound.

The Legendre comparison identifies this convergent upper limit with the
all-denominator upper limit: its only alternative cutoff is two, strictly
below $F(\alpha)$. The digits retain their global bound and their prescribed
seed. This is the continuous feedback construction in Section 5 of the
half-line proof associated with Peltomäki–Whiteland, arXiv:1809.09047v2.


## 9. Mechanical power endpoint progression

Let $0\le\alpha<1$, let $k\ge1$, and suppose that $e>0$ consecutive
length-$m$ blocks of the lower mechanical word, beginning at $s$, are
pairwise $k$-abelian equivalent. There is an integer $c$ such that, for
every $0\le i\le e$,

$$
\{(s+im)\alpha\}=\{s\alpha\}+i(m\alpha-c),
\qquad e|m\alpha-c|<1.
$$

The final endpoint is included. Count the occurrences of the singleton
word $1$ in each block. The actual position filter identifies this with
the mechanical window count. Equivalence makes that count a single
integer $c$. The telescoping floor formula gives

$$
\lfloor(s+(i+1)m)\alpha\rfloor-\lfloor(s+im)\alpha\rfloor=c.
$$

Induction on the block index gives the floor at every endpoint. Subtracting
those floors gives the affine phase formula. Both the first and last phases
belong to $[0,1)$, so their absolute difference is strictly less than one.
In particular $e\lVert m\alpha\rVert<1$, by the nearest-integer inequality.
This is the no-wrap input in the power geometry of Peltomäki--Whiteland,
arXiv:1809.09047v2, Section 3. It does not identify the $k$-abelian class cuts.


## 10. The actual abelian exponent

For an irrational $\alpha\in(0,1)$ and an integer $m>0$, put
$\delta=|m\alpha-\operatorname{round}(m\alpha)|$. For the fixed
occurrence-based power definition and natural-number supremum,

$$
\operatorname{Ae}_{1,\alpha}(m)=\left\lceil\frac1\delta\right\rceil-1.
$$

The endpoint progression implies $e\delta<1$ for every attainable
positive exponent $e$, so every attainable exponent is at most the
displayed integer $E$. To attain $E$, take $c=\operatorname{round}(m\alpha)$
and $d=m\alpha-c$. The ceiling constraint gives $E|d|<1$. Therefore

$$
\bigl(\max(0,-Ed),\min(1,1-Ed)\bigr)
$$

is a nonempty open interval. Irrational forward-orbit density gives an
actual starting phase $x$ in it. Every $x+id$, $0\le i\le E$, belongs to
$(0,1)$. The floor at the corresponding endpoint is consequently the
initial floor plus $ic$. Each block has exactly $c$ true letters; equal
length then gives equal false counts. The extension-mass identity at
boundary length zero identifies those letter counts with the fixed
singleton occurrence counts. All nonempty test words of length at most
one are singletons, proving actual abelian equivalence of the blocks.
The bound and attained exponent identify the natural-number supremum.

Equivalently, the two abelian class intervals have largest length
$1-\delta$, and the answer is $\lceil(1-\delta)/\delta\rceil$. This is
the $k=1$ power calculation underlying Peltomäki--Whiteland,
arXiv:1809.09047v2, Lemma 3.8. It does not yet identify the critical
exponent upper limit with the Lagrange constant.


## 11. Power attainment inside a rotation-cut interval

Let $\alpha\in(0,1)$ be irrational, let $k\ge1$, and let $m\ge k-1$.
Suppose $0\le a<b\le1$ and no cut $1-\{r\alpha\}$ lies in $(a,b)$,
where $1\le r\le k-1$ or $m-(k-1)\le r\le m$.
Put $c=\operatorname{round}(m\alpha)$ and $d=m\alpha-c$.
For every integer $e\ge1$ such that $(e-1)|d|<b-a$, an actual forward
factor of the lower mechanical word is a $k$-abelian power of period $m$
and exponent $e$.

Indeed, writing $E=e-1$, the open interval

$$
\bigl(\max(a,a-Ed),\min(b,b-Ed)\bigr)
$$

is nonempty. Density supplies a starting phase $x$ there. Each
$x+id$, $0\le i\le E$, belongs to $(a,b)$ and is the actual fractional
part at block start $s+im$: its complementary integer part is the initial
floor plus $ic$. For each relevant offset $r$, the floor increment
$\lfloor x+id+r\alpha\rfloor$ is constant in $i$, because its only
possible change is at the excluded cut $1-\{r\alpha\}$.
The offset $m$ gives equal true-letter counts in the full blocks.
Successive prefix offsets give equal prefixes of length $k-1$, and
successive suffix offsets give equal suffixes of that length. Equal block
length gives equal false counts. The occurrence-based mechanical
classification then gives $k$-abelian equivalence of every pair of blocks.
All chosen phases are interior, so no half-open endpoint identification
is assumed. This is the attainment direction of the partition geometry
in Peltomäki--Whiteland, arXiv:1809.09047v2, Section 3.

## 12. Necessary rotation-class confinement

Let $0\le\alpha<1$, $k\ge1$, $m\ge k-1$, and $e>0$. Suppose the
$e$ consecutive length-$m$ factors at a starting index $s$ are pairwise
$k$-abelian equivalent, in the occurrence-count sense. Then there are
$0\le a<b\le1$ such that all their starting phases belong to $[a,b)$,
and every cut

$$
1-\{r\alpha\},\qquad 0<r\le m,\quad
r\le k-1\ \text{or}\ m-(k-1)\le r,
$$

lies at or outside the interval endpoints: it is at most $a$ or at least $b$.
The endpoints are selected from these cuts together with $0$ and $1$.
Moreover

$$
(e-1)|m\alpha-\operatorname{round}(m\alpha)|<b-a.
$$

Equal boundaries recover the prefix floor increments. For a suffix cut,
subtract the corresponding equal terminal-window increment from the equal
whole-block increment. These tests locate every starting phase between the
same two consecutive finite cuts. The ordinary-coordinate endpoint
progression gives its span; nearest-integer distance can only decrease it.
This is the necessary interval estimate accompanying the sufficient
construction of Section 11, without assuming a partition or an exponent formula.

## 13. Stability of maximal empty intervals

Let $S,T$ be finite subsets of $[0,1]$, both containing $0$ and $1$.
An adjacent interval of $S$ has endpoints $a,b\in S$, $a<b$, and
$S\cap(a,b)=\varnothing$; define adjacent intervals of $T$ in the same way.
Suppose that each point of either set has distance at most $\delta$ from
some point of the other set. Then maximal adjacent intervals $[a,b]$ of
$S$ and $[c,d]$ of $T$ exist, and

$$
\bigl|(b-a)-(d-c)\bigr|\le 2\delta.
$$

The positive adjacent intervals form a nonempty finite family: take $0$
and the least strictly positive point. Choose a member of maximal length.
For an adjacent interval $[a,b]$ of $S$ with $b-a>2\delta$, no point of
$T$ lies in $(a+\delta,b-\delta)$. Otherwise its corresponding point of
$S$ would lie in $(a,b)$. The midpoint of $[a,b]$ is therefore between
two consecutive points $u,v$ of $T$, with
$u\le a+\delta$ and $v\ge b-\delta$. Consequently
$b-a\le(v-u)+2\delta\le(d-c)+2\delta$.
When $b-a\le2\delta$ the same bound follows from $c<d$.
Interchanging $S$ and $T$ proves the claimed estimate.

This argument permits collisions and changes in order. For a sequence
of such pairs with errors $\delta_m$, the normalized gap error is at
most $2\delta_m/m$. Identifying the finite sets with a particular
rotation partition requires a separate equality of cut sets.
