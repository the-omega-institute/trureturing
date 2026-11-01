# Mixed vacancies in packing-domatic colourings of the integer path

## 1. The common packing and its vacancies

**Definition 1.1 (Packing and interval counts).** Let $t\ge1$ be an integer.
A packing is a single map $f:\mathbb Z\to\{1,\ldots,t\}$ such that

$$
u\ne v,\quad f(u)=f(v)=j\quad\Longrightarrow\quad |u-v|\ge j+1.
$$

For $1\le j\le t$ and $z\in\mathbb Z$, put

$$
A_j(z)=\mathbf1_{\{f(z)=j\}},\qquad
h_j(z)=1-\sum_{r=0}^{j}A_j(z+r).
$$

For integers $b$ and $m\ge1$, write
$I(b,m)=\{b,b+1,\ldots,b+m-1\}$ and
$N_j(I)=\sum_{z\in I}A_j(z)$. Each length-$(j+1)$ window contains at most
one centre of colour $j$, so $h_j(z)\in\{0,1\}$. In particular all these
vacancies are nonnegative, including when a colour is absent. No
periodicity, frequency limit or stationarity is imposed.

The graph and colour conventions are those of Brešar, Ferme and Hu,
[*Partitioning an S-packing coloring into broadcast dominating sets*,
arXiv:2610.03477v1](https://arxiv.org/html/2610.03477v1), Sections 1 and 3.2:
the vertex $u_z$ is identified with $z$, path distance is $|u-v|$, and their
ordinary packing sequence is $S=(1,2,3,\ldots)$.

**Definition 1.2 (A common partition).** For positive integers $k,t$, let
$Q(k,t)$ mean that there exist a packing $f$ as in 1.1 and one map
$c:\mathbb Z\to\{1,\ldots,k\}$ satisfying

$$
\forall z\in\mathbb Z\ \forall i\in\{1,\ldots,k\}
\exists a\in\mathbb Z:\quad c(a)=i,\quad |z-a|\le f(a).
$$

Thus the source's partition sets are $c^{-1}(i)$, and its broadcast radius
at $a$ is exactly this same $f(a)$. The class map need not depend only on
the colour. Whenever consequences of $Q(k,t)$ are considered below, one
witnessing pair $(f,c)$ is fixed throughout.

## 2. Mixed vacancies on a complete product window

**Theorem 2.1 (The actual coprime relation).** For every packing of 1.1,
every pair of coprime integers $p,q\ge2$ with $p-1,q-1\le t$, every
$z\in\mathbb Z$, and $L=pq$,

$$
\sum_{s=0}^{L-p}h_{p-1}(z+s)
+\sum_{s=0}^{L-q}h_{q-1}(z+s)\ge1. \tag{2.1}
$$

Proof. All summands are nonnegative integers. If the left side were
less than 1, every displayed vacancy would vanish. Set
$a_r=A_{p-1}(z+r)$ for $0\le r<L$. Vanishing says

$$
\sum_{r=s}^{s+p-1}a_r=1\qquad(0\le s\le L-p).
$$

Subtract consecutive equalities. For every $0\le s\le L-p-1$ this gives
$a_{s+p}=a_s$. The first block has a unique occupied position
$\alpha\in\{0,\ldots,p-1\}$. Iterating the equality inside the window
therefore proves, for every $0\le r<L$,

$$
A_{p-1}(z+r)=1\quad\Longleftrightarrow\quad r\equiv\alpha\pmod p.
$$

Indeed reducing $r$ by $p$ repeatedly never leaves $[0,L-1]$ and ends in
$[0,p-1]$. Applying the same argument to the length-$q$ windows gives a
$\beta\in\{0,\ldots,q-1\}$ such that

$$
A_{q-1}(z+r)=1\quad\Longleftrightarrow\quad r\equiv\beta\pmod q
\qquad(0\le r<L).
$$

The $q$ integers $\alpha+kp$, $0\le k<q$, have distinct residues modulo
$q$: equal residues would give $q\mid p(k-k')$, hence $q\mid k-k'$
by coprimality, and thus $k=k'$. They consequently include a residue
$\beta$. Every one lies between 0 and
$(p-1)+(q-1)p=pq-1$. At the selected position both indicators equal 1.
Since coprime $p,q\ge2$ are distinct, this assigns two different colours
to the same vertex, a contradiction.

If colour $p-1$ is absent, the first sum alone equals $L-p+1\ge1$;
if colour $q-1$ is absent the second sum alone equals $L-q+1\ge1$.
Thus no existence assumption on either colour is hidden in the proof.
The residue intersection used here is the elementary Chinese remainder
argument; only the forced residue classes inside this one window are
used, with no global periodicity conclusion. $\square$

**Proposition 2.2 (The coprimality boundary).** Removing coprimality from
2.1 gives a false assertion, even for a packing on the whole integer path.

Proof. Take $p=2$, $q=4$, $t=3$, and define

$$
f(a)=\begin{cases}
1,&a\equiv0,2\pmod4,\\
3,&a\equiv1\pmod4,\\
2,&a\equiv3\pmod4.
\end{cases}
$$

Consecutive centres of colour 1 are separated by 2, and those of colours
2 and 3 by 4, so all packing inequalities hold. Every length-2 window
contains one colour-1 centre and every length-4 window one colour-3
centre. Hence $h_1=h_3=0$ identically and the proposed left side, with
endpoints $L-p=6$ and $L-q=4$, is 0 at every translate. $\square$

## 3. A uniform palette-five incidence bound

**Definition 3.1 (Three local slacks and corrected multiplicity).** Fix any
packing $f:\mathbb Z\to\{1,2,3,4,5\}$. At every $z\in\mathbb Z$ put

$$
\begin{aligned}
T_{23}(z)&=\sum_{s=0}^{9}h_2(z+s)+\sum_{s=0}^{8}h_3(z+s)-1,\\
T_{34}(z)&=\sum_{s=0}^{16}h_3(z+s)+\sum_{s=0}^{15}h_4(z+s)-1,\\
T_{45}(z)&=\sum_{s=0}^{25}h_4(z+s)+\sum_{s=0}^{24}h_5(z+s)-1.
\end{aligned}
$$

These are nonnegative integers by 2.1 with $(p,q)=(3,4),(4,5),(5,6)$,
respectively. Define, using all integer centres,

$$
\begin{aligned}
B_a&=[a-f(a),a+f(a)]\cap\mathbb Z,\\
M_f(z)&=\#\{a\in\mathbb Z:z\in B_a\},\\
C_f(z)&=M_f(z)+\frac{T_{23}(z)}{15}
+\frac{2T_{34}(z)}{85}+\frac{7T_{45}(z)}{221}
+\frac{359h_5(z)}{663}.
\end{aligned}
$$

The count is finite, since a centre covering $z$ belongs to $[z-5,z+5]$.
In particular $C_f\ge M_f$ pointwise. No class map is required.

**Theorem 3.2 (Uniform translated-interval estimate).** For every packing
in 3.1, every $b\in\mathbb Z$, and every integer $m\ge10$, with
$I=I(b,m)$,

$$
\left|\sum_{z\in I}C_f(z)-\frac{23464}{3315}m\right|\le420,
\qquad
\sum_{z\in I}M_f(z)\le\frac{23464}{3315}m+420. \tag{3.1}
$$

Proof. We retain boundary terms explicitly. For any $g:\mathbb Z\to[0,1]$
and integer $r$,

$$
\left|\sum_{z\in I}g(z+r)-\sum_{z\in I}g(z)\right|\le |r|. \tag{3.2}
$$

To prove this, cancel the common points of $I+r$ and $I$. The two
remaining sets each have $\min(m,|r|)$ points. Each remaining sum lies
in $[0,\min(m,|r|)]$, so their difference has absolute value at most
$\min(m,|r|)\le|r|$. This includes both signs of $r$ and disjoint intervals.

Write $N_j=N_j(I)$ and $H_j=\sum_{z\in I}h_j(z)$. The partition into
colours gives $\sum_{j=1}^5N_j=m$. Summing the vacancy definition and
using (3.2) for $A_j$ gives exact errors $e_j$ such that

$$
H_j=m-(j+1)N_j+e_j,\qquad |e_j|\le\sum_{r=0}^j r
=\frac{j(j+1)}2. \tag{3.3}
$$

The exact incidence formula is

$$
M_f(z)=\sum_{j=1}^5\sum_{u=-j}^{j}A_j(z+u).
$$

Here $a=z+u$ ranges over every centre that can cover $z$, including
centres outside $I$. Applying (3.2) to each shift proves

$$
\begin{aligned}
\sum_{z\in I}M_f(z)
&=\sum_{j=1}^5(2j+1)N_j+e_M\\
&=3m+2N_2+4N_3+6N_4+8N_5+e_M,\\
|e_M|&\le\sum_{j=1}^5\sum_{u=-j}^{j}|u|
=\sum_{j=1}^5j(j+1)=70. \tag{3.4}
\end{aligned}
$$

This is the finite incidence-counting intermediate of the private
[`no_four`](../../../D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.lean)
argument; the finite-path counterpart is
[`local_counting`](../../../D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting.lean).
Neither its six-class lower demand nor the finite-path endpoint bound is
assumed here.

Apply (3.2) again, now to $h_j\in[0,1]$. Exact summation of 3.1's slacks gives

$$
\begin{aligned}
\sum_I T_{23}&=10H_2+9H_3-m+\eta_{23},
&|\eta_{23}|&\le45+36=81,\\
\sum_I T_{34}&=17H_3+16H_4-m+\eta_{34},
&|\eta_{34}|&\le136+120=256,\\
\sum_I T_{45}&=26H_4+25H_5-m+\eta_{45},
&|\eta_{45}|&\le325+300=625.
\end{aligned} \tag{3.5}
$$

For example the first error is the sum, for $0\le s\le9$ and $0\le s\le8$,
of the differences between the shifted vacancy sum and $H_2,H_3$;
the two arithmetic sums bound it. The other two rows use precisely their
displayed endpoint ranges.

The coefficients of $H_2,H_3,H_4,H_5$ in the corrected sum are respectively

$$
\frac{10}{15}=\frac23,\quad
\frac9{15}+\frac{34}{85}=1,\quad
\frac{32}{85}+\frac{182}{221}=\frac65,\quad
\frac{175}{221}+\frac{359}{663}=\frac43. \tag{3.6}
$$

Their products with $3,4,5,6$ are $2,4,6,8$. Thus substitution of
(3.3)--(3.5) into the definition of $C_f$ cancels all four $N_j$ terms,
and gives

$$
\begin{aligned}
\sum_I C_f&=\frac{23464}{3315}m+E,\\
E&=e_M+\frac23e_2+e_3+\frac65e_4+\frac43e_5
+\frac{\eta_{23}}{15}+\frac{2\eta_{34}}{85}
+\frac{7\eta_{45}}{221}.
\end{aligned} \tag{3.7}
$$

The constant is verified by

$$
3+\frac23+1+\frac65+\frac43
-\left(\frac1{15}+\frac2{85}+\frac7{221}\right)
=\frac{36}{5}-\frac{404}{3315}=\frac{23464}{3315}.
$$

Finally all errors are bounded independently of $b,m$:

$$
\begin{aligned}
|E|&\le70+2+6+12+20+\frac{81}{15}
+\frac{512}{85}+\frac{4375}{221}\\
&=\frac{156048}{1105}<142\le420.
\end{aligned}
$$

This proves the absolute estimate; $M_f\le C_f$ proves its consequence.
All shifts refer to the original whole-line map $f$. $\square$

## 4. Seven classes on the same realization

**Theorem 4.1 (The nonnegative seven-class budget).** Fix any witnessing
pair $(f,c)$ for $Q(7,5)$ and use its same $f$ in 3.1. Define

$$
R(z)=M_f(z)-7,\qquad P(z)=C_f(z)-7.
$$

Then at every integer $z$,

$$
R(z)\ge0,\qquad
P(z)=R(z)+\frac{T_{23}(z)}{15}+\frac{2T_{34}(z)}{85}
+\frac{7T_{45}(z)}{221}+\frac{359h_5(z)}{663}\ge0. \tag{4.1}
$$

For every $I=I(b,m)$ with $b\in\mathbb Z$ and integer $m\ge10$,

$$
\begin{aligned}
\left|\sum_I P-\frac{259}{3315}m\right|&\le420,\\
\sum_I R&\le\frac{259}{3315}m+420,\\
\#\{z\in I:M_f(z)\ge8\}&\le\frac{259}{3315}m+420.
\end{aligned} \tag{4.2}
$$

Proof. At a fixed $z$, choose a covering centre $a_i$ for each of the
seven labels. If $a_i=a_{i'}$, applying the one function $c$ gives
$i=c(a_i)=c(a_{i'})=i'$. The seven centres are therefore distinct and
are all counted by $M_f(z)$, proving $M_f(z)\ge7$. Nonnegativity of the
three local slacks and $h_5$ proves (4.1). Subtract $7m$ from (3.1), using
$23464/3315-7=259/3315$, to get the first estimate in (4.2). The second
follows from $0\le R\le P$. Since $M_f$ is integer-valued and at least 7,
$\mathbf1_{\{M_f(z)\ge8\}}\le R(z)$, proving the last bound by summation.
The injection of class witnesses is the same counting intermediate used
in `no_four` and `local_counting`, cited in the proof of 3.2; here its
seven witnesses use the single fixed pair $(f,c)$. $\square$

## 5. Every common subsequential count limit

**Theorem 5.1 (Common limits and the exact loss identity).** Fix a
palette-five packing $f$. Let $I_n=I(b_n,m_n)$ be any integer intervals
with $m_n\to\infty$. On any one subsequence $n_\ell$ on which all five
ratios $N_j(I_{n_\ell})/m_{n_\ell}$ converge, denote their limits by $x_j$.
Set

$$
d_j=\frac1{j+1}-x_j,\qquad
W=\sum_{j=1}^5(2j+1)x_j.
$$

Then $d_j\ge0$, $\sum_jx_j=1$, and

$$
\begin{aligned}
\tau_{23}&=30d_2+36d_3-1\ge0,\\
\tau_{34}&=68d_3+80d_4-1\ge0,\\
\tau_{45}&=130d_4+150d_5-1\ge0, \tag{5.1}\\
\frac{36}{5}-W
&=\frac{404}{3315}+\frac{\tau_{23}}{15}
+\frac{2\tau_{34}}{85}+\frac{7\tau_{45}}{221}
+\frac{718}{221}d_5. \tag{5.2}
\end{aligned}
$$

Consequently $W\le23464/3315$. If $f$ belongs to a fixed witnessing pair
$(f,c)$ for $Q(7,5)$, then on this very same subsequence the average of
$R$ converges to $\overline R=W-7\ge0$, and

$$
\overline R+\frac{\tau_{23}}{15}+\frac{2\tau_{34}}{85}
+\frac{7\tau_{45}}{221}+\frac{718}{221}d_5
=\frac{259}{3315}. \tag{5.3}
$$

Proof. For any finite interval of length $m$, list the $N=N_j(I)>0$
centres of colour $j$ increasingly. The first and last differ by at
least $(N-1)(j+1)$ and at most $m-1$. Hence

$$
\frac{N_j(I)}m\le\frac1{j+1}+\frac{j}{(j+1)m}.
$$

The same upper bound holds if $N=0$. Nonnegative counts and passage along
the specified subsequence give $0\le x_j\le1/(j+1)$. This is the classical
single-colour spacing ingredient underlying Goddard and Xu,
[*The S-packing chromatic number of a graph*, Section 4, Proposition 10](https://www.dmgt.uz.zgora.pl/publish/pdf.php?doi=1642),
DOI 10.7151/dmgt.1642, with their separation parameter $a_j=j$.
The finite endpoint estimate above establishes exactly the required scope,
without presupposing ordinary densities. Summing the five actual counts
before taking the common limit gives $\sum_jx_j=1$.

Equations (3.3) and (3.5), divided by $m=m_{n_\ell}$, have errors tending
to zero uniformly in the translates $b_{n_\ell}$. They therefore give,
on this same subsequence,

$$
\begin{aligned}
\frac1m\sum_I h_j&\longrightarrow1-(j+1)x_j=(j+1)d_j,\\
\frac1m\sum_I T_{23}&\longrightarrow30d_2+36d_3-1,\\
\frac1m\sum_I T_{34}&\longrightarrow68d_3+80d_4-1,\\
\frac1m\sum_I T_{45}&\longrightarrow130d_4+150d_5-1.
\end{aligned}
$$

The last three finite sums are nonnegative, so their limits give (5.1).
There is no requirement that finite quantities $1/(j+1)-N_j(I)/m$ be
nonnegative; only their limits have the asserted sign.

Eliminating $x_1$ by $\sum_jx_j=1$ yields

$$
W=3+2x_2+4x_3+6x_4+8x_5,
\qquad \frac{36}{5}-W=2d_2+4d_3+6d_4+8d_5.
$$

The three exact coefficient identities

$$
\begin{aligned}
2d_2+4d_3+6d_4+8d_5
&=\frac{30d_2+36d_3}{15}
+\frac{2(68d_3+80d_4)}{85}\\
&\quad+\frac{7(130d_4+150d_5)}{221}
+\frac{718d_5}{221},\\
\frac1{15}+\frac2{85}+\frac7{221}&=\frac{404}{3315},\\
\frac{1050+718}{221}&=8
\end{aligned}
$$

verify (5.2) by direct expansion. This use of nonnegative constraint
slacks is classical weak-duality algebra, as in the private
[`weak_duality`](../../../D5/S3/Analytic/Knapsack/FractionalKnapsackDual.lean)
and the zero-gap identity in
[Arithmetic Boundary Quantization, 33.10](ARITHMETIC_BOUNDARY_QUANTIZATION.md).
Those generic identities are intermediates; the constraints used here
are (2.1) for the actual three colour pairs. No optimizer-attainment or
independently chosen marginal extremum is substituted for them.

Finally (3.4) divided by $m$ gives $m^{-1}\sum_I M_f\to W$ on the same
subsequence. Under $Q(7,5)$, (4.1) gives $R\ge0$ and thus
$m^{-1}\sum_I R\to W-7=\overline R\ge0$. Rearranging (5.2), with
$36/5-7-404/3315=259/3315$, proves (5.3). Equivalently the limiting
$h_5$ contribution is $(359/663)\,6d_5=(718/221)d_5$, consistent with
the pointwise definition of $P$. $\square$

## 6. Strictness and the remaining existence questions

**Proposition 6.1 (Strict strengthening of the separate-colour relaxation).**
The necessary conditions (5.1) strictly strengthen the relaxation

$$
0\le x_j\le\frac1{j+1},\qquad \sum_{j=1}^5x_j=1,
$$

including its additional seven-class necessary condition $W\ge7$.

Proof. The relaxed vector

$$
(x_1,x_2,x_3,x_4,x_5)=\left(\frac1{20},\frac13,\frac14,\frac15,\frac16\right)
$$

satisfies all five coordinate bounds and sums to 1. It gives $W=36/5\ge7$.
For this vector $d_2=d_3=d_4=d_5=0$, so all three expressions in (5.1)
equal $-1$. In particular the vector is not an actual simultaneous
subsequential count realization of a packing. It is used solely as a
point in the old relaxation. Moreover the relaxation has maximum $W=36/5$:
use $W=3+2x_2+4x_3+6x_4+8x_5$ and the four coordinate caps, with equality
at this vector. The actual upper bound is smaller by $404/3315>0$.
This proves strict logical strengthening, without asserting that the new
upper bound is sharp or attained. $\square$

**Proposition 6.2 (Finite deficits can be negative).** Even for $m=10$,
$1/(j+1)-N_j(I)/m$ can be negative in an actual palette-five packing.

Proof. Repeat the pattern $[2,1,3,2,1,4]$ on $\mathbb Z$, starting with
colour 2 at 0. Colours 1 and 2 have separation 3; colours 3 and 4 have
separation 6; colour 5 is absent. Thus this is a palette-five packing.
The interval $I(0,10)$ has colour-2 centres at $0,3,6,9$, giving
$1/3-4/10=-1/15$. This does not affect the nonnegativity of any $h_j$
or the limiting deficits in 5.1. $\square$

**Definition 6.3 (Existence and sharpness questions).** The remaining
questions here are whether $Q(7,5)$ holds, whether $23464/3315$ is the
sharp supremum of the actual $W$, and whether equality is attained.
Equation (5.3) has the strictly positive residual $259/3315$, so its
nonnegative terms do not give a contradiction. None of these questions
is decided by the displayed inequalities.

The distinct source question is Brešar--Ferme--Hu, Section 5,
[Problem 3](https://arxiv.org/html/2610.03477v1): whether
$\chi_{\rho,k}(P_\infty)\le k-1$ for every integer $k\ge4$.
In the notation of 1.2 this asks for $Q(k,k-1)$; its $k=7$ instance asks
for $Q(7,6)$, an upper construction with six colours. Increasing the
palette bound keeps both maps and shows $Q(7,5)\Rightarrow Q(7,6)$;
no converse or construction follows from the necessary inequalities above.
That source question is likewise not settled here.

For comparison of domains, Zhang,
[*Density regions, integer certificates and packing colorings of distance
graphs*, arXiv:2609.09018v1](https://arxiv.org/html/2609.09018v1), Sections 1--2,
uses $D(1,r)$ with edges of displacement 1 or $r$, and its shortest-path
metric. These metrics differ from $|u-v|$. A packing for $D(1,r)$ is a
path packing because graph distance there is at most $|u-v|$; the reverse
implication fails. For example the path packing $[1,2,1,3]$, repeated with
colour 1 at even integers, assigns colour 1 to both endpoints of an edge
of displacement 6, or of displacement 8. It is therefore not a packing
for either $D(1,6)$ or $D(1,8)$. Thus the numerical lower bounds for those
stronger distance constraints supply no numerical lower bound here.

All conclusions concern one actual whole-line packing, and, when needed,
one common class map. The count limits are conditional on a specified
common subsequence; existence of ordinary densities is not asserted.
Neither equality of limiting averages nor a vanishing limiting slack is
used to infer a pointwise identity.

## 追加锚（本行以下为增补区）

## 7. Broadcast holes and local multiplicity deficits

**Definition 7.1 (Broadcast holes and deficits).** For one packing
$f:\mathbb Z\to\{1,2,3,4,5\}$, with the intervals $B_a$ of 3.1, define

$$
n_j(z)=\#\{a\in\mathbb Z:f(a)=j,\ |a-z|\le j\},\qquad
V_5(z)=\mathbf1_{\{n_5(z)=0\}},\qquad
D(z)=\max\{7-M_f(z),0\}.
$$

Thus $M_f(z)=\sum_{j=1}^5n_j(z)$ counts all original centres.
The condition $V_5(z)=1$ excludes colour 5 at all eleven positions
$z-5,\ldots,z+5$. It differs from $h_5(z)=1$, which excludes colour 5
only at the six positions $z,\ldots,z+5$.

**Theorem 7.2 (A deficit within distance two).** For every packing in
7.1 and every $z\in\mathbb Z$,

$$
n_5(z)=0\quad\Longrightarrow\quad
\exists w\in[z-2,z+2]\cap\mathbb Z:\ M_f(w)\le6. \tag{7.1}
$$

Consequently the pointwise inequality

$$
V_5(z)\le\sum_{u=-2}^{2}D(z+u) \tag{7.2}
$$

holds on the entire integer path.

Proof. Translate $z$ to 0. Suppose $n_5(0)=0$ and, towards a
contradiction, $M_f(w)\ge7$ for every $-2\le w\le2$. There is no
colour-5 centre in $[-5,5]$. Spacing gives $n_j(w)\le2$ for every
$j$: three centres in $[w-j,w+j]$ would span at least $2(j+1)>2j$.
Also $n_5(w)\le1$ when $|w|\le2$, since the only possible colour-5
centres covering such a $w$ lie in $\{-7,-6\}$ or $\{6,7\}$.
Both members of either pair cannot have colour 5.

Put $r=f(0)\in\{1,2,3,4\}$. Spacing gives $n_r(0)=1$.
Thus $M_f(0)\le1+2+2+2=7$, and the assumed lower bound implies
$n_j(0)=2$ for every $j\in\{1,2,3,4\}\setminus\{r\}$.
Each such colour has one centre at $-p_j$ and one at $q_j$, where

$$
1\le p_j,q_j\le j,\qquad p_j+q_j\ge j+1. \tag{7.3}
$$

Indeed neither centre is 0, and two on one side would be less than
$j+1$ apart. Centres of different colours occupy different positions.
These conclusions use the hole and the multiplicity at 0 jointly.

If $r=4$, the colour-1 centres are $\pm1$, the colour-2 centres must
then be $\pm2$, and the colour-3 centres must be $\pm3$.
At 1 the respective counts for colours 1, 2 and 3 are each 1.
Together with $n_4(1)\le2$ and $n_5(1)\le1$, this gives
$M_f(1)\le6$, a contradiction.

If $r=3$, the colour-1 and colour-2 centres are again $\pm1,\pm2$.
The two colour-4 centres have distances 3 or 4 from 0.
At 1, $n_1(1)=n_2(1)=1$, so $M_f(1)\ge7$ forces
$n_3(1)=n_4(1)=2$ and $n_5(1)=1$. The second colour-3 centre in
$[-2,4]$, besides 0, must be 4. Hence the positive colour-4 centre
is 3, and $n_4(1)=2$ puts its negative counterpart at $-3$.
The same argument at $-1$ puts colour 3 at $-4$.
The resulting values are

$$
f(0)=3,\qquad f(\pm1)=1,\quad f(\pm2)=2,\quad
f(\pm3)=4,\quad f(\pm4)=3.
$$

At 2 the counts for colours 1 through 4 are respectively $1,1,2,1$.
For example the colour-3 centres counted there are 0 and 4;
spacing excludes any further one in $[-1,5]$. All these counts use
the full covering windows. Since $n_5(2)\le1$, again $M_f(2)\le6$.

Suppose $r=2$. The colour-1 centres are $\pm1$.
On each side let $(p,q)$ denote the distances of the colour-3 and
colour-4 centres covering 0. Position 2 on that side cannot have
colour 1, 2 or 5, so it has colour 3 or 4. Consequently the possible
ordered pairs are exactly among

$$
A=(2,3),\qquad B=(2,4),\qquad C=(3,2). \tag{7.4}
$$

Here the assertion is only a necessary list: if colour 3 is at distance
2, colour 4 is at distance 3 or 4; if colour 4 is at distance 2,
colour 3 is at distance 3. In particular the pair $(3,4)$ is excluded
by the value required at position 2, not by an ordering assumption.
For either side put $s=\mathbf1_{\{p=2\}}+\mathbf1_{\{q\le3\}}$;
its value is 2 for $A$ and 1 for $B,C$. Use subscripts $L,R$ for the
two sides, and put

$$
x_R=\mathbf1_{\{f(3)=2\}},\quad x_L=\mathbf1_{\{f(-3)=2\}},\qquad
b_R=\mathbf1_{\{f(6)=5\}},\quad b_L=\mathbf1_{\{f(-6)=5\}}.
$$

Directly counting the windows $[0,2],[-1,3],[-2,4],[-3,5],[-4,6]$
gives the exact formulas

$$
M_f(1)=4+s_L+x_R+b_R,\qquad
M_f(-1)=4+s_R+x_L+b_L. \tag{7.5}
$$

For instance the colour-2 count at 1 is $1+x_R$, the colour-3 count
is $1+\mathbf1_{\{p_L=2\}}$, and the colour-4 count is
$1+\mathbf1_{\{q_L\le3\}}$. No additional same-side centre can
enter these windows because its separation from the displayed centre
would be too small. The colour-5 contribution comes precisely from 6.

If $s_L=1$, the first lower bound in (7.5) forces $x_R=b_R=1$.
The condition $x_R=1$ forces the right pair to be $B$, since position
3 is then unavailable to colours 3 and 4. Hence $s_R=1$, and the
second lower bound forces $x_L=b_L=1$, putting the left pair at $B$
as well. If $s_L=2$, the left pair is $A$, so $x_L=0$.
The second lower bound now forces $s_R=2$ and $b_L=1$;
the right pair is $A$, so $x_R=0$, and the first bound forces $b_R=1$.
Thus the only possibilities under both neighbouring lower bounds
are $A,A$ and $B,B$.

For $A,A$, the values at $\pm2,\pm3$ are 3 and 4 respectively.
At 2, $n_1=1$, $n_2\le2$, $n_3=1$, $n_4=1$, $n_5\le1$.
For $B,B$, the values at $\pm2,\pm3,\pm4$ are 3, 2 and 4
respectively. At 2 the corresponding counts satisfy the same bounds
(the colour-2 count is exactly 2). Each possibility gives $M_f(2)\le6$.

It remains to treat $r=1$. For $j=2,3,4$ keep the notation $p_j,q_j$
of (7.3), and define

$$
\begin{aligned}
e_L&=\#\{j\in\{2,3,4\}:p_j=j\},&
e_R&=\#\{j\in\{2,3,4\}:q_j=j\},\\
a_L&=\mathbf1_{\{f(-2)=1\}},&a_R&=\mathbf1_{\{f(2)=1\}},\\
b_L&=\mathbf1_{\{f(-6)=5\}},&b_R&=\mathbf1_{\{f(6)=5\}}.
\end{aligned}
$$

A centre at $-p_j$ covering 0 ceases to cover 1 precisely when $p_j=j$.
The positive centre still covers 1. There is no further colour-$j$
centre in $[1-j,1+j]$: a further positive centre would have to be at
least $q_j+j+1>j+1$, and a further negative centre would be less than
$1-j$. The colour-1 count is $1+a_R$ and the colour-5 count is $b_R$.
Reflection gives the other formula, so exactly

$$
M_f(1)=7-e_L+a_R+b_R,\qquad
M_f(-1)=7-e_R+a_L+b_L. \tag{7.6}
$$

If $a_R=1$, the positive colour-2 centre must be at 1, the colour-3
centre at 3, and the colour-4 centre at 4. Thus $e_R=2$.
Likewise $a_L=1$ implies $e_L=2$.
If $e_L=2$, the lower bound at 1 in (7.6) forces $a_R=b_R=1$,
hence $e_R=2$; the lower bound at $-1$ then forces $a_L=b_L=1$.
Both colour-2 centres would be at $-1,1$, contrary to their required
separation 3. The reflected argument excludes $e_R=2$, and (7.6)
already bounds each $e$ by 2. Therefore

$$
e_L,e_R\le1,\qquad a_L=a_R=0. \tag{7.7}
$$

By (7.3), at least one of $p_2,q_2$ is 2. Reflect if necessary so that
$p_2=2$. This already contributes one to $e_L$, so (7.7) forces
$p_3<3$ and $p_4<4$. Distinct occupied positions give $p_3=1,p_4=3$.
The colour-3 separation then forces $q_3=3$. Now $e_R\le1$ forces
$q_2=1,q_4=2$. In particular the ordering is derived from both
neighbouring multiplicities and the packing constraints. The values
at $-3,-2,-1$ are respectively $4,2,3$. At $-2$ this gives
$n_1=0$ and $n_2=1$: in the colour-2 window $[-4,0]$, a further
colour-2 centre at $-4$ is forbidden by the centre at $-2$.
Together with $n_3\le2$, $n_4\le2$ and $n_5\le1$, it follows that
$M_f(-2)\le6$.

Every possible $r$ contradicts the five assumed lower bounds, proving
(7.1). These arguments never assume $M_f(\pm1)=7$ or
$M_f(\pm2)=7$; the equalities used are the window counts explicitly
derived above. All covering windows retain their original external
centres. Finally, if $V_5(z)=0$, (7.2) follows from $D\ge0$.
If $V_5(z)=1$, (7.1) supplies a summand at least 1, since $M_f$ is
integer-valued. This proves (7.2). $\square$

**Proposition 7.3 (The radius is sharp).** There is a packing on all
of $\mathbb Z$ with $n_5(0)=0$ and
$M_f(-1)=M_f(0)=M_f(1)=7$.

Proof. Define $f(a)=g(|a|)$, where

$$
(g(0),g(1),g(2),g(3),g(4),g(5),g(6))=(3,1,2,4,3,1,5),
$$

and for every integer $m\ge7$ set

$$
g(m)=
\begin{cases}
2,&m\equiv3\pmod4,\\
3,&m\equiv1\pmod4,\\
1,&m\equiv0,2\pmod4.
\end{cases}
$$

On the nonnegative half-line the colour-1 centres are 1, 5 and all even
integers at least 8; their successive gaps are 4, 3 and then 2.
The colour-2 centres are 2 and $7+4q$ for $q\ge0$, with gaps 5 and
then 4. The colour-3 centres are 0, 4 and $9+4q$ for $q\ge0$, with
gaps 4, 5 and then 4. Colours 4 and 5 occur only at 3 and 6.
Reflection gives the negative half-line. Across 0 the nearest
colour-1, colour-2, colour-4 and colour-5 pairs are $\pm1,\pm2,\pm3$
and $\pm6$, with separations 2, 4, 6 and 12 respectively.
Colour 3 includes 0 and has nearest other centres at $\pm4$.
Thus all successive same-colour gaps are at least $j+1$; summing
successive gaps gives the required separation for any pair of distinct
colour-$j$ centres. This proves the whole-line packing property.

The only colour-5 centres are $\pm6$, so $n_5(0)=0$. At 0 the vector
$(n_1,n_2,n_3,n_4,n_5)$ is $(2,2,1,2,0)$.
At 1 it is $(1,1,2,2,1)$, using centres $1$ for colour 1, $2$ for
colour 2, $0,4$ for colour 3, $-3,3$ for colour 4, and 6 for colour 5.
Reflection gives the same total at $-1$. Hence radius 1 cannot replace
radius 2 in (7.1), nor in (7.2). This packing has $M_f(2)=6$, so it is
not a witness for $Q(7,5)$. $\square$

**Lemma 7.4 (The classical interval-cover bridge on the whole line).**
Fix positive integers $t,k$ and any one map $g:\mathbb Z\to\{1,\ldots,t\}$,
without a packing assumption. Put
$B_a^g=[a-g(a),a+g(a)]\cap\mathbb Z$ and
$M_g(z)=\#\{a:z\in B_a^g\}$. Then

$$
\begin{aligned}
&\exists c:\mathbb Z\to\{1,\ldots,k\}\quad
\forall z\in\mathbb Z\ \forall i\in\{1,\ldots,k\}\quad
\exists a\in\mathbb Z:\ c(a)=i,\ z\in B_a^g\\
&\hspace{35mm}\Longleftrightarrow\quad
\forall z\in\mathbb Z:\ M_g(z)\ge k. \tag{7.8}
\end{aligned}
$$

Proof. The forward implication is the injection of class witnesses in
4.1: centres carrying distinct values of one function $c$ are distinct.
For the converse use the finite interval multi-hypergraph result of
Pritchard and Rothvoß,
[*Edge-Colouring Hypergraphs Properly (Covering with Matchings) or
Polychromatically (Packing Covers)*, arXiv:1009.6144v1](https://arxiv.org/pdf/1009.6144v1),
Section 3, pp. 4--5: a finite family of intervals on a finite ordered
ground set, of minimum degree $\delta$, partitions into $\delta$ covers.
Their Section 1.1 explicitly retains parallel hyperedges. This is the
classical finite input to the following compactness argument.

For each integer $N\ge0$, take ground set $W_N=[-N,N]\cap\mathbb Z$
and the nonempty intervals $B_a^g\cap W_N$, indexed by all original
centres $a$ whose intervals meet $W_N$. There are finitely many of them,
since such an $a$ lies in $[-N-t,N+t]$. Equal clipped intervals remain
distinct indexed copies. At every $z\in W_N$ the degree is exactly
$M_g(z)$: every interval containing $z$ has been retained, including
those with centre outside $W_N$. The minimum degree $\delta_N$ is
therefore at least $k$. The cited finite result supplies $\delta_N$
covering classes. Keep $k-1$ of them and merge the others into the
last class to obtain $k$ covering classes. This also applies when
$k=1$. Assign arbitrary label 1 to all centres not indexing this finite
family, obtaining a map $c_N:\mathbb Z\to\{1,\ldots,k\}$ satisfying
every covering requirement on $W_N$.

Enumerate $\mathbb Z$ as $a_1,a_2,\ldots$. Starting with all indices
$N\ge0$, repeatedly use the finiteness of the label set to choose nested
infinite index sets $S_1\supseteq S_2\supseteq\cdots$ on which
$c_N(a_j)$ is constant for $N\in S_j$. Define $c(a_j)$ to be that
constant. Choose strictly increasing $N_\ell\in S_\ell$ with
$N_\ell\ge\ell$. For a fixed $z$, all centres covering $z$ lie in
$[z-t,z+t]$ and hence among $a_1,\ldots,a_J$ for some finite $J$.
For every sufficiently large $\ell$, $N_\ell\ge|z|$ and
$c_{N_\ell}$ agrees with $c$ on all of these centres. Since
$c_{N_\ell}$ supplies each of the $k$ labels among them, so does $c$.
This proves all requirements simultaneously for the one map $c$,
with the original $g$ unchanged. $\square$

**Corollary 7.5 (The colour-5 centres of a possible seven-class witness).**
For palette-five packings, $Q(7,5)$ is equivalent to the existence of
one such packing $f$ with $M_f(z)\ge7$ at every $z\in\mathbb Z$.
In any witnessing pair $(f,c)$, the set
$S_5=\{a\in\mathbb Z:f(a)=5\}$ satisfies

$$
\bigcup_{a\in S_5}[a-5,a+5]\cap\mathbb Z=\mathbb Z. \tag{7.9}
$$

It is unbounded in both directions, and any two consecutive members
$a<b$ have

$$
6\le b-a\le11. \tag{7.10}
$$

Proof. Apply 7.4 to the same fixed $f$, with $t=5,k=7$, and compare
with 1.2. For a witness, $M_f\ge7$ everywhere, so $D=0$ everywhere.
Inequality (7.2) gives $V_5=0$ everywhere, which is precisely (7.9).
If $S_5$ were empty or bounded above, an integer more than 5 above an
upper bound would not be covered. The reflected argument excludes a
lower bound. Thus each member has a next and a previous member: the
nonempty sets of positive integer distances have least elements.
The packing condition gives $b-a\ge6$. If consecutive members had
$b-a\ge12$, the integer $a+6$ would be at distance at least 6 from
both, and still farther from every other member, contradicting (7.9).
This gives the inclusive upper endpoint 11. Conversely, for a set
unbounded in both directions with consecutive gaps at most 11, every
integer is within 5 of a member: between consecutive $a,b$, an
uncovered integer would satisfy $z\ge a+6$ and $z\le b-6$, forcing
$b-a\ge12$. This converse concerns only colour-5 broadcast domination,
not the existence of seven common covering classes. No step requires
$S_5$ to be a class of $c$. $\square$

The new joint restriction on the actual realization is (7.1), with its
pointwise deficit form (7.2) and sharp radius witnessed by 7.3.
The interval-cover equivalence (7.8) is classical supporting machinery;
its finite input concerns indexed intervals, and the bounded radius
makes the common whole-line map follow as above. The vacancy
constraints of Sections 2--5 still apply to this same $f$.
Broadcast domination by colour 5 is only a necessary condition for a
seven-class witness; no sufficiency follows from (7.9)--(7.10).
Neither existence nor nonexistence of $Q(7,5)$ follows here.
The bound $23464/3315$, its sharpness and attainment questions, and
the positive residual $259/3315$ in (5.3) retain their stated scope:
no improved bound, realizable marginal optimum, or contradiction from
that residual is asserted. The source's $Q(7,6)$ question in 6.3 is
likewise not decided by these local restrictions.

## 追加锚（本行以下为增补区）
## 8. Adjacent colours and a uniform bound below seven

**Theorem 8.1 (Adjacent-colour interval counts).** For every packing
$f:\mathbb Z\to\{1,2,3,4,5\}$ of 1.1, every $b\in\mathbb Z$, every
integer $m\ge1$, and each $j\in\{2,3,4\}$, the counts on the same
interval $I=I(b,m)$ satisfy

$$
N_j(I)+(j+1)N_{j+1}(I)\le m+j. \tag{8.1}
$$

Proof. Fix $j$ and $I$, and let $a_1<\cdots<a_n$ be all the
colour-$(j+1)$ centres in $I$. If $n=0$, then $N_j(I)\le m$ proves
the assertion. Suppose $n\ge1$. Their separation is at least $j+2$,
so the integer blocks

$$
K_i=[a_i,a_i+j+1]\cap\mathbb Z\qquad(1\le i\le n)
$$

are pairwise disjoint. Each contains at most one colour-$j$ centre:
its first position has colour $j+1$, and its remaining $j+1$ positions
span distance $j$, less than the required separation $j+1$.
Consequently a complete block contains at least $j+1$ positions
not of colour $j$.

For $i<n$, the endpoint $a_i+j+1$ is smaller than $a_{i+1}$, so
$K_i\subseteq I$. If $K_n\subseteq I$ also, the blocks account for
at least $(j+1)n$ positions of $I$ not of colour $j$. Otherwise
$K_n\cap I$ still contains $a_n$, whose colour is not $j$.
The first $n-1$ complete blocks and this one position account for
at least

$$
(j+1)(n-1)+1=(j+1)n-j
$$

such positions. In either case $m-N_j(I)\ge(j+1)n-j$, proving
(8.1). This includes $n=1$ and $m=1$; it uses no centres outside
$I$ and imposes no condition on their values. $\square$

**Theorem 8.2 (Uniform incidence bound below seven).** For every
packing in 8.1, every $b\in\mathbb Z$ and every integer $m\ge1$,
with $M_f$ counting all original centres as in 3.1,

$$
2475\sum_{z\in I(b,m)}M_f(z)\le17315m+215674. \tag{8.2}
$$

Thus the coefficient of $m$ in the corresponding average estimate is
$3463/495=7-2/495$.

Proof. Write $I=I(b,m)$ and $N_j=N_j(I)$. We first use the complete
coprime relation 2.1 with $p=3$, $q=5$, $L=15$ and initial position
$z-7$. Its two vacancy ranges are $0\le s\le12$ and $0\le s\le10$.
Expanding the vacancy definitions gives

$$
\sum_{r=-7}^{7}\bigl(u_r A_2(z+r)+v_r A_4(z+r)\bigr)\le23,
\quad
u_r=\min\{3,8-|r|\},\quad v_r=\min\{5,8-|r|\}. \tag{8.3}
$$

Indeed $u_r$ counts pairs $(s,a)$ with $0\le s\le12$,
$0\le a\le2$, $s+a=r+7$; $v_r$ counts the pairs with
$0\le s\le10$, $0\le a\le4$, $s+a=r+7$.
These are respectively the sequences
$1,2,3,\ldots,3,2,1$ and $1,2,3,4,5,\ldots,5,4,3,2,1$
on the fifteen offsets. The constant is $13+11-1=23$.
In particular

$$
\sum_{r=-7}^{7}u_r=39,\qquad
\sum_{r=-7}^{7}v_r=55,\qquad 0\le u_r\le v_r.
$$

For a fixed $r$ define
$G_r(x)=u_rA_2(x)+v_rA_4(x)$. Since the two colours are distinct
values of the same function $f$, $0\le G_r(x)\le v_r$.
Applying the interval-shift estimate (3.2) to $G_r/v_r$ therefore gives

$$
\left|\sum_{z\in I}G_r(z+r)-\sum_{z\in I}G_r(z)\right|
\le v_r|r|.
$$

Here $v_r\ge1$ for all displayed offsets. Sum (8.3) over $z\in I$
and retain these shift errors. Since

$$
\sum_{r=-7}^{7}v_r|r|
=2\bigl(5(1+2+3)+4\cdot4+3\cdot5+2\cdot6+7\bigr)=160,
$$

we obtain the finite inequality

$$
39N_2+55N_4\le23m+160. \tag{8.4}
$$

All translates in (8.3) concern the original whole-line packing;
centres outside $I$ are included before the shift comparison.

The three inequalities (8.1) and the single-colour spacing bound give

$$
\begin{aligned}
N_2+3N_3&\le m+2,\\
N_3+4N_4&\le m+3,\\
N_4+5N_5&\le m+4,\\
5N_4&\le m+4.
\end{aligned} \tag{8.5}
$$

For the last row, if $N_4>0$, its first and last centres span at least
$5(N_4-1)$ and at most $m-1$; if $N_4=0$, the row is immediate.
This is the finite spacing argument in 5.1, with separation 5,
rather than an assertion about existence of a density.

Multiply the first three rows of (8.5) by $460,320,680$ respectively,
(8.4) by $10$, and the last row of (8.5) by $8$.
All multipliers are positive. Their left-hand coefficients are

$$
\begin{aligned}
460+10\cdot39&=425\cdot2,\\
3\cdot460+320&=425\cdot4,\\
4\cdot320+680+10\cdot55+8\cdot5&=425\cdot6,\\
5\cdot680&=425\cdot8.
\end{aligned}
$$

Their right-hand sum is

$$
(460+320+680+230+8)m
+2\cdot460+3\cdot320+4\cdot680+1600+32
=1698m+6232.
$$

Hence

$$
425(2N_2+4N_3+6N_4+8N_5)\le1698m+6232. \tag{8.6}
$$

This is a nonnegative weighted sum of inequalities for the same actual
counts. The weak-duality algebra of 5.2 supplies no new packing premise;
the additional premise is the positional restriction (8.1).

For completeness, the incidence identity (3.4) and its shift proof apply
to every $m\ge1$: estimate (3.2) has that domain, and no step of the
incidence argument uses $m\ge10$. In particular, using
$\sum_{j=1}^5N_j=m$,

$$
\begin{aligned}
\sum_{z\in I}M_f(z)
&=3m+2N_2+4N_3+6N_4+8N_5+e_M,\\
|e_M|&\le\sum_{j=1}^5\sum_{a=-j}^{j}|a|=70.
\end{aligned}
$$

The identity uses
$M_f(z)=\sum_{j=1}^5\sum_{a=-j}^{j}A_j(z+a)$, so it includes
every original centre covering $z$, with no truncation at the endpoints
of $I$. Substituting (8.6) yields the stronger intermediate estimate

$$
\sum_{z\in I}M_f(z)
\le\frac{2973}{425}m+\frac{35982}{425}.
$$

Finally

$$
\frac{2973}{425}=7-\frac2{425}<7-\frac2{495}
=\frac{3463}{495},\qquad
\frac{35982}{425}<85<87<\frac{215674}{2475},
$$

where $35982<85\cdot425=36125$ and
$87\cdot2475=215325<215674$. Since $m\ge1$, these comparisons give
(8.2), using $2475(3463/495)=17315$. $\square$

**Corollary 8.3 (A deficit in every window and exclusion of seven classes).**
Every packing $f:\mathbb Z\to\{1,2,3,4,5\}$ of 1.1 satisfies

$$
\forall b\in\mathbb Z\quad
\exists z\in I(b,21568):\ M_f(z)\le6. \tag{8.7}
$$

Consequently $\neg Q(7,5)$, with $Q$ exactly as in 1.2.

Proof. If $M_f(z)\ge7$ throughout one such interval, (8.2) would give

$$
17325\cdot21568\le17315\cdot21568+215674,
\qquad
215680\le215674,
$$

a contradiction. The multiplicity is integer-valued, so a position
where it is smaller than 7 has multiplicity at most 6. The translate
$b$ was arbitrary.

Suppose now that one packing $f$ and one map
$c:\mathbb Z\to\{1,\ldots,7\}$ witnessed $Q(7,5)$.
The class-witness injection in 4.1 gives $M_f(z)\ge7$ at every $z$:
choose a centre $a_i$ of each label covering $z$; equality
$a_i=a_{i'}$ would imply $i=c(a_i)=c(a_{i'})=i'$.
All seven centres are counted in the same $M_f(z)$, contradicting
(8.7). No dependence of $c$ on $f$'s colour is assumed.
This uses the forward implication of the classical interval-cover
bridge 7.4; its converse is not needed. $\square$

**Corollary 8.4 (Common count limits and extremal scope).** On every
common subsequence in 5.1, its actual limiting incidence satisfies

$$
W\le\frac{2973}{425}<\frac{3463}{495}<7
<\frac{23464}{3315}. \tag{8.8}
$$

In particular $23464/3315$ remains a valid upper bound but is not the
supremum of the actual values of $W$. Neither coefficient below seven
in (8.8) is asserted to be sharp or attained. The actual supremum and
its attainment, and the least interval length forcing a multiplicity
at most 6, remain undetermined here. The question $Q(7,6)$ in 6.3,
which is the $k=7$ instance of the source's Problem 3, is not decided
by the exclusion of $Q(7,5)$.

Proof. Divide the stronger intermediate estimate in 8.2 by $m$ along
the specified common subsequence. Equation (3.4) gives convergence of
the left side to $W$, while $35982/(425m)$ tends to zero, uniformly
in the interval's translate. The first strict comparison was computed
in 8.2, the second is $3463/495=7-2/495$, and the last is
$23464/3315=7+259/3315$. Thus every actual value of $W$ is bounded
strictly below $23464/3315$, and so is their supremum.

The proof supplies upper bounds and a sufficient interval length;
it supplies no equality realization or matching lower bound for those
extremal quantities. A palette-six packing may use colour 6 and is
outside the hypotheses of 8.1--8.3. In the source notation of 1.1--1.2,
$u_z\leftrightarrow z$, distance is $|u-v|$, radius is the same
$f(a)$, and $A_i=c^{-1}(i)$. Accordingly Problem 3 at $k=7$
asks for a palette bound $k-1=6$, whereas 8.3 excludes palette bound
5. Palette monotonicity gives only $Q(7,5)\Rightarrow Q(7,6)$,
whose antecedent is false; it gives no answer to $Q(7,6)$.
$\square$

## 追加锚（本行以下为增补区）

## 9. The exact seven-class palette on the infinite path

**Definition 9.1 (A period-28 six-colour packing).** Put

$$
\begin{aligned}
S_1&=\{1,8,11,15,22,26\}+28\mathbb Z,\\
S_2&=\{2,6,13,18,25\}+28\mathbb Z,\\
S_3&=\{3,10,16,20,24\}+28\mathbb Z,\\
S_4&=\{4,9,17,23\}+28\mathbb Z,\\
S_5&=\{5,12,19,27\}+28\mathbb Z,\\
S_6&=\{0,7,14,21\}+28\mathbb Z,
\end{aligned}
$$

where the notation means the union of all translates of the displayed
finite set. Define one map $f:\mathbb Z\to\{1,\ldots,6\}$ by
$f(a)=j$ exactly when $a\in S_j$. Thus one period, from $0$ through
$27$, is

$$
(6,1,2,3,4,5,2,6,1,4,3,1,5,2,6,1,3,4,2,5,3,6,1,4,3,2,1,5).
$$

For this palette-six map put

$$
M_f^{[6]}(z)=\#\{a\in\mathbb Z:|a-z|\le f(a)\}.
$$

**Theorem 9.2 (A common seven-class realization).** The map $f$ of
Definition 9.1 is a packing on the whole integer path and satisfies

$$
M_f^{[6]}(z)\ge7\qquad(z\in\mathbb Z).
$$

Consequently $Q(7,6)$ holds with this same $f$ supplying every radius
and every centre.

Proof. The successive gaps in each $S_j$, including the wrap-around gap
to the next period, are

$$
\begin{array}{c|c|c}
j&\text{centres in one period}&\text{cyclic gaps}\\ \hline
1&1,8,11,15,22,26&7,3,4,7,4,3\\
2&2,6,13,18,25&4,7,5,7,5\\
3&3,10,16,20,24&7,6,4,4,7\\
4&4,9,17,23&5,8,6,9\\
5&5,12,19,27&7,7,8,6\\
6&0,7,14,21&7,7,7,7.
\end{array}
$$

Every entry in row $j$ is at least $j+1$. Any two distinct members of
$S_j$ are separated by a sum of consecutive cyclic gaps, so their
distance is at least $j+1$. This proves the packing inequalities, and
the displayed definition gives $1\le f(a)\le6$ for every integer $a$.

For the covering count, let

$$
n_j(r)=\#\{a\in S_j:|a-r|\le j\},\qquad 0\le r\le27.
$$

The count is over all integer translates of the listed residue sets, so
centres outside $[0,27]$ are included. Directly taking the indicated
integer intervals gives the following complete rows, written in order
$r=0,1,\ldots,27$:

$$
\begin{aligned}
(n_6(r))&=(1,2,2,2,2,2,2,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1,2,2,2,2,2,2),\\
(n_5(r))&=(2,2,2,2,2,1,1,2,2,2,2,1,1,1,2,2,2,2,1,1,1,1,2,2,2,1,1,1),\\
(n_4(r))&=(1,1,1,1,1,2,2,2,2,1,1,1,1,2,1,1,1,1,1,2,2,2,1,1,1,1,1,1),\\
(n_3(r))&=(1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,2,2,2,1,2,2,2,1,1,1,1),\\
(n_2(r))&=(1,1,1,1,2,1,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1),\\
(n_1(r))&=(1,1,1,0,0,0,0,1,1,1,1,1,1,0,1,1,1,0,0,0,0,1,1,1,0,1,1,1).
\end{aligned}
$$

Adding the six rows yields

$$
(M_f^{[6]}(r))_{r=0}^{27}=(7,8,8,7,8,7,7,8,9,7,7,7,7,8,7,8,8,8,7,8,7,7,8,9,7,7,7,7).
$$

In particular every entry is at least $7$. Since $f(a+28)=f(a)$, the
translation $a\mapsto a+28$ bijects the centres covering $z$ with those
covering $z+28$. Thus $M_f^{[6]}(z+28)=M_f^{[6]}(z)$, and the residue calculation
proves $M_f^{[6]}(z)\ge7$ for every integer, including negative integers and
all period endpoints.

Apply Lemma 7.4 with $g=f$, $t=6$, and $k=7$. Its hypotheses are exactly
the bounded-radius whole-line interval family just verified, and the
inequality $M_f^{[6]}\ge7$ is its right-hand side because its $M_g$ is
the same count. The lemma therefore
gives one map $c:\mathbb Z\to\{1,\ldots,7\}$ such that, for every
$z\in\mathbb Z$ and every class $i$, there is a centre $a$ with
$c(a)=i$ and $|z-a|\le f(a)$. This is the required single common
realization; no class is required to be determined by the value of $f$,
and no assertion about periodicity of arbitrary solutions is made.
\square$

**Theorem 9.3 (Exact value for seven classes).** With the source
notation for packing-domatic colourings of the two-way infinite path,

$$
\chi_{\rho,7}(P_\infty)=6.
$$

Proof. Under the source's identification $u_z\leftrightarrow z$, the
path distance is $|u-v|$, the ordinary packing sequence is
$(1,2,3,\ldots)$, and the class sets are $c^{-1}(i)$. Therefore the
definition of $Q(7,t)$ in 1.2 is exactly the source predicate that
$\chi_{\rho,7}(P_\infty)\le t$. Theorem 9.2 gives
$\chi_{\rho,7}(P_\infty)\le6$.

The delivered Corollary 8.3 proves $\neg Q(7,5)$ under the same
whole-line hypotheses and the same single class map. If some
$t\le5$ satisfied $Q(7,t)$, increasing the palette bound while keeping
both maps and every centre would give $Q(7,5)$ by the palette
monotonicity already used in 6.3, a contradiction. Hence no palette
bound at most $5$ is possible, so the least bound is $6$.

This is the $k=7$ instance of Brešar--Ferme--Hu, *Partitioning an
$S$-packing coloring into broadcast dominating sets*, arXiv:2610.03477v1,
Sections 1 and 3.2 and Problem 3 in Section 5. The argument resolves
only this instance on the original two-way integer path; it makes no
claim about other values of $k$, extremizers, or optimal deficit lengths.
\square$


## 追加锚（本行以下为增补区）

## 10. Every odd number of classes at least nine

**Definition 10.1 (Complementary blocks on the integer path).** Let
$m\ge4$ be an integer, and put $k=2m+1$ and $T=2k=4m+2$. Define

$$
s_m=\begin{cases}m+4,&m\text{ even},\\2,&m\text{ odd}.\end{cases}
$$

All indices $h$ in the following sets are integers. Set

$$
D_m=\begin{cases}
\{2+2h:0\le h<(m-2)/2\}\ \cup\ \{m+1\}\cup\ \{m+5+2h:0\le h<(m-4)/2\},&m\text{ even},\\[2mm]
\{3+2h:0\le h<(m-3)/2\}\ \cup\ \{m+1\}\cup\ \{m+4+2h:0\le h<(m-3)/2\},&m\text{ odd}.
\end{cases} \tag{10.1}
$$

An index range with upper bound zero is empty. Write the members of
$D_m$ in increasing order as $d_1<\cdots<d_{m-2}$. Define a function
$F_m$ on the integer residues $0,\ldots,T-1$ by

$$
\begin{aligned}
F_m(0)=F_m(k)&=2m,\\
F_m(s_m)=F_m(s_m+k)&=m,\\
F_m(1)=F_m(m+3)=F_m(m+k)&=m+1,\\
F_m(m)=F_m(1+k)=F_m(m+3+k)&=m-1,\\
F_m(d_j)=F_m(d_j+1+k)&=j&& (1\le j\le m-2),\\
F_m(d_j+1)=F_m(d_j+k)&=2m-j&& (1\le j\le m-2).
\end{aligned} \tag{10.2}
$$

For every $a\in\mathbb Z$, let $R_T(a)$ and $R_k(a)$ be its unique
remainders in $\{0,\ldots,T-1\}$ and $\{0,\ldots,k-1\}$, respectively.
Put

$$
f_m(a)=F_m(R_T(a)),\qquad c_m(a)=1+R_k(a). \tag{10.3}
$$

Thus the class labelled $i$ is precisely $(i-1)+k\mathbb Z$. The
remainders are Euclidean remainders for all integers, including negative
integers.

**Theorem 10.2 (The original odd-family upper bound).** For every integer
$m\ge4$, Definition 10.1 gives well-defined maps

$$
f_m:\mathbb Z\longrightarrow\{1,\ldots,2m\},\qquad
c_m:\mathbb Z\longrightarrow\{1,\ldots,2m+1\}
$$

such that

$$
\begin{aligned}
u\ne v,\quad f_m(u)=f_m(v)=j&\quad\Longrightarrow\quad |u-v|\ge j+1,\\
\forall z\in\mathbb Z\ \forall i\in\{1,\ldots,2m+1\}\quad
\exists a\in\mathbb Z:&\quad c_m(a)=i,\quad |z-a|\le f_m(a).
\end{aligned} \tag{10.4}
$$

Consequently $Q(k,k-1)$ of Definition 1.2 holds for every odd integer
$k\ge9$. Equivalently, in Brešar--Ferme--Hu,
[*Partitioning an S-packing coloring into broadcast dominating sets*,
arXiv:2610.03477v1](https://arxiv.org/html/2610.03477v1), Sections 1 and
3.2 and Problem 3 in Section 5,

$$
\chi_{\rho,k}(P_\infty)\le k-1\qquad(k\ge9\text{ odd}). \tag{10.5}
$$

Proof. First verify that (10.2) assigns exactly one value to every
residue. The five exceptional positions in the first block
$\{0,\ldots,2m\}$ are

$$
E_m=\{0,1,m,m+3,s_m\}.
$$

For even $m\ge4$ they are distinct and their complement is the disjoint
union of integer intervals

$$
[2,m-1]\cap\mathbb Z,\qquad
[m+1,m+2]\cap\mathbb Z,\qquad
[m+5,2m]\cap\mathbb Z. \tag{10.6}
$$

Their cardinalities are $m-2$, $2$, and $m-4$, respectively. Each is
even, and pairing consecutive positions from its left endpoint gives
exactly the pairs $\{d,d+1\}$ from the even row of (10.1). When $m=4$,
the last interval is empty and the corresponding set of starting
positions is empty, as prescribed. Hence there are
$(m-2)/2+1+(m-4)/2=m-2$ such pairs.

For odd $m\ge4$, necessarily $m\ge5$. The exceptional positions are
$0,1,2,m,m+3$, and their complement is

$$
[3,m-1]\cap\mathbb Z,\qquad
[m+1,m+2]\cap\mathbb Z,\qquad
[m+4,2m]\cap\mathbb Z. \tag{10.7}
$$

These intervals have even cardinalities $m-3$, $2$, and $m-3$.
Pairing consecutive positions from the left again gives exactly (10.1),
with $(m-3)/2+1+(m-3)/2=m-2$ pairs. In either case the pairs are
mutually disjoint and exhaust the complement of $E_m$. All their
endpoints lie in $\{0,\ldots,2m\}$. Also $s_m\le2m$, including the
endpoint $s_4=8$.

Thus the first block is partitioned into the five exceptional positions
and these $m-2$ pairs. Translating this partition by $k$ gives the
second block, which is disjoint from the first. Every position in
(10.2) belongs to one of the two blocks and receives a single value.
The values in the paired positions are $j$ and $2m-j$ for
$1\le j\le m-2$; those at exceptional positions are
$m-1,m,m+1,2m$. All lie in $\{1,\ldots,2m\}$. These colour ranges
are disjoint, so the occurrences of each colour can now be read
exhaustively from (10.2). Equations (10.3) define positive maps on all
of $\mathbb Z$, with $f_m(a+T)=f_m(a)$ and $c_m(a+k)=c_m(a)$.

We next prove the packing inequalities, retaining the gap from each
period to the next. Colour $2m$ occurs exactly at $k\mathbb Z$, whose
successive gaps are $k=2m+1$. Colour $m$ occurs exactly at
$s_m+k\mathbb Z$, with successive gaps $k\ge m+1$.

Fix $1\le j\le m-2$ and write $d=d_j$. The complete occurrence sets
of the two colours assigned to its pair are

$$
\begin{aligned}
\{a:f_m(a)=j\}&=\{d,d+1+k\}+T\mathbb Z,\\
\{a:f_m(a)=2m-j\}&=\{d+1,d+k\}+T\mathbb Z.
\end{aligned} \tag{10.8}
$$

The two listed positions in each row are in increasing order inside
one period. The successive cyclic gaps in the first row are $k+1,k-1$;
in the second row they are $k-1,k+1$. In particular every gap is at
least $k-1=2m$. This is at least $j+1$ and at least
$(2m-j)+1$, since $j\ge1$ and $j\le m-2$.

The remaining colours have the complete occurrence sets

$$
\begin{aligned}
\{a:f_m(a)=m+1\}&=\{1,m+3,m+k\}+T\mathbb Z,\\
\{a:f_m(a)=m-1\}&=\{m,1+k,m+3+k\}+T\mathbb Z.
\end{aligned} \tag{10.9}
$$

Each displayed triple is in increasing order in $[0,T-1]$. For colour
$m+1$ the successive gaps, including the last-to-first gap, are

$$
(m+3)-1=m+2,\qquad
(m+k)-(m+3)=2m-2,\qquad
(1+T)-(m+k)=m+2.
$$

For colour $m-1$ they are

$$
(1+k)-m=m+2,\qquad
(m+3+k)-(1+k)=m+2,\qquad
(m+T)-(m+3+k)=2m-2.
$$

The hypothesis $m\ge4$ gives $2m-2\ge m+2$. Every gap in the first
set is therefore at least $(m+1)+1$, and every gap in the second is
at least $(m-1)+1$. At $m=4$ all six gaps just displayed are 6, so
this endpoint is included. These sets, (10.8), and the two single
residue classes exhaust the palette. Any two distinct centres of a
fixed colour are separated by a nonempty sum of its successive gaps.
Their distance is consequently at least the colour plus one. Because
the occurrence sets include all translates by $T\mathbb Z$, this
argument includes every pair across a period boundary and every pair
of negative integers.

For coverage use the original intervals
$B_a^{f_m}=[a-f_m(a),a+f_m(a)]\cap\mathbb Z$ of Lemma 7.4, with
$g=f_m$ and $t=2m$. The two halves of (10.2) give, for every integer
$a$, the exact identity

$$
f_m(a)+f_m(a+k)=
\begin{cases}
4m,&a\equiv0\pmod k,\\
2m,&a\not\equiv0\pmod k.
\end{cases} \tag{10.10}
$$

Indeed the value $2m$ stays unchanged at the residue 0, the value $m$
stays unchanged at $s_m$, and each other value is exchanged with its
complement to $2m$. The identity holds in both directions through the
two blocks, since translating twice by $k$ is a period. In particular
$f_m(a)+f_m(a+k)\ge2m=k-1$ for every $a\in\mathbb Z$.

The consecutive-broadcast covering argument used in the source's
Theorem 3.6 applies here with the following inclusive integer endpoints.
Fix any $z\in\mathbb Z$ and any label $i\in\{1,\ldots,k\}$. Euclidean
division of $z-(i-1)$ by $k$ gives an integer $q$ and a remainder
$e\in\{0,\ldots,k-1\}$ such that

$$
a=i-1+qk,\qquad z=a+e,\qquad a\le z<a+k. \tag{10.11}
$$

Both $a$ and $a+k$ have label $i$ under the single map $c_m$.
If $e\le f_m(a)$, the original centre $a$ covers $z$. Otherwise the
integrality of $e$ gives $e\ge f_m(a)+1$, and hence

$$
|z-(a+k)|=k-e\le k-1-f_m(a)\le f_m(a+k). \tag{10.12}
$$

Thus the original centre $a+k$ covers $z$ in the other case. Equivalently,
the right endpoint $a+f_m(a)$ and the next left endpoint
$a+k-f_m(a+k)$ leave no missing integer, since the latter is at most
the former plus one. This includes equality in (10.10)'s lower bound,
$e=0$, and $e=k-1$. Division in (10.11) is valid also when $q<0$;
no half-line boundary or clipped broadcast is introduced. The same
$f_m$ determines every radius in (10.8)--(10.12), and every integer
remains a centre with its positive value. Since $z$ and $i$ were
arbitrary, this proves the second line of (10.4) for the one common
$c_m$ in (10.3).

Every odd integer $k\ge9$ is uniquely $2m+1$ with integer $m\ge4$,
so (10.4) proves $Q(k,k-1)$ on the entire claimed range. For (10.5),
the source parameter map is $u_a\leftrightarrow a$,
$d_{P_\infty}(u_a,u_b)=|a-b|$, the ordinary packing sequence
$S=(1,2,3,\ldots)$, palette bound $t=2m=k-1$, and partition sets
$A_i=c_m^{-1}(i)=(i-1)+k\mathbb Z$. A restricted broadcast is $f_m$
on $A_i$ and zero outside $A_i$, exactly as in the source's Section 1;
the single positive packing $f_m$ itself is unchanged. This is precisely
the interpretation of $Q$ in Definition 1.2.

The local supplier citations below use
[source version fe6e2625fb21b97e340cfc50244b975befaf7008](https://github.com/the-omega-institute/trureturing/tree/fe6e2625fb21b97e340cfc50244b975befaf7008).
The fixed-six predicate in
[`PackingDomaticInfiniteSix`](../../../D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.lean)
has the same full integer domain and radius convention, with $k=6$
and labels $0,\ldots,5$ instead of $1,\ldots,6$. Its private
`upperColour`, `upperClass`, and `five_exists` give the source's
six-class input; Theorem 9.2 gives the seven-class input. Neither is an
inductive premise for the construction (10.1)--(10.3). The finite-path
predicate in
[`PackingDomaticPathDefs`](../../../D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs.lean)
has domain $\operatorname{Fin}(n)$, rather than $\mathbb Z$.
Its endpoint-dependent bound
[`local_counting`](../../../D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting.lean)
and its application in
[`PackingDomaticPath`](../../../D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath.lean)
concern finite paths and supply no endpoint restriction on the present
whole-line witness. Likewise the finite interval decomposition cited
in Lemma 7.4 supplies covering classes once an adequate interval
multiplicity is given; here (10.10)--(10.12) supply the covering classes
explicitly for the packing whose same-colour gaps were proved above.
The additional infinite-family inference is the compatibility of this
packing with these common covering classes for every $m\ge4$.

The bound (10.5) contains no matching lower bound, and therefore no
assertion of the exact least palette for these odd values of $k$.
The construction has periods $T$ and $k$ for its two maps; no periodicity
condition is imposed on arbitrary witnesses of $Q$. The assertions
$Q(k,k-1)$ for even $k\ge8$, and consequently the assertion for every
integer $k\ge4$ in the source's Problem 3, remain outside this result.
$\square$

## 追加锚（本行以下为增补区）

## 11. Every even number of classes at least eight

**Definition 11.1 (Complementary blocks for an even class count).** Let
$m\ge4$ be an integer, put $k=2m$ and $T=2k=4m$, and define

$$
q_m=\begin{cases}m,&m\text{ even},\\m-1,&m\text{ odd},\end{cases}\qquad
r_m=\begin{cases}m+3,&m\text{ even},\\m+2,&m\text{ odd}.
\end{cases}
$$

For the even and odd cases respectively, let

$$
D_m=
\begin{cases}
\{2+2h:0\le h<(m-2)/2\}\cup\{m+1\}
 \cup\{m+4+2h:0\le h<(m-4)/2\},&m\text{ even},\\[2mm]
\{2+2h:0\le h<(m-3)/2\}\cup\{m\}
 \cup\{m+3+2h:0\le h<(m-3)/2\},&m\text{ odd}.
\end{cases}
$$

Write the members of $D_m$ increasingly as
$d_1<\cdots<d_{m-2}$. Define $F_m$ on the residues
$0,\ldots,T-1$ by

$$
\begin{aligned}
F_m(0)&=F_m(k)=2m-1,\\
F_m(1)&=m-1,&F_m(1+k)&=m,\\
F_m(q_m)&=m,&F_m(q_m+k)&=m-1,\\
F_m(r_m)&=m-1,&F_m(r_m+k)&=m,\\
F_m(d_j)&=j,&F_m(d_j+1)&=2m-1-j,\\
F_m(d_j+k)&=2m-1-j,&F_m(d_j+1+k)&=j
\qquad(1\le j\le m-2).
\end{aligned}
$$

For an integer $a$, let $R_T(a)$ and $R_k(a)$ be its Euclidean remainders
in $\{0,\ldots,T-1\}$ and $\{0,\ldots,k-1\}$, and put

$$
f_m(a)=F_m(R_T(a)),\qquad c_m(a)=1+R_k(a).
$$

Thus $c_m$ has the $k$ residue classes modulo $k$ as its classes.

**Theorem 11.2 (The original even-family upper bound).** For every integer
$m\ge4$, the maps in Definition 11.1 are well-defined and satisfy

$$
\begin{aligned}
u\ne v,\quad f_m(u)=f_m(v)=j&\Longrightarrow |u-v|\ge j+1,\\
\forall z\in\mathbb Z\ \forall i\in\{1,\ldots,2m\}\ \exists a\in\mathbb Z:
&\quad c_m(a)=i,\quad |z-a|\le f_m(a).
\end{aligned}
$$

Consequently $Q(k,k-1)$ of Definition 1.2 holds for every even integer
$k\ge8$. In the notation of Brešar--Ferme--Hu,
[*Partitioning an $S$-packing coloring into broadcast dominating sets*](https://arxiv.org/html/2610.03477v1),
Sections 1 and 3.2 and Problem 3 in Section 5, this gives
$\chi_{\rho,k}(P_\infty)\le k-1$ for every even $k\ge8$.

**Proof.** If $m$ is even, the exceptional positions in the first block
$[0,2m-1]\cap\mathbb Z$ are $\{0,1,m,m+3\}$, and their complement is the disjoint union

$$
[2,m-1]\cap\mathbb Z,\qquad [m+1,m+2]\cap\mathbb Z,\qquad
[m+4,2m-1]\cap\mathbb Z.
$$

Their lengths are $m-2$, $2$, and $m-4$, all even. Pairing consecutive
positions from the left endpoint gives exactly the pairs
$\{d_j,d_j+1\}$ in the even row of Definition 11.1. If $m$ is odd,
then $m\ge5$, the exceptional positions are $\{0,1,m-1,m+2\}$, and the complement is

$$
[2,m-2]\cap\mathbb Z,\qquad [m,m+1]\cap\mathbb Z,\qquad
[m+3,2m-1]\cap\mathbb Z.
$$

These lengths are $m-3$, $2$, and $m-3$, again all even, and consecutive
pairing gives the odd row. Hence the exceptional positions and the
$m-2$ pairs partition the first block. Translating by $k$ partitions the
second block, so every residue receives exactly one value. The assigned
values are $1,\ldots,2m-1$, all positive and at most $2m-1=k-1$.

It remains to check the packing. The value $2m-1$ occurs exactly at
$k\mathbb Z$, whose successive gaps are $k=2m$, the required value plus
one. For $1\le j\le m-2$, the complete occurrence sets of the two
values assigned to the pair beginning at $d_j$ are

$$
\begin{aligned}
\{a:f_m(a)=j\}&=\{d_j,d_j+1+k\}+T\mathbb Z,\\
\{a:f_m(a)=2m-1-j\}&=\{d_j+1,d_j+k\}+T\mathbb Z.
\end{aligned}
$$

Their cyclic gaps are respectively $k+1,k-1$ and $k-1,k+1$. Since
$k-1=2m-1\ge 2m-j$ for $j\ge1$, every such gap is at least one more
than either colour in its row.

The remaining occurrence sets are

$$
\{a:f_m(a)=m-1\}=\{1,r_m,q_m+k\}+T\mathbb Z,\qquad
\{a:f_m(a)=m\}=\{q_m,1+k,r_m+k\}+T\mathbb Z.
$$

For even $m$, their cyclic gap triples are

$$
(m+2,\,2m-3,\,m+1)\quad\text{and}\quad
(m+1,\,m+2,\,2m-3),
$$

while for odd $m$ they are

$$
(m+1,\,2m-3,\,m+2)\quad\text{and}\quad
(m+2,\,m+1,\,2m-3).
$$

Because $m\ge4$, every displayed gap is at least $m+1$. This is at
least one more than $m$, and hence also at least one more than $m-1$.
The listed occurrence sets exhaust all values, and any two distinct
members of one set are separated by a nonempty sum of its cyclic gaps.
Thus the packing inequalities hold across every period boundary and on
the whole integer line.

The assignments also give, for every integer $a$,

$$
f_m(a)+f_m(a+k)=
\begin{cases}
4m-2,&a\equiv0\pmod k,\\
2m-1,&a\not\equiv0\pmod k.
\end{cases}
\tag{11.1}
$$

In particular the sum is always at least $2m-1=k-1$. Fix $z\in\mathbb Z$
and a class label $i\in\{1,\ldots,k\}$. Euclidean division gives
integers $q$ and $e$ with $0\le e<k$ such that

$$
a=i-1+qk,\qquad z=a+e.
$$

Both $a$ and $a+k$ have class label $i$. If $e\le f_m(a)$, then $a$
covers $z$. Otherwise integrality gives $e\ge f_m(a)+1$, and (11.1)
implies

$$
|z-(a+k)|=k-e\le k-1-f_m(a)\le f_m(a+k).
$$

So $a+k$ covers $z$. This uses the original interval endpoints and the
same positive $f_m$ for every radius and every centre; negative $q$ and
the endpoint values $e=0,k-1$ are included in the same division. Since
$z$ and $i$ were arbitrary, the common covering condition in Definition
1.2 follows. Every even $k\ge8$ is $2m$ for an integer $m\ge4$, proving
the assertion. The source parameter map is
$u_a\leftrightarrow a$, $d_{P_\infty}(u_a,u_b)=|a-b|$, ordinary packing
sequence $S=(1,2,3,\ldots)$, palette $t=2m-1=k-1$, and partition classes
$c_m^{-1}(i)=(i-1)+k\mathbb Z$, exactly as in the source definition.
\square$

**Corollary 11.3 (The all-$k\ge4$ source consequence).** Combining the
published BFH $k=4,5,6$ upper assertions with Theorem 9.2 for $k=7$,
Theorem 10.2 for odd $k\ge9$, and Theorem 11.2 for even $k\ge8$ gives

$$
\forall k\in\mathbb Z,\quad k\ge4\Longrightarrow Q(k,k-1),
$$

and therefore

$$
\chi_{\rho,k}(P_\infty)\le k-1\qquad(k\ge4).
$$

Here the BFH input is its original whole-line definition and its exact
small-case assertions; the owner construction at $k=7$ is the same
whole-line $Q(7,6)$ realization of Theorem 9.2, and the two infinite
families use the same $f$ simultaneously for every class and every
integer position. The cited finite-path suppliers and the six-class
palette theorem concern different predicates or already-consumed cases;
no finite endpoint, least-palette, sharpness, extremizer, or periodicity
claim is added by this corollary.

## 追加锚（本行以下为增补区）
