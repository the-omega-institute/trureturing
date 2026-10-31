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
