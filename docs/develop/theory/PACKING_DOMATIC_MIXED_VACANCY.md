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
