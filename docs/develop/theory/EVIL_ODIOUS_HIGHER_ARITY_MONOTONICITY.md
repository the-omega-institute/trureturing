# Higher-arity monotonicity for evil and odious sums

## 1. Ordered representations

**Definition 1.1 (supports and literal counts).** Put
$\mathbb N=\{0,1,2,\ldots\}$. Let $t:\mathbb N\to\{0,1\}$ be determined by

$$
t_0=0,\qquad t_{2m}=t_m,\qquad t_{2m+1}=1-t_m
\qquad(m\in\mathbb N),
$$

and define the evil and odious supports by

$$
E=\{a\in\mathbb N:t_a=0\},\qquad
O=\{a\in\mathbb N:t_a=1\}.
$$

For every integer $k\geq1$ and every $n\in\mathbb N$, set

$$
\begin{aligned}
r_k(n)&=\#\{(a_1,\ldots,a_k)\in E^k:a_1+\cdots+a_k=n\},\\
s_k(n)&=\#\{(a_1,\ldots,a_k)\in O^k:a_1+\cdots+a_k=n\}.
\end{aligned}
$$

Coordinates are ordered and repetitions are allowed. These are the conventions
of Allouche--Shallit, [*Additive properties of the evil and odious numbers and
similar sequences*, arXiv:2112.13627v3](https://arxiv.org/pdf/2112.13627v3),
equations (2)--(3). Write $a_r=\mathbf1_E$ and $a_s=\mathbf1_O$. For
$x\in\{r,s\}$ the defining recursion gives

$$
a_x(2q)+a_x(2q+1)=1\qquad(q\in\mathbb N). \tag{1.1}
$$

We use the standard ordered-convolution and composition-count inputs from
Sándor--Yang, [*On the monotonicity of higher-fold representation functions*,
arXiv:2606.28849v1](https://arxiv.org/pdf/2606.28849v1), Lemmas 4.2--4.3:

$$
x_{k+1}(n)=\sum_{j=0}^{n}a_x(j)x_k(n-j),\qquad
0\leq x_k(n)\leq\binom{n+k-1}{k-1}. \tag{1.2}
$$

Here the convolution follows by fixing the last coordinate $j$ of the ordered
tuple. For the bound, the unrestricted nonnegative $k$-tuples with sum $n$
are in bijection with placements of $k-1$ separators among $n+k-1$ positions;
restricting their coordinates to $E$ or $O$ cannot increase their number.
For $k=1$ there are no separators and the unrestricted count is $1$.
These inputs concern ordered tuples, including the endpoint $j=n$.

## 2. Correction for a finite prefix

**Definition 2.1 (integer differences and prefix variation).** For
$f:\mathbb N\to\mathbb N$, regard its values as integers when taking

$$
\delta f(m)=f(m+1)-f(m)\in\mathbb Z.
$$

For $u\in\mathbb Z$ put $u_-:=\max\{0,-u\}$. For $R\in\mathbb N$ define

$$
V_R(f)=\sum_{m=0}^{R-1}(\delta f(m))_-.
$$

An empty sum is $0$. For nonnegative integers $u,v$ use $\binom uv=0$ when
$v>u$. All subtractions below are in $\mathbb Z$.

**Proposition 2.2 (quantified finite-prefix correction).** Let
$a:\mathbb N\to\{0,1\}$, $f:\mathbb N\to\mathbb N$, and $R\in\mathbb N$.
Suppose that

$$
a(2q)+a(2q+1)=1\quad(q\in\mathbb N),\qquad
\delta f(m)\geq1\quad(m\in\mathbb N,\ m\geq R).
$$

Define $g:\mathbb N\to\mathbb N$ by

$$
g(n)=\sum_{j=0}^{n}a(j)f(n-j).
$$

Then, for every integer $n\geq R$, the following identity and inequalities hold:

$$
\begin{aligned}
\delta g(n)
={}&a(n+1)f(0)
  +\sum_{m=0}^{R-1}a(n-m)\delta f(m)
  +\sum_{j=0}^{n-R}a(j)\delta f(n-j)\\
\geq{}&a(n+1)f(0)
  +\left\lfloor\frac{n-R+1}{2}\right\rfloor
  -\sum_{m=0}^{R-1}a(n-m)(\delta f(m))_-\\
\geq{}&a(n+1)f(0)
  +\left\lfloor\frac{n-R+1}{2}\right\rfloor-V_R(f).
\end{aligned} \tag{2.1}
$$

In particular, $\delta g(n)\geq1$ for every
$n\geq R+2V_R(f)+1$. If in addition an integer $k\geq1$ satisfies

$$
f(m)\leq\binom{m+k-1}{k-1}\qquad(m\in\mathbb N),
$$

then

$$
V_R(f)\leq\binom{R+k-1}{k},\qquad
\delta g(n)\geq1\quad
\left(n\geq R+2\binom{R+k-1}{k}+1\right). \tag{2.2}
$$

Proof. Subtract the convolution at $n$ from that at $n+1$. The new summand
$j=n+1$ must be retained, giving

$$
\delta g(n)=a(n+1)f(0)+\sum_{j=0}^{n}a(j)\delta f(n-j).
$$

For $n\geq R$, the indices with $n-j<R$ are precisely
$j=n-R+1,\ldots,n$. Reindex these by $m=n-j$ to obtain the identity
in (2.1). This partition includes $m=0$ in the prefix whenever $R>0$,
and includes $m=R$ in the tail. When $R=0$ the prefix is empty and the
tail is the whole sum, so the same identity holds.

For each prefix index, $0\leq a(n-m)\leq1$ and
$\delta f(m)\geq-(\delta f(m))_-$. Therefore its total contribution is at
least the negative of the weighted prefix sum in (2.1). No early negative
difference is discarded. The tail has $\delta f(n-j)\geq1$ for every
$0\leq j\leq n-R$. If $L=n-R+1$, the integers $0,\ldots,L-1$ contain
$\lfloor L/2\rfloor$ complete pairs $(2q,2q+1)$, and possibly one further
even integer. Each complete pair has $a$-sum $1$, and the remaining value
is nonnegative. Consequently

$$
\sum_{j=0}^{n-R}a(j)\geq\left\lfloor\frac{n-R+1}{2}\right\rfloor.
$$

The weighted prefix sum is at most $V_R(f)$, proving both inequalities in
(2.1). Since $a(n+1)f(0)\geq0$, if $n\geq R+2V_R(f)+1$ then

$$
\delta g(n)\geq
\left\lfloor\frac{2V_R(f)+2}{2}\right\rfloor-V_R(f)=1.
$$

For the additional conclusion, nonnegativity of $f(m+1)$ gives

$$
(\delta f(m))_-\leq f(m)\leq\binom{m+k-1}{k-1}.
$$

Thus the classical cumulative composition count yields

$$
V_R(f)\leq\sum_{m=0}^{R-1}\binom{m+k-1}{k-1}
=\binom{R+k-1}{k}. \tag{2.3}
$$

For completeness, when $R=0$ both sides of the equality are $0$; increasing
$R$ by $1$ adds $\binom{R+k-1}{k-1}$ to the sum, and Pascal's identity adds
the same amount to $\binom{R+k-1}{k}$. This proves the equality for every
$R\geq0$, including $k=1$. Substitution into (2.1) proves (2.2). $\square$

## 3. The higher-arity quantitative consequence

**Definition 3.1 (recursive sufficient bounds).** For $x\in\{r,s\}$ set

$$
R_{r,6}=37,\qquad R_{s,6}=5,
$$

and for every integer $k\geq6$ define

$$
R_{x,k+1}=R_{x,k}+2\binom{R_{x,k}+k-1}{k}+1. \tag{3.1}
$$

**Theorem 3.2 (evil and odious counts at every higher arity).** For every
$x\in\{r,s\}$, every integer $k\geq6$, and every integer $n\geq R_{x,k}$,

$$
x_k(n+1)>x_k(n). \tag{3.2}
$$

The first recursive bounds are

$$
R_{r,7}=38+2\binom{42}{6},\qquad R_{s,7}=426. \tag{3.3}
$$

The bounds depend on $k$ and are sufficient; the statement makes no assertion
of a common threshold or of sharpness.

Proof. The supplied sixfold result is

$$
r_6(n+1)>r_6(n)\quad(n\geq37),\qquad
s_6(n+1)>s_6(n)\quad(n\geq5). \tag{3.4}
$$

We use (3.4) from the repository's
[SixfoldMonotonicity.result](https://github.com/the-omega-institute/trureturing/blob/84ebe63b875f6ca10d1b4d7aefb68a24ce0ff80f/D5/S1/Words/EvilOdious/SixfoldMonotonicity.lean),
whose literal counts are those of Definition 1.1. The thresholds are the
clauses of Allouche--Shallit, arXiv:2112.13627v3, Conjecture 12; that
conjecture is the source of the statements, rather than a proof of (3.4).

First fix the evil support. The case $k=6$ of (3.2) is (3.4). Suppose for
an integer $k\geq6$ that $r_k(m+1)>r_k(m)$ for every $m\geq R_{r,k}$.
Since the counts are integers, $\delta r_k(m)\geq1$ on that entire tail.
Apply Proposition 2.2 with

$$
a=\mathbf1_E,\qquad f=r_k,\qquad R=R_{r,k}.
$$

The pair condition is (1.1) and the composition bound is (1.2).
The convolution $g$ is exactly $r_{k+1}$ by (1.2). Consequently

$$
\delta r_{k+1}(n)\geq
\left\lfloor\frac{n-R_{r,k}+1}{2}\right\rfloor
-V_{R_{r,k}}(r_k)\geq1
\qquad(n\geq R_{r,k+1}), \tag{3.5}
$$

because

$$
V_{R_{r,k}}(r_k)\leq\binom{R_{r,k}+k-1}{k}.
$$

This proves the induction step and hence the evil branch for every $k\geq6$.
The finite-prefix correction (2.1), applied in (3.5), is the additional
inference beyond the cited convolution and counting inputs. In particular,
it does not assume that the evil counts increase below $R_{r,k}$.

For the odious branch use the classical global propagation of Bell--Shallit,
[*Counterexamples to a conjecture of Dombi in additive number theory*,
arXiv:2212.12473v3](https://arxiv.org/pdf/2212.12473v3), Remark 3, with the
following explicit shift. Since $t_0=0$ and $t_1=1$, $O$ has minimum $1$.
Put

$$
B=O-1=\{b\in\mathbb N:t_{b+1}=1\},\qquad
q_k(m)=\#\{(b_1,\ldots,b_k)\in B^k:b_1+\cdots+b_k=m\}
\quad(m\in\mathbb N).
$$

The coordinatewise bijection $a_i=b_i+1$ gives, for every $k\geq1$,

$$
s_k(n)=0\ (0\leq n<k),\qquad
s_k(n)=q_k(n-k)\ (n\geq k),\qquad q_k(0)=1. \tag{3.6}
$$

Indeed every odious coordinate is at least $1$, and $0\in B$; the unique
nonnegative tuple with sum $0$ is the zero tuple. From (3.4) at
$n=m+6$ we get

$$
q_6(m+1)>q_6(m)\qquad(m\in\mathbb N).
$$

Thus the shifted sixfold counts are strictly increasing from $0$, as required
by Bell--Shallit's propagation. To spell out that supplied implication with
its endpoint, let $b=\mathbf1_B$. If $\delta q_k(m)\geq1$ for all $m\geq0$,
the classical difference-convolution identity gives

$$
\delta q_{k+1}(m)=b(m+1)q_k(0)
 +\sum_{j=0}^{m}b(j)\delta q_k(m-j)\geq\delta q_k(m)\geq1,
$$

because $b(0)=1$ and all the other summands are nonnegative. Induction gives
this global strictness for every $k\geq6$. For $n\geq k$ translate by
$m=n-k$ in (3.6); for $n=k-1$ use
$s_k(k)=q_k(0)=1>0=s_k(k-1)$. Hence the cited propagation supplies the
stronger odious range

$$
s_k(n+1)>s_k(n)\qquad(k\geq6,\ n\geq k-1). \tag{3.7}
$$

It is an intermediate consequence of that classical supply, rather than a
separate higher-arity assertion here. As $R_{s,6}=5$ and
$R_{s,k+1}\geq R_{s,k}+1$, induction gives $R_{s,k}\geq k-1$.
Thus (3.7) implies the required odious branch of (3.2) for all
$n\geq R_{s,k}$. Formula (3.1) also gives

$$
R_{r,7}=37+2\binom{37+5}{6}+1=38+2\binom{42}{6},\qquad
R_{s,7}=5+2\binom{5+5}{6}+1=5+2\cdot210+1=426.
$$

For the relation with the other cited higher-arity input,
Allouche--Shallit's Theorem 10 already supplies qualitative eventual strictness
for every fixed $k\geq10$. Its hypothesis holds for the Thue--Morse signs
with exponent $\alpha=\log3/\log4$ (as used in its Corollary 11), and
$k>2/(1-\alpha)$ holds for all $k\geq10$, since $3^5<4^4$ implies
$\alpha<4/5$. Its positive-coordinate supports
are $E+1$ and $O+1$: adding $1$ to each coordinate raises a $k$-tuple sum by
$k$. In the notation $r(k,L,N)$ of that paper the exact correspondence is

$$
r(k,E+1,n+k)=r_k(n),\qquad r(k,O+1,n+k)=s_k(n).
$$

That qualitative range and the whole odious propagation above are cited
inputs. The quantitative evil conclusion uses the finite-prefix correction
and the supplied sixfold seed as shown in (3.5). $\square$

## 追加锚（本行以下为增补区）
