# Higher-arity monotonicity for evil and odious sums

## 1. The representation functions

Let $\mathbb N=\{0,1,2,\ldots\}$. The Thue--Morse sequence is the map
$t:\mathbb N\to\{0,1\}$ determined by

$$
t_0=0,\qquad t_{2m}=t_m,\qquad t_{2m+1}=1-t_m.
$$

Write

$$
E=\{a\in\mathbb N:t_a=0\},\qquad
O=\{a\in\mathbb N:t_a=1\}.
$$

For $x\in\{r,s\}$, $k\geq1$, and $n\in\mathbb N$, define the literal ordered
representation counts

$$
\begin{aligned}
r_k(n)&=\#\{(a_1,\ldots,a_k)\in E^k:a_1+\cdots+a_k=n\},\\
s_k(n)&=\#\{(a_1,\ldots,a_k)\in O^k:a_1+\cdots+a_k=n\}.
\end{aligned}
$$

The coordinates are ordered, repetitions are allowed, and every coordinate is
nonnegative. Let $e$ and $o$ be the characteristic functions of $E$ and $O$.
The Thue--Morse recursion gives, for every $m$,

$$
e(2m)+e(2m+1)=1,\qquad o(2m)+o(2m+1)=1. \tag{1.1}
$$

The usual ordered-convolution identity (the last coordinate is separated from
the first $k$ coordinates) is

$$
x_{k+1}(n)=\sum_{j=0}^{n}a_x(j)x_k(n-j),\qquad
a_r=e,\quad a_s=o. \tag{1.2}
$$

This is the specialization of the ordered composition convolution in Sándor--Yang,
Lemma 4.2, to the supports $E$ and $O$. The same counting argument gives the
composition bound

$$
0\leq x_k(m)\leq\binom{m+k-1}{k-1}. \tag{1.3}
$$

The right side counts all ordered $k$-tuples of nonnegative integers with sum
$m$; thus (1.3) does not use any density assertion about $E$ or $O$.

The sixfold inequalities

$$
r_6(n+1)>r_6(n)\quad(n\geq37),\qquad
s_6(n+1)>s_6(n)\quad(n\geq5) \tag{1.4}
$$

are supplied by Allouche--Shallit, *Additive properties of the evil and odious
numbers and similar sequences*, arXiv:2112.13627v3, Conjecture 12 and its
settling sixfold result. Their generating-function identities and the
dyadic coefficient estimates are inputs here. Their analytic theorem for each
fixed $k\geq10$ is likewise an input and is not used as a separate assertion
below.

## 2. The finite-prefix correction

For an integer $u$, put $u_-:=\max\{0,-u\}$. If $f:\mathbb N\to\mathbb N$
and $R\in\mathbb N$, define the exact negative variation in the finite prefix by

$$
V_R(f):=\sum_{m=0}^{R-1}\bigl(f(m+1)-f(m)\bigr)_-. \tag{2.1}
$$

The empty sum is $0$. The next proposition keeps every early negative
difference in (2.1), including the endpoint $m=0$, instead of replacing the
prefix by an assumed monotone sequence.

**Proposition 2.1 (finite-prefix correction).** Let $k\geq1$, $R\geq0$, and
let $a:\mathbb N\to\{0,1\}$ satisfy

$$
a(2q)+a(2q+1)=1\qquad(q\in\mathbb N). \tag{2.2}
$$

Let $f:\mathbb N\to\mathbb N$ satisfy

$$
f(m)\leq\binom{m+k-1}{k-1}\quad(m\in\mathbb N),\qquad
f(m+1)-f(m)\geq1\quad(m\geq R). \tag{2.3}
$$

Define

$$
g(n):=\sum_{j=0}^{n}a(j)f(n-j),\qquad
B:=\binom{R+k-1}{k}.
$$

Then

$$
g(n+1)-g(n)\geq1
\qquad\text{for every }n\geq R+2B+1. \tag{2.4}
$$

**Proof.** First, (2.3) and $f(m+1)\geq0$ give

$$
\bigl(f(m+1)-f(m)\bigr)_-\leq f(m)\leq\binom{m+k-1}{k-1}.
$$

Summing and using the hockey-stick identity yields the fully quantified
finite-prefix estimate

$$
V_R(f)\leq\sum_{m=0}^{R-1}\binom{m+k-1}{k-1}
=\binom{R+k-1}{k}=B. \tag{2.5}
$$

For $n\geq R$, subtract the two convolution sums in the definition of $g$ and
retain the new endpoint term:

$$
\begin{aligned}
g(n+1)-g(n)
={}&a(n+1)f(0)\\
&+\sum_{m=0}^{R-1}a(n-m)\bigl(f(m+1)-f(m)\bigr)\\
&+\sum_{j=0}^{n-R}a(j)\bigl(f(n+1-j)-f(n-j)\bigr).
\end{aligned} \tag{2.6}
$$

The middle line is at least $-V_R(f)$. In the last line every difference is at
least $1$ by (2.3). Among the first $L=n-R+1$ integers, (2.2) puts exactly one
support point in each adjacent pair, so

$$
\sum_{j=0}^{n-R}a(j)\geq\left\lfloor\frac{L}{2}\right\rfloor. \tag{2.7}
$$

The endpoint in (2.6) is nonnegative. Combining (2.5)--(2.7), and using
$n\geq R+2B+1$, gives

$$
g(n+1)-g(n)\geq\left\lfloor\frac{n-R+1}{2}\right\rfloor-B
\geq(B+1)-B=1.
$$

This proves (2.4). ∎

## 3. The recursive quantitative consumer

Define, for $x\in\{r,s\}$,

$$
R_{r,6}=37,\qquad R_{s,6}=5, \tag{3.1}
$$

and recursively, for $k\geq6$,

$$
R_{x,k+1}=R_{x,k}+2\binom{R_{x,k}+k-1}{k}+1. \tag{3.2}
$$

**Theorem 3.1 (evil and odious higher-arity monotonicity).** For each
$x\in\{r,s\}$, every integer $k\geq6$, and every $n\geq R_{x,k}$,

$$
x_k(n+1)>x_k(n). \tag{3.3}
$$

The bounds in (3.1)--(3.2) are sufficient bounds depending on $k$; no common
threshold or sharpness assertion is part of the statement.

**Proof.** We first establish the evil branch, which is the new quantitative
consumer of Proposition 2.1. Assume $r_k(m+1)>r_k(m)$ for every
$m\geq R_{r,k}$. Apply Proposition 2.1 with

$$
a=e,\qquad f=r_k,\qquad R=R_{r,k}.
$$

Equation (1.1) supplies (2.2), equation (1.3) supplies the first part of
(2.3), and the induction hypothesis supplies its second part. By (1.2), the
resulting $g$ is $r_{k+1}$. Therefore

$$
r_{k+1}(n+1)>r_{k+1}(n)
\quad\left(n\geq R_{r,k}+2\binom{R_{r,k}+k-1}{k}+1\right),
$$

which is exactly the recurrence (3.2). The base case is the evil inequality
in (1.4), so induction proves (3.3) for $x=r$ and all $k\geq6$. In particular,

$$
R_{r,7}=37+2\binom{42}{6}+1
=38+2\binom{42}{6}. \tag{3.4}
$$

For the odious coordinate, we use the shifted support and the global propagation
input rather than introduce a separate odious theorem. Put

$$
B:=O-1=\{b\in\mathbb N:t_{b+1}=1\},\qquad
q_k(m):=\#\{(b_1,\ldots,b_k)\in B^k:b_1+\cdots+b_k=m\}.
$$

The coordinatewise bijection $a_i=b_i+1$ gives, for $n\geq k$,

$$
s_k(n)=q_k(n-k),\qquad s_k(k-1)=0,\qquad q_k(0)=1. \tag{3.5}
$$

The sixfold inequality in (1.4), including its endpoint at $n=5$, says via
(3.5) that $q_6(m+1)>q_6(m)$ for every $m\geq0$. Bell--Shallit,
arXiv:2212.12473v3, Remark 3, supplies the propagation fact that a set whose
ordered $q$-fold representation function is strictly increasing from $0$ has
the same property for every larger arity. Hence $q_k(m+1)>q_k(m)$ for every
$m\geq0$ and $k\geq6$. Translating back through (3.5) gives

$$
s_k(n+1)>s_k(n)\qquad(n\geq k-1). \tag{3.6}
$$

It remains only to compare the supplied odious range (3.6) with the requested
recursive bound. From (3.1)--(3.2), $R_{s,6}=5$ and
$R_{s,k+1}\geq R_{s,k}+1$; induction gives $R_{s,k}\geq k-1$. Thus (3.6)
implies (3.3) for $x=s$ whenever $n\geq R_{s,k}$. The first recursive value is

$$
R_{s,7}=5+2\binom{10}{6}+1=426. \tag{3.7}
$$

Both branches therefore satisfy the single combined conclusion (3.3). ∎

## 4. Scope of the cited inputs

The tuple convention, the Thue--Morse recursion, and the sixfold seed are those
of Allouche--Shallit, arXiv:2112.13627v3, equations (2)--(3) and Conjecture 12.
The convolution and composition estimates used in (1.2)--(1.3) are the ordered
composition estimates of Sándor--Yang, arXiv:2606.28849v1, Lemmas 4.2--4.3,
specialized here to $E$ and $O$. The only higher-arity propagation used in the
odious branch is Bell--Shallit, arXiv:2212.12473v3, Remark 3, applied after the
explicit shift in (3.5). The comparison is limited to these accessible source
versions; the publisher text associated with DOI 10.7169/facm/2108 and the
inaccessible monotonicity sequel DOI 10.1016/j.disc.2008.01.057 are not used as
additional premises.

## 5. 追加锚（本行以下为增补区）
