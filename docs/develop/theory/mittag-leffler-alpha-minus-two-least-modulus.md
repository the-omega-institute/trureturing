# The negative least-modulus zero of $E_{\alpha,\alpha-2}(-z)$

## 1. Definitions and the least-modulus question

**Definition 1.1 (Mittag–Leffler function).** For real $\alpha>0$ and
$\beta\in\mathbb R$, write

$$
E_{\alpha,\beta}(w)
 =\sum_{k=0}^{\infty}\frac{w^k}{\Gamma(\alpha k+\beta)},
\qquad w\in\mathbb C.
\tag{1}
$$

At a pole of $\Gamma$, its reciprocal is interpreted by the entire
extension of $1/\Gamma$. This is the definition in Li–Morgan–Siegrist
[LMS, §6, equation (26)]. For fixed parameters the series defines an
entire function of $w$; in particular, it converges absolutely at every
complex argument and uniformly on compact subsets. This analyticity
is also a supplied property of the source function.

**Definition 1.2 (Order and first positive real zero).** Throughout,
$\alpha$ is real and $1<\alpha<2$. Set

$$
f_\alpha(z)=E_{\alpha,\alpha-2}(-z),
\qquad
\lambda(\alpha)=\min\{t>0:f_\alpha(t)=0\}.
\tag{2}
$$

In the notation of [LMS, Theorem 6.3, PDF pp. 39–40], the order
$\alpha$ is suppressed in

$$
\lambda_\beta=\inf\{t>0:E_{\alpha,\beta}(-t)=0\}.
$$

Thus $\lambda(\alpha)=\lambda_{\alpha-2}$. The existence of this first
positive real zero is supplied by [LMS, Theorem 6.2 and the proof of
Theorem 6.3]. Theorem 6.3 also supplies the ordering

$$
\lambda_{\alpha-1}<\lambda_{\alpha-2}<\lambda_\alpha.
$$

These positive-zero results are credited inputs. Only the existence
and positivity of $\lambda(\alpha)$ are needed for the comparison
with a negative real zero below.

**Definition 1.3 (Zero of least modulus).** A zero $\zeta$ of an entire
function $h$ is a zero of least modulus if $|\zeta|\leq |z|$ for every
$z\in\mathbb C$ with $h(z)=0$. The least-modulus question in [LMS,
PDF p. 40, the paragraph immediately preceding the proof of
Theorem 6.3] asks whether the first positive real zero
$\lambda_{\alpha-2}$ has this property for $f_\alpha$. For a fixed
$\alpha\in(1,2)$, the property in question is

$$
\forall z\in\mathbb C,\qquad
f_\alpha(z)=0\ \Longrightarrow\ \lambda(\alpha)\leq |z|.
\tag{3}
$$

Here the minimum in (2) is over positive real zeros, whereas the
comparison in (3) is with all complex zeros of the same function.

## 2. The least-modulus zero and its equality case

**Theorem 2.1 (Negative least-modulus zero).** For every real
$\alpha\in(1,2)$ there is a unique $r_\alpha>0$ such that
$E_{\alpha,\alpha-2}(r_\alpha)=0$. The number $-r_\alpha$ is a zero
of $f_\alpha$, and for every $z\in\mathbb C$,

$$
f_\alpha(z)=0\ \Longrightarrow\ |z|\geq r_\alpha.
\tag{4}
$$

Among the zeros of $f_\alpha$, equality in (4) holds if and only if
$z=-r_\alpha$. Moreover, the first positive real zero in (2) satisfies

$$
0<r_\alpha<\lambda(\alpha).
\tag{5}
$$

**Proof.** Fix $1<\alpha<2$. The Euler integral for $\Gamma$ gives
$\Gamma(x)>0$ for $x>0$ [G, equation (5.2.1)]. Applying the recurrence
$\Gamma(x+1)=x\Gamma(x)$ [G, equation (5.5.1)] at $x=\alpha-2$
gives

$$
\frac{1}{\Gamma(\alpha-2)}
 =\frac{\alpha-2}{\Gamma(\alpha-1)}<0.
\tag{6}
$$

Define

$$
c_\alpha=\frac{2-\alpha}{\Gamma(\alpha-1)},
\qquad
 a_{\alpha,k}=\frac{1}{\Gamma((k+1)\alpha-2)}\quad(k\geq1).
$$

Then $c_\alpha>0$. For $k\geq1$,
$(k+1)\alpha-2\geq2\alpha-2>0$, so $a_{\alpha,k}>0$.
The constant-term argument $\alpha-2$ lies in $(-1,0)$, and all
subsequent gamma arguments are positive, so none of these arguments
is a pole. Consequently (1), with $\beta=\alpha-2$, reads

$$
E_{\alpha,\alpha-2}(w)
 =-c_\alpha+\sum_{k=1}^{\infty}a_{\alpha,k}w^k.
\tag{7}
$$

For $t\geq0$, let

$$
A_\alpha(t)=\sum_{k=1}^{\infty}a_{\alpha,k}t^k.
$$

The compact uniform convergence in Definition 1.1 makes $A_\alpha$
continuous. It satisfies $A_\alpha(0)=0$ and is strictly increasing.
Indeed, if $0\leq s<t$, absolute convergence permits subtraction
of the series, giving

$$
A_\alpha(t)-A_\alpha(s)
 =\sum_{k=1}^{\infty}a_{\alpha,k}(t^k-s^k)
 \geq a_{\alpha,1}(t-s)>0.
\tag{8}
$$

Also $A_\alpha(t)\geq a_{\alpha,1}t$, so $A_\alpha(t)$ tends to
infinity as $t$ tends to infinity. Since $c_\alpha>0$, the intermediate
value theorem and strict monotonicity yield a unique $r_\alpha>0$
with

$$
A_\alpha(r_\alpha)=c_\alpha.
\tag{9}
$$

Equation (7) proves that this is exactly the unique positive real
zero of $E_{\alpha,\alpha-2}(w)$. It also gives
$f_\alpha(-r_\alpha)=0$.

Now let $z\in\mathbb C$ be any zero of $f_\alpha$ and set $w=-z$.
Equation (7) gives

$$
c_\alpha=\sum_{k=1}^{\infty}a_{\alpha,k}w^k.
\tag{10}
$$

Absolute convergence justifies the triangle inequality for this
infinite series. Since $|w|=|z|$,

$$
c_\alpha
 =\left|\sum_{k=1}^{\infty}a_{\alpha,k}w^k\right|
 \leq\sum_{k=1}^{\infty}a_{\alpha,k}|w|^k
 =A_\alpha(|z|).
\tag{11}
$$

Combining (9), (11), and strict monotonicity gives
$|z|\geq r_\alpha$, proving (4).

To determine the equality case, suppose $|z|=r_\alpha$, so
$|w|=r_\alpha$. Taking real parts in (10) and subtracting from (9)
yields

$$
0=\sum_{k=1}^{\infty}
 a_{\alpha,k}\bigl(r_\alpha^k-\operatorname{Re}(w^k)\bigr).
\tag{12}
$$

This subtraction is justified by absolute convergence: the absolute
value of the $k$th summand is at most
$2a_{\alpha,k}r_\alpha^k$. Every summand is nonnegative, because
$\operatorname{Re}(w^k)\leq |w^k|=r_\alpha^k$. A sum of nonnegative
terms can be zero only if each term is zero. In particular, its first
term and $a_{\alpha,1}>0$ give
$\operatorname{Re}w=r_\alpha$. Together with $|w|=r_\alpha$, this
forces $w=r_\alpha$, hence $z=-r_\alpha$. Conversely,
$-r_\alpha$ is already known to be a zero of modulus $r_\alpha$.
This proves the full equality assertion.

Finally, the credited positive-zero existence in Definition 1.2
ensures that $\lambda(\alpha)>0$ is a zero of $f_\alpha$. Applying
(4) gives $\lambda(\alpha)\geq r_\alpha$. Equality would force
$\lambda(\alpha)=-r_\alpha$ by the equality assertion, contradicting
positivity. Thus $\lambda(\alpha)>r_\alpha$, proving (5).
$\square$

**Theorem 2.2 (Answer to the first-positive-zero question).** For
every real $\alpha\in(1,2)$, the first positive real zero
$\lambda(\alpha)$ of $E_{\alpha,\alpha-2}(-z)$ is not a zero of
least modulus. More precisely, for each such $\alpha$ there is a
complex zero $z=-r_\alpha$ of that same function such that

$$
E_{\alpha,\alpha-2}(-z)=0,
\qquad |z|=r_\alpha<\lambda(\alpha).
\tag{13}
$$

In particular, the universal statement

$$
\forall\alpha\in(1,2)\ \forall z\in\mathbb C,\qquad
E_{\alpha,\alpha-2}(-z)=0
 \ \Longrightarrow\ \lambda(\alpha)\leq |z|
$$

is false.

**Proof.** For an arbitrary $\alpha\in(1,2)$, Theorem 2.1 supplies
$r_\alpha>0$. With $z=-r_\alpha$ one has
$-z=r_\alpha$, so $E_{\alpha,\alpha-2}(-z)=0$ and
$|z|=r_\alpha<\lambda(\alpha)$. This contradicts (3) for each
$\alpha$ in the stated interval. The substitution $w=-z$ preserves
modulus, so the positive root of $E_{\alpha,\alpha-2}(w)$ used in
the proof is a negative root of precisely the function appearing in
the question. The equality assertion in Theorem 2.1 also excludes
any other zero on the circle $|z|=r_\alpha$. All these conclusions
hold on the open interval $1<\alpha<2$; neither endpoint is included.
$\square$

## 3. Mathematical references

[LMS] Yulong Li, Rachel Morgan and Michael Siegrist,
*Concavity structure of fractional differential equations and zeros
of Mittag–Leffler functions*, The Journal of Analysis,
[DOI 10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9),
[publisher PDF](https://link.springer.com/content/pdf/10.1007/s41478-026-01192-9.pdf).
The function and its analyticity are supplied in §6, equation (26).
Theorem 6.2 supplies positive-zero existence; Theorem 6.3, whose
statement spans PDF pp. 39–40, gives the notation and ordering of
the first positive real zeros. The least-modulus question is the
paragraph on PDF p. 40 between the statement and proof of
Theorem 6.3. It concerns all complex zeros and is distinct from
Conjecture 6.1 on PDF p. 43, concerning uniqueness of a concavity
transition. Theorems 2.1–2.2 use the supplied existence input and
the series definition to prove the least-modulus comparison.

[G] NIST Digital Library of Mathematical Functions,
[§5.2, equation (5.2.1)](https://dlmf.nist.gov/5.2.E1), the Euler
integral for $\Gamma$, and
[§5.5, equation (5.5.1)](https://dlmf.nist.gov/5.5.E1), the recurrence
$\Gamma(x+1)=x\Gamma(x)$.

## 追加锚（本行以下为增补区）
