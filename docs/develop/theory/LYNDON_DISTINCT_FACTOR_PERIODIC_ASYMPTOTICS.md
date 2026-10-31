# Distinct contiguous Lyndon factors: periodic asymptotics

## 1. Words, expectation, and notation

**Definition 1.1 (The random word and its statistic).** Fix an integer
$q\geq2$ and a totally ordered alphabet $\mathcal A$ of exactly $q$
letters. For each integer $n\geq0$, let $W_n$ be uniform on
$\mathcal A^n$; equivalently, its letters are independent and uniform on
$\mathcal A$. The lexicographic order on finite words puts a proper
prefix before the word containing it. A word $w$ is Lyndon if it is
nonempty and $w<vu$ whenever $w=uv$ with $u,v$ nonempty. Let

$$
D(W_n)=\#\{w:\ w\text{ is Lyndon and }W_n=xwy
                   \text{ for some finite words }x,y\},
\qquad E_D(q,n)=\mathbb E D(W_n).
$$

Thus factors are contiguous, equal factor words are counted once, and
letters are included. The empty word is excluded; a whole word is
included exactly when it is Lyndon. In particular, $E_D(q,0)=0$.

These are the factor and distinctness conventions in Glen, Simpson, and
Smyth, *Counting Lyndon factors*, arXiv:1701.00928v1, §§1 and 4,
pp. 1–2 and 4–5, [equation (6)](https://arxiv.org/pdf/1701.00928v1).
Their $\sigma$ is $q$ and their $E_D(\sigma,n)$ is precisely the
expectation defined here. The same quantity is $E_{DF}(\sigma,n)$ in
Hirakawa, Nakashima, Inenaga, and Takeda, *Counting Lyndon Subsequences*,
arXiv:2106.01190v2, Table 1, p. 2
([exact version](https://arxiv.org/pdf/2106.01190v2)); its subsequence
quantities in Table 2 are different statistics.

The rotation predicate also agrees with `IsLyndon` in
[LyndonOrder](https://github.com/the-omega-institute/trureturing/blob/455f91f2040f1cc940bce4cd333b6c21ab61a2e6/D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.lean),
and the set of factor words agrees with `distinctLyndon` in
[LyndonFactorChristoffelMinimumRefutation](https://github.com/the-omega-institute/trureturing/blob/455f91f2040f1cc940bce4cd333b6c21ab61a2e6/D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.lean):
a position starts at zero, a factor has length $m\geq1$, and its
starting position $i$ satisfies $i+m\leq n$. The alphabet $\mathcal A$
is carried to `Fin q` by its increasing bijection. That bijection
preserves rotations, order, contiguous occurrences, equality of words,
and the uniform law, so it preserves $E_D$.

**Definition 1.2 (Analytic notation).** All logarithms are natural except
$\log_q x=(\log x)/(\log q)$. Write

$$
\alpha=\log q>0,\qquad t=\log_q n,\qquad
\{x\}=x-\lfloor x\rfloor,\qquad
H_k=\sum_{m=1}^k\frac1m\quad(k\geq1),
$$

and put $H_k=0$ for integers $k\leq0$.
Euler's constant is $\gamma=\lim_{k\to\infty}(H_k-\log k)$.
For $\operatorname{Re}z>0$ set
$\Gamma(z)=\int_0^\infty e^{-x}x^{z-1}\,dx$, using the real logarithm
in the power. The Bernoulli polynomials $B_r$ have normalization

$$
\frac{ze^{uz}}{e^z-1}=\sum_{r=0}^{\infty}B_r(u)\frac{z^r}{r!}
\quad (|z|<2\pi),\qquad B_1(u)=u-\frac12.
$$

An $O_{q,R}$ constant may depend on the fixed integers $q,R$ only.
The variable tending to infinity is the integer $n$; neither $q$ nor
$R$ varies with $n$.

## 2. An analytic expression for this expectation

**Proposition 2.1 (Removing the finite-word occurrence corrections).**
For $x>0$ define

$$
f(x)=x-1+e^{-x},\qquad
F_q(n)=\sum_{m=1}^{\infty}\frac{q^m}{m}f(nq^{-m}).
$$

The sum converges for every real $n>0$. For each fixed integer $q\geq2$,
as integer $n\to\infty$,

$$
E_D(q,n)=(n+1)H_n-n-F_q(n)
            +O_q(\sqrt n+\log n).                                      \tag{2.1}
$$

*Proof.* Let $L_m$ be the number of Lyndon words of length $m$.
The primitive-conjugacy count in GSS-v1, §3, p. 3, gives

$$
L_m=\frac1m\sum_{d\mid m}\mu(m/d)q^d.
$$

We need its elementary estimate, with its sign. There is exactly one
Lyndon representative in each primitive conjugacy class and each such
class has $m$ elements. Every nonprimitive word of length $m$ is a
power of a word of length at most $\lfloor m/2\rfloor$. Consequently

$$
0\leq \frac{q^m}{m}-L_m
 \leq \frac1m\sum_{d=1}^{\lfloor m/2\rfloor}q^d
 \leq C_q\frac{q^{m/2}}m,\qquad L_m\leq\frac{q^m}{m}.                    \tag{2.2}
$$

The sum on the middle right is empty when $m=1$; thus letters are
covered as well.

A Lyndon word has no nonempty proper border. Indeed, the suffix
characterization says it is strictly smaller than each nonempty proper
suffix, while a proper prefix is strictly smaller than the word itself.
A border would give both inequalities in opposite directions.
The suffix characterization is GSS-v1, §1, p. 2, and is exactly
`isLyndon_iff_lt_suffix` in the cited complete `LyndonOrder` source.
Thus two occurrences of the same Lyndon word of length $m$ cannot have
starting positions at distance $1,\ldots,m-1$: their overlap would
supply a border of length $m$ minus that distance.

Fix such a word $w$, with $1\leq m\leq n$. Put
$N=n-m+1$, $p=q^{-m}$, and $\lambda=Np$. For
$i\in\{0,\ldots,N-1\}$ let $X_i$ indicate an occurrence at position $i$.
Then $\mathbb E X_i=p$. Use the dependence neighborhoods

$$
B_i=\{j\in\{0,\ldots,N-1\}:|i-j|<m\}.
$$

Each $X_i$ is independent of the sigma-algebra generated by the
$X_j$ outside $B_i$, since all those windows use letters outside its
own window. For $j\in B_i\setminus\{i\}$ the product $X_iX_j$ is zero
by borderlessness. In the notation of Arratia, Goldstein, and Gordon,
*Two moments suffice for Poisson approximations: the Chen–Stein method*,
Ann. Probab. **17** (1989), 9–25, §2, Theorem 1, p. 11
([complete original](https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/AGG-1.pdf)),
we therefore have

$$
b_1\leq N(2m-1)p^2,\qquad b_2=0,\qquad b_3=0.
$$

All its hypotheses hold: the index set is finite, the $X_i$ are
Bernoulli with $p>0$, each neighborhood contains its index, and
$0<\lambda<\infty$. The zero-event part of that theorem, rather than
its differently normalized total-variation inequality, gives

$$
\begin{aligned}
\left|\mathbb P(w\text{ occurs})-(1-e^{-\lambda})\right|
 &\leq b_1\frac{1-e^{-\lambda}}{\lambda}\\
 &\leq(2m-1)p\min(1,\lambda).
\end{aligned}                                                          \tag{2.3}
$$

This includes $m=1$, when the neighborhoods are singletons.

Linearity applied to indicators of distinct factor words gives
$E_D(q,n)=\sum_{m=1}^n\sum_{w\text{ Lyndon},\ |w|=m}
\mathbb P(w\text{ occurs})$.
By (2.2)–(2.3), replacing each probability by $1-e^{-Nq^{-m}}$
costs at most

$$
2\sum_{m=1}^n\min(1,nq^{-m})=O_q(1+\log n).                            \tag{2.4}
$$

To see the estimate explicitly, split at $k=\lfloor\log_q n\rfloor$.
The part $m\leq k$ is at most $k$ and the rest is at most
$nq^{-k-1}/(1-q^{-1})\leq(1-q^{-1})^{-1}$.

Next replace $L_m$ by $q^m/m$. Since $1-e^{-Np}\leq\min(1,np)$,
the additional absolute error, using (2.2), is bounded by

$$
C_q\left(\sum_{m\leq k}\frac{q^{m/2}}m
       +n\sum_{m>k}\frac{q^{-m/2}}m\right)=O_q(\sqrt n).                \tag{2.5}
$$

For this last estimate it suffices to drop $1/m$ and sum two geometric
series; $q^k\leq n<q^{k+1}$. Thus

$$
E_D(q,n)=\sum_{m=1}^n\frac{q^m}{m}
                  (1-e^{-(n-m+1)q^{-m}})+O_q(\sqrt n+\log n).           \tag{2.6}
$$

For clarity, retain the boundary $n-m+1$ before replacing it. From
$1-e^{-x}=x-f(x)$ the main sum in (2.6) is exactly

$$
(n+1)H_n-n-\sum_{m=1}^n\frac{q^m}{m}
                                  f((n-m+1)q^{-m}).                    \tag{2.7}
$$

We have $f'(x)=1-e^{-x}$ and $0\leq f'(x)\leq\min(1,x)$ for $x\geq0$.
The mean value estimate therefore gives

$$
0\leq\frac{q^m}{m}
 \bigl[f(nq^{-m})-f((n-m+1)q^{-m})\bigr]
 \leq\frac{m-1}{m}\min(1,nq^{-m}).                                     \tag{2.8}
$$

Summing (2.8) costs only $O_q(1+\log n)$ by (2.4).
Finally $0\leq f(x)\leq x^2/2$ for $x\geq0$, since
$f(x)=\int_0^x(1-e^{-u})\,du$. This proves convergence of $F_q$ and
bounds the missing tail by

$$
0\leq\sum_{m>n}\frac{q^m}{m}f(nq^{-m})
 \leq\frac{n^2}{2(n+1)}\sum_{m>n}q^{-m}=O_q(nq^{-n}).
$$

Inserting these bounds in (2.7) proves (2.1). In particular the term
$-n$ in (2.1) retains the finite-word boundary contribution. $\square$

## 3. Coefficients and the full fixed-order expansion

**Definition 3.1 (The coefficient functions).** For $x>0$ set

$$
A(x)=\frac{f(x)}x=1-\frac{1-e^{-x}}x
     =1-\int_0^1 e^{-ux}\,du.
$$

For $v\in\mathbb R$ define

$$
K_q(v)=\frac{d}{dv}A(q^v)
 =\alpha q^v\int_0^1u e^{-uq^v}\,du
 =\alpha\frac{1-(1+q^v)e^{-q^v}}{q^v}.                                \tag{3.1}
$$

For every integer $r\geq1$ and real $\theta$, define

$$
\Phi_{q,r}(\theta)=\frac1r\int_{-\infty}^{\infty}
      K_q(v)B_r\bigl(v+\{\theta-v\}\bigr)\,dv.                         \tag{3.2}
$$

These definitions use the same $q$ as the alphabet size.

**Theorem 3.2 (Every fixed order, including all phases).** For each fixed
integer $q\geq2$, (3.2) defines real $C^\infty$ functions of period one
for every integer $r\geq1$. For every fixed integer $R\geq1$, as integer
$n\to\infty$ with $t=\log_q n$,

$$
E_D(q,n)=n\log n-n\log t-n
       +n\sum_{r=1}^R\frac{\Phi_{q,r}(\{t\})}{t^r}
       +O_{q,R}\left(\frac{n}{t^{R+1}}\right).                         \tag{3.3}
$$

The remainder applies to the full integer sequence $n$, including
phases tending to zero from either side. The assertion fixes $q$ and
$R$ before taking the limit; it asserts neither uniformity for growing
$q$ or $R$ nor convergence of the infinite expansion.

The coarse expression
$n\log n-n\log\log n+(\log\log q-1)n+O_q(n/\log n)$
is the already recorded
[distinct-factor expectation asymptotic](https://github.com/the-omega-institute/trureturing/issues/18576).
The coefficient statement (3.3) refines that expression. The classical
harmonic-number and logarithmic-lattice ingredients used below are
attributed to Flajolet, Gourdon, and Dumas, *Mellin transforms and
asymptotics: Harmonic sums*, Theoret. Comput. Sci. **144** (1995), 3–58,
Example 7, Proposition 1, and the periodicity discussion on pp. 23 and
30–35 ([complete original](https://algo.inria.fr/flajolet/Publications/FlGoDu95.pdf)).

*Proof.* The integral expression in (3.1) shows $K_q(v)>0$.
Since $A(0+)=0$ and $A(+\infty)=1$,

$$
\int_{\mathbb R}K_q(v)\,dv=1.                                         \tag{3.4}
$$

For every integer $j\geq0$ there is $C_{q,j}<\infty$ such that

$$
|K_q^{(j)}(v)|\leq C_{q,j}e^{-\alpha|v|}\quad(v\in\mathbb R).           \tag{3.5}
$$

Indeed, at $x=q^v\to0$ the expression
$[1-(1+x)e^{-x}]/x$ has a convergent power series starting with $x/2$;
applying $\alpha x\,d/dx$ any fixed number of times preserves this
$O(x)$ bound. At $x\to\infty$ it equals
$x^{-1}-(1+x^{-1})e^{-x}$; the same differentiations leave an
$O(x^{-1})$ term plus a polynomial in $x,x^{-1}$ times $e^{-x}$.
These estimates, together with boundedness on a compact interval, prove
(3.5). In particular $K_q$ has all absolute polynomial moments.

Since $|v+\{\theta-v\}|\leq|v|+1$, (3.2) converges absolutely.
Its argument is unchanged by $\theta\mapsto\theta+1$, proving
periodicity. Its smoothness at every phase, including integer phases,
can be read without differentiating a fractional part. Split the
integral into $\theta-v\in[j,j+1)$ to obtain

$$
\Phi_{q,r}(\theta)=\frac1r\sum_{j\in\mathbb Z}
 B_r(\theta-j)\int_{\theta-j-1}^{\theta-j}K_q(v)\,dv.                    \tag{3.6}
$$

For $\theta$ in any compact interval, every derivative of a summand in
(3.6) is bounded by a polynomial in $1+|j|$ times
$C e^{-\alpha|j|}$. This follows from (3.5), the endpoint rule for the
integral, and the polynomial character of $B_r$. Hence the series and
each of its differentiated series converge uniformly there.
It follows that $\Phi_{q,r}$ is real and $C^\infty$ on all of
$\mathbb R$. Formula (3.6) also verifies equality of all derivatives
across the endpoints of a period by reindexing $j$.

We next evaluate $F_q(n)/n$. By (3.4) and the definition of $K_q$,

$$
A(q^{t-m})=\int_{-\infty}^{t-m}K_q(v)\,dv.
$$

All terms are nonnegative. Tonelli's theorem therefore gives the exact
identity

$$
\begin{aligned}
\frac{F_q(n)}n
 &=\sum_{m\geq1}\frac1m A(q^{t-m})\\
 &=\int_{\mathbb R}K_q(v)H_{\lfloor t-v\rfloor}\,dv.
\end{aligned}       \tag{3.7}
$$

Here the convention $H_k=0$ for $k\leq0$ is essential. It covers the
whole region $v>t-1$, so no truncation of a probability law has been
made.

We give the required harmonic estimate with its uniform remainder.
The finite Euler summation formula for $1/x$, or the harmonic-number
expansion in FGD-1995, Example 7, gives, for any fixed $p\geq1$,

$$
H_k=\log k+\gamma+\frac1{2k}
    -\sum_{s=1}^p\frac{B_{2s}(0)}{2s\,k^{2s}}
    +O_p(k^{-2p})\qquad(k\to\infty).                                 \tag{3.8}
$$

For the stated error bound one may apply finite Euler summation to
$1/x$ on $[k,M]$, then let $M\to\infty$ after subtracting $\log M$.
The endpoint terms are those in (3.8). The remainder has absolute
value at most

$$
\frac{\sup_{0\leq u\leq1}|B_{2p}(u)|}{(2p)!}
\int_k^\infty\left|\frac{d^{2p}}{dx^{2p}}\frac1x\right|\,dx
 =\frac{\sup_{[0,1]}|B_{2p}|}{2p}\,k^{-2p}.
$$

Finite Euler summation here follows by integrating by parts on each
unit interval, using $B_j'=jB_{j-1}$ and
$B_j(1)=B_j(0)$ for $j\ne1$; the jump of the periodic $B_1$ gives the
endpoint half-weights. This also fixes the signs and normalization in
(3.8).

Let $k$ be an integer, $d=t-k$, and $|d|\leq t/2$.
Choose $p$ with $2p\geq R+1$ and expand (3.8) about $k=t-d$.
Taylor's finite geometric expansions, with $|d/t|\leq1/2$, give

$$
H_k=\log t+\gamma
    -\sum_{r=1}^R\frac{B_r(d)}{r\,t^r}
    +O_R\left(\frac{(1+|d|)^{R+1}}{t^{R+1}}\right),                   \tag{3.9}
$$

uniformly over these integers $k$ for sufficiently large $t$.
For completeness the coefficient of $t^{-r}$ obtained by expansion is

$$
-\frac{d^r}r+\frac{d^{r-1}}2
 -\sum_{2s\leq r}\frac{B_{2s}(0)}{2s}
                    {r-1\choose 2s-1}d^{r-2s}
 =-\frac{B_r(d)}r.
$$

The equality follows by multiplying the defining generating function
of $B_j(0)$ by $e^{dz}$; $B_1(0)=-1/2$ and the odd $B_j(0)$ vanish for
$j>1$. The logarithmic Taylor remainder is bounded by
$C_R|d|^{R+1}t^{-R-1}$, the reciprocal-power remainders by
$C_R(1+|d|)^{R+1}t^{-R-1}$, and the remainder of (3.8) by
$C_Rt^{-R-1}$. This proves the uniform form (3.9).

In (3.7), first restrict to $|v|\leq t/3$. Put

$$
k=\lfloor t-v\rfloor,\qquad
 d=t-k=v+\{t-v\}=v+\{\{t\}-v\}.
$$

For sufficiently large $t$, $|d|\leq t/3+1\leq t/2$ and $k\geq1$.
Thus (3.9) applies throughout this region, and its integrated
remainder is at most

$$
\frac{C_R}{t^{R+1}}\int_{\mathbb R}K_q(v)(2+|v|)^{R+1}\,dv
 =O_{q,R}(t^{-R-1}).
$$

The omitted part of (3.7) is exponentially small in $t$, up to a
logarithmic factor. For $v<-t/3$, use
$H_{\lfloor t-v\rfloor}\leq1+\log(t+|v|+1)$ and (3.5).
For $v>t/3$ with $\lfloor t-v\rfloor\geq1$, use
$H_{\lfloor t-v\rfloor}\leq1+\log(t+1)$; it is zero otherwise.
Both tails are $O_q((1+\log(t+1))e^{-\alpha t/3})$.
Extending the main and coefficient integrals back to $\mathbb R$
also costs an exponentially small quantity, because each coefficient
integrand is bounded by $C_{q,r}(1+|v|)^re^{-\alpha|v|}$.
Consequently (3.7) yields

$$
\frac{F_q(n)}n=\log t+\gamma
     -\sum_{r=1}^R\frac{\Phi_{q,r}(\{t\})}{t^r}
     +O_{q,R}(t^{-R-1}).                                               \tag{3.10}
$$

Finally $H_n=\log n+\gamma+O(1/n)$ gives

$$
(n+1)H_n-n=n\log n+(\gamma-1)n+O(\log n).
$$

Combine this with (2.1) and (3.10). For every fixed $R$,
$\sqrt n+\log n=O_{q,R}(n/t^{R+1})$, since $n=q^t$ and an
exponential dominates every fixed power of $t$. This proves (3.3)
with exactly its stated range of $q$, $R$, and integer $n$. $\square$

## 4. The first coefficient and its Fourier normalization

**Theorem 4.1 (Mean and nonzero harmonics).** Let
$\Psi_q=\Phi_{q,1}$ and use the Fourier convention

$$
\widehat\Psi_q(\ell)=\int_0^1\Psi_q(\theta)
                              e^{-2\pi i\ell\theta}\,d\theta
\qquad(\ell\in\mathbb Z).
$$

For every fixed integer $q\geq2$,

$$
\widehat\Psi_q(0)=\frac{1-\gamma}{\log q},                              \tag{4.1}
$$

and for every nonzero integer $\ell$,

$$
\widehat\Psi_q(\ell)=
 -\frac{\Gamma(1-2\pi i\ell/\log q)}
 {2\pi i\ell\,(1+2\pi i\ell/\log q)}\ne0.                            \tag{4.2}
$$

In particular $\Psi_q$ is nonconstant. The Gamma transform used here is
the classical Euler transform in FGD-1995, §1, equation (12), and its
logarithmic rescaling is the Mellin–Fourier correspondence in §1 and
the periodicity discussion following Theorem 4. The following proof
computes it for the kernel (3.1) directly.

*Proof.* By $B_1(u)=u-1/2$, (3.2) reads

$$
\Psi_q(\theta)=\int_{\mathbb R}vK_q(v)\,dv
  +\int_{\mathbb R}K_q(v)\left(\{\theta-v\}-\frac12\right)\,dv.         \tag{4.3}
$$

The first integral is absolutely convergent by (3.5), and the second
has a bounded second factor, so Fubini applies to all Fourier
integrals. The period-one function $b(u)=\{u\}-1/2$ has mean zero.
For $\ell\ne0$, integration by parts on $(0,1)$ gives

$$
\int_0^1(u-1/2)e^{-2\pi i\ell u}\,du=-\frac1{2\pi i\ell}.              \tag{4.4}
$$

Its value at an endpoint has no effect on the integral. Translation
by $v$ multiplies this Fourier coefficient by $e^{-2\pi i\ell v}$.
Therefore

$$
\widehat\Psi_q(0)=\int_{\mathbb R}vK_q(v)\,dv,\qquad
\widehat\Psi_q(\ell)=-\frac1{2\pi i\ell}
         \int_{\mathbb R}K_q(v)e^{-2\pi i\ell v}\,dv\quad(\ell\ne0).
                                                                         \tag{4.5}
$$

Write $\tau=2\pi\ell/\alpha$ and change variables $x=q^v$.
Since $K_q(v)\,dv=A'(x)\,dx$ and
$A'(x)=\int_0^1u e^{-ux}\,du$, we obtain

$$
\begin{aligned}
\int_{\mathbb R}K_q(v)e^{-2\pi i\ell v}\,dv
 &=\int_0^\infty A'(x)x^{-i\tau}\,dx\\
 &=\int_0^1\int_0^\infty u e^{-ux}x^{-i\tau}\,dx\,du\\
 &=\Gamma(1-i\tau)\int_0^1u^{i\tau}\,du
 =\frac{\Gamma(1-i\tau)}{1+i\tau}.
\end{aligned}       \tag{4.6}
$$

The absolute value of the double integrand is $u e^{-ux}$ and its
double integral is one; thus the exchange is justified for every
real $\tau$, without continuation of an integral outside its
convergence strip. Equations (4.5)–(4.6) give (4.2), apart from its
nonvanishing assertion.

For the mean, the same change of variables gives

$$
\begin{aligned}
\int_{\mathbb R}vK_q(v)\,dv
 &=\frac1\alpha\int_0^\infty A'(x)\log x\,dx\\
 &=\frac1\alpha\int_0^1\int_0^\infty u e^{-ux}\log x\,dx\,du\\
 &=\frac1\alpha\int_0^1\bigl(\Gamma'(1)-\log u\bigr)\,du
 =\frac{\Gamma'(1)+1}{\alpha}.
\end{aligned}       \tag{4.7}
$$

Absolute integrability holds: after $y=ux$ the integral of the absolute
value is bounded by
$\int_0^\infty e^{-y}|\log y|\,dy+\int_0^1|\log u|\,du<\infty$.

We include the elementary Gamma identities needed for (4.7) and
nonvanishing. Repeated integration by parts in the beta integral gives,
for $\operatorname{Re}z>0$ and integer $N\geq1$,

$$
\int_0^1s^{z-1}(1-s)^N\,ds
       =\frac{N!}{z(z+1)\cdots(z+N)}.
$$

Multiplying by $N^z$ and putting $x=Ns$ shows

$$
\Gamma(z)=\lim_{N\to\infty}
            \frac{N!N^z}{z(z+1)\cdots(z+N)}.                           \tag{4.8}
$$

Indeed $(1-x/N)^N\mathbf1_{0<x<N}\leq e^{-x}$, and it tends to
$e^{-x}$ for each $x>0$. Dominated convergence proves (4.8), locally
uniformly for $z$ near $1$, also after differentiating in $z$ because
$x^{\operatorname{Re}z-1}(1+|\log x|)e^{-x}$ has an integrable bound
when, for example, $1/2\leq\operatorname{Re}z\leq3/2$.
The value at $z=1$ of the expression in (4.8) is $N/(N+1)$,
and its derivative there is

$$
\frac{N}{N+1}(\log N-H_{N+1})\longrightarrow-\gamma.
$$

Hence $\Gamma'(1)=-\gamma$. Equation (4.7) proves (4.1).

For real $\tau$, take the absolute square of (4.8) at $z=1-i\tau$:

$$
|\Gamma(1-i\tau)|^2
 =\lim_{N\to\infty}\frac{N^2}{(N+1)^2}
          \prod_{j=1}^{N+1}\left(1+\frac{\tau^2}{j^2}\right)^{-1}>0.
$$

The strict positivity follows from
$0\leq\sum_{j\geq1}\log(1+\tau^2/j^2)
 \leq\tau^2\sum_{j\geq1}j^{-2}<\infty$.
Thus the Gamma numerator in (4.2) is never zero. For $\ell\ne0$,
both $2\pi i\ell$ and $1+i\tau$ are nonzero. Every coefficient in
(4.2) is nonzero, proving nonconstancy. $\square$

## 5. Phase limits and exclusion of a constant correction

**Corollary 5.1 (All phase limits and the complete limit set).** Fix an
integer $q\geq2$. For integers $n>1$ define

$$
Z_q(n)=\frac{\log n}{n}\bigl[
 E_D(q,n)-n\log n+n\log\log n-(\log\log q-1)n\bigr].                   \tag{5.1}
$$

For every real $\theta\in[0,1)$ and integers $h\to\infty$, put
$n_h=\lfloor q^{h+\theta}\rfloor$. Then

$$
\lim_{h\to\infty}Z_q(n_h)=(\log q)\Psi_q(\theta).                     \tag{5.2}
$$

The complete set of subsequential limits of $Z_q(n)$, over integer
$n\to\infty$, is

$$
\{(\log q)\Psi_q(\theta):0\leq\theta<1\}
 =\left[(\log q)\min_{\theta\in[0,1]}\Psi_q(\theta),
        (\log q)\max_{\theta\in[0,1]}\Psi_q(\theta)\right],             \tag{5.3}
$$

a nondegenerate compact interval. In particular there is no real
constant $C_q$ such that

$$
E_D(q,n)=n\log n-n\log\log n+(\log\log q-1)n
          +C_q\frac{n}{\log n}+o_q(n/\log n).                          \tag{5.4}
$$

*Proof.* Since $\log n=\alpha t$,
$\log\log n=\log\alpha+\log t$ exactly. Applying (3.3) with $R=1$
therefore gives

$$
Z_q(n)=\alpha\Psi_q(\{\log_q n\})+O_q(t^{-1}).                        \tag{5.5}
$$

For $0<\theta<1$ the floor defining $n_h$ satisfies
$n_h/q^{h+\theta}=1+O_q(q^{-h})$. It follows that
$\log_q n_h=h+\theta+O_q(q^{-h})$, so its fractional part tends to
$\theta$. For $\theta=0$, integrality of $q$ gives $n_h=q^h$ exactly
for every integer $h\geq0$; the phase is exactly zero. Continuity and
periodicity of $\Psi_q$, together with (5.5), prove (5.2) at all the
stated phases.

Every value on the left of (5.3) is a subsequential limit by (5.2).
Conversely, if some $Z_q(n_j)$ converges, compactness of $[0,1]$
provides a further subsequence whose phases converge to a point of
$[0,1]$. Formula (5.5) identifies its limit as $\alpha\Psi_q$ at that
point. A limiting phase of $1$ has the same value as $0$, so this is
in the displayed image of $[0,1)$. This proves that there are no
additional subsequential limits. The image is the interval between
its minimum and maximum by continuity and the intermediate value
theorem. It is nondegenerate by Theorem 4.1 and $\alpha>0$.

If (5.4) held, (5.1) would give $Z_q(n)\to C_q$. Equations (5.2)–(5.3)
would force the nonconstant function $\alpha\Psi_q$ to have a
single-point image, a contradiction. $\square$

## 追加锚（本行以下为增补区）

## 6. Fixed positive letter probabilities and entropy

**Definition 6.1 (The fixed source law).** Fix an integer $q\geq2$,
the ordered alphabet $\mathcal A=\{a_1<\cdots<a_q\}$, and real numbers
$p_1,\ldots,p_q>0$ with $\sum_{i=1}^q p_i=1$. The vector
$p=(p_1,\ldots,p_q)$ is independent of $n$. In this section $W_n$ has
independent letters with $\mathbb P(W_n[j]=a_i)=p_i$, for every
integer $n\geq0$. Retain exactly the factor statistic $D$ of
Definition 1.1, and write

$$
E_p(n)=\mathbb E_pD(W_n),\qquad
P(w)=\prod_{j=1}^{|w|}p_{i_j}\quad(w=a_{i_1}\cdots a_{i_{|w|}}),\qquad
h=h(p)=-\sum_{i=1}^q p_i\log p_i.                                    \tag{6.1}
$$

In particular $E_p(0)=0$. Every length $1\leq m\leq n$ and every
starting position $0\leq i\leq n-m$ is admissible; equal factor words
are counted once. The increasing bijection $a_i\mapsto i-1$ identifies
these words with the `Fin q` words in Definition 1.1 and transports the
law by assigning probability $p_i$ to $i-1$. It preserves order, rotations, and the factor words counted by
`distinctLyndon` cited there. Thus the statistic is unchanged, while
its sampling law is specified by $p$.
When $p_i=1/q$ for every $i$, $E_p(n)=E_D(q,n)$ and $h=\log q$.
The GSS-v1 parameter $\sigma$ is still $q$; its expectation formula (6)
is for the uniform law. Throughout this section, $O_p$ denotes a
deterministic bound with constants depending on the fixed vector $p$
(and hence its fixed length $q$), never a stochastic order symbol.

**Theorem 6.2 (The entropy-dependent linear term).** For every law in
Definition 6.1, along the full sequence of integers $n\to\infty$,

$$
E_p(n)=n\log n-n\log\log n+(\log h(p)-1)n
                         +O_p\left(\frac{n}{\log n}\right).          \tag{6.2}
$$

Precisely, for each fixed $p$ there exist finite $C(p)$ and an integer
$n_0(p)\geq2$ such that the absolute difference between the two sides
of (6.2) without the remainder is at most $C(p)n/\log n$ for every
integer $n\geq n_0(p)$. The linear coefficient is uniquely
$\log h(p)-1$. The assertion includes both arithmetic and
nonarithmetic laws of the letter information $-\log p_i$.

*Proof.* For the uniform vector, Theorem 3.2 with $R=1$ and boundedness
of the continuous periodic function $\Phi_{q,1}$ give (6.2), since
$t=\log n/\log q$ and $\log t=\log\log n-\log\log q$.
Theorems 3.2 and 4.1 and Corollary 5.1 give the more precise uniform
expansion and its phase limits under their fixed-$q$, fixed-order
hypotheses. The argument below establishes (6.2) for the remaining
fixed positive laws.

Put

$$
\rho=\max_i p_i<1,\qquad a=-\log\rho>0,\qquad
b=-\log\min_i p_i<\infty,\qquad s_2=\sum_i p_i^2<1.
$$

Thus $0<a\leq-\log p_i\leq b$ and $a\leq h\leq b$.
Use the functions $f(x)=x-1+e^{-x}$ and $A(x)=f(x)/x$ from
Proposition 2.1 and Definition 3.1. Their elementary bounds, valid
for $x\geq0$ (with $A$ used only for $x>0$), are

$$
0\leq f(x)\leq x^2/2,\qquad
0\leq f'(x)=1-e^{-x}\leq\min(1,x),\qquad
0\leq A(x)\leq\min(1,x/2).
$$

We first obtain the weighted occurrence expression, retaining all
finite-word boundaries. The classical conjugacy and borderlessness
facts used in Proposition 2.1 apply without a sampling assumption:
Glen, Simpson, and Smyth, *Counting Lyndon factors*,
[arXiv:1701.00928v1](https://arxiv.org/pdf/1701.00928v1), §§1, 3–4,
pp. 1–5. In particular each primitive rotation class of length $m$
has exactly $m$ members and exactly one Lyndon representative.
Rotations preserve $P(w)$. Consequently, for every nonnegative
function $g$ on $(0,1]$,

$$
\sum_{\substack{w\text{ Lyndon}\\|w|=m}}g(P(w))
 =\frac1m\sum_{\substack{w\in\mathcal A^m\\w\text{ primitive}}}
                       g(P(w))
 \leq\frac1m\sum_{w\in\mathcal A^m}g(P(w)).                          \tag{6.3}
$$

The suffix characterization in the same source, also the theorem
`isLyndon_iff_lt_suffix` cited in Proposition 2.1, implies
borderlessness: a nonempty proper border would be a proper prefix,
hence smaller than $w$, and a proper suffix, hence larger than $w$.
Thus two occurrences of the same Lyndon word of length $m$ cannot
start at distances $1,\ldots,m-1$.

For such a word and $1\leq m\leq n$, set $r=P(w)$,
$N=n-m+1$, and $\lambda=Nr>0$. The occurrence indicators at positions
$0,\ldots,N-1$ have means $r$. Take the dependence neighborhood of
position $i$ to be all admissible $j$ with $|j-i|<m$. The indicator at
$i$ is independent of the sigma-algebra of all indicators outside
this neighborhood, because those windows use only letters outside
its own window. Products of two different indicators inside the
neighborhood are zero by borderlessness. In Arratia, Goldstein, and
Gordon, *Two moments suffice for Poisson approximations: the
Chen–Stein method*, Ann. Probab. **17** (1989), 9–25,
[§2, Theorem 1, pp. 10–11](https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/AGG-1.pdf),
this gives $b_1\leq N(2m-1)r^2$, $b_2=b_3=0$. The index set is finite,
each neighborhood contains its index, and $0<\lambda<\infty$;
these are the hypotheses of its zero-event inequality. It yields

$$
\left|\mathbb P_p(w\text{ occurs})-(1-e^{-Nr})\right|
 \leq(2m-1)r(1-e^{-Nr})
 \leq(2m-1)r\min(1,nr).                                             \tag{6.4}
$$

This is the zero-event bound, with no total-variation normalization
factor. It includes $m=1$ and $m=n$.

Since $\sum_{w\in\mathcal A^m}P(w)=1$ and $P(w)\leq\rho^m$,
(6.3) bounds the sum of errors in (6.4) by

$$
2\sum_{m=1}^n\sum_{w\in\mathcal A^m}P(w)\min(1,nP(w))
 \leq2\sum_{m\geq1}\min(1,n\rho^m)=O_p(1+\log n).                   \tag{6.5}
$$

Indeed, for $k_\rho=\lfloor\log n/a\rfloor$, the part $m\leq k_\rho$
is at most $k_\rho$, and the remaining geometric sum is at most
$(1-\rho)^{-1}$. Linearity of expectation over indicators of distinct
words therefore replaces occurrence probabilities by $1-e^{-NP(w)}$
with exactly this error.

We next remove the primitive restriction in (6.3). If a length-$m$
word is not primitive, it is $u^r$ for some proper divisor $d$ of $m$,
where $|u|=d\leq m/2$ and $r=m/d\geq2$. Its total probability, summed
over all $u$ of this length, is

$$
\sum_{u\in\mathcal A^d}P(u)^r
 =\left(\sum_i p_i^r\right)^d
 \leq\rho^{(r-1)d}=\rho^{m-d}\leq\rho^{m/2}.
$$

There are at most $m$ such divisors, so

$$
\sum_{\substack{w\in\mathcal A^m\\w\text{ not primitive}}}P(w)
 \leq m\rho^{m/2}.                                                  \tag{6.6}
$$

For $m=1$ this is an upper bound for an empty sum. Let
$k=\lfloor\log n/(2\log q)\rfloor$, for $n$ large enough that $k\geq1$.
In lengths $m\leq k$ use $1-e^{-NP(w)}\leq1$ and count all $q^m$
words. In lengths $m>k$ use $1-e^{-NP(w)}\leq nP(w)$ and (6.6).
The total error introduced by replacing primitive words by all words
is at most

$$
\sum_{m\leq k}\frac{q^m}{m}
       +n\sum_{m>k}\rho^{m/2}
 =O_p(\sqrt n+n\rho^{k/2})=O_p(n^{1-\delta}),\qquad
\delta=\frac{-\log\rho}{4\log q}>0.                                 \tag{6.7}
$$

Here $q^k\leq\sqrt n$, $\rho^{k/2}\leq\rho^{-1/2}n^{-\delta}$,
and $\rho\geq1/q$ implies $\delta\leq1/4$, so the last bound absorbs
$\sqrt n$. Combining (6.3)–(6.7) gives

$$
E_p(n)=\sum_{m=1}^n\frac1m\sum_{w\in\mathcal A^m}
                 (1-e^{-(n-m+1)P(w)})
             +O_p(n^{1-\delta}+\log n).
$$

Define, for every real $x>0$,

$$
F_p(x)=\sum_{m\geq1}\frac1m\sum_{w\in\mathcal A^m}f(xP(w)).
$$

The series converges, since its $m$-th summand is at most
$x^2s_2^m/(2m)$. Using $1-e^{-x}=x-f(x)$ and summing the linear part
with its exact boundary $n-m+1$ gives

$$
\sum_{m=1}^n\frac{n-m+1}{m}=(n+1)H_n-n.
$$

For each $w\in\mathcal A^m$ the derivative bound for $f$ gives

$$
0\leq\frac{f(nP(w))-f((n-m+1)P(w))}{m}
 \leq\frac{m-1}{m}P(w)\min(1,nP(w)).
$$

Summing costs $O_p(1+\log n)$ by (6.5). The extension past $m=n$
costs at most

$$
\sum_{m>n}\frac{n^2s_2^m}{2m}
 \leq\frac{n^2s_2^{n+1}}{2(n+1)(1-s_2)}=O_p(ns_2^n).
$$

It follows that

$$
E_p(n)=(n+1)H_n-n-F_p(n)
                        +O_p(n^{1-\delta}+\log n).                  \tag{6.8}
$$

Only the combinatorial facts and the cited Poisson inequality from
Proposition 2.1 have been used here; its uniform-law formula (2.1)
has not been applied to a nonuniform law.

To estimate $F_p$, let $I_1,I_2,\ldots$ be independent letter indices
with $\mathbb P(I_j=i)=p_i$, and set $Y_j=-\log p_{I_j}$. This
construction includes coincident information values by adding the
probabilities of their indices. Put $S_0=0$ and
$S_m=Y_1+\cdots+Y_m$. Thus

$$
\mathbb EY_j=h,\qquad a\leq Y_j\leq b,\qquad
\sigma^2=\mathbb E(Y_j-h)^2<\infty.
$$

These are the information sums of the original iid source: for any
function $B$ for which the finite sum exists,
$\mathbb EB(e^{-S_m})=\sum_{w\in\mathcal A^m}P(w)B(P(w))$.
For $L=\log n$ this yields the exact nonnegative series

$$
\frac{F_p(n)}n=\sum_{m\geq1}\frac1m
                            \mathbb E A(e^{L-S_m}).                 \tag{6.9}
$$

The elementary representation $A(x)=1-(1-e^{-x})/x$ shows that

$$
\left|A(e^u)-\mathbf1_{\{u\geq0\}}\right|\leq e^{-|u|}
                    \qquad(u\in\mathbb R).
$$

For $u\geq0$ use $1-A(e^u)\leq e^{-u}$; for $u<0$ use
$A(e^u)\leq e^u/2$. This bound also holds at $u=0$ with the indicated
choice of the indicator.

We bound its sum path by path. Since successive $S_m$ differ by at
least $a$, any interval of length one contains at most
$M_a=2+\lceil1/a\rceil$ of them. Partitioning the real line into the
half-open intervals $[L+j,L+j+1)$, $j\in\mathbb Z$, gives

$$
\sum_{m\geq1}e^{-|L-S_m|}
 \leq eM_a\sum_{j\in\mathbb Z}e^{-|j|}=:C_a<\infty.
$$

For $m<L/(2b)$, $S_m\leq bm<L/2$, so the weighted error is at most
$e^{-L/2}H_{\lfloor L/(2b)\rfloor}$. For the remaining $m$,
$1/m\leq2b/L$, so their weighted error is at most $2bC_a/L$.
Taking expectations proves, for all sufficiently large real $L$,

$$
\sum_{m\geq1}\frac1m\mathbb E A(e^{L-S_m})
 =\sum_{m\geq1}\frac1m\mathbb P(S_m\leq L)+O_p(L^{-1})
 =\mathbb E H_{T(L)}+O_p(L^{-1}),                                   \tag{6.10}
$$

where $T(L)=\max\{m\geq0:S_m\leq L\}$ and $H_0=0$.
The maximum exists because $S_m\geq am$; moreover

$$
\lfloor L/b\rfloor\leq T(L)\leq\lfloor L/a\rfloor.
$$

The second equality in (6.10) is exact before the error is added:
strict increase of $S_m$ makes the admissible indices precisely
$1,\ldots,T(L)$. In particular equality $S_m=L$ is retained.
Nonnegativity justifies exchanging expectations and sums.

For completeness, the finite stopping-sum identities give the needed
precision for $\mathbb EH_{T(L)}$ without a renewal limit theorem.
Let $K=T(L)+1$, the first index with $S_K>L$, and
$M_K=S_K-hK$. The integer $K$ is bounded by
$J=\lfloor L/a\rfloor+1$, and
$\{K\geq j\}=\{S_{j-1}\leq L\}$ depends only on the first $j-1$
variables. Expanding the finite sums

$$
S_K=\sum_{j=1}^JY_j\mathbf1_{\{K\geq j\}},\qquad
M_K=\sum_{j=1}^J(Y_j-h)\mathbf1_{\{K\geq j\}}
$$

therefore gives

$$
\mathbb ES_K=h\mathbb EK,\qquad
\mathbb EM_K=0,\qquad
\mathbb EM_K^2=\sigma^2\mathbb EK.                                  \tag{6.11}
$$

For the last identity, each diagonal term has expectation
$\sigma^2\mathbb P(K\geq j)$. In a cross term indexed by $i<j$, all
factors except $Y_j-h$ depend only on the first $j-1$ variables;
conditioning on them makes that term zero. Finally
$\sum_{j=1}^J\mathbb P(K\geq j)=\mathbb EK$.

The overshoot obeys $0<S_K-L\leq b$. Consequently (6.11) implies
$\mathbb EK=L/h+O_p(1)$ and, using
$hK-L=(S_K-L)-M_K$,

$$
\mathbb E(K-L/h)^2
 \leq\frac2{h^2}\bigl(b^2+\sigma^2\mathbb EK\bigr)=O_p(L).
$$

Since $T=K-1$, it follows that
$\mathbb E(T-L/h)=O_p(1)$ and
$\mathbb E(T-L/h)^2=O_p(L)$. For $L\geq2b$,
$T\geq L/(2b)$ and $L/h\geq L/b$.
Taylor's theorem for $\log x$, whose second derivative has magnitude
$x^{-2}$, thus gives, uniformly on every possible value of $T$,

$$
\log T=\log(L/h)+\frac hL(T-L/h)
                         +O_p\left(\frac{(T-L/h)^2}{L^2}\right).
$$

Taking expectations and applying the two moment bounds yields
$\mathbb E\log T=\log(L/h)+O_p(L^{-1})$.
The classical harmonic estimate
$H_k=\log k+\gamma+O(k^{-1})$, with its remainder as in (3.8), now
applies because $T\geq L/(2b)$. This is the harmonic-number ingredient
of Flajolet, Gourdon, and Dumas, *Mellin transforms and asymptotics:
Harmonic sums*, Theoret. Comput. Sci. **144** (1995), 3–58,
[Example 7, p. 27](https://algo.inria.fr/flajolet/Publications/FlGoDu95.pdf),
used here only at this first-order precision. We obtain

$$
\mathbb EH_{T(L)}=\log L-\log h+\gamma+O_p(L^{-1}).                  \tag{6.12}
$$

No restriction on the support of $Y_j$ was used in (6.9)–(6.12).
In particular a common positive span for its possible values, when
one exists, and equality with the threshold cause no exceptional
values of $L$.

Combining (6.9), (6.10), and (6.12) gives

$$
F_p(n)=n\bigl(\log\log n-\log h+\gamma\bigr)
                                   +O_p(n/\log n).                 \tag{6.13}
$$

Finally $(n+1)H_n-n=n\log n+(\gamma-1)n+O(\log n)$, as in the
proof of Theorem 3.2. Inserting (6.13) into (6.8) proves (6.2), since
$\delta>0$ is fixed and
$n^{1-\delta}+\log n=O_p(n/\log n)$. All estimates hold for every
sufficiently large integer $n$, with constants fixed after $p$ is
fixed. They assert no uniform bound as a coordinate of $p$ tends to
zero or as $p$ or $q$ varies with $n$.

If another real coefficient $c$ satisfied (6.2) with the same first
two terms and an $O_p(n/\log n)$ remainder, subtraction and division
by $n$ would give $c-(\log h-1)=O_p(1/\log n)$ for all sufficiently
large integers $n$. Taking their limit proves $c=\log h-1$.
$\square$

## 追加锚（本行以下为增补区）
