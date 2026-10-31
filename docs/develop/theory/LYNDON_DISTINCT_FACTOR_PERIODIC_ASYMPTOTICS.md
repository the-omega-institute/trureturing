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

## 7. The first correction for a fixed positive source

**Definition 7.1 (Information arithmetic and the coefficient).** Retain
all the hypotheses, the iid law, and the distinct contiguous word
statistic of Definition 6.1. Set $L=\log n$ for integers $n>1$ and
$\mu=1-\gamma$. Let $I$ have $\mathbb P(I=i)=p_i$, and put

$$
Y=-\log p_I,\qquad h=\mathbb EY,\qquad
\sigma^2=\operatorname{Var}(Y),\qquad m_2=\mathbb EY^2.
$$

Repeated information values carry the sum of their letter
probabilities. Call $Y$ arithmetic if its support is contained in
$d\mathbb Z$ for some $d>0$, and take $d$ maximal; otherwise call it
nonarithmetic. Containment in a translate of a lattice is not this
condition. This is the definition of a $d$-lattice variable in
Blackwell, *Extension of a renewal theorem*, Pacific J. Math. **3**
(1953), 315–320, §1
([complete original](https://msp.org/pjm/1953/3-2/pjm-v3-n2-p03-p.pdf)).
Define, for real $v,u,x$,

$$
k(v)=\frac{1-(1+e^v)e^{-e^v}}{e^v},\qquad
b(u)=\{u\}-\frac12,\qquad
B_p(x)=
\begin{cases}
\mu,&Y\text{ nonarithmetic},\\
\displaystyle\mu+d\int_{\mathbb R}k(v)b((x-v)/d)\,dv,
       &Y\text{ arithmetic of span }d.
\end{cases}                                                        \tag{7.1}
$$

In particular $b(j)=-1/2$ for every integer $j$. The integral in (7.1)
is an ordinary absolutely convergent integral. Indeed, the kernel
calculations in §§3–4, with $v=(\log q)w$, give

$$
K_q(w)=(\log q)k((\log q)w),\qquad
\int_{\mathbb R}k(v)\,dv=1,\qquad
\int_{\mathbb R}vk(v)\,dv=\mu,\qquad
|k^{(j)}(v)|\leq C_j e^{-|v|}\quad(j\geq0).                         \tag{7.2}
$$

Thus (7.1) contains no unspecified expectation or remainder.

**Theorem 7.2 (The full fixed-source first correction).** For every
fixed integer $q\geq2$ and every fixed positive probability vector $p$
of length $q$, along all integers $n\to\infty$,

$$
E_p(n)=n\log n-n\log\log n+(\log h-1)n
             +\frac{n}{\log n}B_p(\log n)+r_p(n),\qquad
\lim_{n\to\infty}\frac{\log n}{n}r_p(n)=0.                          \tag{7.3}
$$

The remainder is deterministic for each fixed $p$. In particular,
(7.3) includes arithmetic and nonarithmetic information laws, and
$\sigma^2=0$. Its quantifiers do not give a nonarithmetic convergence
rate, an $O_p(n/(\log n)^2)$ remainder, higher biased orders, or bounds
uniform as $p$ approaches the boundary or as $p$ or $q$ varies with $n$.

*Proof.* The weighted occurrence reduction (6.8) and the exact
information-sum expression (6.9) apply under precisely these
hypotheses. In their notation $a=-\log\max_i p_i>0$ and
$b_0=-\log\min_i p_i<\infty$; use $b_0$ here to distinguish this bound
from the function $b$. For independent copies $Y_j$ of $Y$, put
$S_0=0$ and $S_m=\sum_{j=1}^mY_j$. The reused formulas are

$$
\begin{aligned}
E_p(n)&=(n+1)H_n-n-F_p(n)+O_p(n^{1-\delta}+\log n),\\
\frac{F_p(n)}n&=\sum_{m\geq1}\frac1m\mathbb E A(e^{L-S_m}),
\qquad \delta=\frac{a}{4\log q}>0.
\end{aligned}                                                       \tag{7.4}
$$

Here $A$ is Definition 3.1's function, and $a\leq Y_j\leq b_0$.
These formulas retain single letters, the boundary $n-m+1$, every
legal window, and whole Lyndon words. Their combinatorial input is
Glen–Simpson–Smyth, arXiv:1701.00928v1, §§1, 3–4, pp. 1–5; the
probability input is the zero-event inequality, not the
total-variation normalization, in Arratia–Goldstein–Gordon (1989),
§2, Theorem 1. The parameter map and word transport are exactly
Definition 6.1's. The uniform occurrence formula is not being applied
to a biased law. The refinement required beyond Theorem 6.2 is the
coefficient of $L^{-1}$ in (7.4).

For real $t\geq0$ define

$$
T(t)=\max\{m\geq0:S_m\leq t\},\qquad
K(t)=T(t)+1,\qquad R(t)=S_{K(t)}-t,\qquad
Q(t)=\mathbb EH_{T(t)}.
$$

Put $Q(t)=0$ for $t<0$. Thus $K(t)$ is the first index with $S_m>t$,
not the first with $S_m\geq t$. We have $0<R(t)\leq b_0$ and
$\lfloor t/b_0\rfloor\leq T(t)\leq\lfloor t/a\rfloor$.
We shall use Blackwell's Theorem 1 at its actual hypotheses:
independent identically distributed increments of positive mean,
with arithmeticity defined through $d\mathbb Z$. It gives the
nonarithmetic interval-renewal limit of interval mass divided by its
length, equal to $1/h$, and in the arithmetic case the point-renewal
limit equal to $d/h$. Our increments are positive and bounded with
finite mean $h>0$. No density, positive-variance hypothesis, or rate
is part of this application.

To make the resulting overshoot calculation explicit, let
$U=\sum_{m\geq0}\mathcal L(S_m)$ be the renewal measure and set
$g(u)=\mathbb E(Y-u)_+$ for $u\geq0$. This function is continuous,
nonnegative, and zero for $u\geq b_0$. Conditioning on the last sum
not exceeding $t$ gives the exact identity

$$
\mathbb ER(t)=\int_{[0,t]}g(t-s)\,U(ds).                            \tag{7.5}
$$

Indeed, on each path exactly one of the events
$S_m\leq t<S_m+Y_{m+1}$ occurs, and its overshoot is
$Y_{m+1}-(t-S_m)$. A zero difference contributes zero, so conditioning
also gives the displayed $g$ at equality. Only finitely many terms
are possible for fixed $t$, since $S_m\geq am$.

If $Y$ is nonarithmetic, Blackwell's interval limit implies

$$
\mathbb ER(t)\longrightarrow
       \frac1h\int_0^{b_0}g(u)\,du=\frac{m_2}{2h}.                 \tag{7.6}
$$

Here is the passage from intervals to this integral, including its
endpoints. For fixed $\varepsilon>0$ the mass $U\{s\}$ at a point
$s\to\infty$ is bounded by the renewal mass of an interval of length
$2\varepsilon$ containing $s$; its limit superior is at most
$2\varepsilon/h$. Letting $\varepsilon\downarrow0$ makes point masses
vanish. On $[0,b_0]$ sandwich $g$ by the upper and lower step functions
of a finite partition. Blackwell's limit applies to each translated
interval; endpoint masses have just been handled. The limiting upper
and lower bounds are the corresponding Riemann sums divided by $h$.
Their difference tends to zero by continuity of $g$, proving (7.6).
Finally, integrating $(Y-u)_+$ over $u\geq0$ gives $Y^2/2$, which
proves the last equality. This argument uses only the classical
interval theorem and does not impose a convergence rate.

If $Y$ has maximal arithmetic span $d$, write $t=d(k+\theta)$ with
$k=\lfloor t/d\rfloor$ and $0\leq\theta<1$. Put
$u_j=U\{jd\}$. Blackwell's arithmetic conclusion is $u_j\to d/h$.
This follows by applying its interval conclusion to
$((j-1)d,jd]$, which contains just the possible renewal value $jd$.
At $t=kd$, (7.5) is a finite convolution with the fixed finitely
supported sequence $g(jd)$, so

$$
\begin{aligned}
\mathbb ER(kd)&\longrightarrow
 \frac dh\sum_{j\geq0}g(jd)
 =\frac dh\mathbb E\left[\frac{Y^2}{2d}+\frac Y2\right]
 =\frac{m_2}{2h}+\frac d2.
\end{aligned}
$$

For $Y=md$ the sum used here is
$\sum_{j=0}^{m-1}(md-jd)=dm(m+1)/2$; hence it includes the $j=0$
term. Since no renewal sum lies strictly between $kd$ and $(k+1)d$,
$K(t)=K(kd)$ and $R(t)=R(kd)-d\theta$ exactly. Consequently

$$
\mathbb ER(t)=\frac{m_2}{2h}
                   -d\,b(t/d)+o_p(1),                             \tag{7.7}
$$

where the error tends to zero uniformly over $0\leq\theta<1$ as
$k\to\infty$. At $\theta=0$ the right-hand correction is $d/2$,
as required by the strict crossing definition of $K$.

We next retain enough of the stopping-sum fluctuations to determine
$Q(t)$. All the following estimates hold as real $t\to\infty$.
Write $K=K(t)$, $T=T(t)$, and $M=S_K-hK$. The finite stopping-sum
identities (6.11), with the same bounded stopping time, give

$$
h\mathbb EK=t+\mathbb ER(t),\qquad
\mathbb EM^2=\sigma^2\mathbb EK,\qquad \mathbb EM=0.
$$

In particular $\mathbb EK=t/h+O_p(1)$. Since $hK-t=R(t)-M$ and
$R(t)$ is bounded, Cauchy–Schwarz gives

$$
\mathbb E(T-t/h)=\frac{\mathbb ER(t)}h-1,\qquad
\mathbb E(T-t/h)^2=\frac{\sigma^2}{h^3}t+O_p(\sqrt t+1).            \tag{7.8}
$$

For the second equality, expand $(R-M)^2$, use
$|\mathbb E(RM)|\leq b_0(\mathbb EM^2)^{1/2}$, then replace $K$ by
$T=K-1$; the first equality bounds the additional linear term.
These statements also hold when $\sigma^2=0$.

A third absolute moment small enough for Taylor's remainder follows
without a limit theorem. Let $J=\lfloor t/a\rfloor+1$, and, for
$1\leq j\leq J$, let
$D_j=(Y_j-h)\mathbf1_{\{K\geq j\}}$ and
$N_j=\sum_{i=1}^jD_i$, with $N_0=0$. Relative to the first $j-1$
increments, $\mathbb E(D_j\mid Y_1,\ldots,Y_{j-1})=0$, and
$|D_j|\leq c$ for a constant depending only on $p$. Thus
$\mathbb EN_j^2\leq c^2j$. Expanding $(N_{j-1}+D_j)^4$ and
conditioning gives

$$
\mathbb EN_j^4\leq\mathbb EN_{j-1}^4
 +6c^2\mathbb EN_{j-1}^2+4c^3\mathbb E|N_{j-1}|+c^4.
$$

Summing and using $\mathbb E|N_j|\leq c\sqrt j$ proves
$\mathbb EM^4=\mathbb EN_J^4=O_p(t^2)$.
Since $T-t/h=(R-M)/h-1$, it follows that

$$
\mathbb E|T-t/h|^3=O_p(t^{3/2}),\qquad
\mathbb E|T-t/h|=O_p(\sqrt t).                                    \tag{7.9}
$$

For example the cubic bound follows from
$\mathbb E|M|^3\leq(\mathbb EM^2\mathbb EM^4)^{1/2}$ and boundedness
of $R$.

For $t\geq2b_0$, both $T$ and $t/h$ are at least $t/(2b_0)$.
Taylor's theorem for the logarithm, through its quadratic term,
therefore has a uniform cubic remainder bounded by
$C_p|T-t/h|^3/t^3$. The same lower bounds give
$\mathbb E(1/T)=h/t+O_p(t^{-3/2})$. Apply the classical harmonic
estimate $H_j=\log j+\gamma+1/(2j)+O(j^{-2})$ from (3.8), equivalently
Flajolet–Gourdon–Dumas (1995), Example 7, p. 27. Equations
(7.8)–(7.9) yield

$$
\begin{aligned}
Q(t)
 &=\log(t/h)+\gamma
   +\frac h t\left(\frac{\mathbb ER(t)}h-1\right)
   -\frac{h^2}{2t^2}\frac{\sigma^2t}{h^3}
   +\frac h{2t}+o_p(t^{-1})\\
 &=\log(t/h)+\gamma
   +\frac1t\left(\mathbb ER(t)-\frac{m_2}{2h}\right)
   +o_p(t^{-1}).
\end{aligned}                                                       \tag{7.10}
$$

The identity $m_2=h^2+\sigma^2$ accounts for the cancellation of the
variance term. Define $\beta(t)=0$ in the nonarithmetic case, and
$\beta(t)=d\,b(t/d)$ in the arithmetic case. By (7.6)–(7.7),

$$
Q(t)=\log t-\log h+\gamma-\frac{\beta(t)}t
                         +\frac{\varepsilon_p(t)}t,\qquad
\varepsilon_p(t)\longrightarrow0\quad(t\to\infty).                  \tag{7.11}
$$

The limit is over all real $t$, including arithmetic thresholds.
In particular $\sup_{t\geq T_0}|\varepsilon_p(t)|\to0$ as
$T_0\to\infty$. This is an asymptotic conclusion for each fixed law,
not a rate statement for nonarithmetic laws.

Since $dA(e^v)/dv=k(v)$ and $A(e^v)\to0$ as $v\to-\infty$,
Tonelli's theorem applied to (7.4) gives the exact smoothing identity

$$
\frac{F_p(n)}n
 =\int_{\mathbb R}k(v)
       \sum_{m\geq1}\frac1m\mathbb P(S_m\leq L-v)\,dv
 =\int_{\mathbb R}k(v)Q(L-v)\,dv.                                  \tag{7.12}
$$

The event retains $S_m=L-v$; for negative thresholds the sum is
empty. On $|v|\leq L/3$, insert (7.11) and use

$$
\log(L-v)=\log L-\frac vL+O(v^2/L^2),\qquad
\frac1{L-v}=\frac1L+O(|v|/L^2).
$$

The integrated $\varepsilon_p$ term is $o_p(1/L)$ by the supremum
bound following (7.11). The other integrated errors are $O_p(L^{-2})$
by (7.2) and boundedness of $\beta$. The remaining region is
negligible at this precision: for $s\geq0$,
$0\leq Q(s)\leq1+\log(1+s/a)$, and for $s<0$ it is zero.
Together with $k(v)\leq C e^{-|v|}$ this bounds the tails of (7.12)
by $O_p((1+\log(L+1))e^{-L/3})$. For the negative tail one can use
$\log(1+(L+|v|)/a)\leq C_p+\log(L+1)+\log(1+|v|)$ and integrate
against $e^{-|v|}$. Extending the coefficient integrals to the whole
line also costs only exponential tails with polynomial factors.
Using (7.2) now gives

$$
\frac{F_p(n)}n
 =\log L-\log h+\gamma
   -\frac1L\left[\mu+\int_{\mathbb R}k(v)\beta(L-v)\,dv\right]
   +o_p(L^{-1})
 =\log L-\log h+\gamma-\frac{B_p(L)}L+o_p(L^{-1}).                   \tag{7.13}
$$

Finally, $(n+1)H_n-n=n\log n+(\gamma-1)n+O(\log n)$.
Since $\delta>0$ is fixed, $n^{1-\delta}+\log n=o_p(n/\log n)$.
Substitution of (7.13) into (7.4) proves (7.3) on the full integer
sequence. For uniform $p$ the stronger all-order result is already
Theorem 3.2; the added inference here is its first-correction
counterpart for fixed nonuniform $p$, using the weighted reduction
already proved in §6 and the classical renewal theorem. $\square$

**Theorem 7.3 (Fourier coefficients and the exact arithmetic
obstruction).** If $Y$ is arithmetic of span $d$, then $B_p$ is real,
$C^\infty$, and $d$-periodic, with period mean $\mu$ and
$|B_p(x)-\mu|\leq d/2$. For $C_d(\theta)=B_p(d\theta)$, using
$\widehat C_d(\ell)=\int_0^1C_d(\theta)e^{-2\pi i\ell\theta}\,d\theta$,

$$
\widehat C_d(0)=\mu,\qquad
\widehat C_d(\ell)=
 -\frac{d\,\Gamma(1-2\pi i\ell/d)}
 {2\pi i\ell(1+2\pi i\ell/d)}\ne0
                 \quad(\ell\in\mathbb Z\setminus\{0\}).             \tag{7.14}
$$

A constant $c_p$ can replace $B_p(\log n)$ in (7.3) with an
$o_p(n/\log n)$ remainder if and only if $Y$ is nonarithmetic; in
that case $c_p=\mu$. In the arithmetic case the complete
subsequential limit set, along integers $n\to\infty$, of

$$
Z_p(n)=\frac{\log n}{n}
 \left[E_p(n)-n\log n+n\log\log n-(\log h-1)n\right]                 \tag{7.15}
$$

is $B_p([0,d])$, a nondegenerate compact interval. Omitting the
$n/\log n$ correction altogether gives no $o_p(n/\log n)$ remainder
in either arithmeticity class.

*Proof.* The bound and periodicity follow directly from (7.1),
$|b|\leq1/2$, positivity of $k$, and its unit integral. For smoothness,
subdivide according to $(x-v)/d\in[j,j+1)$ to write the integral part
of (7.1) as

$$
d^2\int_0^1(u-1/2)\sum_{j\in\mathbb Z}k(x-d(j+u))\,du.
$$

For $x$ in a compact interval, each derivative series converges
uniformly by (7.2). Differentiation under this bounded integral is
therefore valid at every order. This proves smoothness also at period
endpoints, without differentiating a fractional part.

The transform calculation (4.6), after $v=(\log q)w$, gives for every
real $\tau$, not just a discrete frequency,

$$
\int_{\mathbb R}k(v)e^{-i\tau v}\,dv
 =\int_0^1\int_0^\infty u e^{-ux}x^{-i\tau}\,dx\,du
 =\frac{\Gamma(1-i\tau)}{1+i\tau}.                                 \tag{7.16}
$$

The absolute double integral is one, so Fubini applies in the stated
range. This is the Euler transform on its convergence half-plane,
as in Flajolet–Gourdon–Dumas, §1, equation (12), not a continuation
past that range. The same complete calculation (4.7) gives
$\int vk(v)\,dv=\Gamma'(1)+1=\mu$. The proof of (4.8) establishes
$\Gamma'(1)=-\gamma$ and $\Gamma(1-i\tau)\ne0$ for all real $\tau$;
these Gamma facts and the kernel transform are reused here.

The function $b$ has integral zero on a period and nonzero Fourier
coefficient $-1/(2\pi i\ell)$ at integer $\ell\ne0$, by (4.4).
Fubini in (7.1) is justified by its bounded factor $b$ and
$\int k=1$. Translation by $v/d$ multiplies that coefficient by
$e^{-2\pi i\ell v/d}$. Formula (7.16) with
$\tau=2\pi\ell/d$ proves (7.14), including the zero coefficient.
Its nonzero numerator and nonzero denominators prove that $B_p$ is
nonconstant.

Equation (7.3) gives $Z_p(n)=B_p(\log n)+o_p(1)$. For every real
$\theta\in[0,1]$ choose integers
$n_j=\lfloor\exp(d(j+\theta))\rfloor$. They tend to infinity, and
$\log n_j-d(j+\theta)\to0$. Continuity and periodicity give
$Z_p(n_j)\to B_p(d\theta)$ even at $\theta=0,1$; a fractional part
approaching one has the same coefficient value as zero. Conversely,
any convergent subsequence of $Z_p(n)$ has a further subsequence
whose phases modulo $d$ converge in $[0,d]$. Its limit is the value
of $B_p$ at that phase. This proves the claimed complete limit set.
The image is a compact interval by continuity and the intermediate
value theorem, and it is nondegenerate by (7.14).

A constant replacement would force $Z_p(n)\to c_p$, contradicting
this interval in the arithmetic case. In the nonarithmetic case
(7.1) and (7.3) give convergence to $\mu$, so this constant works
and is unique. Finally $\mu>0$: the decreasing sequence
$H_j-\log j$ has limit $\gamma$; its decrease follows from
$\log(1+1/j)=\int_j^{j+1}x^{-1}\,dx>1/(j+1)$. Moreover,
$\gamma\leq H_2-\log2<1$, since
$\log2=\int_1^2x^{-1}\,dx>1/2$. Hence the nonarithmetic normalized
residual is not zero. In the arithmetic case the nonconstant
interval of limits cannot be the singleton $\{0\}$, either.
Thus omission cannot leave an $o_p(n/\log n)$ remainder. $\square$

**Proposition 7.4 (Classification, uniform specialization, and two
positive-variance examples).** The information law is arithmetic if
and only if every ratio $(-\log p_i)/(-\log p_1)$ is rational.
Furthermore $\sigma^2=0$ if and only if $p_i=1/q$ for every $i$.
In that case $d=h=\log q$ and

$$
B_p(\log n)=(\log q)\Phi_{q,1}(\{\log_q n\}).                       \tag{7.17}
$$

For $p=(1/2,1/4,1/4)$ one has

$$
d=\log2,\qquad h=\tfrac32\log2,\qquad
\sigma^2=\tfrac14(\log2)^2>0,\qquad
B_p(x)=(\log2)\Phi_{2,1}(x/\log2).                                 \tag{7.18}
$$

For $p=(1/3,2/3)$ one has $\sigma^2>0$, $Y$ nonarithmetic, and
$B_p(x)=\mu$. Thus positive variance admits both arithmeticity
classes and contributes no separate term to the first coefficient.

*Proof.* Write $y_i=-\log p_i>0$. If $y_i\in d\mathbb Z$, each
$y_i/y_1$ is a ratio of positive integers. Conversely, if all these
ratios are rational, a common denominator supplies $c>0$ such that
$y_i=c m_i$ with positive integers $m_i$. Put $g=\gcd_i m_i$.
Then $d=cg$ is a span. For any other span $d'$, a Bezout combination
of the $m_i$ shows $cg/d'\in\mathbb Z_{>0}$, so $d'\leq cg$.
This proves both the equivalence and existence of the maximal span
in Definition 7.1.

All $p_i$ are strictly positive. Therefore zero variance means that
all $y_i$ agree, hence all $p_i$ agree; their sum forces $p_i=1/q$.
The converse is immediate. A single positive support value has
maximal span equal to itself, giving $d=h=\log q$. Equation (4.3)
and $K_q(w)=(\log q)k((\log q)w)$ give

$$
(\log q)\Phi_{q,1}(\theta)
 =\mu+(\log q)\int_{\mathbb R}
                    k(v)b(\theta-v/\log q)\,dv.
$$

This is (7.1) with $d=\log q$ and $x=(\log q)\theta$.
Periodicity proves (7.17). This specialization, its all-order
extension, its transform, and its phase limits are the results
already established in §§3–5.

For $(1/2,1/4,1/4)$, the information values $\log2$ and $2\log2$
each have probability $1/2$. Their mean and variance are the values
in (7.18), and the presence of $\log2$ makes the maximal span
$\log2$. Formula (7.1) depends only on that span within the
arithmetic class, so the uniform binary identity just proved gives
(7.18), despite the different entropy.

For $(1/3,2/3)$ the two information values $\log3$ and $\log(3/2)$
are distinct, each of positive probability, so variance is positive.
If their ratio were a positive rational $r/s$, with positive integers
$r,s$, then $s\log3=r\log(3/2)$, hence
$2^r3^s=3^r$. Unique prime factorization makes this impossible.
The ratio criterion therefore proves nonarithmeticity, and (7.1)
gives $B_p=\mu$. Nevertheless its two support values lie in the
translated lattice $\log(3/2)+(\log2)\mathbb Z$. This also proves
explicitly why translated-lattice containment is insufficient.
The cancellation in (7.10) and the formula (7.1) show that variance
adds no further first coefficient. $\square$

## 追加锚（本行以下为增补区）
## 8. Second scale for the original fixed-source expectation

**Definition 8.1 (Second-scale notation).** Retain every hypothesis of
Definition 6.1 and the arithmetic convention of Definition 7.1. In
particular $q\geq2$ and $p$ are fixed, all $p_i$ are strictly positive,
and $D$ counts distinct nonempty contiguous Lyndon words once, with
letters and every legal length and window included. Write

$$
\begin{aligned}
L&=\log n,\qquad \mu=1-\gamma,\qquad
M_p(n)=n\log n-n\log\log n+(\log h-1)n,\\
c_*&=\frac{\mu^2+1+\pi^2/6}{2},\qquad
\varphi_p(t)=\sum_{i=1}^q p_i^{1+it},\\
R_n(p)&=\frac{(\log n)^2}{n}
 \left[E_p(n)-M_p(n)-\frac{\mu n}{\log n}\right]\quad(n\geq2).
\end{aligned}                                                       \tag{8.1}
$$

Powers of $p_i$ use its real logarithm. For $d>0$ and $x,v\in\mathbb R$
define

$$
r_x(v)=v+d\{(x-v)/d\},\qquad
\mathcal C_d(x)=\frac12\int_{\mathbb R}k(v)
       \left[r_x(v)^2-dr_x(v)+\frac{d^2}{6}\right]dv.                 \tag{8.2}
$$

Here $k$ and $B_p$ are exactly (7.1)–(7.2).
The symbol $\mathcal C_d$ denotes the second coefficient; $C_d$ in
Theorem 7.3 denotes the rescaled first coefficient.
All remainder symbols below are deterministic for fixed $p$ and all
sufficiently large integers $n$.

For use in proofs let $\rho=\mathcal L(Y)$, $\rho_y(ds)=s\rho(ds)$,
and define locally finite measures and functions by

$$
\begin{aligned}
U&=\sum_{m\geq0}\rho^{*m},&
V&=\sum_{m\geq1}\frac{\rho^{*m}}m,&
Q(u)&=V((0,u])\quad(u\geq0),\\
Q(u)&=0\quad(u<0),&
J_p(x)&=\frac{F_p(e^x)}{e^x}
       =\int_{\mathbb R}k(v)Q(x-v)\,dv.
\end{aligned}                                                       \tag{8.3}
$$

Thus $Q(u)=\mathbb EH_{T(u)}$ as in §7; (8.3) is precisely (7.12),
with real $x$ in place of $L$. The measure $V$ is the classical
harmonic renewal measure. Its definition, rather than a renewal-rate
assertion, is used here. The underlying random increments are the
actual information values $-\log p_i$, with masses $p_i$, merging
equal values by addition. The transport of the ordered alphabet to
`Fin q`, and hence the statistic and all its endpoints, is the one in
Definition 6.1. The occurrence reduction (6.8), the information-sum
formula (6.9), and the first correction in §7 are used with this exact
parameter map. The uniform expansions in §§3–5 already apply when
$p_i=1/q$.

**Theorem 8.2 (The arithmetic second coefficient).** If $Y$ is
arithmetic with maximal origin span $d>0$, then

$$
E_p(n)=M_p(n)+\frac nL B_p(L)
              +\frac n{L^2}\mathcal C_d(L)+O_p(n/L^3).              \tag{8.4}
$$

The function $\mathcal C_d$ is real, smooth, and $d$-periodic,
depends only on $d$, and has period mean $c_*$. There is no excluded
phase or positive-variance assumption. In the uniform case,

$$
\mathcal C_{\log q}(\log n)
       =(\log q)^2\Phi_{q,2}(\{\log_q n\}).                         \tag{8.5}
$$

For $p=(1/2,1/4,1/4)$, the span is $\log2$, the entropy is
$\tfrac32\log2$, and $\mathcal C_d$ is the same second-coefficient
function as for uniform binary letters.

*Proof.* First record the second moment of the kernel, with its
normalization. The substitution $z=e^v$ and
$A'(z)=\int_0^1u e^{-uz}\,du$ used in (4.6)–(4.7) gives

$$
\int_{\mathbb R}v^2k(v)\,dv
 =\int_0^1\int_0^\infty e^{-y}(\log y-\log u)^2\,dy\,du
 =\Gamma''(1)+2\Gamma'(1)+2=2c_*.                                  \tag{8.6}
$$

All the integrals are absolutely convergent, since
$\int_0^1|\log u|^2du=2$ and
$\int_0^\infty e^{-y}|\log y|^2dy<\infty$.
Here $\Gamma'(1)=-\gamma$ is proved in §4. Twice logarithmically
differentiating its locally uniform Euler product (4.8) gives
$(\log\Gamma)''(1)=\sum_{j\geq1}j^{-2}=\pi^2/6$, and hence
$\Gamma''(1)=\gamma^2+\pi^2/6$. The differentiation is justified
uniformly near $1$ by convergence of $\sum j^{-2}$; the value of that
sum is the classical Basel identity, for example
[NIST DLMF, (25.6.1)](https://dlmf.nist.gov/25.6#E1).
This proves (8.6).

Write $Y=dZ$, where $Z$ takes finitely many positive integer values
with greatest common divisor one, and set

$$
P(z)=\mathbb E z^Z,\qquad
G(z)=\frac{1-P(z)}{1-z},\qquad G(1)=\mathbb EZ=h/d.
$$

The polynomial $G$ has no zero in $|z|\leq1$. For $|z|<1$,
$|P(z)|\leq P(|z|)<1$. On $|z|=1$, equality $P(z)=1$ forces
$z^j=1$ for every support value $j$, since every mass is positive.
Their greatest common divisor is one, so $z=1$. At $1$ the removed
factor has nonzero value $h/d$. Consequently some disk $|z|<r$,
$r>1$, contains no zero of $G$. The analytic logarithm with
$\log G(0)=0$ exists on that disk. If
$-\log G(z)=\sum_{j\geq1}c_jz^j$, Cauchy's coefficient bound on a
smaller disk of radius greater than one gives $|c_j|\leq C\eta^j$
for some $0<\eta<1$.

For $|z|<1$ the absolutely convergent logarithmic series gives

$$
\sum_{m\geq1}\frac{P(z)^m}{m}
 =-\log(1-P(z))=-\log(1-z)-\log G(z).
$$

The coefficient of $z^j$ on the left is $V\{jd\}$, and that of
$-\log(1-z)$ is $1/j$. At real $z\uparrow1$ the chosen logarithm
has value $\log(h/d)$, since $G(z)>0$ for $0\leq z\leq1$.
Summing coefficients through $k$ therefore proves

$$
Q(t)=H_{\lfloor t/d\rfloor}-\log(h/d)
                 +O_p(\eta^{\lfloor t/d\rfloor})\qquad(t\to\infty).
                                                                    \tag{8.7}
$$

The error is uniform over each entire half-open interval
$kd\leq t<(k+1)d$. In particular it includes $t=kd$, with the
right-continuous convention in (8.3). This coefficient calculation
uses neither variance nor a nondegenerate central limit theorem.

Insert (8.7) into (8.3). On $|v|\leq x/3$, put
$k_x=\lfloor(x-v)/d\rfloor$. The uniform harmonic estimate (3.9),
applied with its large variable $x/d$, through order two, yields

$$
\begin{aligned}
H_{k_x}
 ={}&\log(x/d)+\gamma-\frac{r_x(v)-d/2}{x}\\
 &-\frac{r_x(v)^2-dr_x(v)+d^2/6}{2x^2}
      +O_p\bigl((1+|v|)^3/x^3\bigr).
\end{aligned}                                                       \tag{8.8}
$$

Indeed $x/d-k_x=r_x(v)/d$, with
$|r_x(v)|\leq |v|+d$, and the Bernoulli polynomials are
$B_1(z)=z-1/2$ and $B_2(z)=z^2-z+1/6$.
The exponential error in (8.7) is uniform on this central interval.
The bound $Q(s)\leq1+\log(1+s/a)$ for $s\geq0$, with
$a=\min\operatorname{supp}\rho>0$, and $Q(s)=0$ for $s<0$, handles
both complementary tails as in (7.12)–(7.13). The exponential bounds
on $k$ make their integrals, and the tails of the polynomial
coefficient integrals, $O_p(x^{-3})$. Integrating the remainder of
(8.8) costs $O_p(x^{-3})$ by the third absolute moment of $k$.
Since

$$
\int k(v)(r_x(v)-d/2)\,dv
 =\mu+d\int k(v)b((x-v)/d)\,dv=B_p(x),
$$

we obtain

$$
J_p(x)=\log x-\log h+\gamma
       -\frac{B_p(x)}x-\frac{\mathcal C_d(x)}{x^2}+O_p(x^{-3}).       \tag{8.9}
$$

The occurrence error in (6.8) is $O_p(n^{1-\delta}+\log n)$,
$\delta>0$, and hence is $O_p(n/L^3)$. Combining (8.9) at $x=L$
with $(n+1)H_n-n=n\log n+(\gamma-1)n+O(\log n)$ proves (8.4)
for every sufficiently large integer $n$.

For the regularity assertions, absolute convergence in (8.2) follows
from $|r_x(v)|\leq|v|+d$. Put $P_d(z)=z^2-dz+d^2/6$.
Subdivision into $(x-v)/d\in[j,j+1)$ gives

$$
\mathcal C_d(x)=\frac12\sum_{j\in\mathbb Z}
 P_d(x-jd)\int_{x-(j+1)d}^{x-jd}k(v)\,dv.                           \tag{8.10}
$$

On each compact $x$-interval, every differentiated summand is bounded
by a polynomial in $1+|j|$ times $C e^{-d|j|}$. Thus every derivative
series converges uniformly. Formula (8.10) proves real smoothness
at all points, including period endpoints, and reindexing proves
$d$-periodicity. Only $k$ and $d$ occur in its definition.
For fixed $v$, the variable $\{(x-v)/d\}$ is uniform on $[0,1)$
under period averaging in $x$. Therefore

$$
\frac1d\int_0^d P_d(r_x(v))\,dx
 =\int_0^1\bigl[(v+du)^2-d(v+du)+d^2/6\bigr]du=v^2.
$$

Fubini is valid by an integrable quadratic bound in $v$.
Together with (8.6) this proves the asserted mean $c_*$.
When $d=\alpha=\log q$, substitute $v=\alpha w$ in (8.2) and use
$\alpha k(\alpha w)=K_q(w)$: the resulting integral is exactly
$\alpha^2\Phi_{q,2}(x/\alpha)$ from (3.2). This is the already
established uniform second coefficient and proves (8.5).
Proposition 7.4 gives both the zero-variance case and the span and
entropy of $(1/2,1/4,1/4)$, proving the last assertion. $\square$

**Theorem 8.3 (A quantitative sufficient condition).** Suppose some
$c_0>0$ and finite $\kappa\geq0$ satisfy the exact inequality

$$
|1-\varphi_p(t)|\geq c_0(1+|t|)^{-\kappa}
                  \qquad(t\in\mathbb R,\ |t|\geq1).                \tag{8.11}
$$

Then $Y$ is nonarithmetic and, on the full integer sequence,

$$
E_p(n)=M_p(n)+\frac{\mu n}{L}
                   +\frac{c_*n}{L^2}+O_p(n/L^3).                  \tag{8.12}
$$

*Proof.* An arithmetic law would have
$\varphi_p(2\pi j/d)=1$ for all integers $j$, contradicting (8.11).
More generally, for this finite positive law,
$\varphi_p(t)=1$ at a nonzero $t$ forces
$e^{-it(-\log p_i)}=1$ for every $i$, by equality in a convex
combination of points of the unit circle. It would therefore make
$Y$ arithmetic. Thus no additional zeros occur on a bounded
frequency interval away from zero.

We use the following classical result at its stated conditions:
Boyer, *The speed of convergence in the renewal theorem*,
[arXiv:1506.07625v1](https://arxiv.org/pdf/1506.07625v1),
Definition 2.11, Definition 3.5, and Proposition 4.3, pp. 11, 19,
and 31. A Borel probability measure $\rho$ on $\mathbb R$ with an
exponential moment $\int e^{\eta|y|}\rho(dy)<\infty$ for some
$\eta>0$, positive drift $h$, and

$$
\liminf_{|t|\to\infty}|t|^{\kappa}
       |1-\widehat\rho(it)|>0
$$

has $(G-T_h)*f\in\mathcal S(\mathbb R)$ for every Schwartz
function $f$. His conventions are
$\widehat\rho(z)=\int e^{-zy}\rho(dy)$,
$G=\sum_{m\geq0}\widetilde\rho^{*m}$, reflection
$\widetilde\rho(B)=\rho(-B)$, and
$T_h(ds)=h^{-1}\mathbf1_{\{s\leq0\}}ds$.
Our $\rho$ is a finite measure supported in $[a,b_0]$ with
$0<a\leq b_0<\infty$, so it is Borel, has every exponential moment,
and has positive drift $h$. Moreover
$\widehat\rho(it)=\varphi_p(t)$, and (8.11) implies exactly the
positive liminf above. This is the weakly diophantine condition;
a bound on $1-|\widehat\rho(it)|$ is not being assumed.

For clarity, reflection of Boyer's conclusion gives, for each fixed
$g\in\mathcal S(\mathbb R)$ and each integer $N\geq1$,

$$
(U*g)(x)=\frac1h\int_{-\infty}^x g(v)\,dv+O_{p,g,N}(x^{-N})
       =\frac1h\int_{\mathbb R}g(v)\,dv+O_{p,g,N}(x^{-N})
                       \quad(x\to+\infty).                         \tag{8.13}
$$

In fact apply his result to $f(u)=g(-u)$ at $-x$:
$(G*f)(-x)=(U*g)(x)$ and
$(T_h*f)(-x)=h^{-1}\int_{-\infty}^xg$.
The difference is Schwartz, as is the tail integral of $g$ at
$+\infty$. This verifies both the sign and the half-line in (8.13).

We now pass from this classical renewal result to the harmonic
weights in (8.3). Define $\nu(ds)=sV(ds)$. Symmetry of the $m$
independent increments gives the equality of measures

$$
s\rho^{*m}(ds)=m(\rho_y*\rho^{*(m-1)})(ds),\qquad
\nu=\rho_y*U.                                                       \tag{8.14}
$$

To verify it, integrate a nonnegative test function against the first
measure, write $S_m=\sum_{j=1}^mY_j$, and use symmetry to replace
$S_m$ by $mY_1$ inside that expectation. Summing the resulting
identities after division by $m$ proves (8.14) by Tonelli.

All intervals of length one have $U$-mass at most
$2+\lceil1/a\rceil$: pathwise the increasing sums are spaced by at
least $a$, including $S_0$. Hence $\nu$ also has a uniform bound on
its mass in a unit interval, by (8.14) and $\rho_y(\mathbb R)=h$.
Its support is contained in $[a,\infty)$.
For $j=0,1,2$, put $k_j(v)=v^jk(v)$ and
$m_j=\int_{\mathbb R}v^jk(v)\,dv$.
The bounds (7.2) show $k_j$ and $\rho_y*k_j$ are Schwartz.
By (8.13)–(8.14), for every $N$,

$$
(k_j*\nu)(x)=m_j+O_{p,j,N}(x^{-N}),
\qquad m_0=1,\quad m_1=\mu,\quad m_2=2c_*.                         \tag{8.15}
$$

Differentiating the smoothing in (8.3), or integrating by parts
against the distributional derivative $Q'=V$, gives

$$
J_p'(x)=(k*V)(x)=\int_{[a,\infty)}\frac{k(x-s)}s\,\nu(ds).
                                                                    \tag{8.16}
$$

This is ordinary differentiation: $k$ and its derivatives decay
exponentially, while $Q$ grows logarithmically; equivalently the
locally finite measure $V\leq U$ has uniformly bounded unit-interval
mass. Both arguments justify the derivative and its continuity.

For $v=x-s$ with $|v|\leq x/2$, expand

$$
\frac1{x-v}=\frac1x+\frac v{x^2}+\frac{v^2}{x^3}
              +O\left(\frac{|v|^3}{x^4}\right).
$$

The integral of $|v|^3k(v)$ against the translate of $\nu$ is
uniformly bounded, by the unit-interval bound and exponential decay.
The complementary tails in (8.16) are exponentially small:
$s\geq a$ bounds $1/s$, and the same unit-interval estimate sums
the exponential tails of $k(x-s)$. The corresponding tails of the
three expanded moments are exponentially small as well. Substituting
(8.15), with for example $N=4$, thus gives

$$
J_p'(x)=\frac1x+\frac\mu{x^2}+\frac{2c_*}{x^3}+O_p(x^{-4}).         \tag{8.17}
$$

The nonarithmetic first correction (7.13) already fixes the
integration constant:
$J_p(x)-\log x\to\gamma-\log h$.
The derivative of
$J_p(x)-\log x+\mu/x+c_*/x^2$ is $O_p(x^{-4})$.
Integrating that derivative from $x$ to infinity proves

$$
J_p(x)=\log x+\gamma-\log h-\frac\mu x-\frac{c_*}{x^2}
                                      +O_p(x^{-3}).                 \tag{8.18}
$$

Finally (6.8), with its fixed positive $\delta$, turns (8.18) at
$x=L$ into (8.12), exactly as in the final step of Theorem 8.2.
The new inference here is this passage from the classical Schwartz
renewal estimate through the harmonic measure and occurrence
reduction to the specified second coefficient of $E_p(n)$.
$\square$

**Proposition 8.4 (An explicit positive law satisfying (8.11)).** Let
$x$ be the unique number in $(0,1)$ such that
$x+x^{\sqrt2}=1$. The binary law $p=(x,x^{\sqrt2})$ satisfies
(8.11) with $\kappa=2$ and some $c_0>0$, and hence satisfies (8.12).

*Proof.* The function $u\mapsto u+u^{\sqrt2}$ is continuous and
strictly increasing from $0$ to $2$ on $[0,1]$, so the specified
root exists and is unique. Put $a=-\log x>0$. Its information
values are $a$ and $\sqrt2a$, both with positive masses, so their
irrational ratio proves nonarithmeticity by Proposition 7.4.
Let $\|v\|$ denote distance to the nearest integer and put
$u=at/(2\pi)$. Since $1-\cos(2\pi v)\geq8\|v\|^2$,

$$
|1-\varphi_p(t)|\geq1-\operatorname{Re}\varphi_p(t)
 \geq8\min(x,x^{\sqrt2})
                 \bigl(\|u\|^2+\|\sqrt2u\|^2\bigr).              \tag{8.19}
$$

For $|u|\geq1$ choose nearest integers $m$ and $r$ to $u$ and
$\sqrt2u$. Then $m\ne0$, so $2m^2-r^2$ is a nonzero integer.
It follows that

$$
\frac1{\sqrt2|m|+|r|}
 \leq|\sqrt2m-r|
 \leq\sqrt2\|u\|+\|\sqrt2u\|.
$$

The denominator on the left is at most a constant times
$1+|u|$. Squaring and applying Cauchy–Schwarz gives
$\|u\|^2+\|\sqrt2u\|^2\geq c(1+|u|)^{-2}$.
This proves the required bound when $|t|\geq2\pi/a$.
On the remaining compact set $1\leq|t|\leq\max(1,2\pi/a)$,
$1-\varphi_p(t)$ has no zero by nonarithmeticity and the convexity
argument in Theorem 8.3. Its continuous absolute value has a positive
minimum there. Combining the two bounds and rescaling by the fixed
$a/(2\pi)$ proves (8.11) for all $|t|\geq1$ with $\kappa=2$.
This proof bounds $|1-\varphi_p|$ itself; it does not replace it by
$1-|\varphi_p|$. $\square$

**Theorem 8.5 (Actual fixed-law obstruction on a dense set).** For
each fixed integer $q\geq2$, the open probability simplex

$$
\Delta_q^\circ=\{(p_1,\ldots,p_q):p_i>0,\ \sum_i p_i=1\}
$$

contains a dense $G_\delta$ consisting of nonarithmetic laws for
which, for the same fixed law $p$,

$$
\limsup_{n\to\infty}R_n(p)=+\infty,\qquad
\liminf_{n\to\infty}R_n(p)=-\infty.                                \tag{8.20}
$$

Thus their original expectations, after the first correction in
Theorem 7.2, do not have an $O_p(n/L^2)$ remainder.

*Proof.* Arithmetic laws are dense in $\Delta_q^\circ$. To prove
this within the actual letter-law constraint, fix a target $p$ and
write $y_i=-\log p_i$. For positive $\varepsilon\downarrow0$ take
positive integers $m_i(\varepsilon)$ such that
$\varepsilon m_i(\varepsilon)\to y_i$. There is a unique
$d_\varepsilon>0$ with
$\sum_i\exp(-d_\varepsilon m_i(\varepsilon))=1$, since that sum
is continuous and strictly decreasing from $q$ to zero.
For each $0<\eta<1$, at $d=(1-\eta)\varepsilon$ its limit is
$\sum_i p_i^{1-\eta}>1$, while at
$d=(1+\eta)\varepsilon$ its limit is
$\sum_i p_i^{1+\eta}<1$. Therefore
$d_\varepsilon/\varepsilon\to1$, and

$$
p_i^{(\varepsilon)}
 =\exp(-d_\varepsilon m_i(\varepsilon))\longrightarrow p_i.
$$

These are strictly positive normalized laws with arithmetic
information values. This establishes density without changing the
number of letters or introducing arbitrary information masses.

The arithmetic laws form a countable set $\mathcal A_q$: every
one is represented by a tuple of positive integers $(m_1,\ldots,m_q)$
and the unique positive root $d$ of $\sum_i e^{-dm_i}=1$.
Conversely every such tuple gives an arithmetic law. Each singleton
is closed with empty interior in this positive-dimensional simplex.
Thus $\Delta_q^\circ\setminus\mathcal A_q$ is a dense $G_\delta$.

For every arithmetic law, Theorem 7.3 says that $B_p-\mu$ is a
continuous nonzero function of mean zero. It consequently has both
strictly positive and strictly negative values. For either chosen
phase $\theta$, integers
$n_j=\lfloor\exp(d(j+\theta))\rfloor$ satisfy
$\log n_j-d(j+\theta)\to0$; continuity covers both endpoints too.
The already established first correction (7.3) gives

$$
R_n(p)=L\bigl(B_p(L)-\mu\bigr)+o_p(L).
$$

Choosing one phase of each strict sign therefore gives (8.20) for
every arithmetic law. This step uses the published first correction;
no nonarithmetic error-rate assertion has been inferred from it.

For fixed $n$, the exact expectation is a finite polynomial:

$$
E_p(n)=\sum_{w\in\mathcal A^n}D(w)\prod_{j=1}^n p_{i_j}
                    \quad(w=a_{i_1}\cdots a_{i_n}).
$$

The entropy is positive and continuous on the open simplex, so
$R_n(p)$ is continuous there. For positive integers $j,N$, set

$$
\mathcal U_{j,N}^{+}=\bigcup_{n\geq\max(2,N)}\{p:R_n(p)>j\},\qquad
\mathcal U_{j,N}^{-}=\bigcup_{n\geq\max(2,N)}\{p:R_n(p)<-j\}.
                                                                    \tag{8.21}
$$

Both sets are open. Each contains every arithmetic law by (8.20),
and hence is dense. The open simplex, an open subset of a Euclidean
affine space, is a Baire space. The countable intersection

$$
\mathcal G_q=(\Delta_q^\circ\setminus\mathcal A_q)
       \cap\bigcap_{j,N\geq1}
              (\mathcal U_{j,N}^{+}\cap\mathcal U_{j,N}^{-})         \tag{8.22}
$$

is therefore a dense $G_\delta$. Its members are fixed strictly
positive nonarithmetic laws. For each such member, (8.21) supplies
arbitrarily late original integer expectations exceeding each
positive threshold in both signs, which is exactly (8.20).
A bounded $O_p(n/L^2)$ remainder would make $R_n(p)$ bounded,
contradicting (8.20). $\square$

**Theorem 8.6 (One exactly specified binary law with both
obstructions).** There is a single fixed law $p^*=(u^*,1-u^*)$,
$2/5<u^*<3/5$, which is nonarithmetic, satisfies both limits (8.20),
and has an increasing sequence $t_j\to\infty$ such that

$$
0<|1-\varphi_{p^*}(t_j)|<t_j^{-j}.
                                                                    \tag{8.23}
$$

In particular the nonzero denominator is smaller than every inverse
polynomial along that sequence. The following nested-interval rule
is an exact ordinary mathematical specification of this one law.

*Proof.* First establish the open dense conditions needed by the
specification. For binary parameters $u\in(0,1)$, let
$\delta_u(t)=|1-u^{1+it}-(1-u)^{1+it}|$.
For positive integers $j$ and real $T>0$, the set

$$
\mathcal V_{j,T}
 =\bigcup_{t>T}\{u:0<\delta_u(t)<t^{-j}\}                           \tag{8.24}
$$

is open and dense in $(0,1)$. It is open by continuity for fixed
$t$. To prove density, take an arithmetic parameter $u_0$, with
span $d$. At $t_0=2\pi k/d>T$ its denominator is zero. At nearby
$t\ne t_0$ that denominator is nonzero: the derivative of
$1-\varphi_{(u_0,1-u_0)}(t)$ at $t_0$ is $ih\ne0$.
Continuity then makes $0<\delta_{u_0}(t)<t^{-j}$ for some $t>T$
as close to $t_0$ as necessary. Every arithmetic parameter belongs
to (8.24), and these parameters are dense by Theorem 8.5's density
argument. This proves density of (8.24). The union in (8.24) can
also be taken over rational $t>T$: the inequalities are strict and
continuous in $t$, so rational approximation preserves them.

Here is a fixed ordering convention to make every choice unique.
Write a rational as $a/b$ in lowest terms with $b>0$, and assign it
height $|a|+b$. Order finite tuples of a fixed number of integers and
rationals by increasing sum of integer absolute values and rational
heights, breaking ties by lexicographic order of their integer
entries and their reduced numerator-denominator pairs. Every
bounded-height class is finite, so this orders the relevant countable
sets as sequences and every nonempty subset has a first member.

List all positive integer pairs $(m_1,m_2)$ by increasing
$m_1+m_2$, then by $m_1$. For the $\ell$-th pair let $z_\ell$ be
the unique root of
$z^{m_1}+z^{m_2}=1$ in $(0,1)$, and put
$\xi_\ell=z_\ell^{m_1}$. This list includes every binary arithmetic
parameter, allowing repetitions.
Set $I_0=[2/5,3/5]$, $n_0^+=n_0^-=2$, and $t_0=1$.
Recursively, for $j\geq1$, choose the first tuple

$$
(n_j^+,n_j^-,t_j,a_j,b_j)
       \in\mathbb N^2\times\mathbb Q^3
$$

in the ordering just specified that satisfies all the following
conditions, with $I_j=[a_j,b_j]$:

$$
\begin{gathered}
a_j<b_j,\qquad I_j\subset\operatorname{int}I_{j-1},\qquad
b_j-a_j<2^{-j},\qquad
I_j\cap\{\xi_1,\ldots,\xi_j\}=\varnothing,\\
n_j^+,n_j^->\max(j,n_{j-1}^+,n_{j-1}^-),\qquad
t_j>\max(j,t_{j-1}+1),\\
\text{for every }u\in I_j:\quad
 R_{n_j^+}(u,1-u)>j,\qquad R_{n_j^-}(u,1-u)<-j,\\
\text{for every }u\in I_j:\quad
           0<\delta_u(t_j)<t_j^{-j}.
\end{gathered}                                                       \tag{8.25}
$$

A tuple always exists. In the nonempty open interval
$\operatorname{int}I_{j-1}$, intersect the two open dense sets
(8.21) with integer indices larger than all the previously chosen
indices, the open dense set (8.24) with
$T=\max(j,t_{j-1}+1)$, and the complement of the first $j$
arithmetic parameters. This finite intersection of open dense sets
is nonempty and open. Choose a point in it. Membership supplies two
integer witnesses and a rational frequency witness. Continuity of
these three strict inequalities gives an open neighborhood where
the same witnesses work. Inside it choose a rational closed interval
of positive length less than $2^{-j}$, contained in
$\operatorname{int}I_{j-1}$ and avoiding the finitely many excluded
parameters. This produces a tuple satisfying (8.25), so its first
member in the fixed ordering is well defined. No computability
claim is needed for this specification.

The nested compact intervals $I_j$ have diameters tending to zero,
so their intersection is a singleton; define $u^*$ to be that point.
Already $I_1\subset(2/5,3/5)$ proves strict interiority.
For each $\ell$, exclusion of $\xi_\ell$ at stage $j\geq\ell$
proves $u^*\ne\xi_\ell$. Thus $p^*$ is nonarithmetic.
The two integer sequences in (8.25) increase to infinity and give
$R_{n_j^+}(p^*)>j$ and $R_{n_j^-}(p^*)<-j$, proving both limits
in (8.20) for this very law. Its frequency sequence increases to
infinity and gives (8.23). For every fixed $A>0$, when $j>A$ and
$t_j>1$, (8.23) implies $0<|1-\varphi_{p^*}(t_j)|<t_j^{-A}$.
These are separate witnesses for the small-divisor property and the
two original-expectation divergences, all imposed on the same
singleton parameter. In particular failure of (8.11) is not the
argument for the expectation divergences; the latter have their own
integer witnesses in (8.25). $\square$

**Theorem 8.7 (Uniqueness of a second constant without a rate).** Let
$p$ be any fixed strictly positive nonarithmetic law of Definition
6.1. If a finite real constant $C$ satisfies

$$
E_p(n)=M_p(n)+\frac{\mu n}{L}
                     +\frac{Cn}{L^2}+o_p(n/L^2)
                         \quad(n\to\infty,\ n\in\mathbb N),       \tag{8.26}
$$

then $C=c_*$. No polynomial lower bound on $|1-\varphi_p(t)|$ and
no renewal convergence rate is an assumption of this assertion.

*Proof.* We use a real Laplace identity for the harmonic measure,
so no estimate at large imaginary frequencies is required.
For $s>0$ put

$$
f_p(s)=\int e^{-sy}\rho(dy)=\sum_i p_i^{1+s}<1.
$$

Tonelli and $\sum_{m\geq1}z^m/m=-\log(1-z)$ for $0\leq z<1$
give

$$
\int_0^\infty e^{-sx}Q(x)\,dx
 =\frac1s\int e^{-sy}V(dy)
 =-\frac1s\log(1-f_p(s)).                                          \tag{8.27}
$$

For $|s|<1$ the kernel transform is

$$
K(s)=\int_{\mathbb R}e^{-sv}k(v)\,dv
      =\frac{\Gamma(1-s)}{1+s}
      =1-\mu s+c_*s^2+O(s^3).                                     \tag{8.28}
$$

For real $|s|<1$, substitute $z=e^v$ and integrate
$\int_0^1u\int_0^\infty e^{-uz}z^{-s}\,dz\,du$ to obtain the
middle expression. Absolute convergence follows from
$\operatorname{Re}(1-s)>0$ and $\int_0^1u^sdu<\infty$.
Exponential decay of $k$ justifies its Taylor expansion; the moments
(7.2) and (8.6) give the last equality. These are the same Euler
transform calculations as in §§4 and 7, on their actual convergence
strip.

For real $0<s<1$, (8.3), (8.27), and Tonelli imply the exact
bilateral Laplace identity

$$
\mathcal T(s):=\int_{\mathbb R}e^{-sx}J_p(x)\,dx
       =-\frac{K(s)}s\log(1-f_p(s)).                               \tag{8.29}
$$

To justify all subsequent differentiations, note that
$Q(x)\leq1+\log(1+x/a)$ on $x\geq0$ and is zero on $x<0$.
For $x\leq0$, (6.9) and $A(z)\leq z/2$ give

$$
0\leq J_p(x)\leq\frac{e^x}{2}
        \sum_{m\geq1}\frac{(\mathbb Ee^{-Y})^m}{m}=O_p(e^x).
$$

For $x\to+\infty$, (7.13) gives $J_p(x)=O_p(1+\log x)$.
These bounds allow two derivatives under the integral in (8.29)
on every compact subinterval of $0<s<1$.

Near $s=0$, $1-f_p(s)=hs(1+O_p(s))$, with the factor after $hs$
real analytic and equal to one at zero. Hence

$$
-\log(1-f_p(s))=-\log(hs)+A_p(s),
$$

where $A_p$ is real analytic near zero and $A_p(0)=0$.
Multiplying this by (8.28) and dividing by $s$ in (8.29) shows

$$
\mathcal T(s)
 =-\frac{\log(hs)}s+\mu\log(hs)-c_*s\log(hs)
                   +B_p^{\mathrm{an}}(s)+O_p(s^2|\log s|),
                                                                    \tag{8.30}
$$

where $B_p^{\mathrm{an}}$ is analytic near zero; it is unrelated to
the periodic first coefficient $B_p$. The remainder in (8.30) is
an analytic function vanishing to order two times $\log(hs)$.
It can therefore be differentiated twice with error
$O_p(1+|\log s|)$. In particular

$$
\mathcal T''(s)
 =\frac{3-2\log(hs)}{s^3}-\frac\mu{s^2}-\frac{c_*}{s}
                                      +o_p(s^{-1})\quad(s\downarrow0).
                                                                    \tag{8.31}
$$

Now translate the assumed original-expectation asymptotic (8.26),
using (6.8) and its fixed $\delta>0$. At $x=\log n$ it gives

$$
J_p(x)=\log x+\gamma-\log h-\frac\mu x-\frac C{x^2}+o_p(x^{-2}).    \tag{8.32}
$$

This extends to all real $x\to\infty$ without a renewal rate.
Indeed $V\leq U$ has uniformly bounded unit-interval masses by
the spacing argument in Theorem 8.3, independent of (8.11).
Consequently $J_p'=k*V$ exists and is uniformly bounded on
$\mathbb R$. The gap between $x$ and $\log\lfloor e^x\rfloor$
is $O(e^{-x})$; the comparison expression in (8.32) also has a
bounded derivative for large $x$. The extension follows.

The second derivative in (8.29) is
$\int_{\mathbb R}x^2e^{-sx}J_p(x)\,dx$.
Insert (8.32) on the positive half-line. The negative half-line
contributes $O_p(1)$ as $s\downarrow0$. On the positive half-line,
$\int_0^\infty x^{z-1}e^{-sx}dx=\Gamma(z)s^{-z}$ and its
$z$-derivative at $z=3$ give

$$
\begin{aligned}
\mathcal T''(s)
 & =\frac{3-2\gamma-2\log s+2(\gamma-\log h)}{s^3}
                    -\frac\mu{s^2}-\frac C s+o_p(s^{-1})\\
 & =\frac{3-2\log(hs)}{s^3}-\frac\mu{s^2}-\frac C s+o_p(s^{-1}).
\end{aligned}                                                       \tag{8.33}
$$

For the remainder assertion, multiply the error in (8.32) by $x^2$;
it tends to zero. Its Laplace integral is $o(s^{-1})$ by splitting
at a fixed large bound, bounding the tail by
$\varepsilon\int_0^\infty e^{-sx}dx$, and then letting
$\varepsilon\downarrow0$. Changing the comparison on a bounded
interval changes the integral by $O_p(1)$, so its apparent singular
terms at zero create no problem after multiplication by $x^2$.
The values $\Gamma(3)=2$ and $\Gamma'(3)=3-2\gamma$ follow from
$\Gamma(z+1)=z\Gamma(z)$ and $\Gamma'(1)=-\gamma$.
Comparing (8.31) with (8.33), multiplying by $s$, and taking
$s\downarrow0$ proves $C=c_*$. No estimate for a renewal remainder
or for $\varphi_p$ at large frequencies has entered this argument.
$\square$

## 追加锚（本行以下为增补区）
## 9. Strict exponential thresholds for a fixed nonarithmetic source

**Definition 9.1 (The exponential denominator index).** Fix exactly the
ordered alphabet, positive iid vector, word statistic, and endpoints
of Definition 6.1. Retain $h$, $L$, $\mu$, $M_p$, $c_*$, and $R_n(p)$
from (8.1). Throughout this section assume origin-nonarithmeticity
in the sense of Definition 7.1. Put $y_i=-\log p_i$ and

$$
\begin{aligned}
 f_p(s)&=\sum_i p_i e^{-s y_i},&
 D_p(s)&=1-f_p(s),&
 \delta_p(t)&=|D_p(it)|=|1-\varphi_p(t)|,\\
 \beta(p)&=\limsup_{t\to+\infty}
       \frac{\log^+(1/\delta_p(t))}{t},&
 \log^+u&=\max(0,\log u).
\end{aligned}                                                       \tag{9.1}
$$

Here $s$ is a complex variable; $D_p(s)$ is unrelated to the random
word count $D(W_n)$. Positivity of every $p_i$ implies that
$f_p(it)=1$ at nonzero $t$ precisely when $ty_i\in2\pi\mathbb Z$
for every $i$: equality in the convex combination of unit complex
numbers forces each summand to be one. Such a $t$ exists precisely
in the arithmetic case. Thus $\delta_p(t)>0$ for $t\ne0$ under the
present hypotheses, and $\beta(p)\in[0,+\infty]$ is well defined.
All constants below may depend on this one fixed vector, including
its length $q$. No translated-lattice condition is substituted for
origin-nonarithmeticity.

The inputs concerning this exact statistic are the whole results of
§§1–8. In particular §§1–5 supply the uniform fixed-order expansion,
Fourier normalization, and phase endpoints; §6 supplies the weighted
occurrence reduction and entropy term; §7 supplies the first
correction and arithmetic classification; and §8 supplies the
arithmetic second coefficient, the polynomial sufficient class with
its stronger $O_p(n/L^3)$ remainder, the dense $G_\delta$ obstruction,
its specified example, and second-constant uniqueness. The inference
below concerns individual fixed nonarithmetic laws outside the
polynomial class as well as within it.

**Theorem 9.2 (The two strict exponential sides).** For every fixed
positive origin-nonarithmetic vector of Definition 9.1,

$$
\beta(p)<\frac\pi2
\quad\Longrightarrow\quad
 E_p(n)=M_p(n)+\frac{\mu n}{L}+\frac{c_*n}{L^2}
                                      +o_p(n/L^2)                 \tag{9.2}
$$

on all integers $n\to\infty$. Equivalently, $R_n(p)\to c_*$.
On the other strict side,

$$
\beta(p)>\frac\pi2
\quad\Longrightarrow\quad
 \limsup_{\substack{n\to\infty\\n\in\mathbb N}}|R_n(p)|=+\infty,
                                                                    \tag{9.3}
$$

including $\beta(p)=+\infty$. Consequently boundedness of $R_n(p)$
requires $\beta(p)\leq\pi/2$. These assertions give no classification
at equality $\beta(p)=\pi/2$.

*Proof.* Write $a_0=\min_i y_i>0$ and $b_0=\max_i y_i<\infty$.
Use exactly the measures $U,V$, the function $Q$, and the smoothing
$J_p$ in (8.3). Their origin is the weighted reduction (6.8), not an
application of a uniform-source formula to biased letters. From
(6.8), with its fixed $\delta_0=a_0/(4\log q)>0$, we have

$$
\frac{E_p(n)}n
 =\log n+\gamma-1-J_p(\log n)
                 +O_p(n^{-\delta_0}+\log n/n).                    \tag{9.4}
$$

Thus an $o(x^{-2})$ statement for $J_p(x)$ at real $x\to\infty$
will give the full integer assertion (9.2). We shall also justify
the reverse transfer needed for (9.3).

First define a comparison function, independent of any convergence
rate, by

$$
 g_h(u)=\begin{cases}\log u+\gamma-\log h,&u>0,\\0,&u\leq0,
 \end{cases}
 \qquad J_0(x)=\int_{\mathbb R}k(v)g_h(x-v)\,dv,
 \qquad H(x)=J_p(x)-J_0(x).                                        \tag{9.5}
$$

The logarithmic singularity is locally integrable. Exponential
decay of $k$ and its derivatives makes $J_0$ continuous, indeed
smooth, and gives $J_0(x)=O_p(e^x)$ for $x\leq0$. For example, with
$u=x-v>0$ its absolute value there is at most
$C e^x\int_0^\infty e^{-u}|\log u+\gamma-\log h|\,du$.
The moments (7.2) and (8.6) give

$$
 J_0(x)=\log x+\gamma-\log h-\frac\mu x-\frac{c_*}{x^2}
                                         +O_p(x^{-3}).             \tag{9.6}
$$

Here is an explicit tail justification for this expansion. On
$|v|\leq x/2$, Taylor's theorem gives
$\log(x-v)=\log x-v/x-v^2/(2x^2)+O(|v|^3/x^3)$.
Integrate using the first three moments of $k$. For $v<-x/2$,
exponential decay absorbs $\log(x+|v|)$ and the polynomial comparison
terms. For $x/2<v<x$, put $u=x-v$ and bound the integrand by
$Ce^{-x+u}(|\log u|+C_p)$ on $0<u<x/2$; its integral is
$O_p(e^{-x/2}(1+x+\log(x+1)))$. For $v\geq x$, $g_h(x-v)=0$.
The removed polynomial tails also decay exponentially. This proves
(9.6) with all the original smoothing endpoints intact.

For $0<\operatorname{Re}s<1$ put

$$
 K(s)=\frac{\Gamma(1-s)}{1+s},\qquad A_0(s)=\frac{K(s)}s,
 \qquad
 \ell(s)=\log D_p(s)-\log h-\log s.
$$

Both logarithms in the last expression are the analytic branches
on the right half-plane with real values on its positive real axis.
Indeed, $|f_p(s)|\leq f_p(\operatorname{Re}s)<1$, so
$\operatorname{Re}D_p(s)>0$. Near zero,
$D_p(s)=hs+O_p(s^2)$; hence $\ell$ extends analytically across zero,
with $\ell(0)=0$. Reuse the exact transform (8.29) and the kernel
transform (8.28). Their complex versions on this strip follow by
absolute convergence: $Q$ vanishes on the negative half-line and
grows at most logarithmically, $J_p(x)=O_p(e^x)$ as $x\to-\infty$,
and the series for $-\log(1-f_p(s))$ converges absolutely because
$|f_p(s)|<1$. Also

$$
 \int_0^\infty e^{-su}(\log u+\gamma-\log h)\,du
                              =-\frac{\log(hs)}s.
$$

This equality follows by differentiating
$\Gamma(z)s^{-z}$ at $z=1$, initially for positive real $s$ and
then by analyticity on $\operatorname{Re}s>0$. All differentiated
integrals converge absolutely. Fubini in (9.5) now proves

$$
 \mathcal H(s):=\int_{\mathbb R}e^{-sx}H(x)\,dx
                         =-A_0(s)\ell(s).                        \tag{9.7}
$$

The singularity of its right side at zero is removable.

We record precisely the classical Gamma estimates consumed below.
Stirling's expansion and its logarithmic derivative, in the sectors
$|\arg z|\leq\pi-\varepsilon$, are
[NIST DLMF (5.11.1)–(5.11.2)](https://dlmf.nist.gov/5.11#E1).
Together with
[the convergent series (5.15.1)](https://dlmf.nist.gov/5.15#E1)
for $\psi'(z)$, they imply, uniformly for
$0\leq\sigma\leq1/4$ and $|t|\geq2$,

$$
\begin{aligned}
 |A_0(\sigma+it)|&\asymp
       |t|^{-3/2-\sigma}e^{-\pi|t|/2},\\
 |A_0'(\sigma+it)/A_0(\sigma+it)|
       &\leq C\log(2+|t|),\\
 |A_0^{(r)}(\sigma+it)|
       &\leq C(1+|t|)^C e^{-\pi|t|/2}\qquad(0\leq r\leq2).
\end{aligned}                                                       \tag{9.8}
$$

The constants in $\asymp$ are positive and independent of $\sigma,t$
in this strip. To check the substitution, take $z=1-\sigma-it$,
whose real part is in $[3/4,1]$ and whose argument stays in a fixed
closed sector away from the negative real axis. Stirling gives
$|\Gamma(z)|\asymp |t|^{1/2-\sigma}e^{-\pi|t|/2}$;
dividing by $s(1+s)$ gives the first line. Logarithmic
differentiation gives
$A_0'/A_0=-\psi(1-s)-1/s-1/(1+s)$, proving the second.
The series for $\psi'$ is bounded in this strip by
$\sum_{m\geq0}((m+3/4)^2+t^2)^{-1}\leq C$.
One more differentiation proves the last line. Thus the exponential
constant used here is exactly $\pi/2$.

Suppose first that $\beta(p)<\pi/2$, and fix once and for all a real
number $b$ with $\beta(p)<b<\pi/2$. By the definition of limsup,
symmetry in $t$, and compactness away from the sole zero at zero,
there is $c_b>0$ such that

$$
 \delta_p(t)\geq c_b e^{-b|t|}\qquad(|t|\geq1).                    \tag{9.9}
$$

A local integral bound will avoid squaring the exponential index
when differentiating a logarithm twice. For $D(t)=D_p(it)$,

$$
 \sum_i p_i|e^{-ity_i}-1|^2=2\operatorname{Re}D(t)
                                                   \leq2|D(t)|.
$$

Cauchy–Schwarz consequently gives
$|D'(t)-ih|\leq(2\mathbb EY^2|D(t)|)^{1/2}$.
Also $|D''(t)|\leq\mathbb EY^2$. Choose fixed $\varepsilon>0$ and
$r\in(0,1)$ small enough that

$$
 |D(t_0)|<\varepsilon,\quad |t-t_0|\leq r
       \quad\Longrightarrow\quad
          \frac{d}{dt}\operatorname{Im}D(t)\geq h/2.              \tag{9.10}
$$

For example make the displayed square-root bound at $t_0$ at most
$h/4$, and then choose $r\mathbb EY^2\leq h/4$.
In a unit interval $[T,T+1]$, take a maximal $r$-separated collection
of points where $|D|<\varepsilon$. It has at most $2+1/r$ members,
and intervals of radius $r$ around them cover the small-value set.
On each such interval (9.10) makes $u=\operatorname{Im}D(t)$ a
strictly increasing coordinate. If

$$
 m_T=\min_{T-r\leq t\leq T+1+r}|D(t)|>0,
$$

then $|D(t)|^2\geq\max(m_T^2,u^2)$, and therefore

$$
 \int_{t_0-r}^{t_0+r}\frac{dt}{|D(t)|^2}
 \leq\frac2h\int_{\mathbb R}\frac{du}{\max(m_T^2,u^2)}
 \leq\frac{C_p}{m_T}.
$$

On the rest of the unit interval use $|D|\geq\varepsilon$.
For $T\geq2$, (9.9) on the enlarged interval yields

$$
 \int_T^{T+1}\bigl(1+\delta_p(t)^{-1}+\delta_p(t)^{-2}\bigr)dt
                                           \leq C_{p,b}e^{bT}.
                                                                    \tag{9.11}
$$

The $\delta_p^{-1}$ term is bounded by $1+\delta_p^{-2}$.
Negative unit intervals have the same bound by conjugation.
This argument requires only finitely many support values with
positive masses and positive finite $h$; repeated values cause no
change.

Define on the real frequency line

$$
 \Psi(t)=-A_0(it)\bigl[\log D_p(it)-\log h-\log(it)\bigr],           \tag{9.12}
$$

taking the continuous value at $t=0$ from (9.7). For $t\ne0$ the
logarithms are the limits from the right half-plane. They are
smooth because $D_p(it)\ne0$, and their imaginary parts are
bounded. In particular
$|\log D_p(it)|\leq C_{p,b}+b|t|$ for $|t|\geq1$ by (9.9) and
$|D_p(it)|\leq2$. Since the first two derivatives of $D_p(it)$ are
bounded, differentiation gives

$$
 \left|\frac{d}{dt}\log D_p(it)\right|\leq C_p\delta_p(t)^{-1},
 \qquad
 \left|\frac{d^2}{dt^2}\log D_p(it)\right|
       \leq C_p(\delta_p(t)^{-1}+\delta_p(t)^{-2}).
$$

The corresponding derivatives of $\log(it)$ are $1/t$ and
$-1/t^2$. Combining these bounds with (9.8) and integrating on unit
intervals using (9.11) proves

$$
 \Psi,\ \Psi',\ \Psi''\in L^1(\mathbb R),\qquad
 \Psi(t),\Psi'(t)\longrightarrow0\quad(t\to\pm\infty).             \tag{9.13}
$$

At zero these assertions use the removable analytic expression,
not separate singular bounds on its factors. At infinity all
unit-interval integrals are bounded by a fixed polynomial in
$1+|T|$ times $e^{-(\pi/2-b)|T|}$, which is summable.
For the pointwise limit of $\Psi'$ it suffices to use (9.9)
directly, since its denominator occurs only to the first power.

We justify the inverse-transform identification, including the
boundary limit. Uniformly for $0\leq\sigma\leq1/4$,

$$
 |D_p(\sigma+it)|\geq c_p|D_p(it)|.                               \tag{9.14}
$$

Indeed $|D_p(\sigma+it)-D_p(it)|\leq h\sigma$.
If $|D_p(it)|\geq2h\sigma$, use the triangle inequality.
Otherwise use
$\operatorname{Re}D_p(\sigma+it)\geq1-f_p(\sigma)\geq c_p\sigma$;
the last inequality follows by taking the positive minimum of
$(1-f_p(\sigma))/\sigma$ on $[0,1/4]$, with value $h$ at zero.
This proves (9.14). The imaginary parts of both logarithms remain
bounded, so (9.9), (9.14), and (9.8) dominate
$\mathcal H(\sigma+it)$ by an integrable exponential times a fixed
polynomial in $|t|$, uniformly for $0<\sigma\leq1/4$ and
$|t|\geq1$. On bounded frequency intervals use compactness and the
removable singularity at zero. Dominated convergence gives

$$
 \mathcal H(\sigma+i\,\cdot)\longrightarrow\Psi
                      \quad\hbox{in }L^1(\mathbb R)
                      \quad(\sigma\downarrow0).                  \tag{9.15}
$$

For each $0<\sigma\leq1/4$ the continuous function $e^{-\sigma x}H(x)$
is integrable. This follows from logarithmic growth at $+\infty$
and exponential decay at $-\infty$ of both terms of (9.5).
Its Fourier transform is (9.7), with convention
$\widehat f(t)=\int e^{-itx}f(x)dx$.
The elementary $L^1$ Fourier inversion theorem, applied using the
integrability just proved, gives

$$
 e^{-\sigma x}H(x)=\frac1{2\pi}\int_{\mathbb R}
                 e^{itx}\mathcal H(\sigma+it)\,dt.
$$

One may obtain this version directly by multiplying the transform
by $e^{-\eta t^2}$, using Fubini and the Gaussian integral, then
letting $\eta\downarrow0$: Gaussian convolution tends to the
continuous original function, and dominated convergence applies to
its integrable transform. Thus no distributional boundary
assumption is needed. Letting $\sigma\downarrow0$ in this equality
using (9.15), and then integrating by parts twice using (9.13), gives

$$
 H(x)=\frac1{2\pi}\int e^{itx}\Psi(t)dt
     =-\frac1{2\pi x^2}\int e^{itx}\Psi''(t)dt=o_p(x^{-2}).         \tag{9.16}
$$

For the last limit the Riemann–Lebesgue lemma needs only
$\Psi''\in L^1$: approximate it in $L^1$ by finite step functions
of bounded support, whose oscillatory integrals tend to zero by
explicit integration on their intervals. Equations (9.6), (9.16),
and (9.4) prove (9.2), with no omitted integer subsequence.

For the other side suppose, toward a contradiction, that $R_n(p)$
is bounded for all sufficiently large integers $n$. Equation (9.4)
then gives, at $x=\log n$,

$$
 J_p(x)=\log x+\gamma-\log h-\mu/x+O_p(x^{-2}).                   \tag{9.17}
$$

This extends to every real $x\to+\infty$. To verify the extension,
the sums defining $U$ have pathwise spacing at least $a_0$; hence
$U$, and therefore $V\leq U$, has uniformly bounded mass in each
unit interval. Differentiation of (8.3), with its exponentially
decaying kernel, gives $J_p'=k*V$, uniformly bounded on the whole
real line. The distance between $x$ and
$\log\lfloor e^x\rfloor$ is $O(e^{-x})$; the comparison function
in (9.17) also has bounded derivative for large $x$. The
interpolation error is therefore $O_p(e^{-x})$. In view of (9.6),
(9.17) implies $H(x)=O_p(x^{-2})$ at $+\infty$.
At $-\infty$ we already have $H(x)=O_p(e^x)$.
Consequently differentiation of the absolutely convergent integral
(9.7) gives, uniformly in real $t$ and $0<\sigma\leq1/4$,

$$
 |\mathcal H'(\sigma+it)|
 \leq\int_{\mathbb R}|x|e^{-\sigma x}|H(x)|dx
 \leq C_p\bigl(1+\log(1/\sigma)\bigr).                            \tag{9.18}
$$

For example split the positive tail at $1/\sigma$ and use
$|xH(x)|\leq C_p/x$; the negative tail is integrable uniformly.
No bound on $\beta(p)$ has entered (9.18).

If $\beta(p)>\pi/2$, choose a finite $b>\pi/2$ below $\beta(p)$.
There are $t_j\to+\infty$ with
$\delta_j:=\delta_p(t_j)<e^{-bt_j}$.
This also follows when $\beta(p)=+\infty$.
Put $u_j=\log(1/\delta_j)$ and $s_j=\delta_j+it_j$.
The estimates used in (9.14) give

$$
 c_p\delta_j\leq|D_p(s_j)|\leq(1+h)\delta_j.
$$

Moreover

$$
 |D_p'(s_j)-h|
 \leq\sum_i p_i y_i|e^{-it_jy_i}-1|+\delta_j\mathbb EY^2
 \leq(2\mathbb EY^2\delta_j)^{1/2}
                                  +\delta_j\mathbb EY^2\to0.
$$

Here the prime is now the complex derivative; the factor $i$ in
(9.10) came from differentiating along the imaginary axis.
It follows that $|D_p'(s_j)|\geq h/2$ for all sufficiently large $j$.
The branch choices in (9.7) give
$|\ell(s_j)|\leq C_p+u_j+\log t_j$. Differentiating (9.7) exactly,

$$
 \mathcal H'(s)=-A_0'(s)\ell(s)
                  -A_0(s)\left(\frac{D_p'(s)}{D_p(s)}-\frac1s\right).
$$

At $s_j$ the $D_p'/D_p$ term has magnitude at least
$c_p|A_0(s_j)|/\delta_j$. The sum of the other terms is at most

$$
 C_p|A_0(s_j)|\log(2+t_j)(1+u_j+\log t_j).
$$

Dividing this error by $|A_0(s_j)|/\delta_j$ gives a quantity
tending to zero: $u_j\geq bt_j$ and
$e^{-u_j}(1+u_j)\log(2+u_j)\to0$.
Also $t_j^{-\delta_j}$ stays bounded away from zero, since
$\delta_j\log t_j\to0$. The lower estimate in (9.8) therefore yields

$$
 |\mathcal H'(s_j)|\geq
     c_p t_j^{-3/2}\exp(u_j-\pi t_j/2).                            \tag{9.19}
$$

Comparison with (9.18) would bound
$t_j^{-3/2}e^{u_j-\pi t_j/2}/(1+u_j)$.
But $e^u/(1+u)$ increases for $u>0$, so this ratio is at least

$$
 \frac{e^{(b-\pi/2)t_j}}{t_j^{3/2}(1+bt_j)}\longrightarrow+\infty.
$$

This contradiction excludes boundedness of the original integer
residual. A nonnegative sequence has finite limsup precisely when
it is eventually bounded; applying this to $|R_n(p)|$ proves (9.3).
It supplies neither separate signs nor a divergence rate.
The necessary condition and the unclassified equality endpoint
follow exactly as stated. $\square$

## 10. The binary index and continued fractions

**Theorem 10.1 (Exact binary translation).** Let $p=(p_1,p_2)$ be
any fixed positive binary origin-nonarithmetic law. Put

$$
 a=-\log p_1>0,\qquad \alpha=\frac{-\log p_2}{a},
 \qquad \alpha=[b_0;b_1,b_2,\ldots],
$$

and let $P_j/Q_j$ be its simple continued-fraction convergents,
with $Q_{-1}=0$, $Q_0=1$, and
$Q_{j+1}=b_{j+1}Q_j+Q_{j-1}$. Then $\alpha$ is irrational and

$$
 \boxed{\displaystyle
 \beta(p)=\frac a\pi\limsup_{j\to\infty}
                            \frac{\log Q_{j+1}}{Q_j}.}            \tag{10.1}
$$

This is an identity in $[0,+\infty]$. The continued-fraction and
irrationality-base ingredients are classical: Sondow,
*Irrationality measures, irrationality bases, and a theorem of
Jarník*, [arXiv:math/0406300v1](https://arxiv.org/pdf/math/0406300v1),
§3, Lemmas 1–2 and Theorem 1, equation (3), pp. 4–6.
His irrationality base, denoted here by $B(\alpha)$ to distinguish
it from (9.1), satisfies
$\log B(\alpha)=\limsup_j(\log Q_{j+1})/Q_j$.
The source-specific inference in (10.1) is the factor $a/\pi$
for the continuously varying frequency of this probability law.

*Proof.* Proposition 7.4 gives irrationality of $\alpha$, since
its rationality is equivalent to origin-arithmeticity. Define

$$
 \lambda(\alpha)=\limsup_{m\to\infty}
                  \frac{\log(1/\|m\alpha\|)}m,
$$

where $\|\cdot\|$ is distance to the nearest integer.
We first spell out the classical parameter conversion. The
definition of $B(\alpha)$ in Sondow's Definition 3 uses the eventual
lower bound $|\alpha-r/m|>(B+\varepsilon)^{-m}$ for all integers
$r,m$ with $m$ sufficiently large. Minimization over $r$ gives
$\|m\alpha\|/m$. The difference between the logarithmic exponents
of $\|m\alpha\|/m$ and $\|m\alpha\|$ is $\log m/m\to0$.
The definition of a limsup, including an infinite one, therefore
gives $\lambda(\alpha)=\log B(\alpha)$.
Sondow's equation (3) gives

$$
 \lambda(\alpha)=\limsup_j\frac{\log Q_{j+1}}{Q_j}.                \tag{10.2}
$$

The convergent error inequalities used there are
$1/(2Q_jQ_{j+1})<|\alpha-P_j/Q_j|<1/(Q_jQ_{j+1})$;
these and Legendre's criterion isolate every exponentially good
rational approximation among the convergents. Multiplication by
$Q_j$ changes their logarithmic bounds by at most $\log2$, and
hence does not alter (10.2). Thus neither (10.2) nor the
continued-fraction existence machinery is a new assertion about
irrational numbers here.

It remains to compute the continuous-frequency index from
$\lambda(\alpha)$. Write $w=p_1$, $z=p_2$, and $u=at/(2\pi)$.
The real part gives the elementary bound

$$
 \delta_p(t)\geq8\min(w,z)
                           (\|u\|^2+\|\alpha u\|^2),             \tag{10.3}
$$

using $1-\cos(2\pi v)\geq8\|v\|^2$.
If $m$ is a nearest integer to $u$, the circle-distance triangle
inequality gives

$$
 \|m\alpha\|\leq\alpha\|u\|+\|\alpha u\|,
 \qquad \delta_p(t)\geq c_p\|m\alpha\|^2.                         \tag{10.4}
$$

For $t\to+\infty$, $m\to+\infty$ and
$t=2\pi(m+O(1))/a$. If $\lambda(\alpha)<+\infty$, for every
$\varepsilon>0$ the defining limsup gives eventually
$\log(1/\|m\alpha\|)\leq(\lambda(\alpha)+\varepsilon)m$.
Equations (10.4) and (9.1) consequently yield
$\beta(p)\leq a(\lambda(\alpha)+\varepsilon)/\pi$.
Let $\varepsilon\downarrow0$. This proves the required upper
bound also when $\lambda=0$; when $\lambda=+\infty$ it is vacuous.

For the matching lower bound choose any positive integer $m$ and
a nearest integer $r$ to $m\alpha$, and set

$$
 \epsilon_m=m\alpha-r,\qquad
 u_m=m-\frac{z\epsilon_m}{w+z\alpha},\qquad t_m=2\pi u_m/a.
                                                                    \tag{10.5}
$$

For all sufficiently large $m$, $u_m>0$. The two centered phase
errors are

$$
 u_m-m=-\frac{z\epsilon_m}{w+z\alpha},\qquad
 \alpha u_m-r=\frac{w\epsilon_m}{w+z\alpha}.
$$

Their weighted linear combination is zero. The elementary estimate
$|e^{-i\theta}-1+i\theta|\leq\theta^2/2$, obtained by integrating
the second derivative on the real segment from $0$ to $\theta$,
therefore implies

$$
 0<\delta_p(t_m)\leq C_p\epsilon_m^2.                              \tag{10.6}
$$

Strict positivity is the nonarithmetic zero criterion in
Definition 9.1. Also $t_m=2\pi(m+O(1))/a$.
If $0<\lambda(\alpha)<+\infty$, choose integers $m$ along which
$\log(1/\|m\alpha\|)/m\to\lambda(\alpha)$; (10.6) gives
$\beta(p)\geq a\lambda(\alpha)/\pi$.
If $\lambda=+\infty$, choose the ratios tending to infinity and
obtain $\beta=+\infty$ by the same inequality.
If $\lambda=0$, $\beta\geq0$ already gives the lower bound.
Combining these cases with (10.2) proves (10.1) on the entire
stated domain. $\square$

## 11. Two fixed binary consumers specified without residuals

**Definition 11.1 (Two convergent specifications).** For each
$\nu\in\{1,2\}$ define positive integers recursively by

$$
\begin{gathered}
 b_0^{(\nu)}=1,\quad b_1^{(\nu)}=2,\quad
 Q_{-1}^{(\nu)}=0,\quad Q_0^{(\nu)}=1,\quad Q_1^{(\nu)}=2,\\
 b_{j+1}^{(\nu)}=\left\lceil
                 \exp((Q_j^{(\nu)})^\nu)\right\rceil,\qquad
 Q_{j+1}^{(\nu)}=b_{j+1}^{(\nu)}Q_j^{(\nu)}+Q_{j-1}^{(\nu)}
                                                    \quad(j\geq1),\\
 \alpha_\nu=[1;2,b_2^{(\nu)},b_3^{(\nu)},\ldots].
\end{gathered}                                                       \tag{11.1}
$$

Let $x_\nu$ be the unique root in $(0,1)$ of
$x+x^{\alpha_\nu}=1$, put $a_\nu=-\log x_\nu$, and fix the ordered
binary letter probabilities

$$
 p^{(\nu)}=(x_\nu,x_\nu^{\alpha_\nu}).                              \tag{11.2}
$$

These recursions and scalar equations contain no expectation,
residual, or asymptotic test as a defining parameter.

**Theorem 11.2 (A convergent law beyond every polynomial bound, and
an unbounded law).** Both specifications (11.1)–(11.2) converge to
fixed positive binary nonarithmetic laws. They satisfy

$$
 0<\beta(p^{(1)})=a_1/\pi<\pi/2,\qquad
 R_n(p^{(1)})\longrightarrow c_*                                  \tag{11.3}
$$

on all integers $n\to\infty$, although $p^{(1)}$ satisfies no
inequality (8.11) for any $c_0>0$ and finite $\kappa\geq0$.
For the other fixed law,

$$
 \beta(p^{(2)})=+\infty,\qquad
 \limsup_{\substack{n\to\infty\\n\in\mathbb N}}
                          |R_n(p^{(2)})|=+\infty.                 \tag{11.4}
$$

The second assertion concerns the actual distinct-word expectation;
it asserts neither separate divergence signs nor a rate.

*Proof.* The elementary simple continued-fraction convergence
facts used in Theorem 10.1 apply since all the partial quotients
after $b_0$ are positive integers. To detail convergence, define
$P_{-1}=1$, $P_0=1$ and
$P_{j+1}=b_{j+1}P_j+P_{j-1}$ for each of the two recursions.
The determinant identity
$|P_{j+1}Q_j-P_jQ_{j+1}|=1$ follows by induction.
Also $Q_{j+1}\geq Q_j+Q_{j-1}$ and the $Q_j$ increase to infinity.
The intervals between consecutive convergents are nested and
have lengths $1/(Q_jQ_{j+1})\to0$: the next convergent is a strict
weighted mean of the previous two, by their recursions.
They consequently define exactly one limit $\alpha_\nu$, and
$|\alpha_\nu-P_j/Q_j|\leq1/(Q_jQ_{j+1})$.
This limit is irrational. If it were $r/s$ in lowest terms, every
unequal convergent would be at distance at least $1/(sQ_j)$,
contradicting that bound when $Q_{j+1}>s$; infinitely many
convergents are unequal to $r/s$ by the determinant identity.
The same nesting, starting with $1$ and $3/2$, puts the limit in
$(1,3/2)$. More explicitly, the tail after the initial $2$ is
strictly positive and finite, so
$\alpha_\nu=1+1/(2+1/\xi)$ with $\xi>0$; irrationality excludes
both rational endpoints.

For each real $\alpha>0$ the function $x\mapsto x+x^\alpha$
is continuous and strictly increasing on $[0,1]$, from $0$ to $2$.
Thus (11.2) specifies one positive normalized law uniquely.
Since $\alpha_\nu>1$, its root obeys $x_\nu>1/2$ and hence

$$
 0<a_\nu<\log2.
$$

This also supplies convergence at the level of probability vectors.
Let $x_{\nu,j}$ be the unique root of
$x+x^{P_j^{(\nu)}/Q_j^{(\nu)}}=1$. For each $\eta>0$ smaller
than both $x_\nu$ and $1-x_\nu$, strict monotonicity at
$x_\nu-\eta,x_\nu+\eta$ and continuity in the exponent put
$x_{\nu,j}$ between these two numbers for all sufficiently large
$j$. Therefore $x_{\nu,j}\to x_\nu$, and
$(x_{\nu,j},x_{\nu,j}^{P_j^{(\nu)}/Q_j^{(\nu)}})\to p^{(\nu)}$.
The information values of (11.2) are exactly
$a_\nu,\alpha_\nu a_\nu$ with masses
$x_\nu,x_\nu^{\alpha_\nu}$; their irrational ratio proves
origin-nonarithmeticity. The law is now fixed independently of $n$.

For $Q=Q_j^{(\nu)}$, the ceiling in (11.1) gives

$$
 \log b_{j+1}^{(\nu)}=Q^\nu+O(e^{-Q^\nu}),\qquad
 \log Q_{j+1}^{(\nu)}=Q^\nu+\log Q+O(1).                           \tag{11.5}
$$

For the second equality use the exact denominator recurrence and
$0\leq Q_{j-1}/(b_{j+1}Q_j)\leq1/b_{j+1}$.
Consequently

$$
 \lim_j\frac{\log Q_{j+1}^{(1)}}{Q_j^{(1)}}=1,
 \qquad
 \lim_j\frac{\log Q_{j+1}^{(2)}}{Q_j^{(2)}}=+\infty.
$$

Theorem 10.1 gives $\beta(p^{(1)})=a_1/\pi$ and
$\beta(p^{(2)})=+\infty$. The strict inequality in (11.3) follows
from $a_1<\log2<1<\pi^2/2$. Applying Theorem 9.2 proves the two
claims about the original integer residuals, including (11.4).

For completeness the failure of every polynomial bound in the
first example has direct frequencies as well. Take $m=Q_j^{(1)}$
and $r=P_j^{(1)}$ in (10.5). The classical convergent inequality
quoted in Theorem 10.1 gives
$|m\alpha_1-r|<1/Q_{j+1}^{(1)}$; it is less than $1/2$ for all
sufficiently large $j$, so $r$ is the nearest integer as required.
Equation (10.6) and (11.5) show, with fixed constants,

$$
 t_j\sim\frac{2\pi Q_j^{(1)}}{a_1},\qquad
 0<\delta_{p^{(1)}}(t_j)
       \leq\frac{C_p}{(Q_{j+1}^{(1)})^2}
       \leq C_p\exp(-2Q_j^{(1)}).
$$

For every fixed finite $\kappa\geq0$, multiplication by
$(1+t_j)^\kappa$ makes this upper bound tend to zero.
It therefore contradicts every proposed positive lower constant
$c_0$ in (8.11). Convergence in (11.3) follows from the strict
exponential sufficient side, without a polynomial lower bound.
The construction supplies no $O_p(n/L^3)$ claim for this law.
For (11.4), the argument is the obstruction (9.18)–(9.19) applied
to this very law, rather than failure of (8.11) alone. $\square$

## 12. Source correspondence and mathematical boundaries

The fixed-source parameter correspondence is $Y=-\log p_I$ with
$\mathbb P(I=i)=p_i$, $S_m=Y_1+\cdots+Y_m$,
$f_p(s)=\mathbb Ee^{-sY}$, and $\varphi_p(t)=f_p(it)$.
Coincident $y_i$ have their letter masses added; no independent
choice of information masses is made. The increasing bijection
$a_i\mapsto i-1$ preserves the order, rotations, contiguous words,
and word equality. The finite-word statistic, including letters,
all lengths $1\leq m\leq n$, all starts $0\leq i\leq n-m$, and a
whole word exactly when Lyndon, is therefore precisely that of the
six complete suppliers: the
[Lyndon order source](https://github.com/the-omega-institute/trureturing/blob/66f6190119f8ac52725861db2e53df22a9fb620b/D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.lean)
and its
[Scribe](https://github.com/the-omega-institute/trureturing/blob/66f6190119f8ac52725861db2e53df22a9fb620b/Blueprint/D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder.scribe.cs),
the
[distinct-factor source](https://github.com/the-omega-institute/trureturing/blob/66f6190119f8ac52725861db2e53df22a9fb620b/D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.lean)
and its
[Scribe](https://github.com/the-omega-institute/trureturing/blob/66f6190119f8ac52725861db2e53df22a9fb620b/Blueprint/D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.scribe.cs),
the
[Glen–Simpson–Smyth source note](https://github.com/the-omega-institute/trureturing/blob/66f6190119f8ac52725861db2e53df22a9fb620b/Library/Automata/glensimpsonsmyth2017lyndonfactors.md),
and the complete [§§1–8 of this volume](https://github.com/the-omega-institute/trureturing/blob/66f6190119f8ac52725861db2e53df22a9fb620b/docs/develop/theory/LYNDON_DISTINCT_FACTOR_PERIODIC_ASYMPTOTICS.md).
The proof-local suffix and factor arguments in those suppliers have
the roles specified in §§2 and 6. Their finite Christoffel-minimum
refutation and its stated boundaries retain their own meaning;
the expectation reduction used here is (6.8)–(6.9).

For the original published word convention, the consumed source is
Glen, Simpson, and Smyth,
[*Counting Lyndon factors*, arXiv:1701.00928v1](https://arxiv.org/pdf/1701.00928v1),
§§1, 3–4 and equation (6), with their $\sigma=q$. The version map
to $E_{DF}$ in Hirakawa, Nakashima, Inenaga, and Takeda,
[*Counting Lyndon Subsequences*, arXiv:2106.01190v2](https://arxiv.org/pdf/2106.01190v2),
Table 1, p. 2, is the one in Definition 1.1.
The weighted zero-event estimate is consumed through §6 from
Arratia, Goldstein, and Gordon,
[*Two moments suffice for Poisson approximations: the Chen–Stein method*](https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/AGG-1.pdf),
§2, Theorem 1, pp. 10–11: finite Bernoulli occurrence indicators,
positive finite mean, dependence neighborhoods containing their
indices, $b_2=b_3=0$ by borderlessness and iid independence.
The uniform harmonic-sum and Gamma-transform ingredients retain the
attribution in §§3–4 to Flajolet, Gourdon, and Dumas,
[*Mellin transforms and asymptotics: Harmonic sums*](https://algo.inria.fr/flajolet/Publications/FlGoDu95.pdf),
equation (12), Example 7, and the stated periodicity discussion.
Blackwell's
[*Extension of a renewal theorem*](https://msp.org/pjm/1953/3-2/pjm-v3-n2-p03-p.pdf),
§1, Theorem 1, supplies §7's positive-mean iid interval theorem,
with its origin-lattice definition and without a rate.
Boyer's
[*The speed of convergence in the renewal theorem*, arXiv:1506.07625v1](https://arxiv.org/pdf/1506.07625v1),
Definitions 2.11 and 3.5 and Proposition 4.3, supplies §8's
weakly diophantine Schwartz estimate at a positive drift and an
exponential moment. Its reflected measure and half-line convention
are transported exactly in (8.13); its result is used only in the
polynomial theorem already stated there. No such polynomial
hypothesis is imposed in Theorem 9.2. The additional classical
inputs are the Gamma estimates at the exact strip in (9.8), the
Basel value already used in (8.6), and the continued-fraction and
irrationality-base statements with the parameter map in Theorem
10.1.

The source-specific deductions are the passage from the harmonic
logarithmic transform to the strict exponential sides for the
original expectation, the continuous-frequency binary identity,
and the two fixed-law consumers of those deductions. The
continued-fraction machinery, prescribed approximation growth,
Gamma asymptotics, occurrence reduction, and the results of §§1–8
keep their respective attributions. The cited versions delimit the
literature comparison; no completeness or priority assertion about
the wider literature follows from it.

All assertions keep $p$ and $q$ fixed and strictly interior. They
provide no boundary uniformity, varying-source conclusion, Markov
extension, critical-equality classification, or two-sign conclusion
for $p^{(2)}$. The stronger polynomial remainder in Theorem 8.3,
the arithmetic formulas, the dense $G_\delta$ two-sign obstruction,
and the examples and uniqueness results of §§7–8 retain exactly
their stated hypotheses and conclusions.

## 追加锚（本行以下为增补区）
## 13. A summable critical condition for each fixed source

**Definition 13.1 (Critical weights and local minima).** Fix a strictly
positive finite iid law $p$ on the ordered alphabet of Definition 6.1,
with $q\geq2$, and assume origin-nonarithmeticity as in Definition 7.1.
Retain the original distinct nonempty contiguous Lyndon-word
expectation $E_p(n)$ and all the notation in (8.1) and (9.1). In
particular $Y=-\log p_I$ has masses $\mathbb P(I=i)=p_i$ from this
same law. Set

$$
\begin{aligned}
 c&=\pi/2,& h&=\mathbb EY,& m_2&=\mathbb EY^2,\\
 w(t)&=t^{-3/2}e^{-ct}\quad(t\geq1),&
 r_0&=\min\left(\frac14,\frac{h}{4m_2}\right),\\
 I_N&=[N-r_0,N+1+r_0],&
 d_N&=\min_{t\in I_N}\delta_p(t)\quad(N\geq2),\\
 S(p)&=\sum_{N=2}^{\infty}\frac{N^{-3/2}e^{-cN}}{d_N},&
 W_p(t)&=\frac{t^{-3/2}e^{-ct}}{\delta_p(t)}\quad(t\geq1).
\end{aligned}                                                       \tag{13.1}
$$

Each $d_N$ is positive: the interval is compact and avoids zero,
and origin-nonarithmeticity excludes every other zero of $D_p(it)$
by Definition 9.1. The minima and the series concern one fixed law;
no probabilities or information masses vary with $N$, $t$, or $n$.

**Theorem 13.2 (A critical summability sufficient condition).** For
every law of Definition 13.1,

$$
 S(p)<\infty\quad\Longrightarrow\quad
 R_n(p)\longrightarrow c_*\qquad(n\to\infty,\ n\in\mathbb N).
                                                                    \tag{13.2}
$$

In particular the same conclusion holds if some $C>0$ and some
$0\leq\theta<1/2$ satisfy

$$
 \delta_p(t)\geq C e^{-ct}(1+t)^{-\theta}\qquad(t\geq1).             \tag{13.3}
$$

These are sufficient conditions, with no converse asserted.

*Proof.* Use the functions $J_p,J_0,H$, the complex function $A_0$,
and the analytic logarithm $\ell$ in (9.5)–(9.7). Their precise
transform identity is

$$
 \mathcal H(s)=\int_{\mathbb R}e^{-sx}H(x)\,dx
   =-A_0(s)\ell(s),\qquad
 A_0(s)=\frac{\Gamma(1-s)}{s(1+s)},\qquad
 \ell(s)=\log D_p(s)-\log h-\log s,                                \tag{13.4}
$$

for $0<\operatorname{Re}s<1$. The branches have real values on the
positive real axis. At zero $\ell$ is analytic and vanishes, so
$A_0\ell$ has a removable singularity. These facts do not assume a
bound on $\beta(p)$. The occurrence reduction is exactly (9.4),
coming from (6.8) for the actual weighted word statistic; the
comparison expansion is (9.6).

We need the Gamma estimates with their polynomial factors retained.
The estimates (9.8), with one logarithmic differentiation, give,
uniformly for $0\leq\sigma\leq1/4$, $t\geq2$, and $r=0,1,2$,

$$
\begin{aligned}
 |A_0(\sigma+it)|&\asymp w(t)t^{-\sigma},\\
 |A_0^{(r)}(\sigma+it)|&\leq
       C w(t)t^{-\sigma}\bigl(\log(2+t)\bigr)^r.                  \tag{13.5}
\end{aligned}
$$

Here and below a prime on a complex function is its complex
derivative. The cited classical inputs are precisely
[NIST DLMF (5.11.1)–(5.11.2)](https://dlmf.nist.gov/5.11#E1)
and [the series (5.15.1)](https://dlmf.nist.gov/5.15#E1), at
$z=1-\sigma-it$ with real part in $[3/4,1]$. This stays in a fixed
closed sector strictly inside $|\arg z|<\pi$. In fact

$$
 \frac{A_0'(s)}{A_0(s)}=-\psi(1-s)-\frac1s-\frac1{1+s},\qquad
 \left(\frac{A_0'}{A_0}\right)'(s)
       =\psi'(1-s)+\frac1{s^2}+\frac1{(1+s)^2}.
$$

The series for $\psi'$ is absolutely bounded there, since its term
moduli are at most $((j+3/4)^2+t^2)^{-1}$. Thus the first logarithmic
derivative is $O(\log(2+t))$, its derivative is bounded, and
$A_0''/A_0=O((\log(2+t))^2)$. This proves the second line of
(13.5) with the same exponential factor as the first.

Write $D(t)=D_p(it)$ temporarily, and use dots for real derivatives
in $t$. Positivity of the letter masses gives

$$
 \sum_i p_i|e^{-ity_i}-1|^2=2\operatorname{Re}D(t)
       \leq2\delta_p(t),\qquad
 |\dot D(t)-ih|\leq(2m_2\delta_p(t))^{1/2},\qquad
 |\ddot D(t)|\leq m_2.                                           \tag{13.6}
$$

Choose $\varepsilon=\min(1,h^2/(32m_2))$. If
$\delta_p(t_0)<\varepsilon$ and $|t-t_0|\leq r_0$, (13.6) and
$m_2r_0\leq h/4$ imply

$$
 \frac{d}{dt}\operatorname{Im}D(t)\geq h/2.                        \tag{13.7}
$$

In $[N,N+1]$ take a maximal $r_0$-separated set of points with
$\delta_p<\varepsilon$. It has at most $2+1/r_0$ members, and the
intervals of radius $r_0$ about them cover this small-value set.
All these intervals lie in $I_N$. On each such interval
$u=\operatorname{Im}D(t)$ is an increasing coordinate with
$dt\leq(2/h)du$. Also
$|D(t)|\geq\max(d_N,|u|)$ and $|u|\leq2$. Consequently

$$
\begin{aligned}
 \int_N^{N+1}\delta_p(t)^{-2}\,dt&\leq C_p(1+d_N^{-1}),\\
 \int_N^{N+1}\delta_p(t)^{-1}\,dt&\leq
                         C_p(1+\log^+(1/d_N)).                   \tag{13.8}
\end{aligned}
$$

Indeed the corresponding integrals in $u$ are bounded by
$\int_{\mathbb R}\max(d_N^2,u^2)^{-1}du=4/d_N$ and
$\int_{-2}^2\max(d_N,|u|)^{-1}du\leq C(1+\log^+(1/d_N))$.
On the portion with $\delta_p\geq\varepsilon$ use its fixed lower
bound. Overlaps only increase these upper bounds. If the small-value
set is empty that last bound handles the whole unit interval.

Assume now $S(p)<\infty$. Put $u_N=\log^+(1/d_N)$. Each summand of
$S(p)$ is at most $S(p)$, so

$$
 u_N\leq C_p+cN+\tfrac32\log N=O_p(N+1).                          \tag{13.9}
$$

Let $\Psi(t)=-A_0(it)\ell(it)$, with the continuous value at zero.
For $t\ne0$ the logarithms are the boundary values from the right
half-plane. Their imaginary parts are bounded because
$\operatorname{Re}D_p(it)\geq0$ and $D_p(it)\ne0$; the argument
of $it$ is $\pi/2$ or $-\pi/2$. On $[N,N+1]$ this gives

$$
\begin{aligned}
 |\ell(it)|&\leq C_p+u_N+\log(2+N),\\
 \left|\frac{d}{dt}\ell(it)\right|
       &\leq C_p\delta_p(t)^{-1}+1/t,\\
 \left|\frac{d^2}{dt^2}\ell(it)\right|
       &\leq C_p\bigl(\delta_p(t)^{-1}+\delta_p(t)^{-2}\bigr)+1/t^2.
                                                                    \tag{13.10}
\end{aligned}
$$

Here the first two derivatives of $D(t)$ are bounded by fixed
moments of the bounded positive variable $Y$. The product rule,
(13.5), and (13.8) show

$$
 \int_N^{N+1}|\Psi''(t)|\,dt
 \leq C_p\frac{w(N)}{d_N}
                  +C_p(1+N)^C e^{-cN}.                           \tag{13.11}
$$

To check the only potentially critical term, the factor
$A_0\,\ell''$ contributes at most $C_pw(N)/d_N$ plus an
exponentially summable term. The factor $A_0'\,\ell'$ contributes
at most $C_pw(N)\log(2+N)(1+u_N)$, by the second line of
(13.8), rather than a logarithm times $w(N)/d_N$.
The factor $A_0''\ell$ is at most
$C_pw(N)(\log(2+N))^2(1+u_N+\log(2+N))$ after integration.
Equation (13.9) makes both of these contributions summable.
This proves (13.11) without an extra logarithmic hypothesis on $S$.

The same bounds give $\Psi,\Psi'\in L^1$ on the positive half-line.
For example the inverse-denominator part of $\Psi'$ is controlled
by the logarithmic integral in (13.8). Moreover $\Psi(t)\to0$
and $\Psi'(t)\to0$ as $t\to+\infty$: pointwise on the $N$-th
unit interval the latter's inverse-denominator part is at most
$C_pw(N)/d_N$, which tends to zero because its sum converges.
The other terms tend to zero by (13.9). Conjugation gives all the
same assertions on the negative half-line. At zero use the removable
analytic expression in (13.4). We have therefore proved

$$
 \Psi,\Psi',\Psi''\in L^1(\mathbb R),\qquad
 \Psi(t),\Psi'(t)\longrightarrow0\quad(|t|\to\infty).              \tag{13.12}
$$

For completeness the boundary inversion has the same hypotheses as
in (9.14)–(9.16). Uniformly for $0\leq\sigma\leq1/4$,
$|D_p(\sigma+it)|\geq c_p\delta_p(t)$ by (9.14).
Thus (13.9), (13.5), and the bounded arguments of the logarithms
dominate $\mathcal H(\sigma+it)$ on each large-frequency unit
interval by an exponential times a fixed polynomial, independently
of $\sigma$. On bounded intervals away from zero use compactness;
near zero use the removable expression. Dominated convergence gives
$\mathcal H(\sigma+i\,\cdot)\to\Psi$ in $L^1$.
For every positive $\sigma<1/4$, $e^{-\sigma x}H(x)$ is continuous
and integrable: at $-\infty$ it is $O_p(e^{(1-\sigma)x})$, and at
$+\infty$ it has at most logarithmic growth before multiplication
by $e^{-\sigma x}$. Fourier inversion, or its Gaussian-convolution
proof in §9, consequently yields

$$
 H(x)=\frac1{2\pi}\int_{\mathbb R}e^{itx}\Psi(t)\,dt
     =-\frac1{2\pi x^2}\int_{\mathbb R}e^{itx}\Psi''(t)\,dt
     =o_p(x^{-2}).                                                 \tag{13.13}
$$

The first equality follows by letting $\sigma\downarrow0$ in the
inversion of $e^{-\sigma x}H(x)$. The second uses the vanishing
boundary terms in (13.12); the last is the Riemann–Lebesgue lemma
for its integrable second derivative. This lemma follows here by
$L^1$ approximation by step functions of compact support, as in
(9.16). Combining (13.13) with (9.6) and (9.4) proves (13.2).
In particular the occurrence error multiplied by $L^2$ tends to
zero since the positive $\delta_0$ in (9.4) is fixed.

Finally (13.3), throughout $I_N\subset(1,\infty)$, implies
$d_N\geq C_p e^{-cN}N^{-\theta}$. Hence
$S(p)\leq C_p\sum_{N\geq2}N^{\theta-3/2}<\infty$ when
$\theta<1/2$, proving the final assertion. $\square$

## 14. A necessary critical condition without an index restriction

**Theorem 14.1 (Boundedness and finite limits of the original
residual).** For every law of Definition 13.1, with no additional
restriction on $\beta(p)$, eventual absolute boundedness of the
original integer residual implies

$$
 \sup_{t\geq1}W_p(t)<\infty.                                      \tag{14.1}
$$

Every finite limit of $R_n(p)$ equals $c_*$, and existence of such a
limit implies $W_p(t)\to0$ as real $t\to+\infty$. Consequently

$$
 \limsup_{t\to\infty}W_p(t)=+\infty
 \quad\Longrightarrow\quad
 \limsup_{\substack{n\to\infty\\n\in\mathbb N}}|R_n(p)|=+\infty.
                                                                    \tag{14.2}
$$

*Proof.* First make the real/integer correspondence explicit without
assuming any convergence rate. Define for real $x>1$

$$
 \mathscr R_p(x)=x^2\left[
      \log x+\gamma-\log h-\frac\mu x-J_p(x)\right].                \tag{14.3}
$$

Equation (9.4) gives
$R_n(p)-\mathscr R_p(\log n)\to0$ over all integers. More precisely
the difference is $O_p(L^2 n^{-\delta_0}+L^3/n)$.
The pathwise spacing of renewal sums by
$a_0=\min_i(-\log p_i)>0$ bounds $U$, and thus $V\leq U$, on
every unit interval. Since $k$ decays exponentially,
$J_p'=k*V$ is uniformly bounded; this is the rate-free argument in
(8.16) and (9.17). For $x\to\infty$ put
$z=\log\lfloor e^x\rfloor$. Then $0\leq x-z=O(e^{-x})$.
The derivative of $\log x+\gamma-\log h-\mu/x$ is bounded for
large $x$, and $J_p(x)=O_p(1+\log x)$. These bounds give

$$
 \mathscr R_p(x)-\mathscr R_p(z)
             =O_p(x^2(1+\log x)e^{-x})=o_p(1).
$$

The comparison expansion (9.6) also gives
$\mathscr R_p(x)=c_*-x^2H(x)+O_p(x^{-1})$.
It follows, over all real $x\to\infty$, that

$$
 R_{\lfloor e^x\rfloor}(p)=c_*-x^2H(x)+o_p(1).                    \tag{14.4}
$$

Thus eventual integer boundedness is equivalent to
$H(x)=O_p(x^{-2})$ at $+\infty$. A finite integer limit $C$ is
equivalent to $x^2H(x)\to c_*-C$. By Theorem 8.7, at exactly the
present fixed positive nonarithmetic hypotheses, any such $C$
equals $c_*$. In that case $H(x)=o_p(x^{-2})$.
This uses the uniqueness result already proved there and imposes
no polynomial or exponential denominator bound.

We use the second complex derivative of (13.4). When
$H(x)=O_p(x^{-2})$ at $+\infty$, its $O_p(e^x)$ bound at
$-\infty$ and absolute differentiation under the transform give

$$
 \sup_{t\in\mathbb R}|\mathcal H''(\sigma+it)|
 \leq\int_{\mathbb R}x^2e^{-\sigma x}|H(x)|\,dx
 \leq C_p(1+\sigma^{-1})\quad(0<\sigma\leq1/4).                   \tag{14.5}
$$

If instead $H(x)=o_p(x^{-2})$ at $+\infty$, the stronger conclusion
is

$$
 \sigma\sup_{t\in\mathbb R}|\mathcal H''(\sigma+it)|
                               \longrightarrow0\quad(\sigma\downarrow0).
                                                                    \tag{14.6}
$$

Indeed, for any $\eta>0$ the positive tail of $x^2|H(x)|$ is at
most $\eta$ beyond some fixed threshold. Its Laplace integral is
at most $\eta/\sigma$. The bounded region and the negative half-line
contribute $O_{p,\eta}(1)$ uniformly as $\sigma\downarrow0$.
Multiplication by $\sigma$ and then $\eta\downarrow0$ prove
(14.6). Both estimates are uniform in the imaginary frequency.

We next obtain a lower bound at every sequence where the proposed
necessary condition could fail. Suppose $t_j\to\infty$ and
$W_p(t_j)\geq\eta>0$. Put
$\delta_j=\delta_p(t_j)$, $u_j=\log(1/\delta_j)$, and
$s_j=\delta_j+it_j$. Then

$$
 0<\delta_j\leq\eta^{-1}t_j^{-3/2}e^{-ct_j},\qquad
 \delta_j\log t_j\to0,\qquad t_j=O_\eta(1+u_j).                   \tag{14.7}
$$

In particular eventually $0<\operatorname{Re}s_j\leq1/4$.
The same-law moment estimates and (9.14) give

$$
\begin{aligned}
 c_p\delta_j\leq|D_p(s_j)|&\leq(1+h)\delta_j,\\
 |D_p'(s_j)-h|&\leq(2m_2\delta_j)^{1/2}+m_2\delta_j\to0,\\
 |D_p''(s_j)|&\leq m_2,\qquad
 |\ell(s_j)|\leq C_p+u_j+\log t_j.                               \tag{14.8}
\end{aligned}
$$

For the first upper bound use
$|D_p(\delta_j+it_j)-D_p(it_j)|\leq h\delta_j$.
For the derivative bound apply Cauchy–Schwarz to
$\sum_i p_i y_i(e^{-it_jy_i}-1)$ using (13.6), and bound the
additional real shift by $m_2\delta_j$.

Differentiating (13.4) twice gives the exact formula

$$
\begin{aligned}
 \mathcal H''(s)={}&
 A_0(s)\left(\frac{D_p'(s)}{D_p(s)}\right)^2
 -A_0(s)\frac{D_p''(s)}{D_p(s)}-\frac{A_0(s)}{s^2}\\
 &-2A_0'(s)\left(\frac{D_p'(s)}{D_p(s)}-\frac1s\right)
 -A_0''(s)\ell(s).                                                \tag{14.9}
\end{aligned}
$$

At $s_j$ the first term has modulus at least
$c_p|A_0(s_j)|/\delta_j^2$. By (13.5) and (14.8), the sum of the
moduli of all other terms, divided by
$|A_0(s_j)|/\delta_j^2$, is bounded by

$$
 C_p\left[\delta_j(1+\log(2+t_j))+
 \delta_j^2(\log(2+t_j))^2(1+u_j+\log(2+t_j))\right]=o_p(1).
$$

The equality follows from (14.7): $\delta_j=e^{-u_j}$ and
$t_j=O_\eta(1+u_j)$, so the exponential beats every displayed
polynomial or logarithm. Also (13.5) and
$t_j^{-\delta_j}\to1$ imply $|A_0(s_j)|\asymp w(t_j)$.
The triangle inequality in (14.9) therefore proves

$$
 |\mathcal H''(s_j)|\geq c_p\frac{w(t_j)}{\delta_j^2},\qquad
 \delta_j|\mathcal H''(s_j)|\geq c_p W_p(t_j)                      \tag{14.10}
$$

for all sufficiently large $j$. This lower bound concerns the
exact transform of the exact $H$ related to $R_n$ in (14.4).

If $R_n$ is eventually absolutely bounded but (14.1) fails,
continuity and positivity of $\delta_p$ on compact subsets of
$[1,\infty)$ give a sequence $t_j\to\infty$ with
$W_p(t_j)\to\infty$. Use (14.10) with, for example, $\eta=1$.
Equation (14.5) bounds its left side by a fixed constant, a
contradiction. This proves (14.1) on the full domain $t\geq1$.
If $R_n$ has a finite limit, (14.4), Theorem 8.7, and (14.6)
apply. Failure of $W_p(t)\to0$ would give a sequence as in
(14.7) with fixed $\eta>0$, and (14.10) would contradict (14.6).
This proves the asserted vanishing condition.

Finally, the premise of (14.2) violates (14.1), so the original
integer sequence cannot be eventually absolutely bounded.
For a sequence of finite real numbers this is exactly
$\limsup_{n\to\infty}|R_n|=+\infty$: for every bound and every
integer threshold there is a later integer exceeding that bound.
Equation (14.4) gives the exact accompanying real/integer
correspondence. No sign or rate conclusion is used. $\square$

## 15. An entire binary family at the exact critical index

**Definition 15.1 (A fixed law for each real parameter).** For real
$r\in[1,3/2]$ let $a(r)>0$ be the unique solution of

$$
 e^{-a(r)}+e^{-r a(r)}=1,qquad
 \kappa(r)=\frac{\pi^2}{2a(r)}.                                   \tag{15.1}
$$

For each fixed real $\tau\geq0$ specify integers recursively by

$$
\begin{gathered}
 b_0=1,\quad b_1=2,\quad
 P_{-1}=1,\quad P_0=1,\quad P_1=3,\quad
 Q_{-1}=0,\quad Q_0=1,\quad Q_1=2,\\
 r_j=P_j/Q_j,\qquad
 b_{j+1}=\max\left(2,
       \left\lceil e^{\kappa(r_j)Q_j}Q_j^{\tau-1}\right\rceil\right),\\
 P_{j+1}=b_{j+1}P_j+P_{j-1},\qquad
 Q_{j+1}=b_{j+1}Q_j+Q_{j-1}\qquad(j\geq1),\\
 \alpha_\tau=[1;2,b_2,b_3,\ldots],\qquad
 a_\tau=a(\alpha_\tau),\qquad
 p^{[\tau]}=(e^{-a_\tau},e^{-\alpha_\tau a_\tau}).
\end{gathered}                                                       \tag{15.2}
$$

The letters have the fixed order $0<1$, with these probabilities
in that order. The specification uses only scalar equations,
positive integer recursions, and the continued-fraction limit;
it contains no residual or expectation condition.

**Theorem 15.2 (All parameters and the boundary).** For every fixed
real $\tau\geq0$, (15.2) converges and defines a strictly positive
binary origin-nonarithmetic law, fixed before $n$ varies, with

$$
 \beta(p^{[\tau]})=\pi/2.                                         \tag{15.3}
$$

For its original distinct contiguous Lyndon-word expectation, on
all integers $n\to\infty$,

$$
\begin{array}{ll}
 0\leq\tau<3/4:& R_n(p^{[\tau]})\longrightarrow c_*,\\[2pt]
 \tau=3/4:& R_n(p^{[\tau]})\text{ has no finite limit},\\[2pt]
 \tau>3/4:& \displaystyle
   \limsup_{\substack{n\to\infty\\ n\in\mathbb N}}
                         |R_n(p^{[\tau]})|=+\infty.
\end{array}                                                         \tag{15.4}
$$

Boundedness at $\tau=3/4$ is unresolved here. No assertion is made
about separate signs, a divergence rate, an $O_p(n/L^3)$ remainder
for the convergent part of this family, or uniformity in $\tau$.

*Proof.* First verify convergence and the source-law constraint.
For each $r\in[1,3/2]$, the left side of (15.1) is continuous and
strictly decreasing in $a\geq0$, from $2$ to $0$. Thus $a(r)$
exists and is unique. The implicit differentiation formula is

$$
 a'(r)=-\frac{a(r)e^{-r a(r)}}{e^{-a(r)}+r e^{-r a(r)}}.             \tag{15.5}
$$

Its denominator is strictly positive on this compact parameter
interval. Hence $a$ and $\kappa$ are continuously differentiable,
Lipschitz, and bounded above and below by positive constants there.
This assertion also follows directly by the implicit function
theorem at every point and compactness.

Every $b_{j+1}\geq2$ is a finite positive integer. The recursions
and determinant identity for continued fractions, used in §11,
show that consecutive convergents enclose nested intervals of
length $1/(Q_jQ_{j+1})$. The next convergent is a strict weighted
mean of the preceding two. Starting with $1$ and $3/2$, all $r_j$
therefore lie in $[1,3/2]$, so every evaluation of $\kappa(r_j)$
in (15.2) is legal. Also $Q_{j+1}\geq2Q_j$, and the nested intervals
have lengths tending to zero. They define a unique limit
$\alpha=\alpha_\tau$ with

$$
 |\alpha-r_j|\leq\frac1{Q_jQ_{j+1}}.                              \tag{15.6}
$$

The limit is irrational by the same determinant argument as in
Theorem 11.2: a rational limit $r/s$ would be at distance at least
$1/(sQ_j)$ from each unequal reduced convergent, contradicting
(15.6) when $Q_{j+1}>s$; infinitely many convergents are unequal
by their determinant identity. Thus $1<\alpha<3/2$.
Continuity of $a(r)$ proves that the positive normalized laws
$(e^{-a(r_j)},e^{-r_j a(r_j)})$ converge to exactly the law in
(15.2). Its information values are $a=a(\alpha)$ and $\alpha a$,
with masses $w=e^{-a}$ and $z=e^{-\alpha a}$, respectively.
They are the actual negative logarithms of its probabilities,
not independently assigned information values. Their irrational
ratio gives origin-nonarithmeticity by Proposition 7.4. All these
objects now depend on the fixed $\tau$, not on $n$.

Write $\kappa=\kappa(\alpha)$. For fixed $\tau$, the number
$E_j=e^{\kappa(r_j)Q_j}Q_j^{\tau-1}$ tends to infinity because
$\kappa(r_j)$ has a positive lower bound. Thus the maximum with
$2$ in (15.2) is eventually inactive and $b_{j+1}=E_j+O(1)$.
Using $Q_{j-1}\leq Q_j$, the exact denominator recurrence gives

$$
 Q_{j+1}=e^{\kappa(r_j)Q_j}Q_j^\tau(1+O(E_j^{-1})).
$$

Lipschitz continuity and (15.6) imply
$Q_j|\kappa(r_j)-\kappa|\leq C/Q_{j+1}\to0$.
It follows that

$$
 \frac{Q_{j+1}}{e^{\kappa Q_j}Q_j^\tau}\longrightarrow1,
 \qquad
 \frac{\log Q_{j+1}}{Q_j}\longrightarrow\kappa.                    \tag{15.7}
$$

The exact binary translation (10.1), at these very information
values and masses, now gives
$\beta(p^{[\tau]})=a\kappa/\pi=\pi/2$.
Its classical continued-fraction input remains Sondow,
[*Irrationality measures, irrationality bases, and a theorem of
Jarník*, arXiv:math/0406300v1](https://arxiv.org/pdf/math/0406300v1),
§3, Theorem 1, equation (3); no new identity for an irrationality
base is required.

To prove convergence for the entire range $\tau<3/4$, we must
bound the minima on all the intervals $I_N$, not just selected
frequencies. The convergent error inequalities in Sondow's
§3, equation (5), with numerator $P_j$ and denominator $Q_j$,
are

$$
 \frac1{2Q_{j+1}}<|\epsilon_j|<\frac1{Q_{j+1}},\qquad
 \epsilon_j=Q_j\alpha-P_j.                                       \tag{15.8}
$$

We spell out the needed integer-denominator consequence. The
signed errors of consecutive convergents have opposite signs,
and their integer column vectors $(P_j,Q_j)$ and
$(P_{j+1},Q_{j+1})$ have determinant $1$ or $-1$.
For any integers $m,r$ with $0<m<Q_{j+1}$ there are therefore
integers $A,B$ with

$$
 (r,m)=A(P_j,Q_j)+B(P_{j+1},Q_{j+1}),\qquad
 m\alpha-r=A\epsilon_j+B\epsilon_{j+1}.
$$

If $B=0$, positivity of $m$ forces $A\geq1$. If $B\geq1$,
$m<Q_{j+1}$ forces $A\leq-1$. If $B\leq-1$, positivity of $m$
forces $A\geq1$. In the last two cases the two nonzero error
terms have the same sign, because $\epsilon_j$ and
$\epsilon_{j+1}$ have opposite signs. In every case
$|m\alpha-r|\geq|\epsilon_j|$. Choosing a nearest integer $r$
proves the classical best-approximation bound in the exact form
needed here:

$$
 \|m\alpha\|\geq|\epsilon_j|>\frac1{2Q_{j+1}}
                    \qquad(Q_j\leq m<Q_{j+1}).                   \tag{15.9}
$$

This is an intermediate consequence of the cited convergent
facts; no assumption about the location of intermediate
small divisors is made.

For the present binary law put $u=at/(2\pi)$ and let $m$ be a
nearest integer to $u$. The same elementary real-part estimate
and circle-distance triangle inequality as (10.3)–(10.4) give,
for every real $t$,

$$
 \delta_p(t)\geq8\min(w,z)
            (\|u\|^2+\|\alpha u\|^2)
             \geq c_p\|m\alpha\|^2.                              \tag{15.10}
$$

In fact $\|m\alpha\|\leq\alpha\|u\|+\|\alpha u\|$, and
Cauchy–Schwarz proves the last bound. For sufficiently large
$N$ let $\mathcal M_N$ be the set of positive integers $m$ for
which $|m-at/(2\pi)|\leq1/2$ for some $t\in I_N$.
Every nearest integer relevant to (15.10) belongs to this finite
set. Its cardinality is bounded by a constant depending only on
this law. For $m\in\mathcal M_N$,

$$
 |N-2\pi m/a|\leq C_p,
$$

so $N\asymp_p m$ and
$N^{-3/2}e^{-cN}\leq C_p m^{-3/2}e^{-2\kappa m}$.
Here $c(2\pi/a)=\pi^2/a=2\kappa$ exactly. Moreover each fixed
$m$ belongs to at most $C_p$ of the sets $\mathcal M_N$, since
the displayed bound confines the integer $N$ to an interval of
fixed length. Taking minima in (15.10) and then summing therefore
gives

$$
 S(p)\leq C_p+C_p\sum_{m\geq2}
                     \frac{m^{-3/2}e^{-2\kappa m}}{\|m\alpha\|^2}.
                                                                    \tag{15.11}
$$

Explicitly, $d_N^{-1}$ is at most
$C_p\max_{m\in\mathcal M_N}\|m\alpha\|^{-2}$, which is at most
the sum of these positive quantities. The finitely many remaining
$N$ contribute a finite constant because their $d_N$ are positive.
Thus (15.11) covers the whole continuous-frequency minima.

Use (15.9) on each complete block
$Q_j\leq m<Q_{j+1}$. The geometric exponential sum and (15.7)
give, for all sufficiently large $j$,

$$
\begin{aligned}
 \sum_{m=Q_j}^{Q_{j+1}-1}
       \frac{m^{-3/2}e^{-2\kappa m}}{\|m\alpha\|^2}
 &\leq4Q_{j+1}^2Q_j^{-3/2}
                   \frac{e^{-2\kappa Q_j}}{1-e^{-2\kappa}}\\
 &\leq C_p Q_j^{2\tau-3/2}.                                     \tag{15.12}
\end{aligned}
$$

If $\tau<3/4$, the exponent is strictly negative and
$Q_j\geq2^j$, so the sum of (15.12) over all $j$ converges.
Equations (15.11)–(15.12) prove $S(p)<\infty$ throughout that
whole parameter range. Theorem 13.2 proves its assertion in
(15.4) for the original expectation on all integers.

For the remaining parameters we need lower bounds on $W_p$,
with the exact critical exponential factor. Use the frequencies
from the elementary cancellation in (10.5), here with
$m=Q_j$, $r=P_j$, and signed error $\epsilon_j$:

$$
 u_j=Q_j-\frac{z\epsilon_j}{w+z\alpha},\qquad
 t_j=\frac{2\pi u_j}{a}.                                         \tag{15.13}
$$

They tend to infinity. Their centered phase errors are
$-z\epsilon_j/(w+z\alpha)$ and
$w\epsilon_j/(w+z\alpha)$; their weighted sum is zero.
The elementary inequality
$|e^{-iv}-1+iv|\leq v^2/2$ therefore gives

$$
 0<\delta_p(t_j)\leq C_p\epsilon_j^2
             \leq C_pQ_{j+1}^{-2},\qquad
 t_j=2\pi Q_j/a+O_p(Q_{j+1}^{-1}).                               \tag{15.14}
$$

Strict positivity follows from origin-nonarithmeticity. The error
in $t_j$ tends to zero, so both its exponential factor and its
power factor have the following asymptotics:

$$
 w(t_j)\sim(2\pi/a)^{-3/2}Q_j^{-3/2}e^{-2\kappa Q_j}.
$$

Combining this with (15.7) and (15.14) proves, with a fixed
positive constant for the given law,

$$
 W_p(t_j)\geq c_p Q_j^{2\tau-3/2}\qquad(j\text{ sufficiently large}).
                                                                    \tag{15.15}
$$

At $\tau=3/4$ this prevents $W_p(t)\to0$, so Theorem 14.1
excludes every finite limit of the original integer residual.
For every $\tau>3/4$, (15.15) tends to infinity, and (14.2)
proves the last line of (15.4). In both cases the actual residual
conclusion uses (14.4), rather than identifying a small divisor
with a divergence of a different statistic. $\square$

The conditions $S(p)<\infty$ and the two necessary conditions on
$W_p$ leave the full classification of individual laws with
$\beta(p)=\pi/2$ unresolved. Divergence of $S(p)$ alone has no
residual-divergence implication here; neither boundedness of $W_p$
nor $W_p(t)\to0$ is asserted sufficient. In particular (15.15) at
$\tau=3/4$ excludes convergence but does not decide boundedness.
All statements retain the origin-lattice convention, the actual
same-law information masses, and the original counting of distinct
nonempty contiguous words, including letters and every legal
length and window. The reused reductions (6.8)–(6.9), comparison
and transform (9.4)–(9.8), uniqueness Theorem 8.7, and binary
translation Theorem 10.1 have exactly their fixed-source domains.
The additional inferences are the summability implication, the
necessary critical weight conditions, and their entire-family
consumers (15.3)–(15.4).

## 追加锚（本行以下为增补区）

## 16. Absolute boundedness at the fixed critical law

**Definition 16.1 (Critical binary notation).** In this section fix exactly
the law $p=p^{[3/4]}$ of Definition 15.1. Put

$$
\alpha=\alpha_{3/4},\qquad a=a(\alpha),\qquad
w=e^{-a},\qquad z=e^{-\alpha a},\qquad
\kappa=\frac{\pi^2}{2a},
$$

so that $w+z=1$, and define

$$
D(s)=1-we^{-as}-ze^{-\alpha as},\qquad
\Delta(t)=D(it),\qquad
\omega(t)=t^{-3/2}e^{-\pi t/2}\quad(t\geq1).
$$

Let $Q_j,P_j$ be the convergents in Definition 15.1 and write
$T_j=2\pi Q_j/a$. Fix sufficiently small
$\varepsilon_0>0$ and $r_0\in(0,1/4)$.
Call $m$ resonant when $\|m\alpha\|<\varepsilon_0$. For a resonant
$m$, let $\widehat t_m$ be the unique zero of
$\operatorname {Im}\Delta$ in the fixed neighborhood
$|at/(2\pi)-m|<r_0$; put
$\eta_m=\operatorname {Re}\Delta(\widehat t_m)>0$.
For nonresonant $m$ put $\widehat t_m=2\pi m/a$ and
$\eta_m=\varepsilon_0$. After decreasing $\varepsilon_0,r_0$ once,
compactness of the phase variables gives a uniform lower bound for
$|\Delta|$ on every nonresonant interval. Finitely many small $m$ are
absorbed into constants below.

**Lemma 16.2 (Resonant geometry).** There are constants $c,C,r>0$ and
$j_0$ depending only on $p$ such that, for $j\geq j_0$ and
$Q_j\leq m<Q_{j+1}$,

$$
cQ_{j+1}^{-2}\leq\eta_m\leq C,\qquad
cQ_{j+1}^{-2}\leq\eta_{Q_j}\leq C Q_{j+1}^{-2},                 \tag{16.1}
$$

and, whenever $|t-\widehat t_m|\leq r$,

$$
|\Delta(t)|\geq c\bigl(\eta_m+|t-\widehat t_m|\bigr).         \tag{16.2}
$$

Moreover $|\widehat t_m-2\pi m/a|\leq C$ and

$$
Q_{j+1}=e^{\kappa Q_j}Q_j^{3/4}(1+o(1)).                       \tag{16.3}
$$

*Proof.* Write $u=at/(2\pi)$ and, for $m$ in the indicated interval,
write $\alpha m-r_m=\varepsilon_m$ with $r_m$ the nearest integer.
The best-approximation estimate (15.9) gives

$$
|\varepsilon_m|\geq(2Q_{j+1})^{-1}.                            \tag{16.4}
$$

For a resonant $m$, put $u=m+v$. The two phases of $\Delta$ are
$2\pi v$ and $2\pi(\varepsilon_m+\alpha v)$. Since
$w+z=1$, the equation
$\operatorname {Im}\Delta=0$ has one solution with $v=O(|\varepsilon_m|)$:
the derivative of the imaginary part at $\varepsilon_m=v=0$ is
$2\pi(w+z\alpha)>0$, and the implicit-function theorem applies on a
fixed neighborhood. At that solution, Taylor's formula and
$1-\cos y\geq c y^2$ for $|y|$ small give

$$
\eta_m=1-w\cos(2\pi v)-z\cos(2\pi(\varepsilon_m+\alpha v))
      \asymp \varepsilon_m^2.                                  \tag{16.5}
$$

The two phase errors cannot both be $o(|\varepsilon_m|)$ because their
linear combination has coefficient $w+z\alpha$; this proves the lower
comparison in (16.5). Equations (16.4) and (16.5) give the first bound
in (16.1). For $m=Q_j$, (15.8) gives
$|\varepsilon_{Q_j}|\asymp Q_{j+1}^{-1}$, proving the second bound.

Differentiating $D(it)$ shows that, on the same fixed neighborhood,
the derivative of its imaginary part has modulus at least
$a(w+z\alpha)/3$. Thus the imaginary part is a valid coordinate and
the real part is at least a fixed multiple of $\eta_m$; consequently
$|\Delta(t)|^2\geq c(\eta_m^2+|t-\widehat t_m|^2)$, which implies
(16.2). For nonresonant $m$ the same estimate is unnecessary: the
compactness lower bound makes the whole interval a uniformly smooth
piece. The displacement estimate follows from $v=O(|\varepsilon_m|)$.
Finally (16.3) is (15.7) with $\tau=3/4$. $\qed$

**Lemma 16.3 (One resonant interval).** Let $A_0(s)=\Gamma(1-s)/(s(1+s))$
and let $\ell$ be the boundary logarithm in (13.4), so that
$\Psi(t)=-A_0(it)\ell(it)$. There are constants $c,C>0$ such that,
for every $x\geq1$, every sufficiently large $m$, and the interval
$I_m=[2\pi(m-1/2)/a,2\pi(m+1/2)/a]$,

$$
\left|\int_{I_m}e^{itx}\Psi(t)\,dt\right|
\leq C\left(
\frac{\omega(2\pi m/a)e^{-c\eta_m x}}x
+\frac{\omega(2\pi m/a)}{x^2}\right).                         \tag{16.6}
$$

*Proof.* Choose a fixed smooth cutoff equal to one on the smaller
interval where (16.2) holds. On that interval Taylor's formula gives

$$
\Delta(t)=\eta_m+i\lambda_m(t-\widehat t_m)\,G_m(t),
\qquad |\lambda_m|\asymp1,\qquad G_m(\widehat t_m)=1,
$$

where $G_m$ and its first two derivatives are uniformly bounded and
bounded away from zero; the real part of the linear coefficient is
$O(\eta_m)$. Hence, after changing the bounded smooth factor $G_m$,
the difference between $\log\Delta(t)$ and
$\log(\eta_m+i\lambda_m(t-\widehat t_m))$ has uniformly bounded two
derivatives. The same is true after multiplying by $A_0(it)$, apart
from the factor $|A_0(i\widehat t_m)|\asymp\omega(2\pi m/a)$, by the
Gamma estimates (13.5). For nonresonant $m$, the whole logarithm and
its first two derivatives are uniformly bounded and two integrations
by parts give the second term in (16.6).

For the model logarithm, differentiate once and use the elementary
residue identity, valid for $x>0$,

$$
\int_{\mathbb R}\frac{e^{iux}}{\eta+i\lambda u}\,du
=\frac{2\pi}{\lambda}e^{-\eta x/\lambda}
$$

with the sign chosen by the sign of $\lambda$. Integrating by parts
once in the cutoff identity for $\log(\eta+i\lambda u)$ gives
$O(x^{-1}e^{-c\eta x})+O(x^{-2})$; the cutoff derivatives and the
uniformly smooth difference contribute $O(x^{-2})$. The tails of the
interval are treated by two integrations by parts, using (13.5) and
(16.2). Multiplication by the displayed Gamma factor proves (16.6).
More explicitly, if $\chi$ is one near zero and supported in the
fixed local interval, then

$$
\begin{aligned}
ix\int e^{ixu}\chi(u)\log(\eta+i\lambda u)\,du
 &=-\int e^{ixu}\chi(u)\frac{i\lambda}{\eta+i\lambda u}\,du\\
 &\quad-\int e^{ixu}\chi'(u)\log(\eta+i\lambda u)\,du .
\end{aligned}
$$

The second integral is $O(x^{-2})$ after one further integration by
parts because $\chi'$ is supported away from zero. In the first
integral replace $\chi$ by one; the difference is again smooth away
from zero. Closing the contour in the half-plane selected by the sign
of $\lambda x$ gives the displayed residue and
$O(x^{-1}e^{-c\eta x})$. The quotient estimate
$|\eta+i\lambda u|\asymp\eta+|u|$ and Taylor's remainder show that
the two derivatives of the difference of the actual logarithm and
the model are bounded uniformly; two integrations by parts therefore
give $O(x^{-2})$. The factor $A_0(i(\widehat t_m+u))$ is its value at
$u=0$ plus $u$ times a function with the same bounds, and the latter
term is covered by the same two integrations. The negative-frequency
estimate follows by conjugation. $\qed$

**Lemma 16.4 (Critical block summation).** With

$$
\omega_j=Q_j^{-3/2}e^{-2\kappa Q_j},\qquad
\eta_j=Q_{j+1}^{-2},
$$

there is a constant $C$ such that, for every $x\geq1$,

$$
\sum_{j\geq j_0}\omega_j e^{-c\eta_jx}\leq\frac Cx,
\qquad
\sum_{j\geq j_0}\omega_j<\infty.                               \tag{16.7}
$$

*Proof.* Equation (16.3) gives $\omega_j\asymp\eta_j$ and, after
discarding finitely many terms, $\eta_{j+1}\leq\eta_j/2$. Split the
sum at the last index with $\eta_jx\geq1$. Before that index, group
the terms dyadically and use
$\sum_{k\geq0}2^ke^{-c2^k}<\infty$; afterwards use the geometric
tail $\sum_{j>J}\eta_j\leq2\eta_{J+1}\leq2/x$. The second assertion is
the same geometric estimate with $x=1$. $\qed$

**Theorem 16.5 (Bounded critical residual).** For the single fixed law
$p=p^{[3/4]}$ of Definition 15.1, there is a finite constant $C_p$ such
that

$$
|R_n(p)|\leq C_p\qquad\text{for every integer }n\geq2.            \tag{16.8}
$$

*Proof.* The transform identity (13.4), the comparison kernel (9.5),
and the exact occurrence reduction (9.4) apply to this same ordered
binary iid law and to the original statistic, including letters, every
legal length and window, and the whole word when Lyndon. The estimates
(15.9), (16.1), and (13.5) imply
$\Psi\in L^1(\mathbb R)$: on the block $Q_j\leq m<Q_{j+1}$,
$|\Delta(t)|\geq cQ_{j+1}^{-2}$ by (15.10), and hence
$|\ell(it)|\leq C+Q_j+\log(2+m)$ and the Gamma factor is bounded by
$C\omega(m)$. Abelian Fourier inversion in (13.4), followed by
$\sigma\downarrow0$, therefore gives

$$
H(x):=J_p(x)-J_0(x)=\frac1{2\pi}\int_{\mathbb R}e^{itx}\Psi(t)\,dt.
$$

The finitely many low-frequency pieces are $O(x^{-2})$ by two
integrations by parts. Apply Lemma 16.3 on each $I_m$ and sum first over
$Q_j\leq m<Q_{j+1}$. Since $\omega(2\pi m/a)$ decreases geometrically
with $m$ and (16.1) gives $\eta_m\geq c\eta_j$,

$$
\left|\int_{T_j}^{T_{j+1}}e^{itx}\Psi(t)\,dt\right|
\leq C\left(\frac{\omega_j e^{-c\eta_jx}}x
                        +\frac{\omega_j}{x^2}\right).            \tag{16.9}
$$

The same estimate holds on negative blocks. Equations (16.7) and
(16.9) give $H(x)=O_p(x^{-2})$ for $x\geq1$.

The comparison expansion (9.6) and (14.3) now yield

$$
\mathscr R_p(x)=c_*-x^2H(x)+O_p(x^{-1})=O_p(1).                 \tag{16.10}
$$

The real/integer interpolation in (14.4) gives
$R_n(p)=O_p(1)$ for all sufficiently large integers. The finitely many
values $2\leq n<n_0(p)$ have finite residuals, so enlarging the same
constant proves (16.8). $\qed$

**Theorem 16.6 (Original expectation and the inherited endpoint).** For
the same fixed law $p=p^{[3/4]}$ and all integers $n\to\infty$,

$$
E_p(n)=M_p(n)+\frac{\mu n}{\log n}
       +O_p\!\left(\frac n{(\log n)^2}\right).                  \tag{16.11}
$$

The residual in (16.8) has no finite limit. Consequently there is no
real constant $C$ for which

$$
E_p(n)=M_p(n)+\frac{\mu n}{\log n}
            +\frac{Cn}{(\log n)^2}
            +o_p\!\left(\frac n{(\log n)^2}\right).             \tag{16.12}
$$

*Proof.* Equation (16.11) is exactly the definition of $R_n(p)$ in
(8.1) together with the newly proved absolute bound (16.8). The
nonconvergence statement is the $\tau=3/4$ line of Theorem 15.2,
which concerns this same all-integer residual and this same original
expectation. It is therefore inherited rather than reproved here.
If (16.12) held, multiplying by $(\log n)^2/n$ would give
$R_n(p)\to C$, contradicting that inherited conclusion. Thus the
second-order term is bounded but cannot be replaced by a constant with
an $o_p(n/(\log n)^2)$ remainder. No assertion about arbitrary critical
laws, separate signs, rates, or parameter-uniform constants follows. $\qed$

## 追加锚（本行以下为增补区）
