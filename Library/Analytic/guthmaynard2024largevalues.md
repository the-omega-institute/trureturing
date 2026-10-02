---
bibkey: guthmaynard2024largevalues
authors: Larry Guth and James Maynard
year: 2024
title: New large value estimates for Dirichlet polynomials
doi: null
url: https://arxiv.org/abs/2405.20552v2
claim: Corollary 1.3 supplies uniform prime counts in short intervals, while Theorem 1.2 supplies the zero-density exponent used in cumulative spectral-tail estimates. The FIB applications retain the actual source and do not establish the full signed Robin budget.
strata_touched: []
license: citation-only
triage: anchor
---

# Short intervals and the Fibonacci sampling boundary

The primary source is Guth–Maynard, *New large value estimates for Dirichlet polynomials*, [arXiv:2405.20552v2](https://arxiv.org/abs/2405.20552v2), with [versioned HTML](https://arxiv.org/html/2405.20552v2) and [versioned PDF](https://arxiv.org/pdf/2405.20552v2). The title page identifies this version as 7 April 2026. Theorem 1.2 and Corollary 1.3 were checked in the original text. They are literature inputs; this note does not independently audit the complete large-values and zero-density proof. The applications below are paper derivations, without an originality or full Lean-verification claim.

## The short-interval input

Corollary 1.3, printed pp.2–3, states that for fixed $\epsilon>0$ and $h\in[x^{17/30+\epsilon},x^{0.99}]$,

$$
\pi(x+h)-\pi(x)=\frac h{\log x}
+O_\epsilon\left(h\exp[-(\log x)^{1/4}]\right).
$$

This is a uniform short-interval statement, distinct from Corollary 1.4's almost-all statement. Fixing $\epsilon=1/20$ permits $h=Cx^{2/3}$ for every fixed $C>0$ and sufficiently large $x$. Since the primes in that interval have $\log p=(1+o(1))\log x$, it follows that

$$
\vartheta(x+Cx^{2/3})-\vartheta(x)\sim Cx^{2/3}.
$$

In particular, consecutive primes $r<r^+$ satisfy $r^+-r\le r^{2/3}$ eventually. The exponent $2/3$ is chosen only to leave room inside the cited range; this application makes no improvement to a prime-gap record.

## Finite interpolation without assuming a prime error bound

Use the notation of the [Nicolas comparison note](../ArithSums/nicolas2025comparison.md):

$$
I(x)=I_\psi(x)=\int_x^\infty(\psi(u)-u)k(u)\,du,
\qquad k(u)=\frac{1+\log u}{u^2\log^2u}.
$$

Available unconditional quantitative PNT guarantees convergence. Put $q(x)=1/(x\log x)$, so that $q'=-k<0$, and $k$ is decreasing on $(1,\infty)$. For $1<a<b$ and $x\in[a,b]$, set

$$
\lambda_x=\frac{q(x)-q(b)}{q(a)-q(b)}.
$$

Monotonicity of $\psi$ gives the finite lower interpolation bound

$$
I(x)\ge\lambda_x I(a)+(1-\lambda_x)I(b)
-\frac{[q(a)-q(x)][q(x)-q(b)]}{2k(b)}.
\tag{1}
$$

To verify it despite prime-power jumps, work in $z=q(x)$ and write $H(z)=I(q^{-1}(z))$. This function is locally absolutely continuous, with derivative $\psi(q^{-1}(z))-q^{-1}(z)$ almost everywhere. For $u<v$ in $[q(b),q(a)]$, monotonicity of $\psi$ and the inverse derivative bound give

$$
\begin{aligned}
&[\psi(q^{-1}(v))-q^{-1}(v)]
-[\psi(q^{-1}(u))-q^{-1}(u)]\\
&\qquad\le q^{-1}(u)-q^{-1}(v)
\le\frac{v-u}{k(b)}.
\end{aligned}
$$

Thus the almost-everywhere derivative of $H(z)-z^2/(2k(b))$ has a nonincreasing representative. Integration, or the elementary comparison of its average slopes on adjacent intervals, shows that this function is concave. Its chord inequality is exactly (1). The downward derivative jumps are included in this argument; it does not treat $I$ as twice differentiable at prime powers.

In particular the nonnegative interpolation penalty is at most

$$
\frac{[q(a)-q(b)]^2}{8k(b)}
\le\frac{k(a)^2(b-a)^2}{8k(b)}.
\tag{2}
$$

When $b/a\to1$, its size after multiplying by $\sqrt x\log x$ is

$$
O\left(\frac{(b-a)^2}{a^{3/2}}\right),
$$

uniformly for $x\in[a,b]$. This quadratic loss uses the monotonicity of $\psi$; a bound obtained by integrating $|I'|$ discards this information.

## The sampling implication and its quantifiers

Let $a_j\to\infty$ be strictly increasing, with $a_{j+1}-a_j=O(a_j^{3/4})$. Suppose a finite constant $K\ge0$ satisfies

$$
I(a_j)\ge-\frac K{\sqrt{a_j}\log a_j}
$$

for every sufficiently large $j$. Equations (1)–(2) imply a global eventual lower bound of the same shape with some finite, possibly larger constant. Indeed $a_{j+1}/a_j\to1$, the two normalized endpoint budgets differ by $o(1)$, and the normalized interpolation penalty is bounded. If the spacing is $o(a_j^{3/4})$, that penalty is $o(1)$ and the global bound holds with every fixed constant larger than $K$.

The already recorded [FIB volume, §92.3](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), uses the classical integrated explicit formula and Landau's nonnegative Laplace-transform theorem to show that any finite global eventual lower bound of this shape implies RH. Conversely, under RH, that same argument gives the global bound for every fixed $K>C_\gamma$, where $C_\gamma=2+\gamma-\log(4\pi)$. Thus the existence of such a sampled bound on a mesh satisfying the stated spacing is equivalent to RH. Neither the interpolation lemma nor the short-interval theorem establishes the sampled bound.

## Application to all prime-index FIB windows

For every sufficiently large odd prime $r$, define

$$
V_r=F_r,\quad
A_r=1+V_r\lceil V_r/10\rceil,\quad
X_r=1+V_r\lfloor V_r/5\rfloor.
$$

These are the endpoints of the actual integers $1+V_rg$ used in §§231–234. They satisfy $X_r/A_r<2$. Therefore the window contains at most one primorial threshold, and its integers have at most two adjacent primorial cutoffs; sufficiently large adjacent primorial thresholds have ratio greater than two. This is an upper bound on the number of cutoffs, not a claim that both occur among the actual progression points.

Let $a_r$ be the prime for which $P_{a_r}\le A_r<P_{a_r^+}$. Binet's formula gives

$$
Y_r:=\log A_r=2r\log\varphi-\log50+O(\varphi^{-r}),
\qquad \varphi=\frac{1+\sqrt5}{2}.
$$

Since $0\le Y_r-\vartheta(a_r)<\log a_r^+$, ordinary PNT yields

$$
a_r\sim2r\log\varphi,
\qquad \vartheta(a_r)=2r\log\varphi+O(\log r).
$$

For consecutive prime indices $r<r^+$, the short-interval input then gives

$$
0\le\vartheta(a_{r^+})-\vartheta(a_r)
=O(r^{2/3})=O(a_r^{2/3}).
$$

It is essential to justify the inverse-$\vartheta$ step. Ordinary PNT alone does not give the required local spacing. Choose a fixed $C$ larger than twice the constant in the last bound. The cited uniform short-interval estimate gives

$$
\vartheta(a_r+Ca_r^{2/3})-\vartheta(a_r)
\sim Ca_r^{2/3},
$$

so monotonicity forces $a_{r^+}-a_r=O(a_r^{2/3})$. Removing repeated cutoffs leaves an unbounded increasing sequence with the same bound on successive gaps: each nonzero step already occurs between consecutive prime indices. This sequence therefore satisfies the interpolation hypothesis with normalized error $O(a_r^{-1/6})$.

Consequently, the assertion

$$
\exists K<\infty\ \exists r_0\ \forall\text{ primes }r\ge r_0,
\quad I_\psi(a_r)\ge-\frac K{\sqrt{a_r}\log a_r}
\tag{3}
$$

is already equivalent to RH, by the preceding classical inputs. Restricting this particular estimate to all prime-index FIB window cutoffs does not produce a known weaker analytic task. Taking more cutoffs from each window is unnecessary for this implication; the cutoff at $A_r$ alone suffices.

The exact endpoint $Q(x)$ in the Nicolas note is nonnegative, since $\log(1+t)\le t$ applied twice gives $Q(x)\ge0$. Therefore a uniform finite upper bound for $\sqrt{a_r}\log a_r[Q(a_r)-I_\psi(a_r)]$ at **all** these cutoffs also implies (3) and hence RH. This observation does not prove that upper bound.

## Why this does not settle the actual singleton

The FIB window theorem only allows **at most one** integer with a low-loss divisor in each window; it does not assert existence. The set of cutoffs of actually existing candidates may omit windows, and no bound on its gaps has been established. Equations (1)–(3) cannot be applied to that subset merely because the full set of window cutoffs has small gaps.

An estimate restricted to the actual candidates must still obtain its sign from an independent arithmetic property, or use a positive lower bound for the actual envelope deficit $\log(\Sigma(N)/Z(N))$. A theorem that the required estimate holds for all window cutoffs would be sufficient but already RH-strength. None of these applications proves the candidate estimate, the full Robin criterion, or a bridge from the special FIB family to every required integer.

## The zero-density input for cumulative contributions

Theorem 1.2, printed p.2 of the same version, concerns the actual nontrivial zeros of $\zeta$, counted with multiplicity. With

$$
N(\sigma,T)=\#\{\rho:\Re\rho\ge\sigma,\ |\Im\rho|\le T\},
\qquad a(\sigma)=\frac{15(1-\sigma)}{3+5\sigma},
$$

it gives $N(\sigma,T)\le T^{a(\sigma)+o(1)}$ as $T\to\infty$. No RH hypothesis is present. A use at finitely many fixed $\sigma$ values permits separate constants and thresholds; it need not assume an additional uniformity of the $o(1)$ over a moving real-part parameter.

For comparison, the original paper's equations (1.2) and (1.3), on the same page, record the Ingham and Huxley exponents

$$
a_{\rm I}(\sigma)=\frac{3(1-\sigma)}{2-\sigma},
\qquad a_{\rm H}(\sigma)=\frac{3(1-\sigma)}{3\sigma-1}.
$$

On $1/2\le\sigma\le3/4$, the smaller of these two is $a_{\rm I}$, and at $3/4$ the two coincide with value $3/5$. Theorem 1.2 gives $a(3/4)=5/9$. This is a comparison with these named bounds, not a claim about every other zero-density refinement.

## A controlled infinite sector of the actual cumulative spectrum

Use the same actual $I_\psi$, $Z(x)=\sqrt x\log x\,I_\psi(x)$ and cumulative quantity as [the FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), §§316 and 335:

$$
\mathcal S(X)=\int_{A_0}^X Z(x)\frac{dx}{x},\qquad
X\ge A_0\ge50,\qquad t_0=\log A_0,\quad L=\log X.
$$

The finite true-node certificate and its finite total discretization loss in §335 are reused. The estimate below concerns a part of $\mathcal S$ itself, rather than another interpolation error.

The existing unconditional integrated explicit formula for
$J(x)=\int_x^\infty(\psi(v)-v)dv/v^2$ supplies the zero terms
$-x^{\rho-1}/[\rho(1-\rho)]$ and an elementary remainder $O(x^{-1})$.
Put $a_0(t)=(t+1)/t^2$. Integration by parts gives

$$
I_\psi(e^t)=a_0(t)J(e^t)
+\int_t^\infty a_0'(u)J(e^u)\,du.
\tag{4}
$$

The zero coefficients of $J$ are summable in absolute value, of order
$|\Im\rho|^{-2}$ at large height. Since $0<\Re\rho<1$,
$|e^{(\rho-1)u}|\le1$ for $u\ge t_0$, and $a_0'$ is absolutely
integrable there. Thus (4) can be applied termwise to that integrated
formula. It does not require interchanging the raw, conditionally
convergent zero series for $\psi$ with an infinite integral. The elementary
remainder has bounded cumulative contribution after the same transform.

For an actual zero $\rho=\beta+i\gamma$, the resulting cumulative term is

$$
s_\rho(X)=-\frac1\rho\int_{t_0}^L t e^{t/2}
\left[\int_t^\infty e^{-(1-\rho)u}\frac{u+1}{u^2}\,du\right]dt.
\tag{5}
$$

Both the infinite inner upper limit and the two cumulative endpoints are retained. Set $\lambda=1-\rho$, $z=\rho-1/2$ and

$$
b_\rho(t)=\int_0^\infty e^{-y}
\frac{\lambda(t+y)}{\lambda t+y}\,dy.
\tag{6}
$$

The integrand in (5), including $-1/\rho$, equals
$-e^{zt}b_\rho(t)/[\rho\lambda]$. Indeed,
$(u+1)/u^2=\int_0^\infty e^{-uv}(1+v)dv$; absolute convergence
when $\Re\lambda>0$ permits the exchange of these two integrals, and
$y=tv$ gives (6).

For $t>0$ and $y\ge0$, $|\lambda t+y|\ge|\lambda|t$. The rational
integrand's $t$-derivative is
$\lambda\rho y/(\lambda t+y)^2$. Dominated differentiation on each
positive compact $t$-interval therefore gives, when $|\gamma|\ge1$,

$$
|b_\rho(t)|\le1+\frac1t,\qquad
|b_\rho'(t)|\le\frac{|\rho|}{|\lambda|t^2}
\le\frac{\sqrt2}{t^2}.
\tag{7}
$$

Here $|\rho|/|1-\rho|\le\sqrt2$ follows from
$0<\beta<1$ and $|\gamma|\ge1$. Integration by parts against $e^{zt}$,
with both endpoints and the derivative integral kept, gives

$$
\begin{aligned}
|s_\rho(X)|
&\le\left[2+\frac{2+\sqrt2}{t_0}\right]
\frac{X^{\max(\beta-1/2,0)}}{|\rho(1-\rho)(\rho-1/2)|}\\
&\le3\frac{X^{\max(\beta-1/2,0)}}{|\gamma|^3}.
\end{aligned}
\tag{8}
$$

The constant is valid for $t_0\ge\log50>7/2$. The additional inverse
height power comes from cumulative integration; it is not an assumed
cancellation among zeros. At each fixed $X$, (8) and the usual zero count
make the following infinite sum absolutely convergent:

$$
\mathcal R_{3/4}(X;H)
=\sum_{\substack{\rho=\beta+i\gamma\\
1/2<\beta\le3/4,\ |\gamma|>H}}s_\rho(X),\qquad H\ge1.
\tag{9}
$$

Conjugates and multiplicities are included, so this is a real contribution
of the same actual spectrum.

Take $H=X^h$ with fixed $h>0$. Partition $[1/2,3/4]$ into finitely many
fixed real-part bins of maximum width $\delta$. For a bin starting at
$\sigma$, (8) bounds its cumulative terms by a constant times
$X^{\sigma+\delta-1/2}|\gamma|^{-3}$. At heights
$2^jH<|\gamma|\le2^{j+1}H$, Theorem 1.2 bounds the number of terms by
$O_{\sigma,\eta}((2^{j+1}H)^{a(\sigma)+\eta})$, for any fixed sufficiently
small $\eta>0$ and sufficiently large $H$. Since $a(\sigma)+\eta<3$,
the geometric height sum converges. This bin contributes

$$
O_{\sigma,\eta,A_0}
\left(X^{\sigma+\delta-1/2}H^{a(\sigma)-3+\eta}\right).
\tag{10}
$$

Choose the finite bin widths and $\eta$ in terms of a fixed final
$\varepsilon>0$, so that $\delta+h\eta<\varepsilon$. Only finitely many
fixed density parameters occur. Their separate constants and thresholds
can be combined; no unproved uniformity in $\sigma$ is used.

For $h=31/300$, the exponent
$F(\sigma)=\sigma-1/2+h[a(\sigma)-3]$ is increasing on the entire bin
range: $F'=1-120h/(3+5\sigma)^2>0$. Its endpoint is

$$
F(3/4)=\frac14+\frac{31}{300}\left(\frac59-3\right)
=-\frac7{2700}.
$$

Consequently, for every fixed $\varepsilon>0$, on all sufficiently large
real cutoffs,

$$
|\mathcal R_{3/4}(X;X^{31/300})|
\ll_{\varepsilon,A_0}X^{-7/2700+\varepsilon}.
\tag{11}
$$

In particular this actual infinite sector is $o(1)$ for
$0<\varepsilon<7/2700$. The same calculation with the named
Ingham–Huxley bounds has its maximum at $3/4$, with exponent
$1/4+(31/300)(3/5-3)=1/500>0$:

| Density input to this sector calculation | Allowance at $H=X^{31/300}$ | Endpoint threshold for decay |
|---|---|---|
| Named Ingham–Huxley bounds | $X^{1/500+o(1)}$ | $h>5/48$ |
| Guth–Maynard Theorem 1.2 | $X^{-7/2700+o(1)}$ | $h>9/88$ |

The selected power satisfies $9/88<31/300<5/48$. Thus the new input
changes this comparison from a growing allowance to a decaying one.
The growing allowance is an upper bound supplied by those classical
inputs, not an assertion that the actual sector grows.

## The complementary signed contribution remains

Equation (11) controls neither $\beta>3/4$ nor the right-of-line zeros at
heights $|\gamma|\le X^{31/300}$. Every fixed off-line zero eventually
leaves the controlled sector. For a fixed $\rho$ with $\beta>1/2$, (5)–(7)
retain the cumulative leading term

$$
s_\rho(X)=-\frac{X^{\rho-1/2}}
{\rho(1-\rho)(\rho-1/2)}
\left(1+O_\rho\left(\frac1{\log X}\right)\right)
+O_{\rho,A_0}(1).
\tag{12}
$$

Its conjugate pair still has an oscillatory component on the
$X^{\beta-1/2}$ scale. The sector bound does not control the sign or
cancellation of that remaining contribution and supplies no fixed
logarithmic lower budget for the full $\mathcal S$. It therefore proves
neither the missing budget in §335 nor RH. It computes or verifies no
zeros and makes no estimate on the unknown subset of actual low-loss
FIB candidates.

Transient Lean checks verified the exact height ordering, both endpoint
exponents, the scalar maximum inequalities on the stated real-part
range, the numerical kernel constant under $t_0\ge7/2$, and the
negative-power limit. Their axiom closures contain only `propext`,
`Classical.choice` and `Quot.sound`. These checks retain no new Lean
declarations. The kernel and sector arguments above are paper
derivations; the improper integrals, the zero-density theorem and the
actual-zeta bridge are not Lean-formalized here.
