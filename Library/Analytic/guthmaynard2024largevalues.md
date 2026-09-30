---
bibkey: guthmaynard2024largevalues
authors: Larry Guth and James Maynard
year: 2024
title: New large value estimates for Dirichlet polynomials
doi: null
url: https://arxiv.org/abs/2405.20552v2
claim: Corollary 1.3 supplies uniform prime counts in short intervals; together with monotonicity of the Chebyshev function and the existing global one-sided integral criterion, it shows why testing all prime-index Fibonacci window cutoffs is still an RH-strength requirement. No such estimate is established on the unknown subset of actual low-loss candidates.
strata_touched: []
license: citation-only
triage: anchor
---

# Short intervals and the Fibonacci sampling boundary

The primary source is Guth–Maynard, *New large value estimates for Dirichlet polynomials*, [arXiv:2405.20552v2](https://arxiv.org/abs/2405.20552v2), with [versioned HTML](https://arxiv.org/html/2405.20552v2). Corollary 1.3 and its parameter range were checked in the original text. This note uses that corollary as a literature input; it does not independently audit the complete large-values and zero-density proof. The interpolation and FIB parameter comparison below are paper applications, without an originality or Lean-verification claim.

## The short-interval input

Corollary 1.3, printed pp.2–3, states that for fixed $\epsilon>0$ and $h\in[x^{17/30+\epsilon},x^{0.99}]$,

$$
\pi(x+h)-\pi(x)=\frac h{\log x}
+O_\epsilon\left(h\exp[-(\log x)^{1/4}]ight).
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
