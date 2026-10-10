---
bibkey: chirrehelfgott2025bounded
authors: Andrés Chirre; Harald Andrés Helfgott
year: 2025
title: Optimal bounds for sums of bounded arithmetic functions
url: https://arxiv.org/abs/2511.14736
claim: Finite-height Mertens estimates supply an existing absolute input and a signed spectral formula with a linear height threshold; a lawful finite-annulus transfer retains actual small prefixes and leaves the critical odd-source lower bound unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite spectral data for the actual odd-Möbius source

The primary source is Chirre–Helfgott,
[arXiv:2511.14736v1](https://arxiv.org/pdf/2511.14736v1), submitted
18 November 2025, with title-page date 19 November. The retrieved PDF has
44 pages and SHA-256
`67dbb583b03b42451be44179a85a2bb59590fa6f0922a1f74884401b7f5506ea`.
The arXiv version record inspected on 10 October 2026 lists only v1 and
does not list a journal publication. Corollaries 1.2–1.3, the threshold
in Corollary 6.4, and §9.2.2 were read in the original text.
The [HTML TeX](https://arxiv.org/html/2511.14736v1) confirms
$y\ge e^2T$ and $L=\log(y/T)$ in the formula and its proof. The complete
proof and the authors' rigorous residue computations were not independently
audited or rerun; the applications below are not Lean-verified.

This is a different paper from the
[nonnegative-coefficient companion](../Weil/chirrehelfgott2025nonnegative.md),
arXiv:2512.15709v1. Its results are reused here, not rederived or presented
as new Mertens estimates.

## The supplier's exact signed formula and conditions

Write $M(y)=\sum_{n\le y}\mu(n)$. For $T\ge4\pi$, put
$\delta=\pi/(2T)$ and

$$
Z_T(y)=\delta\sum_{\substack{\rho\text{ nontrivial zero of }\zeta\\
|\Im\rho|\le T}}
\frac{\coth(\delta\rho)-\tanh\delta}{\zeta'(\rho)}y^\rho-2.
$$

Corollary 1.2, PDF p.2, at $\sigma=0$ states

$$
|M(y)-Z_T(y)|\le\frac{\pi y}{2(T-1)}+2,
\qquad y\ge e^2T,\qquad
\max_{r\le1}\frac1{|\zeta(r\pm iT)|}\le(\log y)^2.
\tag{CH1}
$$

All nontrivial zeros through height $T$ must be simple. The horizontal
bound also excludes zeros at height exactly $T$. The displayed $-2$
is $1/\zeta(0)$, not an omitted unit-source correction. No zero in the
formula is assumed to have real part $1/2$.

The restriction $y\ge e^2T$ is part of the signed formula. It also
appears in Corollary 6.4, PDF p.21; the paper's later extension of an
absolute bound to all $y\ge1$ does not remove it from (CH1).

## The whole-range absolute estimate is reusable but insufficient alone

Corollary 1.3, PDF p.3, states, unconditionally,

$$
|M(y)|\le\varepsilon y+11.39\sqrt y\quad(y\ge1),
\qquad\varepsilon=\frac3{\pi\,10^{10}}.
\tag{CH2}
$$

The numerical input includes the authors' residue computations at height
$10^{10}+1$. Reuse the actual dyadic inverse of FIB companion §453.3,

$$
O(t)=\sum_{\substack{n\le t\\n\text{ odd}}}\mu(n)
=\sum_{2^a\le t}M(t/2^a).
$$

The source already recommends this coprimality transfer in §9.2.3.
Here it is specialized to the existing odd filter; no new filtering
theorem is supplied.

Summing the two geometric majorants in (CH2) gives

$$
|O(t)|\le2\varepsilon t+
\frac{11.39}{1-2^{-1/2}}\sqrt t\quad(t\ge1).
\tag{CH3}
$$

For the actual factorial kernel $\mathscr D_x$ and $\ell=\log x$, reuse
(N2)–(N3) of the
[complete odd-source application](ng2004summatorymobius.md).
Inserting the linear part of (CH3) into its infinite Abel integral gives
the divergent upper majorant

$$
\frac{72\varepsilon}{\ell}
\int_N^\infty\frac{(1+\log(t/x))^2}{t}\,dt.
$$

This prevents that particular absolute estimate from paying the infinite
tail by itself. It does not say the actual tail diverges. The existing
Vinogradov–Korobov application already pays that tail; it is not repeated.

## A lawful finite-annulus interface retains the small arguments

Fix an admissible $T$ and let
$C_T=\max_{r\le1}1/|\zeta(r\pm iT)|<\infty$. Set
$Y_T=\max(e^2T,e^{\sqrt{C_T}})$ and define

$$
A_T(v)=
\begin{cases}
Z_T(v),&v\ge Y_T,\\
M(v),&1\le v<Y_T,
\end{cases}
\qquad
\widetilde O_T(t)=\sum_{2^a\le t}A_T(t/2^a).
$$

Every replaced argument satisfies every condition of (CH1); the others
are retained as actual prefixes, not estimated by the signed formula.
Thus, for $t\ge1$,

$$
|O(t)-\widetilde O_T(t)|\le
E_T(t):=\frac{\pi t}{T-1}
+2(1+\lfloor\log_2t\rfloor).
\tag{CH4}
$$

For integers $Q\ge N\ge x\ge e$, the existing finite Abel identity is

$$
\sum_{\substack{N<m\le Q\\m\text{ odd}}}\mu(m)\mathscr D_x(m)
=O(Q)\mathscr D_x(Q)-O(N)\mathscr D_x(N)
-\int_N^Q O(t)\mathscr D'_x(t)\,dt.
$$

Replacing $O$ by $\widetilde O_T$ on the right has error at most

$$
E_T(Q)|\mathscr D_x(Q)|+E_T(N)|\mathscr D_x(N)|
+\int_N^Q E_T(t)|\mathscr D'_x(t)|\,dt.
\tag{CH5}
$$

Both endpoints are required. Reusing (N2) bounds (CH5), with an absolute
implicit constant, by

$$
\frac1{\log x}\left[
\frac{(1+\log(Q/x))^3}{T}
+\frac{(1+\log Q)(1+\log(Q/x))^2}{N}
\right].
\tag{CH6}
$$

The linear contribution uses $\int_N^Q(1+\log(t/x))^2dt/t$;
the logarithmic contribution uses the existing integrable kernel
majorant and $t\ge N$. These are parameter applications of the cited
estimates and Abel identity, not a new spectral or arithmetic theorem.

## A conditional critical-scale annulus use and its remaining duties

Take the already selected sufficient full-source cutoff

$$
Q=N_{18}(x)=\left\lceil
 e^{18(\log x)^{5/3}(\log\log x)^{1/3}}
\right\rceil,
\qquad N=\lceil8x\rceil.
$$

Suppose that for every sufficiently large $x$ an admissible height $T(x)$
is available with $T(x)\asymp x^{3/4}$ and
$C_{T(x)}\le(\log N)^2$. All zeros through each chosen height must be
simple and the horizontal bounds must be certified as in (CH1). Then
$e^2T(x)<N$ eventually and $Y_{T(x)}\le N$. The signed formula can
therefore replace the large dyadic arguments; the smaller arguments remain
actual $M$ prefixes in $A_T$.

At these parameters, both terms in (CH6) are
$o(1/(\sqrt x\log x))$: the first has critical normalized order
$O(x^{-1/4}(1+\log(Q/x))^3)$, and the second has order
$O(x^{-1/2}(1+\log Q)(1+\log(Q/x))^2)$. Both decay since $\log Q$
is a fixed power of $\log x$ times a fixed power of $\log\log x$.
Together with the already paid full odd-source tail beyond $Q$, this
would give

$$
\begin{aligned}
I_\psi(x)={}&
\sum_{\substack{m\le N\\m\text{ odd}}}\mu(m)\mathscr D_x(m)
+\widetilde O_T(Q)\mathscr D_x(Q)
-\widetilde O_T(N)\mathscr D_x(N)\\
&-\int_N^Q\widetilde O_T(t)\mathscr D'_x(t)\,dt
+o\!\left(\frac1{\sqrt x\log x}\right).
\end{aligned}
\tag{CH7}
$$

This conditional application supplies an arithmetic prefix and a signed
finite-spectrum annulus, while retaining every small dyadic argument and
both endpoints. No growing family of admissible verified heights is
supplied here. The source's fixed finite computations do not establish
those unbounded hypotheses. The growing-height simplicity premise implies
global simplicity and is an additional assumption, not a consequence of
RH. The signed residue contributions are retained;
their lower bound against the same actual Robin core remains unproved.
This is neither an unconditional critical error bound nor a proof of RH.

Section 9.2.2 proposes direct continuous-weight analogues with improved
$T^{-2}$ terms; it does not provide a theorem for $\mathscr D_x$.
Such an adaptation could reduce the heights or exact-prefix cost, but needs
its own proof. The whole-range absolute estimate, the conditional signed
formula, and the pending weighted adaptation have distinct roles.
