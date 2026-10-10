---
bibkey: chirrehelfgott2025bounded
authors: Andrés Chirre; Harald Andrés Helfgott
year: 2025
title: Optimal bounds for sums of bounded arithmetic functions
url: https://arxiv.org/abs/2511.14736
claim: Full residues and published good heights give a critically negligible raw odd-source annulus error without additional simplicity or growing-height hypotheses; effective certification and the signed Robin estimate remain unresolved.
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
in Corollary 6.4, Theorem 1.1, the proof of Lemma 6.3, Lemma B.1,
and §9.2.2 were read in the original text.
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

## The general supplier retains arbitrary pole orders

Theorem 1.1, PDF p.2, already uses full residues of a meromorphic
Dirichlet series. Apply it with $A(s)=1/\zeta(s)$, $a_n=\mu(n)$,
$a_\infty=1$ and $\sigma=0$. Retain each distinct nontrivial pole once:

$$
Z_T^{\rm res}(y)=\delta
\sum_{\substack{\rho\text{ distinct nontrivial zero of }\zeta\\
|\Im\rho|<T}}
\operatorname{Res}_{s=\rho}
\frac{(\coth(\delta s)-\tanh\delta)y^s}{\zeta(s)}-2.
\tag{CH1a}
$$

For $T\ge4\pi$ with $C_T=\max_{r\le1}1/|\zeta(r\pm iT)|<\infty$,
the source's Lemma B.1 and the proof of Corollary 6.4 supply the contour
ladder required by Theorem 1.1: horizontal segments at $\pm T$ and
vertical lines $\Re s=-2n+1$ tending to $-\infty$. Multiplication by
$T^s$ preserves boundedness on this ladder, whose real parts are at most
one. Nontrivial poles inside the contour need not be simple.

The pole of the weight at zero contributes $1/\zeta(0)=-2$.
The proof of Lemma 6.3 bounds the absolute trivial-pole contribution,
after multiplying the theorem's normalized formula by $y$, by
$K_Ty^{-2}$, where

$$
K_T=\left(\frac12+2\delta\right)\frac{(2\pi)^2}{\zeta(3)}.
$$

The displayed Lemma 6.3 uses an equality and its proof's first-term
majorant omits the absolute value around $\zeta'(-2)<0$. The
alternating-series argument and (6.6), using $|\zeta'(-2)|$, give the
absolute bound above. Set $L=\log(y/T)$. Theorem 1.1 therefore gives the
explicit error envelope

$$
|M(y)-Z_T^{\rm res}(y)|\le
y\tanh\delta+
\frac{\pi y}{4T^2}\left(L^{-1}+L^{-2}
+\frac{C_T}{(\log y)^2}\right)+2+\frac{K_T}{y^2}
\quad(y>e^2T).
\tag{CH1b}
$$

Here the horizontal integral is bounded by
$C_T\int_0^\infty t y^{-t}dt=C_T/(\log y)^2$. When also
$C_T\le(\log y)^2$, the existing error compression in the proof of
Corollary 1.2 gives

$$
|M(y)-Z_T^{\rm res}(y)|\le\frac{\pi y}{2(T-1)}+2.
\tag{CH1c}
$$

That calculation uses $L>2$, the trivial-pole bound and
$\tanh\delta\le\delta$; it uses no simplicity of the enclosed
nontrivial poles. Explicitly, $\delta\le1/8$ gives $K_T<3\pi^2$,
and $y>e^2T$, $T\ge4\pi$ give
$K_T/y^2<\pi y/(16T^2)$. The bracket term is at most
$7\pi y/(16T^2)$; these corrections sum to less than
$\pi y/(2T^2)$. Finally $1/T+1/T^2<1/(T-1)$.
This is an application of the general source theorem and its error
calculation, not a new explicit-formula theorem.

If a zero $\rho$ has order $m$, write
$\zeta(s)=(s-\rho)^m h_\rho(s)$ locally, $h_\rho(\rho)\ne0$.
Its residue in (CH1a) is

$$
\frac{y^\rho}{(m-1)!}
\left.\frac{d^{m-1}}{ds^{m-1}}
\left[\frac{\coth(\delta s)-\tanh\delta}{h_\rho(s)}
e^{(s-\rho)\log y}\right]\right|_{s=\rho}.
$$

For $m=1$ this is the simple residue in $Z_T$; for larger $m$ it retains
the corresponding polynomial in $\log y$. Multiplying a simple-residue
term by $m$ would not supply this contribution. A numerical certificate
for (CH1a) must account for the actual pole orders and their complete
Laurent data, or an equivalent certified contour evaluation.

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

Fix a height $T\ge4\pi$ with finite horizontal bound and let
$C_T=\max_{r\le1}1/|\zeta(r\pm iT)|<\infty$. Set
$Y_T=\max(e^2T,e^{\sqrt{C_T}})$ and define

$$
A_T(v)=
\begin{cases}
Z_T^{\rm res}(v),&v>Y_T,\\
M(v),&1\le v\le Y_T,
\end{cases}
\qquad
\widetilde O_T(t)=\sum_{2^a\le t}A_T(t/2^a).
$$

Every replaced argument satisfies every condition of (CH1c); the others
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

Suppose that for every sufficiently large $x$ a height $T(x)$
is available with $T(x)\asymp x^{3/4}$ and
$C_{T(x)}\le(\log N)^2$. The horizontal bounds must hold as in
(CH1c); for certified evaluation the complete finite residues must also
be available. Then
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
those unbounded hypotheses. The use of full residues removes the
additional global simplicity premise. The signed residue contributions
and their actual pole orders are retained;
their lower bound against the same actual Robin core remains unproved.
This is neither an unconditional critical error bound nor a proof of RH.

## Published good heights pay the raw critical annulus

The published [Inoue good-height input](inoue2019mobiuszeta.md),
Lemma 1 of arXiv:1705.00853v2, supplies, unconditionally, a height

$$
T=T(x)\in[x^{3/4},x^{3/4}+x^{1/4}],\qquad
C_T\ll_\varepsilon T^\varepsilon
\tag{CH8}
$$

for every sufficiently large real $x$ and each fixed
$\varepsilon>0$. The source attributes this theorem to
Ramachandra–Sankaranarayanan. Its extension to all $r\le1$ uses the
functional equation, as recorded in the linked note. It does not
give $C_T\le(\log N)^2$. The general error formula (CH1b) already
accepts the weaker bound in (CH8), so that stronger certificate is
unnecessary for the following asymptotic application.

Put $B_T=e^2T$ and use the strict hybrid

$$
A_T^{\rm raw}(v)=
\begin{cases}
Z_T^{\rm res}(v),&v>B_T,\\
M(v),&1\le v\le B_T,
\end{cases}
\qquad
\widetilde O_T^{\rm raw}(t)
=\sum_{2^a\le t}A_T^{\rm raw}(t/2^a).
\tag{CH9}
$$

Every small dyadic argument is kept as its actual prefix. For $T\ge4\pi$
and $v>B_T$, (CH1b) has $L>2$, $\log v>\log T$,
$K_T/v^2<1$ and $\tanh\delta\le\pi/(2T)$. Consequently it gives

$$
|M(v)-Z_T^{\rm res}(v)|\le a_Tv+3,\qquad
a_T=\frac\pi{2T}+\frac{3\pi}{16T^2}
       +\frac{\pi C_T}{4T^2(\log T)^2}.
\tag{CH10}
$$

The $3\pi/(16T^2)$ term retains both $L^{-1}$ and $L^{-2}$.
Define $J_T(t)=\#\{a\in\mathbb Z_{\ge0}:t/2^a>B_T\}$.
The existing dyadic inverse and its geometric sum now give

$$
|O(t)-\widetilde O_T^{\rm raw}(t)|
\le E_T^{\rm raw}(t):=2a_Tt+3J_T(t),\qquad
J_T(t)\le1+\lfloor\log_2t\rfloor\quad(t\ge1).
\tag{CH11}
$$

For the same integers $Q\ge N\ge x\ge e$, use the error accounting
in (CH5) with $E_T^{\rm raw}$ in place of $E_T$. Both endpoints and
the integral remain. The same kernel bounds and finite Abel identity
therefore bound this replacement error by

$$
\ll\frac1{\log x}\left[
a_T(1+\log(Q/x))^3
 +\frac{(1+\log Q)(1+\log(Q/x))^2}{N}
\right].
\tag{CH12}
$$

The implicit constant is absolute. No derivative of the hybrid is
used; its switching points introduce no additional endpoint terms.
Taking, for example, $\varepsilon=1/2$ in (CH8) gives
$a_T=O(T^{-1})$. At the already selected
$Q=N_{18}(x)$ and $N=\lceil8x\rceil$, the two terms in (CH12),
multiplied by $\sqrt x\log x$, are respectively

$$
O\!\left(x^{-1/4}(1+\log(Q/x))^3\right),\qquad
O\!\left(x^{-1/2}(1+\log Q)(1+\log(Q/x))^2\right).
$$

They tend to zero since $\log Q$ has the fixed logarithmic order
already given above. The existing paid tail beyond $Q$ then yields

$$
\begin{aligned}
I_\psi(x)={}&
\sum_{\substack{m\le N\\m\text{ odd}}}\mu(m)\mathscr D_x(m)
+\widetilde O_T^{\rm raw}(Q)\mathscr D_x(Q)
-\widetilde O_T^{\rm raw}(N)\mathscr D_x(N)\\
&-\int_N^Q\widetilde O_T^{\rm raw}(t)\mathscr D'_x(t)\,dt
+o\!\left(\frac1{\sqrt x\log x}\right).
\end{aligned}
\tag{CH13}
$$

This is an unconditional asymptotic paper application of the cited
good-height and full-residue theorems and the existing complete-tail
bound. It imposes neither RH nor simple zeros nor an extra growing-height
existence assumption. It changes the raw error allowance, rather than
asserting the identical simplified numerical enclosure (CH1c).
The unspecified source constants and thresholds supply no effective
numerical starting point or certified growing spectral dataset here.
Complete residues, or certified enclosing-contour integrals, must still
be evaluated if this representation is to give a numerical certificate.
The analytic error does not pay that numerical error. No running-time
improvement or new Robin-safe integer range is claimed.

The [existing direct residual formula and core application](polak2026finiterobinca.md)
already retain the same $I_\psi$ and all zero multiplicities. The new
parameter application closes only the extra analytic good-height premise
of this Möbius representation. It gives no lower bound for the signed
expression in (CH13), nor for $I_\psi(x)+D^*(x)$ at the same selected
Robin source. Returning to that actual joint signed estimate requires
additional information; changing between the two representations alone
does not provide it. This application has no Lean verification.

Section 9.2.2 proposes direct continuous-weight analogues with improved
$T^{-2}$ terms; it does not provide a theorem for $\mathscr D_x$.
Such an adaptation could reduce the heights or exact-prefix cost, but needs
its own proof. The whole-range absolute estimate, the conditional signed
formula, and the pending weighted adaptation have distinct roles.
