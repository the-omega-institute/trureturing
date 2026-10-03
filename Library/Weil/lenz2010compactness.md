---
bibkey: lenz2010compactness
authors: Daniel Lenz, Peter Stollmann, and Daniel Wingert
year: 2010
title: Compactness of Schrödinger semigroups
doi: 10.1002/mana.200910054
url: https://arxiv.org/abs/0903.0280v2
claim: The relative-compactness and potential criteria, with the actual theta cutoff and prime-tail checks, confine the even mixed operator's essential spectrum to a bottom of one-half. Constants are the zero-energy space, giving an unspecified positive full-measure Poincare constant. Discrete subthreshold eigenvalues and the RH-strength one-half bound remain unresolved.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# The mixed theta essential threshold and the unresolved gap

## Existing spectral suppliers

The journal reference is *Mathematische Nachrichten* 283 (2010), 94–103.
The inspected primary text is [arXiv:0903.0280v2](https://arxiv.org/pdf/0903.0280v2),
23 March 2010, SHA-256
`046b461e78774fe31f385cf9fe59f6cb69887a5ed27fdf2390451a030d98da5d`.
It identifies itself as a pre-peer-reviewed version. The publisher PDF
was not retrieved; equality with the journal edition is not asserted.

Theorem 1.3, printed p.3, identifies compactness of a bounded map on a
semibounded operator's form domain with relative resolvent compactness.
Theorem 2.1, printed p.4, concerns $H=H_0+V_+-V_-$ on an arbitrary measure
space, where $H_0\ge\gamma$, $V_+\ge0$ is measurable and $V_-$ is form small:

$$
\langle V_-u,u\rangle
\le q\langle(H_0+V_+)u,u\rangle+C_q\|u\|^2,
\qquad q<1.
$$

If $\mathbf1_{\{V_+<s\}}$ is $(H_0+V_+)$-relatively compact, its conclusion is
$\sigma_{\rm ess}(H)\subseteq[(1-q)(\gamma+s)-C_q,\infty)$.
The application below has bounded $V_+$ and $V_-=0$, so its form domain
is dense and $\gamma=q=C_q=0$ is admissible.

For the final perturbation use Gerald Teschl,
[*Mathematical Methods in Quantum Mechanics*](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
authorized first-edition online text dated 12 February 2009, Theorem 6.19,
printed p.146, and the relative-compact perturbation discussion on
pp.147–148. The inspected PDF SHA-256 is
`8dc8de0b58aa0a3fedfe594a345f9b5875322e5526ea581cb640a98d55b82818`.
That theorem preserves essential spectrum under compact resolvent
difference. These generic results are reused; the model checks follow.

## Exact prime diagonal and bounded off-diagonal operator

Retain the [original minimal realization](fukushima2011dirichlet.md),
$d\nu=\rho\,dx=2\Phi\cosh(x/2)\,dx$, and all weights
$w_n=\Lambda(n)/\sqrt n$. Define the outgoing prime rate

$$
a_p(x)=\frac{\sum_{n\ge2}w_n
\bigl(\Phi(x+\log n)+\Phi(x-\log n)\bigr)}{2\cosh(x/2)}.
$$

It is continuous, even and nonnegative. Uniform convergence of its series
on compact sets follows from the theta tails. The already reviewed
[ordinary PNT and Chebyshev suppliers](primenumbertheoremand2026medium.md)
give $a_p(x)\to1/2$ as $|x|\to\infty$, without RH. The parameter map is
explicit: for $x>0$, $X=e^x$ and $f(y)=y^{-1/2}\Phi(\log y)$, its incoming
contribution is

$$
a_{p,-}(x)=\frac1{1+X^{-1}}\frac1X\sum_{n\ge2}\Lambda(n)f(n/X).
$$

With $\Psi(t)=\sum_{2\le n\le t}\Lambda(n)$, Stieltjes integration by
parts writes the last scaled sum as
$-\int_0^\infty\Psi(Xy)f'(y)\,dy/X$.
The source bounds $\Psi(t)\le Bt$ and $\Psi(t)/t\to1$ permit dominated
convergence since
$\int y|f'(y)|\,dy=\int e^{r/2}|\Phi'(r)-\Phi(r)/2|\,dr<\infty$.
The limit is $\int f=\int e^{r/2}\Phi(r)\,dr=1/2$; the outgoing
$x+\log n$ contribution tends to zero by the theta tail. Continuity and
this limit give $a_p\in L^\infty$. This reuses the completed rate argument,
rather than a new PNT or a short-interval prime estimate.

Under the unitary $Uh=v=\sqrt\rho\,h$ from $L^2(\nu)$ to $L^2(dx)$, put
$t_n=\log n$, $(\tau_nv)(x)=v(x+t_n)$ and

$$
b_n(x)=\frac{w_n\sqrt{\Phi(x)\Phi(x+t_n)}}
{2\sqrt{\cosh(x/2)\cosh((x+t_n)/2)}},\qquad S_n=M_{b_n}\tau_n.
$$

The original tail gives $\Phi(x)\le Ce^{-c e^{2|x|}}$ with $c>0$.
Since $e^{2|x|}+e^{2|x+t_n|}\ge2n$, it follows that
$\|b_n\|_\infty\le Cw_ne^{-cn}$ and
$\sum_n\|b_n\|_\infty<\infty$. Therefore
$B=\sum_{n\ge2}(S_n+S_n^*)$ converges in operator norm and is bounded
self-adjoint. Write $B_p=U^{-1}BU$. The complete prime energy is exactly

$$
D_p(h)=\langle M_{a_p}h,h\rangle_\nu-\langle B_ph,h\rangle_\nu,
\qquad 0\le D_p(h)\le2\|a_p\|_\infty\|h\|_\nu^2. \tag{BD}
$$

The inequality follows from the actual symmetric edge measure. It extends
the identity to all $L^2(\nu)$, including every prime power and both
directions. Thus the Gamma and mixed form norms on their common compact
smooth core are equivalent. Their **minimal** form domains agree; no
equality with an arbitrary maximal domain is used.

Let $A_\Gamma$ be the full minimal Gamma operator and
$C=A_\Gamma+M_{a_p}$. The original full mixed minimal operator is
$A=C-B_p$, with $D(A)=D(C)=D(A_\Gamma)$ by bounded self-adjoint
perturbation. Both $A$ and $C$ are nonnegative.

## Two-sided spatial tails and relative compactness

For compact smooth $0\le\chi_R\le1$, one on $[-R,R]$, the exact adjoint
coefficient gives

$$
\begin{aligned}
\|(1-\chi_R)S_n\|&\le\sup_{|x|>R}b_n(x),\\
\|(1-\chi_R)S_n^*\|&\le\sup_{|x|>R}b_n(x-t_n).
\end{aligned}
$$

For each fixed $n$ both suprema tend to zero, and the common summable
global majorant permits summing the limits. Hence
$\|(1-\chi_R)B\|\to0$. Self-adjointness gives $\|B(1-\chi_R)\|\to0$,
and the same assertions hold for $B_p$ because $U$ commutes with scalar
cutoffs. The shifted adjoint coefficient is necessary for this operator
norm statement. Individual weighted translations are not asserted compact.

The [theta cutoff comparison and Jarohs–Weth theorem](jarohsweth2020local.md)
give compact restriction on the Gamma form domain. The bounded potential
preserves that domain and its norm equivalence, so
$\chi_R(C+1)^{-1}$ is compact. In

$$
B_p(C+1)^{-1}
=B_p\chi_R(C+1)^{-1}+B_p(1-\chi_R)(C+1)^{-1},
$$

the first term is compact and the second tends to zero in norm. Thus
$B_p(C+1)^{-1}$ is compact, while all arithmetic edges remain present.

For every $0<s<1/2$, $\{a_p<s\}$ lies in a compact interval. Its indicator
is compact on the form domain of $C$. Apply the source's Theorems 1.3
and 2.1 with $H_0=A_\Gamma$, $V_+=a_p$, $V_-=0$ and
$\gamma=q=C_q=0$. This yields
$\sigma_{\rm ess}(C)\subseteq[s,\infty)$ for every such $s$, hence
$\sigma_{\rm ess}(C)\subseteq[1/2,\infty)$.

Finally, the resolvent difference

$$
(A+1)^{-1}-(C+1)^{-1}
=(A+1)^{-1}B_p(C+1)^{-1}
$$

is compact. Teschl's Weyl theorem gives
$\sigma_{\rm ess}(A)=\sigma_{\rm ess}(C)\subseteq[1/2,\infty)$.

Reflection preserves the measure, the two conductance measures and the
core, so it commutes with the minimal resolvents. The even space reduces
$A$; its spectral projections strictly below $1/2-\varepsilon$ are
restrictions of full-space finite-rank projections. The already reviewed
[infinite critical eigenfamily](lagarias2004li.md) puts $1/2$ in the even
essential spectrum. Therefore

$$
\inf\sigma_{\rm ess}(A_{\rm even})=\tfrac12. \tag{ET}
$$

This identifies its bottom, not all essential spectrum above it or the
complete one-half eigenspace.

## A weaker actual-measure Poincare bound

If $D(h)=0$, positivity of the Gamma conductance off the diagonal forces
$h(y)=h(x)$ for almost every pair. Fubini and equivalence of $dx$ and
$\nu$ make $h$ constant almost everywhere. Conversely the constant $1$
belongs to the minimal domain and has zero energy. Hence
$\ker A=\mathbb C1$.

By (ET), zero is a simple discrete eigenvalue of the even operator and
is isolated. The spectral theorem on its centered reducing space gives
an unspecified constant

$$
0<c_*:=\inf\sigma(A_{\rm even}|_{1^\perp})\le\tfrac12,
\qquad D(h)\ge c_*\operatorname{Var}_\nu(h)
\quad(h\in\mathcal F_{\rm even}). \tag{PG}
$$

The upper bound uses the known critical eigenvectors. This is the original
pole probability measure and complete mixed energy. No explicit numerical
value or effective approximation rate for $c_*$ is obtained, and
$c_*=1/2$ remains unproved.

For the even operator, the remaining possible eigenvalues
$0<\lambda<1/2$ are isolated and have finite multiplicities.
Their eigenvectors are orthogonal to constants and
the known critical family, hence lie in the previously defined remainder.
There are finitely many below each fixed $1/2-\varepsilon$, but there
may be infinitely many accumulating at $1/2$. For example the abstract
positive operator with diagonal $1/2-1/(k+3)$ on one $\ell^2$ summand and
$\tfrac12 I$ on another has exactly this behavior. Thus (ET) and (PG) do
not exclude the remaining subthreshold spectrum or establish RH and full
Robin. The target stays the exact one-half bound.

## Persson and support boundaries

[Lenz–Stollmann, arXiv:1705.10398v2](https://arxiv.org/pdf/1705.10398v2),
Definition 2.1, printed p.5, and Theorem 3.2, printed p.8, use all measurable
sets of finite speed measure in their Persson hypothesis. On this
probability space it would require the
whole semigroup to be compact, incompatible with the known infinite
one-half eigenspace. Compact-set local embedding does not verify it.
The compact-set version in BenAmor–Güneysu–Stollmann, *Essential Spectrum
and Feller Type Properties*, Theorem 5.5,
[DOI 10.1007/s00020-023-02732-9](https://doi.org/10.1007/s00020-023-02732-9),
requires weak Feller, which is not verified here. Neither direct Persson
identity is invoked in the preceding supplier chain.

For an exterior-supported function the actual energy retains jumps into
the removed interval as killing contributions. It is not the censored
kernel restricted to two exterior endpoints. Likewise a compact FIB test
and its noncompact projection onto the critical remainder are different
sources. A finite support estimate alone does not exclude eigenvalues
arbitrarily close to the threshold.

The model-specific estimates and spectral applications above are paper
deductions from the inspected sources, without new Lean certification or
an originality claim. They advance an actual weaker lower bound and
essential-threshold identification; the global RH-strength lower bound
remains unresolved.


## Fixed-gap eigenfunction tails and FIB approximation

Qualitative uniform tails on each spectral subspace strictly below one-half
already follow from the finite-rank projections above. The following
model estimate supplies explicit inputs for the actual noncompact
vectors. It reuses the [nonlocal IMS calculation](frankliebseiringer2006hardy.md)
and the complete prime decomposition, without a new generic theorem or
originality claim.

For $R\ge4$, choose even smooth $0\le\eta_R\le1$, zero on $[-R,R]$, one
outside $[-R-2,R+2]$, with $|\eta_R'|\le1$. Put

$$
\begin{aligned}
e_R(x)&=\frac1{2\cosh(x/2)}\int\Phi(y)\psi(|x-y|)
                 |\eta_R(y)-\eta_R(x)|^2\,dy,\\
E_R&=\|e_R\|_\infty,\qquad b_R=\|M_{\eta_R}B_p\|,\\
\delta_R&=\sup_{|x|\ge R}(\tfrac12-a_p(x))_+.
\end{aligned}
$$

The first expression is exactly the Gamma conductance row divided by the
original speed density $\rho$, with the squared cutoff difference.
Let $k(t)=\psi(|t|)\min(1,t^2)$ for $t\ne0$, $k(0)=0$,
$K=\|k\|_\infty<\infty$, $P=\int\Phi$, $T(r)=\int_{|y|>r}\Phi(y)\,dy$
and $d=(1-e^{-2})^{-1}$. Then

$$
E_R\le\tfrac12\bigl(dP e^{-R/8}+K T(R/4)\bigr)
\longrightarrow0. \tag{TR}
$$

For $|x|\ge R/2$, the cutoff difference is bounded by
$\min(1,|x-y|)$. Split the integral at $|y|=R/4$: on the inner part
$|x-y|\ge R/4\ge1$ gives $k(x-y)\le d e^{-R/8}$; on the outer part
$k\le K$. Divide by $2\cosh(x/2)\ge2$. For $|x|<R/2$, $\eta_R(x)=0$
and a nonzero difference requires $|y|>R$. This gives the smaller bound
$d e^{-R/4}T(R)/2$. Thus (TR) concerns the actual Gamma kernel, rather
than a fractional-kernel replacement.

On the compact smooth core, the product estimate gives
$D_\Gamma(\eta_R h)\le2D_\Gamma(h)+E_R\|h\|_\nu^2$.
Core approximants extend this bounded multiplier to the Gamma minimal
domain. The same argument applies to $\eta_R^2$, whose cutoff rate is
at most $4e_R$. The common minimal domain and (BD) give legality in the
original mixed form domain. No maximal-domain identification is used.
The exact ordered-jump identity is

$$
\begin{aligned}
D_\Gamma(\eta_R h)-\Re D_\Gamma(h,\eta_R^2h)
&=\tfrac12\iint |\eta_R(y)-\eta_R(x)|^2
       \Re\bigl(h(x)\overline{h(y)}\bigr)\,J_\Gamma(dx,dy),\\
\left|D_\Gamma(\eta_R h)-\Re D_\Gamma(h,\eta_R^2h)\right|
&\le\tfrac12 E_R\|h\|_\nu^2.
\end{aligned} \tag{GI}
$$

Here $J_\Gamma(dx,dy)=\Phi(x)\Phi(y)\psi(|x-y|)\,dx\,dy$.
The factor one-half uses both ordered endpoints. Symmetry and
$|\Re(h(x)\overline{h(y)})|\le(|h(x)|^2+|h(y)|^2)/2$ give the bound;
form approximation extends the identity.

Let $Ah=\lambda h$, $\|h\|_\nu=1$, and $t_R=\|\eta_Rh\|_\nu$.
Testing the original eigen-equation with $\eta_R^2h$, using (GI), gives

$$
(\tfrac12-\delta_R-\lambda)t_R^2
\le b_Rt_R+\tfrac12E_R. \tag{EL}
$$

Indeed the left diagonal is at least $(1/2-\delta_R)t_R^2$,
$D_\Gamma(\eta_Rh)\ge0$, and the full prime off-diagonal contribution
has modulus at most $\|\eta_R B_ph\|_\nu t_R\le b_Rt_R$.
All crossing prime-power edges and shifted adjoints remain present.
For $\lambda\le1/2-\varepsilon$ and $\delta_R\le\varepsilon/2$,
the quadratic inequality yields

$$
\|\mathbf1_{\{|x|\ge R+2\}}h\|_\nu\le t_R
\le\frac{b_R+\sqrt{b_R^2+\varepsilon E_R}}{\varepsilon}
\longrightarrow0\quad\text{for fixed }\varepsilon>0. \tag{LT}
$$

The approved potential limit gives $\delta_R\to0$ and the complete prime
operator-tail argument gives $b_R\to0$. An upper input for $b_R$ is

$$
\sum_{n\ge2}\left(\sup_{|x|>R}b_n(x)
                 +\sup_{|x|>R}b_n(x-\log n)\right).
$$

A finite prefix and the existing summable global theta majorant bound
this expression. No numerical values or certified effective convergence
rate are supplied here.

The same equation, $a_p\ge0$ and (BD) also give

$$
D(\eta_Rh)\le(\tfrac12+2\|a_p\|_\infty)t_R^2
                       +b_Rt_R+\tfrac12E_R. \tag{FE}
$$

Thus the compactly supported form-domain vector $h_R=(1-\eta_R)h$
approximates the actual eigenvector in the original form norm:

$$
\|h-h_R\|_\nu^2+D(h-h_R)
\le(\tfrac32+2\|a_p\|_\infty)t_R^2+b_Rt_R+\tfrac12E_R. \tag{FN}
$$

No smoothness of $h_R$ or effective interior discretization is asserted.
If $h\in\mathcal R$, cutting it off need not preserve that remainder.
Its established reducing projection $P_{\mathcal R}$ is a contraction
in both the Hilbert and nonnegative form norms, so $P_{\mathcal R}h_R$
approximates $h$ with at most the same error. The projected vector generally
has noncompact support; a support-limited positivity certificate does
not thereby become a remainder certificate.

These fixed-$\varepsilon$ paper estimates provide a finite-support source
for approximating actual low eigenvectors. Interior discretization and
complete spectral certification remain separate obligations. The
$1/\varepsilon$ loss is uncontrolled as $\varepsilon\to0$; threshold
accumulation and subthreshold eigenvectors are not excluded. The
RH-strength exact-half bound remains unproved.
