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
this expression. The effective original-series estimates below give a
specified convergence rate without discarding the shifted adjoints.

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

## Effective original-measure cutoff inputs

Reuse the [original theta series majorants](../Analytic/romik2021orthogonal.md)
and the [explicit prime-diagonal transfer](trudgian2014pnt.md).
The following bounds evaluate the inputs to (LT) and (FN) for the same
individual eigenvector, measure, minimal form and cutoff. They do not
construct a finite spectral certificate.

### Full prime off-diagonal tail

Let $C_\Phi=144/5$. From the theta majorant (ST), the exact $b_n$
coefficient and $\cosh\ge1$,

$$
b_n(x)\le\frac{C_\Phi}{2}w_n
 \exp\left[-\frac34
       \bigl(e^{2|x|}+e^{2|x+\log n|}\bigr)\right].
$$

The quantity in parentheses is at least $2n$, by the arithmetic-geometric
mean and $|x|+|x+\log n|\ge\log n$. For $|x|>R$ it is also at least
$e^{2R}$. Its mean lower bound is thus $(e^{2R}+2n)/2$.
Exactly the same two bounds hold for the shifted adjoint $b_n(x-\log n)$:
its pair is $x-\log n,x$, so the exterior endpoint is still retained.
Using $w_n\le n$, $e^{-3/4}<1/2$ and
$\sum_{n\ge2}n2^{-n}=3/2$ in the full two-direction norm sum gives

$$
\boxed{b_R\le\frac{216}{5}
          \exp\left(-\frac38e^{2R}\right)}\quad(R\ge0). \tag{BT}
$$

Both prime powers and crossing edges occur in this bound. Because
$(3/8)e^{2R}\ge R$ for $R\ge1$, a simpler consequence is

$$
b_R\le44e^{-R}\quad(R\ge1). \tag{BR}
$$

The nonlinear inequality follows at $R=1$ from $e^2>7$ and thereafter
from its positive derivative. No individual translation is claimed compact.

### Gamma cutoff error

For $t>0$ the elementary bound
$1-e^{-2t}\ge2t/(1+2t)$ gives
$\psi(t)t^2\le3/2$ for $0<t\le1$.
For $t\ge1$ one has $\psi(t)\le d e^{-t/2}$ with
$d=(1-e^{-2})^{-1}<7/6$. Thus
$k(t)=\psi(t)\min(1,t^2)\le3/2$ everywhere.

For $|x|\ge R$, divide the cutoff row by
$2\cosh(x/2)\ge e^{|x|/2}$ and split at $|x-y|=1$.
On long jumps, use
$e^{-|x-y|/2}\le e^{-|x|/2}e^{|y|/2}$ and the original normalization
$\int\Phi(y)e^{|y|/2}\,dy\le1$.
On short jumps, the Lipschitz cutoff bound applies and $|y|>R-1$.
Hence

$$
e_R(x)\le d e^{-R}
       +\frac32e^{-R/2}T(R-1)\quad(|x|\ge R).
$$

For $|x|\le R$, $\eta_R(x)=0$; a nonzero row term requires $|y|>R$.
The same $k$ bound and $2\cosh(x/2)\ge2$ give
$e_R(x)\le(3/4)T(R)$. Combining the two ranges,

$$
E_R\le d e^{-R}+\frac94T(R-1)\quad(R\ge1).
$$

The theta integrated tail (IT) gives $T(R-1)\le e^{-R}$ for $R\ge4$.
Indeed, its ratio to $e^{-R}$ is at most
$(96/5)e^{2-R}\exp[-(3/2)e^{2(R-1)}]$, which decreases; at $R=4$
it is less than $24/35$ using $e^2>7$ and $e^{3/2}>4$.
Therefore the actual ordered Gamma cutoff error satisfies

$$
\boxed{E_R\le4e^{-R}\quad(R\ge4).} \tag{ER}
$$

This sharpens the coarse rate (TR) for these cutoffs. It keeps the singular
Gamma kernel and all endpoint interactions; it is not a fractional-kernel
substitution or a censored exterior energy.

### A specified fixed-gap form-approximation radius

Fix $0<\varepsilon\le1/2$ and a tolerance $0<\tau\le1$.
Use $R_{\rm PNT}(\varepsilon)$ from (PR) in the linked prime-diagonal
note, and take

$$
R\ge\max\left\{
R_{\rm PNT}(\varepsilon),
\log\frac{11264}{\varepsilon\tau},
2\log\frac{256}{\sqrt\varepsilon\,\tau},
\log\frac8{\tau^2}
\right\}. \tag{FR}
$$

For any actual normalized eigenvector $Ah=\lambda h$ with
$\lambda\le1/2-\varepsilon$, (LT), (BR) and (ER) give

$$
t_R\le\frac{2b_R}{\varepsilon}
               +\sqrt{\frac{E_R}{\varepsilon}}
\le\frac{88e^{-R}}{\varepsilon}
               +\frac{2e^{-R/2}}{\sqrt\varepsilon}
\le\frac\tau{64}.
$$

Let $h_R=(1-\eta_R)h$. With $\|a_p\|_\infty<432$ from (AC),
the three terms in (FN) are at most
$(1731/8192)\tau^2$, $(11/128)\tau^3$ and $\tau^2/4$,
respectively. The middle estimate uses (BR) and the last radius in (FR).
Thus

$$
\boxed{
\|h-h_R\|_\nu^2+D(h-h_R)
\le\frac{1121}{2048}\tau^2<\tau^2.
} \tag{FA}
$$

The reducing projection $P_{\mathcal R}$ retains at most this error for
$h\in\mathcal R$; its image generally remains noncompact. These are
coarse analytic constants, with no directed numerical computation,
new Lean certification or originality claim.

The conclusion concerns each individual actual eigenvector under the
stated fixed gap. The whole-projector estimate below uses a separate
bounded commutator and separated-spectra argument for mixtures of
different eigenvalues. Interior discretization, a complete lower spectral
certificate and control uniform as $\varepsilon\downarrow0$ remain missing. The radius in (FR) diverges
with shrinking gap; threshold accumulation, RH and full Robin remain
unresolved.

## Full fixed-gap low-spectral-subspace cutoff

The effective scalar and cutoff bounds also yield a uniform estimate for
all vectors in the low spectral subspace. This is a model transfer of the
standard separated-spectra integral argument; it is not a new general
spectral criterion, interior discretization or complete spectral exclusion.

### Bounded Gamma cutoff commutator

For the same even cutoff define

$$
q_R(x)=\frac{1}{2\cosh(x/2)}\int\Phi(y)\psi(|x-y|)
                  |\eta_R(x)-\eta_R(y)|\,dy,
\qquad Q_R=\|q_R\|_\infty.
$$

This row uses the first power of the cutoff difference. The short-jump
bound is now $\psi(t)t\le3/2$ for $0<t\le1$, still following from
$1-e^{-2t}\ge2t/(1+2t)$. On long jumps use the same $d e^{-t/2}$ bound.
The two spatial ranges used for (ER) therefore give, with no squared-row
substitution,

$$
Q_R\le d e^{-R}+\frac94 T(R-1)\le4e^{-R}\quad(R\ge4). \tag{QC}
$$

On the compact smooth core, the Gamma commutator is

$$
K_Rh(x):=[A_\Gamma,M_{\eta_R}]h(x)
=\frac{1}{2\cosh(x/2)}\int\Phi(y)\psi(|x-y|)
            (\eta_R(x)-\eta_R(y))h(y)\,dy.
$$

The absolute kernel is symmetric relative to $\nu$ and has row mass
$q_R$. The weighted Schur estimate gives $\|K_R\|\le Q_R$ on
$L^2(\nu)$, including the singular Gamma neighborhood.
The existing cutoff multiplier bound and core approximation extend

$$
D_\Gamma(\eta_Rh,k)-D_\Gamma(h,\eta_Rk)=\langle K_Rh,k\rangle_\nu
$$

to the Gamma minimal form domain, with the inner product linear in its
first argument. For $h\in D(A_\Gamma)$ the operator representation of
this identity shows
$\eta_Rh\in D(A_\Gamma)$ and
$A_\Gamma\eta_Rh=\eta_RA_\Gamma h+K_Rh$.
The bounded potential commutes with the cutoff, so the same domain and
commutator statement holds for $C=A_\Gamma+M_{a_p}$.

### The killed exterior operator and separated spectra

Work in the even Hilbert space. Fix $0<\varepsilon\le1/2$, put
$a=1/2-\varepsilon$, and let $P_\varepsilon=\mathbf1_{[0,a]}(A_{\rm even})$.
Write $\mathcal L=\operatorname{ran}P_\varepsilon$ and
$A_\mathcal L=A|_\mathcal L$; it is bounded with $0\le A_\mathcal L\le a$.

Let $\mathcal H_R$ consist of even functions zero on $[-R,R]$.
Restrict the global closed form of $C$ to its form-domain intersection
with $\mathcal H_R$, and let $C_R$ be the associated operator on
$\mathcal H_R$. The restricted form is closed, and smooth even tests
supported outside $[-R,R]$ give density. It keeps the Gamma jumps into
the removed interval as killing terms. Hence

$$
C_R\ge b:=1/2-\delta_R.
$$

For $R\ge R_{\rm PNT}(\varepsilon)$, $b-a\ge\varepsilon/2>0$.
Let $T_R=M_{\eta_R}|_\mathcal L:\mathcal L\to\mathcal H_R$.
The commutator domain statement implies $T_R\mathcal L\subset D(C_R)$.
Indeed, restriction of the global operator identity to exterior form
tests gives

$$
C_RT_R-T_RA_\mathcal L=F_R,
\qquad F_R=\mathbf1_{\{|x|>R\}}(K_R+M_{\eta_R}B_p)|_\mathcal L,
\qquad \|F_R\|\le Q_R+b_R. \tag{SY}
$$

Every prime power and shifted adjoint still occurs in $B_p$.
For each vector in $\mathcal L$, differentiation of
$e^{-tC_R}T_Re^{tA_\mathcal L}$ and integration on $t\ge0$ give the
strong-operator identity

$$
T_R=\int_0^\infty e^{-tC_R}F_Re^{tA_\mathcal L}\,dt.
$$

Its endpoint at infinity vanishes in operator norm, since the separated
spectra give exponential decay by $e^{-(b-a)t}$. Thus

$$
\boxed{
\|M_{\eta_R}P_\varepsilon\|
\le\frac{Q_R+b_R}{\varepsilon-\delta_R}
\le\frac{96}{\varepsilon}e^{-R}=:s_R.
} \tag{LP}
$$

This proves an operator-norm bound for the whole low spectral subspace;
it does not assign a scalar eigenvalue to a mixture of eigenvectors.

### Uniform form approximation on that subspace

For a unit vector $h\in\mathcal L$, put $h_R=(1-\eta_R)h$.
Use the global identity
$C\eta_Rh=\eta_RAh+(K_R+\eta_RB_p)h$.
Because $Ah\in\mathcal L$ and $\|Ah\|\le a$, (LP) gives
$\|\eta_RAh\|\le a s_R$. Therefore

$$
D_\Gamma(\eta_Rh)\le\langle C\eta_Rh,\eta_Rh\rangle_\nu
\le a s_R^2+(Q_R+b_R)s_R.
$$

The complete prime energy bound (BD) gives

$$
\|h-h_R\|_\nu^2+D(h-h_R)
\le(3/2+2\|a_p\|_\infty)s_R^2+(Q_R+b_R)s_R
\le866s_R^2. \tag{UF}
$$

For the last step use $\|a_p\|_\infty<432$,
$Q_R+b_R\le48e^{-R}=\varepsilon s_R/2$ and $\varepsilon\le1/2$.
Consequently, for $0<\tau\le1$, the radius

$$
R\ge\max\left\{R_{\rm PNT}(\varepsilon),
                         \log\frac{2880}{\varepsilon\tau}\right\}
\tag{UR}
$$

ensures, simultaneously for every unit $h\in\mathcal L$,

$$
\|h-h_R\|_\nu^2+D(h-h_R)\le\frac{433}{450}\tau^2<\tau^2.
$$

For $h\in\mathcal L\cap\mathcal R$, the reducing projection
$P_\mathcal R$ retains at most the same form error, while its output
generally has noncompact support. The bound concerns the original
operator's whole fixed-gap spectral subspace. The
[quantitative interior construction](jarohsweth2020local.md) provides a
finite-rank existence map with uniform error in the original form norm.
Computed basis functions, a complete lower spectral certificate and
control uniform as
$\varepsilon\downarrow0$ remain unresolved. Subthreshold accumulation is
not excluded; RH and full Robin remain unresolved. These are paper-level model
deductions, without new Lean certification or an originality claim.
