---
bibkey: lagarias2004li
authors: Jeffrey C. Lagarias
year: 2004
title: Li Coefficients for Automorphic L-Functions
doi: null
url: https://arxiv.org/abs/math/0404394v4
claim: The multiplicity-weighted Li sum over actual nontrivial Riemann zeta zeros converges under zero-modulus cutoffs.
strata_touched:
  - D5/S3/Weil/ZeroData/LiZeroSumConvergence
license: bibliographic-reference-only
triage: anchor
---
<!-- GID: D5/L/Weil/lagarias2004li -->
# Li Zero-Sum Convergence

## Verified locator

https://arxiv.org/abs/math/0404394v4

Lagarias, arXiv:math/0404394v4, Introduction, equation (1.1), printed page 1,
defines the Li expression as the sum of `1-(1-1/rho)^n` over the actual
nontrivial Riemann zeta zeros counted with multiplicity. The prime on the
sum means the limit of the finite sums over `|rho| <= T`. The accompanying
paragraph states convergence for positive and negative integer indices;
the present formalization treats natural indices, including zero. The
first submission is dated 2004; the cited fourth version is dated
4 May 2005 and its title page says 11 April 2005.

The height convention is stated separately in Masatoshi Suzuki,
*Li coefficients as norms of functions in a model space*,
https://arxiv.org/abs/2301.05779v2, Introduction, equation (1.1) and its
following paragraph: take the limit over `|Im rho| <= T`, retaining
multiplicities. The retained versioned HTML has a 14 June 2023 watermark
and a displayed date of 24 August 2026; this bibliographic discrepancy
does not alter the quoted summation convention.

The Lean theorems use the repository's exhaustive, injective `ZeroData`
presentations of actual zeta zeros and their exact analytic multiplicities.
They prove absolute summability of the real parts and convergence of three
conjugation-invariant finite sums: spectral radius, height, and zero modulus.
The spectral parameter is `gamma=-i*(rho-1/2)`; the opposite sign convention
in the source has the same norm. Strict-strip geometry proves that the
height and radial filters of the spectral ball of radius `T+1` have exactly
their stated memberships for every real `T`.

The proof of the real estimate is local to this formalization. Writing
`u=1/rho`, it uses `|Re u| <= |u|^2` and a joint power induction to obtain
`|1-Re((1-u)^n)| <= (2^n-1)*|u|^2` on the tail. The reciprocal-square
zero weight is supplied by the existing zeta summability theorem. For
`|gamma| >= 2`, the majorant is `4*2^n*m/(1+|gamma|^2)`. Every term outside
that tail is retained in a finite exceptional set. This constant is only
a convergence estimate and has no role as Li's fixed first coefficient.

The identification with the derivative definition in Lagarias equation
(1.3), and the resulting positivity equivalence, are separate obligations.
No derivative identity, Riemann hypothesis, or probability representation
is a hypothesis of these convergence results. No assertion of absolute
summability of the unpaired complex terms is made.

The cited passages were read from retained versioned primary-source
excerpts. Li's 1997 publisher endpoint supplied metadata but not the full
article; its PDF request returned HTTP 406. No original Li theorem or
proof is attributed to that inaccessible text here. This note paraphrases
mathematical statements and copies no third-party proof code.

## Mixed nullity and the theta-weighted even Weil interface

Lagarias §3, equation (3.1), printed p.12, defines the absolutely convergent
pairing

$$
\langle F,G\rangle_W=\sum_\rho
F(\rho)\overline{G(1-\bar\rho)},
$$

with the actual nontrivial zeros and their multiplicities. He explicitly
identifies the completed xi-function as a nonzero null vector. For the
trivial representation his normalization is $2\xi$; this scalar does not
affect mixed nullity. Appendix §9, equations (9.3)–(9.7), printed pp.37–38,
gives the arithmetic explicit formula. Its unconditional analytic use
requires a strip extending beyond the closed critical strip.

The following is a paper application of that pairing and the existing
[theta transform](../Analytic/romik2021orthogonal.md), rather than a new
null-vector theorem or a compiled extension of the compact-test interface.
Let $\Phi$ be Romik's original positive smooth even kernel. In the convention
$\widehat f(z)=\int e^{-izx}f(x)\,dx$,

$$
\widehat\Phi(z)=\Xi(z)=\xi(1/2+iz),
\qquad
I:=\int\Phi(x)\cosh(x/2)\,dx=\xi(0)=\xi(1)=\tfrac12.
$$

Evenness converts the source's plus-sign Fourier convention without a
prefactor. Consequently

$$
d\nu(x)=2\Phi(x)\cosh(x/2)\,dx
$$

is a probability measure. For even complex $h\in C_c^\infty(\mathbb R)$ set
$f=\Phi h$ and define

$$
\begin{aligned}
E_\Gamma(h)&=\int_0^\infty
\frac{e^{-t/2}}{1-e^{-2t}}
\int\Phi(x)\Phi(x+t)|h(x+t)-h(x)|^2\,dx\,dt,\\
E_{\rm prime}(h)&=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\int\Phi(x)\Phi(x+\log n)
|h(x+\log n)-h(x)|^2\,dx.
\end{aligned} \tag{2}
$$

All prime powers are retained. Both energies are nonnegative.

### Mixed nullity needs a domain bridge

Write $B_Q$ for the sesquilinear full Weil pairing transported to physical
tests, linear in its first argument, and $Q(f)=B_Q(f,f)$. For compact even
$v$, the required premise is

$$
B_Q(\Phi,v)=0. \tag{3}
$$

The scalar identity $Q(\Phi)=0$ alone would not prove (3) in a form whose
positivity is the question. On the zero side, (3) follows termwise from
$\widehat\Phi(z_\rho)=\xi(\rho)=0$, where
$z_\rho=\Im\rho-i(\Re\rho-1/2)$.

To transfer that statement to the actual arithmetic form, take real even
smooth cutoffs $\chi_R$, equal to one on $[-R,R]$, supported in $[-2R,2R]$,
with uniformly scaled derivatives, and put $\Phi_R=\chi_R\Phi$. The existing
[theta cutoff bounds](frankliebseiringer2006hardy.md) give

$$
\varepsilon_R:=\int e^{|x|/2}
\bigl(|\Phi_R-\Phi|+|(\Phi_R-\Phi)''|\bigr)\,dx\longrightarrow0.
$$

Two integrations by parts bound the Fourier–Laplace error on
$|\Im z|\le1/2$ by $C\varepsilon_R/(1+|\Re z|^2)$. The compact $v$
has the same inverse-square decay there. The mixed zero-side errors are
therefore dominated by
$C_v\varepsilon_R m_\rho/(1+|\Im\rho|^2)^2$, a summable actual-zero
weight. This preserves multiplicities and allows the limit without RH.

On the arithmetic side, the poles converge by the weighted integral bound.
The Gamma small-shift differences are $O(t^2)$ against a kernel asymptotic
to $1/(2t)$; its large-shift integrals are controlled by the theta tails.
For $x$ in the support of $v$, $\Phi(x\pm\log n)$ decays faster than any
power of $n$, and $\Lambda(n)\le\log n$ supplies an absolutely convergent
mixed prime series. These estimates justify the same cutoff passage and
hence (3) for the extended arithmetic pairing. They do not assert a closed
operator realization on a completed Hilbert space.

### Exact jump and variance bookkeeping

Apply (3) with $v=\Phi|h|^2$. The elementary complex ground-state expansion
for a jump edge $x,y$ reads

$$
|u_xh_x-u_yh_y|^2
-(u_x-u_y)(u_x|h_x|^2-u_y|h_y|^2)
=u_xu_y|h_x-h_y|^2,
$$

where $u_x,u_y$ are real and positive. It cancels the diagonal local
potential and gives the two energies in (2). For even tests the pole
contribution is $2|\int\Phi h\cosh(x/2)\,dx|^2$. Subtracting the mixed
pole contribution $2I\int\Phi|h|^2\cosh(x/2)\,dx$ leaves
$-2I^2\operatorname{Var}_\nu(h)$. Thus

$$
Q(\Phi h)=E_\Gamma(h)+E_{\rm prime}(h)
-\tfrac12\operatorname{Var}_\nu(h). \tag{4}
$$

Multiplication by positive smooth even $\Phi$ is a bijection on the full
even complex compact smooth test class. Combining (4) with the existing
[even Weil criterion](../../D5/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion.lean)
therefore leaves exactly the RH-strength estimate

$$
E_\Gamma(h)+E_{\rm prime}(h)\ge\tfrac12\operatorname{Var}_\nu(h)
\quad\text{for every even complex }h\in C_c^\infty. \tag{5}
$$

Equation (5) remains unproved. The weight change is an exact source
application, not a smaller test domain or a new proof of RH. For non-even
tests the full two-pole bilinear term replaces the displayed variance;
(4) is not asserted on that larger domain.

If $\operatorname{supp}h\subset[-L,L]$ and $\log n>2L$, the $n$-th jump
integral in (2) is

$$
\int_{-L}^L\Phi(x)|h(x)|^2
\bigl(\Phi(x+\log n)+\Phi(x-\log n)\bigr)\,dx. \tag{6}
$$

It is strictly positive for nonzero $h$. The original compact correlation
vanishes at those shifts, but these transformed diagonal terms remain.
For fixed $L$ their integrated values are bounded by
$C n^M\exp(-c n^2)$, with $c>0$. They converge absolutely and cannot be
silently dropped from (4).

### A sharp direction excludes Gamma-only replacement

The same published analytic null-vector mechanism applies to
$\Phi''$, whose transform is $-z^2\Xi(z)$. Put $b=\Phi''/\Phi$.
This is an even smooth nonconstant function, with
$b(x)\sim4\pi^2e^{4x}$ on the positive tail. The theta decay makes
$\operatorname{Var}_\nu(b)$ and both energies finite.

For $b_R=\chi_R b$, the variance and both energies converge to those of
$b$. The Gamma small-shift integrals have a uniform $O(t^2)$ majorant.
For large prime shifts, the product of the two theta tails, including the
growth of $b$ and its cutoff, gives a uniform integrated bound
$C n^M\exp(-c n)$. These majorants also justify the paired zero sum for
$\chi_R\Phi''$, so its limit is $Q(\Phi'')=0$. Passing (4) to the limit gives

$$
E_\Gamma(b)+E_{\rm prime}(b)=\tfrac12\operatorname{Var}_\nu(b). \tag{7}
$$

The $n=2$ term is positive: if it vanished, positivity of $\Phi$ and
continuity would make $b$ $\log2$-periodic, contradicting its tail growth.
Thus $E_\Gamma(b)<\operatorname{Var}_\nu(b)/2$, and the same strict
inequality holds for all sufficiently large compact cutoffs $b_R$.
Gamma energy alone fails the required all-test threshold. Equation (7)
also rules out a uniform full-energy threshold strictly above one-half.
Neither statement supplies the lower bound in (5).

The [Chen–Wang estimate](chenwang2012weighted.md) provides a reusable
weaker-weight bound for exactly $E_\Gamma$. Its center, density and
unspecified constant retain the documented mismatch with (5). A FIB
partition comparison must retain the actual measure and every long
prime-power edge; the existing
[prime-2 crossing](frankliebseiringer2006hardy.md) already excludes
replacing those edges by adjacent-window seams alone.

Equations (2)–(7), their noncompact cutoff passages and the sharp-direction
application are paper deductions from the inspected sources. They are not
new Lean declarations or an originality claim. The inspected Lagarias
v4 PDF has SHA-256
`86f3d3c49f5a889f121bb1f04f67694cb9066dc8360f6988165788679594a4a7`.
No spectrum or essential-spectrum conclusion is asserted without a
separate closed-form, operator-domain and spectral argument.

## The full derivative family and the remaining estimate

The [minimal mixed-form realization](fukushima2011dirichlet.md) supplies
the actual closure of the even compact smooth core, with the measure,
energy and all prime powers in (2) unchanged. Write
$D=E_\Gamma+E_{\rm prime}$, let $\mathcal F$ be this even complex form
domain, and let $T$ be its nonnegative self-adjoint operator in
$\mathcal H=L^2_{\rm even}(\nu)$. The following extends the source
application in (7); it is a paper bridge, without Lean certification or
an originality claim. It does not supply a new upper bound on the
one-half threshold, already constrained by (7).

For each fixed derivative order $m$, differentiate the original normally
convergent theta series rather than an asymptotic error term. Its tail
and the positive first-term lower bound give

$$
\begin{gathered}
|\Phi^{(m)}(x)|\le C_m
\exp\bigl((9/2+2m)|x|-\pi e^{2|x|}\bigr),\\
u_m:=\Phi^{(m)}/\Phi,\qquad
|u_m(x)|\le C_m e^{2m|x|},\qquad
|u_m'(x)|\le C_m e^{(2m+2)|x|}.
\end{gathered} \tag{8}
$$

These bounds place every even $u_{2k}$ in the **minimal** domain, not
merely the maximal finite-energy domain. Indeed, with the same cutoffs
$\chi_R$, put $w_R=(1-\chi_R)u_m$. Its $L^2(\nu)$ norm tends to zero.
For $0<t<1$, its squared increments are bounded uniformly in $R\ge1$
by $C_mt^2e^{C_m|x|}$, integrable against
$\Phi(x)\Phi(x+t)\psi(t)\,dx\,dt$. For $t\ge1$, use
$\psi(t)\le Ce^{-t/2}$, boundedness of $\Phi$, and
$\int\Phi|u_m|^2<\infty$. For prime shifts $y=x+\log n$, absorb the
quotient growth into the two theta tails and use

$$
e^{2|x|}+e^{2|x+\log n|}\ge2n.
$$

This gives a uniform integrated majorant $C_me^{-cn}$ for the prime
diagonals, with $c>0$ and $m$ fixed. Dominated convergence gives
$D(w_R)\to0$, including every prime power. Thus
$\chi_Ru_{2k}\to u_{2k}$ in the actual form norm. The case $m=0$
also agrees with the constant membership established in the realization
note.

Repeated integration by parts against $\cosh(x/2)$ gives
$\nu(u_{2k})=4^{-k}$. Define the centered vectors

$$
v_k=\Phi^{(2k)}/\Phi-4^{-k},\qquad k\ge1.
$$

Lagarias's mixed nullity applies to the transform
$(-1)^kz^{2k}\Xi(z)$: it vanishes at every actual zero. To pass from that
zero-side statement to arithmetic tests, the errors in
$\chi_R\Phi^{(2k)}$ and their second derivatives tend to zero in the
same exponentially weighted integral used for (3). Two integrations
by parts give inverse-square strip decay; pairing with a compact test
leaves a summable bound proportional to
$m_\rho/(1+|\Im\rho|^2)^2$. The near-diagonal Gamma and complete prime
majorants above justify the arithmetic passage as well. This is mixed
nullity, not an inference from a single zero quadratic value.

Polarizing (4), passing these cutoffs in the form norm and using core
density gives

$$
D(v_k,g)=\tfrac12\langle v_k,g\rangle_\nu
\quad(g\in\mathcal F),\qquad
v_k\in D(T),\quad Tv_k=\tfrac12v_k. \tag{9}
$$

Operator-domain membership here uses the cited closed-form representation.
The vectors are independent: a finite relation, multiplied by $\Phi$
and Fourier transformed, is a polynomial times $\Xi(z)$. Since
$\Xi(0)=\int\Phi>0$, the polynomial vanishes on a neighborhood of zero
and every coefficient in the relation is zero.

Let $N=\overline{\operatorname{span}\{v_k:k\ge1\}}^{\,L^2(\nu)}$ and
$\mathcal R=(\mathbb C1\oplus N)^\perp$. Closedness of $T$ puts all of
$N$ in its one-half eigenspace; constants have $T1=0$. These subspaces
and their orthogonal complement reduce $T$. Every $h\in\mathcal F$
therefore decomposes as $h=\nu(h)1+n+r$, with $n\in N$ and
$r\in\mathcal R\cap\mathcal F$, and

$$
D(h)-\tfrac12\operatorname{Var}_\nu(h)
=D(r)-\tfrac12\|r\|_\nu^2. \tag{10}
$$

This is the extended form slack; physical $Q$ outside its original
compact domain is not asserted. Core density and form-norm continuity
make (5) equivalent to
$D(r)\ge\|r\|_\nu^2/2$ on $\mathcal R\cap\mathcal F$.
That lower bound remains unproved. The decomposition removes an
independently specified family of critical directions without discarding
an unknown cross term; it does not identify the entire one-half
eigenspace or determine the spectrum on $\mathcal R$.

### Compact support does not survive this projection

If $r\in\mathcal R$ has compact essential support, then $r=0$.
To see this, set $U=r\cosh(x/2)$. The positive smooth density of $\nu$
on that support makes $U$ a compact even $L^1(dx)$ function. Orthogonality
to $1$ and every $v_k$ gives
$\int U(x)\Phi^{(2k)}(x)\,dx=0$ for $k\ge0$; evenness gives the odd
orders as well. The original theta series is holomorphic on
$|\Im w|<\pi/4$, by normal convergence on compact subsets. It is not
being asserted entire in its physical coordinate.

Consequently $A(z)=\int U(x)\Phi(x+z)\,dx$ is holomorphic on this
connected strip. All its derivatives vanish at zero, so the analytic
identity theorem gives $A=0$. On the real axis evenness identifies
$A=U*\Phi$, hence $\widehat U(s)\Xi(s)=0$. The factor $\Xi$ is nonzero
near zero. Compact support makes $\widehat U$ entire, so it vanishes
identically; Fourier injectivity gives $U=0$ and $r=0$.

This does not make $\mathcal R$ trivial. The existing
[sparse compact tests with positive full slack](chenwang2012weighted.md)
have nonzero projected remainders by (10). Those remainders necessarily
have noncompact support. Thus requiring both compact support and all
critical orthogonality conditions would leave only the zero test.
A local FIB support estimate must control the actual projected tails
before it can be used on the remaining space; projecting a compact test
and reusing its old support would change the object being estimated.

The [full mixed spectral application](lenz2010compactness.md) supplies
a paper-level essential bottom of one-half and an unspecified positive
Poincare constant in this same measure. Its local compactness and
relative-compact perturbation checks retain every prime power.
For the even operator, any remaining eigenvalues $0<\lambda<1/2$
are discrete, with eigenvectors in $\mathcal R$, and may accumulate
at $1/2$. These source applications do not prove the one-half bound
in (5), equivalently the remainder lower bound stated after (10).

The [same-form exterior transfer](lenz2010compactness.md#same-form-theta-exterior-bound-and-low-projector-cutoff)
combines (4) with the complete compact Weil formula on the same even
test $f=\Phi h$. Its pole and variance mean terms cancel, leaving a
nonnegative flat translation form and two bounded negative terms.
The bounded multiplier and closed flat form extend that identity through
the actual minimal form closure; original theta tails then control the
full killed exterior energy and cutoff of the whole fixed-gap subspace.
This paper-level transfer replaces the quantitative prime-counting
remainder only in that exterior estimate. It does not establish the
remaining spectral lower bound in (5), RH, Robin or Lean certification.


The [ordered-semigroup source check](karlinmcgregor1959coincidence.md)
separately tests a proposed oscillation route from the critical family.
The actual even theta semigroup fails all-times order-two positivity
under radial ordering. Its ordinary positivity preservation cannot
therefore locate the known half eigenvectors as the first nonzero
spectral level by that route. Weaker justified spectral-ordering
methods and the remainder lower bound are still unresolved.

### The compressed remainder has no inherited positive cone

The [ideal-space exterior-square source check](kushelzabreiko2008ideal.md)
addresses the separate proposal to apply positive-operator theory after
compressing to $\mathcal R$. Because $\mathcal R\subset1^\perp$ and
$\nu$ is finite, its inherited cone of nonnegative functions is
$\{0\}$. It is not an ideal function space in the original radial
coordinates. Any ambient positivity-preserving linear operator with
range in $\mathcal R$ must therefore vanish, whereas
$Q_{\mathcal R}e^{-tA}Q_{\mathcal R}$ and
$Q_{\mathcal R}(A+\alpha)^{-1}Q_{\mathcal R}$ are nonzero for
$t,\alpha>0$. Thus neither compression can supply the source's ordinary
nonnegative-kernel interface in those coordinates. This paper-level
check does not exclude a separately justified transported order and does
not assert compactness of the restriction.

The actual numerical obligation can still be written as
$\|(A|_{\mathcal R}+\alpha)^{-1}\|\le(\alpha+1/2)^{-1}$ for any fixed
$\alpha>0$, by the standard spectral theorem. This is exactly the
remaining half-bound after (10), not an improved estimate. The critical
vectors in $N$ are excluded from $\mathcal R$, so they cannot be used
as its first or second eigenvectors. RH and Robin remain unresolved;
no new Lean certification is asserted.

### A raw absolute Schur certificate must also preserve the critical family

The [Schur equality application](../Fourier/teschl2009mathematical.md#equality-in-schurs-test-checks-the-unprojected-theta-edge-shortcut)
tests a signed-kernel proposal for the same half-slack. With the actual
positive and negative parts of $J-(\nu\otimes\nu)/2$ and their raw
increment maps $C_\pm$, it excludes simultaneous exact reconstruction
$SC_+h=C_-h$ on the entire original even core and an ordinary measurable
kernel's finite-positive-weight absolute Schur product at most one.
The known critical vectors would attain equality in that certificate.
Their theta jets distinguish the unordered radial endpoint pair, forcing
each nonzero row onto a finite fiber of zero input edge measure. Prime
jump lengths are atomic, but the original prime edge graphs still have
zero point mass because their source position is integrated against $dx$.

This is a conditional paper application of the classical equality
mechanism to the original theta family. It excludes neither a better
actual norm estimate than the absolute certificate nor products above
one approaching one, controlled approximate reconstruction, measure
kernels, or a transfer defined only on $\mathcal R$.

The same mixed nullity removes the closed critical edge images jointly:
for $e_\pm=(I-P_\pm)C_\pm$, where $P_\pm$ project onto
$\overline{C_\pm N}$, the slack is
$q(h)=\|e_+h\|^2-\|e_-h\|^2$. Since $e_\pm v_k=0$, the preceding
raw norm-attainment argument has no stated conclusion for this projected
transfer. The actual reconstruction and norm comparison after that
projection remain unproved. No new generic Schur, variance or contraction
theorem, numerical half-bound, RH/Robin result or Lean certification is
claimed.

### A common-source inverse for both critical edge projections

This is a conditional paper application to the accepted original theta measures, not a half-bound or Lean-certified result. Classical two-step path comparison, closed-range projection and Neumann inversion are reused. The additional interface is the explicit coercivity of the actual negative-edge metric, yielding one bounded critical-source inverse for both edge projections.

Retain the probability measure $
u$, signed edge measures $K_\pm$, increment maps $C_\pm$ and mixed nullity from the [Schur application](../Fourier/teschl2009mathematical.md#equality-in-schurs-test-checks-the-unprojected-theta-edge-shortcut), equations (S1)–(S7). Write

$$a(x,y)=\left[1-\frac{\psi_\Gamma(|x-y|)}{2\cosh(x/2)\cosh(y/2)}\right]_+,$$

so $K_-=(a/2)\nu\otimes\nu$ off the diagonal. Put $t=1/2$, $a_t=1-\psi_\Gamma(t)/2>0$, and choose three anchor intervals

$$I_-=[-3/2,-5/4],\quad I_0=[-1/8,1/8],\quad I_+=[5/4,3/2].$$

Let $\eta=\min_j\nu(I_j)>0$ and $c=a_t\eta/8$. The gaps between anchors exceed $2t$. Each forbidden interval $(x-t,x+t)$ intersects at most one anchor; two forbidden intervals therefore leave at least one anchor entirely available. Hence for every $x,y$,

$$\nu\{z:|z-x|\ge t,|z-y|\ge t\}\ge\eta.$$

Apply $|h(y)-h(x)|^2\le2|h(z)-h(x)|^2+2|h(y)-h(z)|^2$ on these common neighbors, then integrate over the same product probability measure. With

$$I_t(h)=\iint_{|x-y|\ge t}|h(y)-h(x)|^2d\nu(x)d\nu(y),$$

this gives $2\eta\operatorname{Var}_\nu(h)\le4I_t(h)$. Monotonicity of the actual psi and cosh>=1 give $a(x,y)\ge a_t$ on those edges. Therefore for every ambient even $h\in L^2(\nu)$,

$$c\operatorname{Var}_\nu(h)\le\|C_-h\|^2\le\operatorname{Var}_\nu(h)/2.\tag{G1}$$

Here $\psi_\Gamma(1/2)<2$ follows from $e>2$ and $e^{-1/4}<1$. This is a positive symbolic constant for the negative-edge metric; it supplies no lower bound for the original positive energy or its half-slack.

Set $B=C_-^*C_-$ on the actual ambient even Hilbert space. It is bounded positive and, in the weak L2 sense,

$$(Bh)(x)=\frac12\int a(x,y)(h(x)-h(y))d\nu(y).\tag{G2}$$

Let $P_N$ be the existing orthogonal projection onto the centered critical source space $N$. The common Gram operator on $N$ is

$$G=P_NB|_N,\qquad cI_N\le G\le\tfrac12I_N.\tag{G3}$$

It is independently invertible. The two maps $A_\pm=C_\pm|_N$ are bounded, have $A_\pm^*A_\pm=G$ by the accepted mixed nullity, and have closed ranges by G1. Thus the closure signs in the known critical edge image spaces can be removed.

For every $h$ in the actual form domain, mixed nullity gives the same coefficient for both projections:

$$A_+^*C_+h=A_-^*C_-h=P_NBh.$$

Consequently with $n_h=G^{-1}P_NBh\in N$,

$$P_\pm C_\pm h=C_\pm n_h,\qquad e_\pm h=C_\pm(h-n_h).\tag{G4}$$

This is one simultaneous source correction, using a generally different projection from the ambient $P_Nh$. It does not assume that $B$ commutes with $P_N$, and $h-n_h$ need not belong to the ambient orthogonal remainder $\mathcal R$.

The classical norm-convergent inverse series is explicit:

$$G^{-1}=2\sum_{j\ge0}(I_N-2G)^j,\qquad\|I_N-2G\|\le1-2c.$$

For $n_h^{(m)}=2\sum_{j=0}^m(I_N-2G)^jP_NBh$, the truncation has the certified bound

$$\|n_h-n_h^{(m)}\|\le\frac{(1-2c)^{m+1}}{c}\|P_NBh\|\le\frac{(1-2c)^{m+1}}{2c}\|h-\nu(h)1\|.\tag{G5}$$

Because its source error lies in $N$, each edge error is at most $\|n_h-n_h^{(m)}\|/\sqrt2$. Mixed nullity also keeps $q(h-n_h^{(m)})=q(h)$ exactly. Thus the two errors are paired through one source, not independently optimized.

What is still missing: explicit acquisition or approximation of $P_N$ itself, a transfer between the actual projected increments, and its joint reconstruction/norm estimate. The anchors' positive mass can be very small and no useful numerical conditioning is claimed. The inverse series is an operator identity involving the exact $P_N$, not a finite algorithm or a spectral certificate for the original remainder. G1 bounds K_- only, not D, and does not prove RH, Robin, the half-bound or the cofinal comparison.


### Even geometry gives a stronger negative-edge inverse constant

Retain the same $a(x,y)$, $B=C_-^*C_-$ and $G$ from (G1)–(G5).
Let $\mu$ be the law of $|X|$ for $X\sim\nu$, and write an even input
as $h(x)=f(|x|)$. Folding the two signs gives

$$\|C_-h\|^2=\frac18\iint
[a(r,s)+a(r,-s)]|f(r)-f(s)|^2\,d\mu(r)d\mu(s).$$

Choose $t>0$ with $\psi_\Gamma(t)<2$ and put
$p_t=\mu([t,\infty))$, $a_t=1-\psi_\Gamma(t)/2>0$.
On $\max(r,s)\ge t$, the opposite-sign edge has $a(r,-s)\ge a_t$.
For $u=f-\mu(f)$, $A=[0,t)$ and $T=[t,\infty)$, direct expansion gives

$$\begin{aligned}
J_T&=\iint_{\max(r,s)\ge t}|u(r)-u(s)|^2\,d\mu(r)d\mu(s)\\
&=2p_t\int_A|u|^2d\mu+2\int_T|u|^2d\mu
  +2\left|\int_Tu\,d\mu\right|^2
\ge2p_t\operatorname{Var}_\mu(f).
\end{aligned}$$

Consequently $\|C_-h\|^2\ge a_tp_t\operatorname{Var}_\nu(h)/4$.
The positive first term of the original theta series has the exact
integrated lower bound

$$p_t\ge[4u(1+e^t)-2]e^{-u},\qquad u=\pi e^{2t}.$$

Its derivative in $t$ is minus twice the first-term $\nu$ density, and
it tends to zero at infinity. At $t=7/20$, outward interval evaluation
with python-flint 0.9.0 at 256 bits gives
$a_t>1662/10000$ and the displayed mass bound $>1059/10000$.
Their product divided by four exceeds $11/2500$. Thus, on the actual
centered even space and in its inherited $L^2(\nu)$ norm,

$$\begin{gathered}
c_*:=\frac{11}{2500},\qquad
c_*\operatorname{Var}_\nu(h)\le\|C_-h\|^2
\le\tfrac12\operatorname{Var}_\nu(h),\\
\|G^{-1}\|\le\frac{2500}{11},\qquad
\kappa(G)\le\frac{1250}{11}<114,\qquad
\|I_N-2G\|\le1-\frac{22}{2500}.
\end{gathered}$$

This controls the negative-edge metric and its critical compression.
It does not bound $D$ or the half-slack. Matrices in an unnormalized
derivative basis need not have this condition number. The comparison
is a paper application of the actual even product measure; the scalar
interval evaluation is numerical evidence, not new Lean certification.

The [theta-translation Fredholm interface](../Dynamics/clason2021regularization.md#actual-theta-translations-generate-the-critical-source)
represents the common correction by a small-window integral kernel and
Tikhonov normal equation, without an exact $P_N$ in its construction.
Its fitted sources converge strongly, with a separate fixed-parameter
discretization bound. The required input's small-spectral-value error
and the projected transfer estimate remain unproved. Positive finite
regularization does not remove the existing exact raw Schur-certificate
obstruction.

### A complete block minorant improves the inverse constant

The [whole-space negative-edge block estimate](../../docs/reports/theta-mixed-matrix/theta-negative-block-gap.md)
reuses the existing depth-two five-mode FIB tiling of $[0,3/2]$, adds
the whole outside cell and integrates the actual folded theta masses.
A nonnegative block conductance minorant separates within-cell
conditional variance from block means. Directed congruence and
Gershgorin margins verify both sufficient conditions at $c_{**}=1/100$.
Under the inherited actual-model and numerical-supplier premises this
gives, for every ambient even $h\in L^2(\nu)$,

$$
\frac1{100}\operatorname{Var}_\nu(h)\le\|C_-h\|^2
\le\frac12\operatorname{Var}_\nu(h),\qquad
\|G^{-1}\|\le100,\quad\kappa(G)\le50,\quad
\|I_N-2G\|\le\frac{49}{50}.
$$

The outside cell retains its conditional variance, so the assertion
does not restrict $h$ to block-constant functions. It is a conditional
paper estimate with directed numerical evidence, not a new generic
Poincare theorem or Lean result. It improves common-source inverse
conditioning; the original energy's half-bound, cofinal projected
comparison, Robin and RH remain unproved.
