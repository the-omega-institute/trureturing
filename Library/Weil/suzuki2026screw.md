---
bibkey: suzuki2026screw
authors: Masatoshi Suzuki
year: 2026
title: Weil's quadratic form via the screw function
doi: null
url: https://arxiv.org/abs/2606.09096v3
claim: The localized Weil operator has a continuous lowest eigenvalue and a positive simple even ground state at sufficiently small support; a specified locally uniform spectral limit would imply RH but remains an additional hypothesis. Positive shifted operators do not supply unshifted positivity at all scales.
strata_touched: []
license: citation-only
triage: anchor
---

# Localized Weil operators and the spectral-limit obligation

The primary source is [Suzuki, arXiv:2606.09096v3](https://arxiv.org/abs/2606.09096v3), submitted **23 September 2026**. The latest version history, selected theorem statements and their differences from v2 were checked on 1 October. This note does not assert independent verification of the whole preprint, its external inputs or a Lean implementation.

## Small support and shifted positivity

For the source's localized Weil operator $A_a$ on $L^2(-a,a)$, Theorem 1.3 states continuity of the lowest eigenvalue $\lambda_a$ in $a$. Theorem 1.4 gives positivity, simplicity and an even ground eigenfunction for **sufficiently small $a>0$**, with its stated small-$a$ asymptotic. These core statements were already in v2 and are not new September discoveries.

Choosing a real $\lambda<\lambda_a$ makes $T_{a,\lambda}=A_a-\lambda I$ positive and supports the Hilbert-space construction. It does not prove $A_a\ge0$. The paper explicitly distinguishes this shift from the unshifted choice $\lambda=0$, whose availability at every sufficiently large scale has RH strength. The expected limiting identification is not obtained by choosing the shift alone.

## The exact limit in v3

Corollary 1.6 assumes choices $\lambda(a)<\lambda_a$, $\theta(a)\in[0,2\pi)$ and a function $\phi(a,z)$ **analytic in the upper half-plane**, for all sufficiently large $a$, such that

$$
e^{\phi(a,z)}W(a,\theta(a);z)
\longrightarrow
\frac{\xi(1/2-iz)}{\xi(1/2-iz)+\xi'(1/2-iz)}
$$

uniformly on every compact subset of that half-plane. Under these hypotheses the corollary concludes RH. Here $W$ is the entire function constructed from the adjoint operator's boundary form in Theorem 1.5; its zeros are precisely the eigenvalues of the specified self-adjoint extension. It also depends on the chosen shift $\lambda(a)$. The limit is a hypothesis; it is not the paper's unconditional conclusion. Compared with the inspected v2 statement, v3 explicitly states the shift inequality, analyticity of the factor's exponent and locally uniform convergence on this domain. Pointwise agreement or sampled eigenvalue agreement cannot replace this limit contract. Section 7 motivates the formula under RH; it is not an unconditional proof of the required limit.

## A related compact-window source and its current range

[arXiv:2608.24827v2](https://arxiv.org/abs/2608.24827v2), submitted **2 September 2026**, is listed under **Xuefeng Zhu**. The arXiv history explicitly says the author name and affiliation were updated; its v1 lists **Marcus Chuk**. Thus the older author's name in the [project's August account](../../docs/develop/theory/GOLDEN_OBSERVER_RH_ROUTE.md) identifies the earlier version, not a different theorem automatically missing a source.

In v2, Theorem 1.2 states a computer-assisted lower bound for real even tests supported in $[-0.8,0.8]$. Theorem 6.2 supplies the parity and ground-state separation, and Corollary 6.3 states the extension

$$
Q(f)\ge8.9\cdot10^{-18}\|f\|_2^2
\qquad (\operatorname{supp}f\subseteq[-0.8,0.8])
$$

for complex $L^2(\mathbb R)$ tests, using its Weil-form convention. These are the preprint's claimed certified results; the certificate programs were not independently rerun for this note. This is one fixed support window, not all-support Weil positivity.

Section 7 expressly retracts an **earlier draft's** claimed certificate at $L=1.19$, or autocorrelation support $2.38$: replacing the true prime-comb envelope by a smaller per-prime quantity used the bound in the wrong direction, so the reduced positive matrix did not bound the actual form. The checked v1 already states the $L=0.8$ range and does not contain that $2.38$ theorem. Hence v2's retraction should not be described as downgrading a theorem found in the arXiv v1. The positive exploratory matrix at $L=1.19$ is not a valid certificate for the full form.

The precise Landau–Widom profile is Conjecture 12.1, supported by fitted finite data. Theorem 1.3's qualitative decay bound explicitly **assumes RH**. Neither statement supplies an unconditional all-scale lower bound. The fixed-window numerical certificates, a conjectural asymptotic profile and the conditional decay theorem have different evidentiary roles.

## A larger author-submitted fixed window

The [Liu source note](liu2026tailcompensation.md) records the pinned manuscript and release for *Certified Weil Positivity Beyond the Unit Window*. Its Theorems A and B state full complex-test coercivity at physical half-widths $1$ and $17/16$, respectively. It is an author-posted journal submission with numerical materials, without claimed journal acceptance or completed external human reproduction. The source note inspects its complete form and tail interfaces; it does not independently replay the certificates.

Theorem B retains a positive rank-two Fourier-tail correction in the finite sign test, using tail-filtered Legendre vectors and the same actual Gamma, pole and prime terms. On the even test space only its even correction survives. This offers a concrete retained positive contribution to consider alongside the [existing signed coupling allowance and its even-sector consumer](../Fourier/montgomery1978largesieve.md). Its half-width is still below $\log3$, the first new FIB cutoff $c=9$. Equality of the two windows' active prime-power lists does not transfer the certified operator, its margin or its support-dependent estimates. Positivity of the enlarged window and the subsequent cofinal layers remains required.

## The existing finite-dictionary tail estimate

[Akiva Groskin, arXiv:2607.02828v3](https://arxiv.org/pdf/2607.02828v3), submitted **14 August 2026**, is already cited in the project's August account. Its latest listed version and the following statements were checked in the primary text on 1 October; this is not an independent audit of its complete proofs.

Theorem 2.5, printed p.6, maps a finite real even Galerkin vector to a specified test function whose **complete nontrivial-zero sum**, with multiplicity, equals a finite matrix quadratic form. The finite dimension belongs to the dictionary. It does not turn a numerical truncation of the zero sum into an exact identity or supply an inverse covering every admissible test. The older account's phrase “finite zero sum” must be read with this correction.

For $c>1$, a fixed frequency cutoff $N\ge0$ and $\rho=2\pi/\log c$, Theorem 3.2 and Corollary 3.3, printed pp.10–12, give a positive archimedean tail and an explicit finite-matrix bound

$$
0\prec Q_\infty-Q_T^{\rm tot}\preceq B_T I,
\qquad T>\max(\rho N,7),
\qquad B_T=O_{c,N}\!\left(\frac{\log T}{T}\right).
$$

Here $Q_T^{\rm tot}$ retains the dictionary's prime and pole terms and truncates its archimedean integral. The asymptotic fixes $(c,N)$; a proposed growing dictionary must instead carry the explicit parameter dependence, threshold and required margin through the limit. This positive omitted tail is not a bound for the signed arithmetic complement or the coupling to an infinite space of additional tests.

The existing [archimedean tail jet](../../D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.lean) uses the corresponding even-sector Cauchy density and bounds its jet remainder. Its source header leaves the identification with the actual Galerkin dictionary at paper level. It is reusable content, not a formalization of all the preceding source statements or a new all-support positivity result.

## Reuse in the FIB scale program

The [half-weighted Mangoldt supplier](chirrehelfgott2025nonnegative.md) gives another observation of this same kernel. With $G(x)=\sum_{n\le x}\Lambda(n)/\sqrt n-2\sqrt x+\zeta'(1/2)/\zeta(1/2)$, its logarithmic primitive plus the explicit shifted Gamma primitive equals the source's $g$ in (1.3), up to a constant. Section 8.1's identity $Q_W(f)=Q_G(Df)$, $D=i\,d/dx$, already owns the corresponding derivative pairing. That constant vanishes because $\int f'=0$; an even $|t|$ drift would not vanish. The cumulative formulation is an application of the existing screw representation, not a new FIB kernel or positivity criterion.

Chirre–Helfgott Proposition 9.1 supplies a quantitative absolute bound for this actual $G$ above its threshold, and the same paper's whole-range and finite-interval estimates supply the missing lower interval by partial summation. These improve the available finite-support error input. For a fixed verified zero height they retain a growing $\sqrt x/T$ allowance and give no favorable sign to the paired arithmetic integral. A finite-height source estimate therefore does not settle the all-scale kernel positivity or the spectral limit described above.

The project already has [golden support-layer positivity induction](../../D5/S3/Weil/TestFunctions/GoldenPositivityInduction.lean), [infinite-complement leakage bounds](../../D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.lean) and [an arithmetic boundary coupling jet](../../D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.lean). Their stated assumptions and Fourier/form-identification boundaries remain in force; this source review did not rebuild them. A generic recurrence or Schur-complement reduction should be reused. The remaining work is an estimate for the actual arithmetic form that pays for the coupling to each new test space, uniformly over all its coefficients and with the required scale and tail controls. Neither a positive shifted model nor fixed-window positivity supplies that estimate.


## Retain the theta model's metric in the derivative coordinates

The [weighted window interface](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/weighted-window-metric.md)
reuses the derivative pairing of Suzuki,
[arXiv:2206.03682v4](https://arxiv.org/html/2206.03682v4), Proposition 3.1,
equation (3.8), and the existing theta ground-transform identity.
It transports the original variance to an explicit rank-one-corrected
operator $B_L$. A sufficient relative window estimate is
$\mathcal G_{L_j}+\varepsilon_jB_{L_j}\succeq0$ with
$L_j\to\infty$ and $\varepsilon_j\to0$, not positivity in a substituted
unweighted metric. Its scalar conversion has a vanishing denominator
and requires a relative error rate for the converted window allowance.
The [fixed-test and centered-window interface](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/centered-window.md)
separately gives the sufficient absolute-error limit on fixed tests and
the original-mean parameter map for the published pole constraint.
These are applications of existing criteria and domain suppliers;
the actual arithmetic estimates remain unproved.
The [finite-pencil source](shi2026finitepencils.md) has a related
relative-control problem with a different contrast space and metric;
no identification of the two metrics is asserted.


## A parameter-integrated Fourier bridge for the actual Riemann kernel

Freedman, *Finite-core Volterra reductions for a Weyl-positive Riemann
phase kernel*, [arXiv:2606.29555v1](https://arxiv.org/html/2606.29555v1),
uses the actual even Riemann kernel $\Phi$ in Section 3, equations
(1)–(6). Its operator is distinct from Suzuki's localized Weil operator.
The inspected source passages are its main reduction status, Section 3,
Section 15.7 and Appendix C.1; its interval certificates were not rerun
and its complete analytic proof was not independently audited.

Section 15.7 retains the full trace-space obligation
$C-\Gamma^*\Gamma\succeq0$. Positivity on $\ker R_{\rm global}$ and
bounded cross coupling supply a quotient decomposition with a possibly
nonzero negative trace repair. The source states that the primitive trace
image is dense in the transported trace space, so the required repair
cannot be discarded by restricting to primitive original tests. Its
stress-value calculations at $\omega=0.49$ supply no uniform positivity
for $0<\omega<1/2$.

Appendix C.1 seeks a same-parameter KLM-to-de Branges pullback. For the
all-parameter positivity target, parameter integration gives a direct
alternative interface. This is a paper-level calculation with the source's
actual kernel, using standard Fourier transport and positivity under
integration; no new general positivity theorem or originality is claimed.

Set

$$
F(z)=\int_{\mathbb R}\Phi(t)e^{izt}\,dt,
\qquad E_\omega(z)=F(z+i\omega).
$$

The source identifies $F$ with Riemann's $\Xi$ up to its fixed overall
normalization. Keeping $F$ avoids mixing that scalar with the kernel
normalization. The displayed theta series is real and even and has
$\int_{\mathbb R}(1+|t|^2)e^{c|t|}|\Phi(t)|\,dt<\infty$ for every
$c>0$; its positive-side tail decays superexponentially. Consequently
$E_\omega^\#(z)=F(z-i\omega)$.
For $z,w$ in the upper half-plane define the algebraic kernel

$$
\mathcal D_\omega(w,z)=
\frac{E_\omega(z)\overline{E_\omega(w)}
-E_\omega^\#(z)\overline{E_\omega^\#(w)}}
{2\pi i(\overline w-z)}.
\tag{W1}
$$

Calling (W1) an algebraic de Branges kernel does not assume its positivity.
For the source's physical kernel put $p=(a+b)/2$, $d=(a-b)/2$:

$$
K_v(a,b)=\frac12\int_{|p|}^\infty
 y\cosh(2vy)\Phi(y+d)\Phi(y-d)\,dy,
\qquad 0\le v<1/2.
\tag{W2}
$$

Its parameter integral is

$$
\overline K_\omega(a,b):=\int_0^\omega K_v(a,b)\,dv
=\frac14\int_{|p|}^\infty
\sinh(2\omega y)\Phi(y+d)\Phi(y-d)\,dy.
\tag{W3}
$$

The exact transport is

$$
\boxed{\mathcal D_\omega(w,z)=\frac4\pi
\int_{\mathbb R^2}\overline K_\omega(a,b)
 e^{iza-i\overline w b}\,da\,db.}
\tag{W4}
$$

To check the constants and orientation, write $k=z-\overline w$ and
$\ell=z+\overline w$. The numerator of (W1), after
$t_1=y+d$, $t_2=y-d$ and evenness of $\Phi$, is

$$
-8i\int_{\mathbb R}\int_0^\infty
\Phi(y+d)\Phi(y-d)\sinh(2\omega y)
\sin(ky)e^{i\ell d}\,dy\,dd.
$$

Its denominator is $-2\pi i k$. On the physical side,
$da\,db=2\,dp\,dd$ and
$\int_{-y}^y e^{ikp}\,dp=2\sin(ky)/k$.
Substitution of (W3) therefore gives (W4). The exponential moments above
dominate all the displayed integrals and the parameter differentiation on
compact parameter and upper-half-plane evaluation sets. Equivalently,

$$
\partial_\omega\mathcal D_\omega(w,z)=\frac4\pi
\int_{\mathbb R^2}K_\omega(a,b)e^{iza-i\overline w b}\,da\,db,
\qquad \mathcal D_0=0.
\tag{W5}
$$

If the actual $K_v$ is positive semidefinite for every $0<v<1/2$,
then $\overline K_\omega$ is positive semidefinite. Test first with
$1_{[-R,R]}(a)e^{iza}$ and finite linear combinations. Positivity follows
from the continuous physical kernel by finite-sum approximation. Dominated
convergence as $R\to\infty$ and (W4) give positivity of
$\mathcal D_\omega$ on every finite upper-half-plane evaluation set.
Thus a positive integral of the parameter family suffices; a pullback from
one fixed $K_\omega$ is not needed for this implication.

The zero-exclusion endpoint can be checked without assuming a de Branges
space in advance. If $F$ had a zero $r$ with $\operatorname{Im}r>0$,
choose $0<\omega<\min\{1/2,\operatorname{Im}r\}$ such that
$F(r-2i\omega)\ne0$, possible by isolated zeros. At $z=r-i\omega$,

$$
\mathcal D_\omega(z,z)
=-\frac{|F(r-2i\omega)|^2}{4\pi\operatorname{Im}z}<0,
$$

contradicting the transported positivity. Real symmetry then excludes
lower-half-plane zeros as well. With the actual Riemann $F$, the full
physical positivity hypothesis would therefore imply RH.

This closes only the conditional Fourier/parameter interface for this
specific actual-kernel target. The required physical positivity, including
the trace-space Schur comparison and coverage arbitrarily close to
$\omega=0$, remains unproved. A single stress value, a positive quotient,
or a positive shifted Suzuki operator cannot replace it. The averaged
kernel and the source's stronger parameterwise target are not claimed to
be equivalent. No identity with Suzuki's Weil form or the same-source
Robin integral is asserted, and no signed Robin estimate or Lean
verification is supplied here.

## Reusing the classical logarithmic-derivative criterion at zero parameter

Lagarias, *On a positivity property of the Riemann ξ-function*,
[Acta Arithmetica 89(3), 217–234](https://doi.org/10.4064/aa-89-3-217-234),
printed pp.217–219, equations (1.4)–(1.5) and Theorem 1.1, supplies

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\Re\frac{\xi'(s)}{\xi(s)}>0\qquad(\Re s>1/2).
\tag{W6}
$$

The source explicitly attributes this known observation to earlier work,
including Hinkkanen. The function is the entire
$\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$;
the half-plane condition includes zero exclusion. The unconditional
positivity on $\Re s>1$ does not supply (W6) on the interior half-strip.
This classical criterion is reused, not reproved or presented as new
mathematics.

The actual physical $K_0$ in (W2) has a direct interface to (W6).
Differentiating (W1) at $\omega=0$ and reusing (W5) gives

$$
\mathcal B(w,z):=\left.\partial_\omega\mathcal D_\omega(w,z)
\right|_{\omega=0}
=\frac{F'(z)\overline{F(w)}-F(z)\overline{F'(w)}}
{\pi(\overline w-z)}
=\frac4\pi\int_{\mathbb R^2}K_0(a,b)
 e^{iza-i\overline w b}\,da\,db.
\tag{W7}
$$

The exponential moments used for (W5) justify this endpoint derivative
and the same cutoff transport. If the actual physical $K_0$ is a positive
semidefinite kernel on $\mathbb R$, then $\mathcal B$ is positive
semidefinite on upper-half-plane evaluation sets. No positive-parameter
coverage is assumed in this implication.

For $y=\Im z>0$ and $F(z)\ne0$, its diagonal is

$$
\mathcal B(z,z)
=-\frac{|F(z)|^2}{\pi y}\Im\frac{F'(z)}{F(z)}
=\frac{|F(z)|^2}{\pi y}
\Re\frac{\xi'(1/2-iz)}{\xi(1/2-iz)}.
\tag{W8}
$$

Here $F'/F=i\,\xi'/\xi(1/2+iz)$, and the functional equation reflects
$1/2+iz$ to $1/2-iz$, whose real part is $1/2+y$.
The fixed normalization scalar of $F$ cancels in the logarithmic
derivative and leaves the positive factor $|F(z)|^2$ intact.

There is no circular zero-free premise in using (W8). If an
upper-half-plane zero $r$ of $F$ had multiplicity $m\ge1$, the standard
local logarithmic-derivative pole would give

$$
\frac{F'(r-i\varepsilon)}{F(r-i\varepsilon)}
=\frac{im}{\varepsilon}+O(1)
\qquad(\varepsilon\downarrow0).
$$

Choose $\varepsilon<\Im r$ small enough that the evaluation point is
not a zero. Its diagonal in (W8) is then strictly negative, contradicting
positivity. Real symmetry excludes lower-half-plane zeros. Thus proving
the full physical $K_0$ positive semidefinite would already imply RH.
This is a source-specific application of the classical pole/positivity
criterion; it supplies no new general RH criterion or positivity theorem.

For this sufficient route, the next analytic target is the original
$\omega=0$ form on its full test space. The stronger all-parameter
positivity program still has its own parameter-coverage obligation, but
that obligation is not needed to obtain RH from the zero-parameter target.
Freedman's Section 5 and Remark 15.6 retain, also at zero, the parity
comparison $A\ge0$, $-A\le B\le A$ and the indefinite Volterra residual.
Section 15.7's full trace-space Schur requirement must therefore be
established for the zero-parameter operators and transported domains;
its $\omega=0.49$ budget cannot be transferred without an operator
comparison. Zero-parameter finite matrices and roundoff-level tests
are not that full-space theorem. No converse to the $K_0$ implication,
parameter monotonicity, identification with Suzuki's Weil operator,
signed Robin estimate or Lean verification is supplied.

## Classical interpolation on a logarithmic FIB sequence

The discrete positivity program is classical. Lagarias, printed p.218,
attributes a suitable-sequence criterion to Hinkkanen's Theorem 2. Its
precise hypotheses are not inferred from that footnote. The application
below instead reuses Pick interpolation as stated in McCarthy,
[*Pick's Theorem—What's the Big Deal?*, Theorem 1, printed p.36](https://doi.org/10.1080/00029890.2003.11919935)
([author's text](https://www.math.wustl.edu/~mccarthy/public_papers/MonthlyWtbd.pdf)),
and the classical bounded-function zero-set theorem stated as Theorem A,
p.1 of [Kraus, arXiv:1110.0275v1](https://arxiv.org/abs/1110.0275v1).
Kraus explicitly credits Jensen, Blaschke and the Nevanlinnas for that
zero-set theorem; her new critical-set results are not used. Neither
classical theorem is reproved or claimed as FIB mathematics.

Write $R(s)=\xi'(s)/\xi(s)$ and use $F_0=0,F_1=1$ for the ordinary
Fibonacci numbers. With the window weights starting at $2,3,5$, the sparse
finite address $[null]^j[2]$ has quantity $n_j=F_{3j+3}$. Choose the
**logarithmic** evaluation nodes

$$
s_j=1+\log n_j>1,\qquad z_j=i(s_j-1/2),\qquad j\ge0.
$$

At these real $s_j$, the unconditional half-plane result in (W6) makes
$R(s_j)$ real and strictly positive. Equation (W7), evenness of $F$ and
the functional equation give the exact sampled matrix interface

$$
\mathcal B(z_k,z_j)=\frac{F(z_j)F(z_k)}{\pi}\,M_{jk},
\qquad
M_{jk}:=\frac{R(s_j)+R(s_k)}{s_j+s_k-1}.
\tag{W9}
$$

Here $F(z_j)$ is real and nonzero. Thus this actual-kernel Gram matrix
and $M$ have the same positive-semidefinite tests under a nonzero diagonal
gauge. The project's existing
[Cayley/Nevanlinna interface](../../D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.lean)
covers finite kernel gauges, not this infinite sampling implication; it
was not rebuilt for this paper application.

For completeness, the parameters entering the classical interpolation
criterion are explicit. On $\Re s>1/2$ the domain Cayley coordinate is
$u=(s-3/2)/(s+1/2)$, and the prescribed target data are
$t_j=(R(s_j)-1)/(R(s_j)+1)\in(-1,1)$. Their disk Pick matrix satisfies

$$
\frac{1-t_jt_k}{1-u_ju_k}
=
\frac{s_j+1/2}{R(s_j)+1}\,
M_{jk}\,
\frac{s_k+1/2}{R(s_k)+1}.
\tag{W10}
$$

If every initial finite matrix $M^{(m)}=(M_{jk})_{0\le j,k<m}$ is
positive semidefinite, classical Pick interpolation and normal-family
compactness supply a Schur function $t$ on $\Re s>1/2$ with these data.
Existence of an interpolant alone would not identify it with the actual
$R$. The required uniqueness comparison takes place on the smaller
half-plane $\Re s>1$, where the actual function
$t_R=(R-1)/(R+1)$ is already holomorphic and bounded by one. There the
domain Cayley coordinate is $v=(s-2)/s$.

The standard Fibonacci growth gives $s_j=3j\log\varphi+O(1)$. Hence

$$
\sum_j(1-|v_j|)=\infty,
\qquad v_j=\frac{s_j-2}{s_j},
\tag{W11}
$$

because the summands equal $2/s_j$ for all sufficiently large $j$.
The classical zero-set theorem forces the bounded holomorphic difference
$t-t_R$, which vanishes at these nodes, to vanish identically on
$\Re s>1$. Consequently $(1+t)/(1-t)$ is the holomorphic continuation
of the actual $R$ to $\Re s>1/2$ and has positive real part there. The
prescribed interior data rule out a constant of modulus one, so $1-t$
cannot vanish. Meromorphic identity then rules out the logarithmic-derivative
poles of any zero of $\xi$ in that half-plane, as in (W8). Reusing (W6)
yields RH. Conversely, under RH the actual
$t_R$ is Schur on the larger half-plane, and the classical Pick theorem
gives every $M^{(m)}\succeq0$.

This is a source-specific application of the classical discrete criterion,
not a new general RH criterion. It permits the sufficient target to be
expressed using this one fixed sequence of actual zero-parameter Gram
matrices, rather than arbitrary upper-half-plane evaluations. It is still
an **all-size** positivity target. Positive entries and positive diagonals
are unconditional here and do not establish it; finitely many verified
matrices would not establish it either.

Raw geometric nodes $s_j=1+n_j$ have a convergent counterpart of (W11).
They therefore do not meet the uniqueness condition used in this
application. That failure does not rule out another criterion specific
to $\xi$ at those nodes. The logarithmic sequence is not mathematically
privileged among sequences with the same divergent uniqueness sum, and
no computational advantage is asserted. No all-size matrix positivity,
full physical $K_0$ positivity, signed Robin estimate or Lean verification
is supplied.

## Square-variable concavity controls reflected physical entries

For the complete original physical kernel (W2), reuse the classical
square-variable concavity stated in Csordas,
[*Fourier transforms of positive definite kernels and the Riemann
xi-function*, arXiv:1309.0055v2](https://arxiv.org/abs/1309.0055v2),
Theorem 4.2(b), PDF p.11. The theorem attributes this concavity to
Csordas--Varga, *Moment inequalities and the Riemann hypothesis*,
Theorem 2.1. With $K_C$ denoting Csordas' kernel, the actual theta
normalization is $\Phi(x)=2K_C(x/2)$, as in the
[fixed-source correspondence](../Zeros/planatsole2026secondlevel.md).
Consequently

$$
h(r)=\log\Phi(\sqrt r)=\log2+\log K_C(\sqrt{r/4})
$$

is strictly concave for $r>0$ and continuous at zero. This uses the
first-level classical result, without an all-order derivative hypothesis
or the newer second-level concavity claim. The following is a paper
application to the original physical kernel, with no literature-priority
or Lean/kernel-verification claim.

For $0\le v<1/2$ and $a,b\ge0$, the actual entries satisfy

$$
\boxed{0<K_v(a,-b)\le K_v(a,b),}
\tag{W12}
$$

with strict second inequality when $ab>0$, and equality when $ab=0$.
In particular this comparison preserves the full theta series and the
infinite integral in (W2).

To obtain it, put $p=(a+b)/2$, $d=|a-b|/2$ and $r_0=p^2+d^2$.
For $c\in\{d,p\}$ and $r\ge r_0$, define

$$
\begin{aligned}
k_c(r)&=2c\sqrt{r-c^2},\\
I_c(r)&=\cosh(2v\sqrt{r-c^2})
 \exp\{h(r+k_c(r))+h(r-k_c(r))\}.
\end{aligned}
$$

The changes of variable $r=y^2+d^2$ and $r=y^2+p^2$ give, respectively,

$$
K_v(a,b)=\frac14\int_{r_0}^{\infty}I_d(r)\,dr,
\qquad
K_v(a,-b)=\frac14\int_{r_0}^{\infty}I_p(r)\,dr.
\tag{W13}
$$

Evenness of $\Phi$ handles the possible negative argument $y-p$.
The square-variable arguments stay nonnegative since $k_c(r)\le r$.
Moreover,

$$
k_p(r)^2-k_d(r)^2=4ab(r-r_0)\ge0.
$$

For concave $h$, the symmetric sum $h(r+k)+h(r-k)$ decreases as
$k$ increases in $[0,r]$. Its endpoint values follow by continuity.
Also $\sqrt{r-p^2}\le\sqrt{r-d^2}$, so the $I_p$ cosh factor is
no larger. Hence $I_p\le I_d$. Strict concavity gives strict inequality
when $ab>0$ and $r>r_0$, including at $v=0$. Integrating proves (W12).

This controls an actual class of smooth original tests. Let a nonzero
real $f\in C_c^\infty(\mathbb R)$ be odd and suppose
$g=f|_{(0,\infty)}\ge0$. Symmetry and (W12) give

$$
\boxed{\begin{aligned}
\iint_{\mathbb R^2}f(a)K_v(a,b)f(b)\,da\,db
&=2\iint_{(0,\infty)^2}g(a)
 [K_v(a,b)-K_v(a,-b)]g(b)\,da\,db\\
&>0.
\end{aligned}}
\tag{W14}
$$

A nonzero smooth nonnegative $g$ is positive on an open set, where
the bracket is strictly positive. No restriction on its compact support
size or truncation of the physical kernel is imposed.
For $a>0$, the two-point Gram matrix on $\{a,-a\}$ also has strictly
positive eigenvalues $K_v(a,a)\pm K_v(a,-a)$. At $a=0$ the points
coincide and only positive semidefiniteness is asserted.

The tests in (W14) form a sign-constrained cone, not the entire linear
odd subspace. Pointwise positivity of the odd-parity difference does
not control arbitrary signed restrictions or their cross terms.
No all-size Gram positivity, full $K_0$ positivity, Green-trace
Schur domination, signed Robin upper estimate or RH proof follows
from (W12)--(W14) alone. Those original targets remain unproved.

## Finite curvature alone does not supply the odd cross bound

The odd sign-constrained result (W14) does not control arbitrary signed
profiles. Even imposing the finite second-level curvature conclusion from
the [existing theta source](../Zeros/planatsole2026secondlevel.md) does not
give a sufficient general hypothesis for the physical odd two-position
bound. The following model also satisfies the full decay class in
Csordas, [arXiv:1309.0055v2](https://arxiv.org/abs/1309.0055v2),
Definition 1.2. Gaussian times polynomial examples are classical; compare
that paper's Example 3.12. Its parameters and assertion differ from those
below. This is a repository-derived paper calculation in that model
family, without a literature-priority or Lean-verification claim.

The input in this construction is explicitly different from the actual
Riemann theta kernel. Set
$c=1/10$, $k=1/300$ and, for $r\ge0$, $\epsilon\ge0$, define

$$
\begin{aligned}
P(r)&=1+cr+kr^2,\\
Q(r)&=P'(r)^2-P(r)P''(r)
     =c^2-2k+2ckr+2k^2r^2,\\
\phi_\epsilon(t)&=e^{-t^2-\epsilon t^4}P(t^2),\\
S_\epsilon(r)&=\phi_\epsilon(\sqrt r)
              =e^{-r-\epsilon r^2}P(r),\\
R_\epsilon(r)&=Q(r)+2\epsilon P(r)^2.
\end{aligned}
$$

Since $c^2-2k=1/300$, $P,Q,R_\epsilon$ are strictly positive.
The two finite curvature conditions hold for every $r\ge0$:

$$
(\log S_\epsilon)''=-2\epsilon-\frac Q{P^2}<0,\qquad
D_\epsilon:=S_\epsilon'^2-S_\epsilon S_\epsilon''
=e^{-2r-2\epsilon r^2}R_\epsilon>0.
$$

For the second logarithmic curvature, differentiation gives

$$
(\log D_\epsilon)''
=-\frac{E_\epsilon}{R_\epsilon^2},\qquad
E_\epsilon=4\epsilon R_\epsilon^2+R_\epsilon'^2-R_\epsilon R_\epsilon''.
$$

Using $P''=2k$, $Q'=2kP'$ and $Q''=4k^2$, expansion yields

$$
E_\epsilon
=8k^3P+24\epsilon k^2P^2
 +24\epsilon^2P^2Q+16\epsilon^3P^4>0.
\tag{W15}
$$

For example, the coefficient of $\epsilon$ divided by four is
$Q^2+2Q'PP'-Q(P'^2+PP'')-\tfrac12P^2Q''=6k^2P^2$.
Thus $(\log D_\epsilon)''<0$ globally, including at $\epsilon=0$.

For every fixed $\epsilon>0$, $\phi_\epsilon$ is positive, even and smooth.
It is strictly decreasing on $t>0$ because
$P'-(1+2\epsilon r)P<P'-P<0$ there, with
$P-P'=(1-c)+(c-2k)r+kr^2>0$.
Each derivative is a polynomial times $e^{-t^2-\epsilon t^4}$ and is
$O(e^{-|t|^3})$ as $t\to\infty$. The constants may depend on $\epsilon$
and derivative order. This supplies Definition 1.2(v) with exponent
$2+\delta=3$. The endpoint $\epsilon=0$ itself has only Gaussian decay.

Fix the physical parameter at $v=0$ and apply the complete integral
construction to this explicitly substituted input:

$$
\begin{aligned}
\mathsf K_\epsilon(a,b)
&=\frac12\int_{|(a+b)/2|}^\infty
 y\,\phi_\epsilon(y+(a-b)/2)\phi_\epsilon(y-(a-b)/2)\,dy,\\
\mathsf L_\epsilon(a,b)
&=\mathsf K_\epsilon(a,b)-\mathsf K_\epsilon(a,-b).
\end{aligned}
$$

Here the subscript is the damping $\epsilon$, not the physical parameter.
At the Gaussian endpoint, exact integration gives, for $a,b>0$,

$$
\mathsf L_0(a,b)=\frac{ab\,e^{-a^2-b^2}}4
 \left[C+ck(a^2+b^2)+2k^2a^2b^2\right],
\qquad C=c^2+2ck+3k^2-2k=\frac{121}{30000}.
\tag{W16}
$$

To verify the full-tail integral, put
$x=((a+b)/2)^2$, $z=((a-b)/2)^2$, $u=y^2$. The polynomial factor in the
product of the two inputs is the symmetric polynomial

$$
\begin{aligned}
A(u,z)={}&1+2c(u+z)+(c^2+2k)(u^2+z^2)+(12k-2c^2)uz\\
&+2ck(u^3+z^3-u^2z-uz^2)+k^2(u-z)^4.
\end{aligned}
$$

Writing $T(x,z)=\sum_{j=0}^4 2^{-j}\partial_x^j A(x,z)$, integration
by parts gives
$\mathsf K_0(a,b)=e^{-2(x+z)}T(x,z)/8$.
Reflection exchanges $x,z$, and differentiation gives

$$
T(x,z)-T(z,x)
=(x-z)\left[2c^2-4k+4ck+6k^2
             +4ck(x+z)+4k^2(x-z)^2\right].
$$

Since $x-z=ab$ and $x+z=(a^2+b^2)/2$, this proves (W16).
No part of the integral tail has been removed.

The entries in (W16) are strictly positive. Nevertheless, for every
distinct $a,b>0$, their two-position determinant is

$$
\begin{aligned}
\Delta_0(a,b)
&:=\mathsf L_0(a,a)\mathsf L_0(b,b)-\mathsf L_0(a,b)^2\\
&=\frac{a^2b^2(a^2-b^2)^2e^{-2(a^2+b^2)}}{16}
\,k^2\left[c^2+4ck+6k^2-4k\right]<0,
\end{aligned}
\tag{W17}
$$

because the last bracket equals $-29/15000$.

For each fixed pair of positions,
$0<\phi_\epsilon(t)\le\phi_0(t)$ and
$\phi_\epsilon(t)\to\phi_0(t)$ as $\epsilon\downarrow0$.
The integrable Gaussian-polynomial products dominate the complete
integrals, including reflected arguments. Dominated convergence therefore
makes $\Delta_\epsilon(1,2)$ continuous at zero. By (W17), there is
$\epsilon_*>0$ such that

$$
\Delta_\epsilon(1,2)<0\qquad(0<\epsilon<\epsilon_*).
\tag{W18}
$$

No numerical value of $\epsilon_*$ or simultaneous all-position
negativity for one positive $\epsilon$ is asserted. Each fixed input
in (W18) satisfies full super-Gaussian admissibility and both finite
curvature inequalities. Thus those hypotheses together do not imply
the general physical odd two-position cross bound.

This countermodel does not change the actual theta input, refute its
reported second-level theorem, or establish a negative actual-theta
minor. A proof for that input can still use its specific series and
Jacobi identities. The original actual-theta cross estimate, full
physical $K_0$ positivity, signed Robin upper and RH remain unproved.

## The actual odd form on sufficiently separated large positions

The complete actual theta input has more information than the two generic
curvature hypotheses above. Reuse Csordas, Theorem 4.2(b), together with monotonicity of $K_C$,
for strict log-concavity on the positive half-line. Evenness, smoothness and
$K_C'(0)=0$ extend concavity to the whole real line. The normalization
$\Phi(x)=2K_C(x/2)$ preserves it. For the tail, reuse
[Planat--Solé, arXiv:2608.19160v1](https://arxiv.org/abs/2608.19160v1),
Section 4, equations (4.2), (4.6)--(4.7):

$$
K_C(r)=\pi(2\pi e^{4r}-3)e^{5r-\pi e^{4r}}(1+\varepsilon),
\qquad \varepsilon\ge0,
$$

with $L=4r$, $y=\pi e^L$ and reported uniform bounds

$$
|\varepsilon_L'|<1.5\cdot10^{-5},\qquad
|\varepsilon_L''|<2.5\cdot10^{-4}\qquad(y\ge5.68).
$$

The source supplies the monotonic tail bounds and their rational
certificate; its certificate is not independently rerun here. This paper
application uses these reported derivative bounds, rather than deriving
an all-order positivity conclusion from finite curvature. It makes no
literature-priority or Lean/kernel-verification claim.

In physical position $x$, $r=x/2$, $L=2x$, $y=\pi e^{2x}$.
Writing $\ell(L)=\log(1+\varepsilon)$ and
$p(x)=-\Phi'(x)/\Phi(x)$ gives

$$
\begin{aligned}
p(x)&=2y-\frac92-\frac6{2y-3}-2\ell'(L),\\
p'(x)&=4y+\frac{24y}{(2y-3)^2}-4\ell''(L).
\end{aligned}
$$

The source bounds imply $|\ell'|<1.5\cdot10^{-5}$ and
$|\ell''|<10^{-3}$. For $x\ge1$, $y>75/4$; the two displayed
expressions give $y<p<2y$ and $p'>y$. Thus

$$
\boxed{e^{2x}\le p(x)\le10e^{2x},\qquad p'(x)\ge e^{2x}
\quad(x\ge1).}
\tag{W19}
$$

Set $L_0(a,b)=K_0(a,b)-K_0(a,-b)$ and $J(a)=L_0(a,a)$.
For $a\ge256$, put $\delta=e^{-2a}/40$. Since $e^{2\delta}<2$,
(W19) implies $\int_0^t p(a+s)\,ds\le1/2$ for $0\le t\le\delta$.
Consequently the complete direct diagonal satisfies

$$
K_0(a,a)=\frac12\int_0^\infty(a+t)\Phi(a+t)^2\,dt
\ge\frac{a}{80e}\Phi(a)^2e^{-2a}.
$$

The reflected diagonal must also be retained. Let $g=\log\Phi$.
Global concavity gives $g(a-y)\le g(a)+p(a)y$ for every $y\ge0$,
including $y>a$. Integrating $g''(a+t)=-p'(a+t)\le-e^{2a}$ gives

$$
g(a+y)\le g(a)-p(a)y-\tfrac12e^{2a}y^2.
$$

These inequalities bound the full reflected integral by

$$
K_0(a,-a)=\frac12\int_0^\infty y\Phi(a+y)\Phi(a-y)\,dy
\le\frac12\Phi(a)^2e^{-2a}.
$$

Since $a\ge256>80e$, subtracting yields the actual diagonal bound

$$
\boxed{J(a)\ge\frac{a}{160e}\Phi(a)^2e^{-2a}
\ge\frac{a}{480}\Phi(a)^2e^{-2a}\quad(a\ge256).}
\tag{W20}
$$

For $b\ge a\ge256$, the exact fixed-limit representation is

$$
K_0(a,b)=\frac14\int_0^\infty(a+b+2t)\Phi(a+t)\Phi(b+t)\,dt.
$$

By (W19) its product is at most
$\Phi(a)\Phi(b)e^{-e^{2b}t}$. Full integration and (W12) give

$$
0<L_0(a,b)\le K_0(a,b)
\le\Phi(a)\Phi(b)\left(\frac{a+b}{4}e^{-2b}+\frac12e^{-4b}\right)
\le\frac{a+b}{2}\Phi(a)\Phi(b)e^{-2b}.
$$

Normalize by the actual diagonal, and use symmetry. With $d=|a-b|$,

$$
\boxed{0<\frac{L_0(a,b)}{\sqrt{J(a)J(b)}}
\le240\frac{a+b}{\sqrt{ab}}e^{-d}
\le240\left(2+\frac d{256}\right)e^{-d}
\quad(a,b\ge256).}
\tag{W21}
$$

For the last inequality, if $b\ge a$, then
$\sqrt{b/a}+\sqrt{a/b}\le b/a+1\le2+d/256$.
Neither a theta tail nor a reflected exterior is truncated in these bounds.

There is an all-size consumer on a restricted sample family. Take any
$N\ge1$ and ordered real positions $256\le a_1<\cdots<a_N$ with
$a_{i+1}-a_i\ge8$. The function $(2+d/256)e^{-d}$ decreases for
$d\ge0$, so every off-diagonal row sum of the matrix normalized in
(W21) is at most

$$
480\sum_{n\ge1}(2+n/32)q^n
=480\left(\frac{2q}{1-q}+\frac{q}{32(1-q)^2}\right),
\qquad q=e^{-8}.
$$

Since $e>5/2$, $q<(2/5)^8<1/1500$. Both $q/(1-q)$ and
$q/(1-q)^2$ are less than $1/1400$. The row sum is therefore less
than $480(2+1/32)/1400=39/56$. Applying the standard symmetric
row-sum bound to this normalized matrix, followed by positive diagonal
congruence, gives

$$
\boxed{\sum_{i,j=1}^N\overline{c_i}L_0(a_i,a_j)c_j
\ge\frac{17}{56}\sum_{i=1}^N J(a_i)|c_i|^2
\qquad(c\in\mathbb C^N).}
\tag{W22}
$$

The constants are uniform in $N$ and in these positions. This is relative
coercivity for actual odd-parity point samples; it is not a uniform
unweighted lower eigenvalue bound, since $J(a)$ decays at infinity.
The sample family is not dense in the full physical test space.
Compact positions, nearby pairs, arbitrary signed smooth profiles and
coupling to all omitted positions remain uncontrolled. Thus (W22)
neither supplies full $K_0$ positivity nor the signed Robin upper
estimate, and does not prove RH. The Jacobi orbit equations and the
second-level theorem are not claimed to pay those remaining estimates.

## Uniform confluence pays all sufficiently large two-position minors

The gap restriction in (W22) can be removed for **two-position** minors
by controlling the actual normalized kernel through second derivatives.
The threshold below is existential; no numerical value is asserted.
Reuse (W12)--(W22), including global concavity of $g=\log\Phi$ and the
actual hazard bounds (W19). The complete physical kernel and its
normalization are unchanged. This is a paper application, without a
literature-priority or Lean/kernel-verification claim.

First retain the finite-order information needed for differentiation.
The exact factorization and relative theta series in Planat--Solé,
Section 4, equations (4.2), (4.6), give, with $y=\pi e^{2u}$,

$$
\begin{aligned}
\Phi(u)&=4\pi^2e^{9u/2-y}(1-3/(2y))(1+\varepsilon),\\
\varepsilon&=\sum_{m\ge2}
 m^2\frac{2m^2y-3}{2y-3}e^{-(m^2-1)y}.
\end{aligned}
$$

For each fixed $0\le k\le6$, applying $(2y\,d/dy)^k$ to a summand
bounds its absolute value by
$C_k(1+y)^km^{4+2k}e^{-(m^2-1)y}$ for $u\ge1$.
The reciprocal denominator has bounded differentiated factors there;
each exponential differentiation adds at most
$C_km^2(1+y)$. The remaining sum is bounded by

$$
\sum_{m\ge2}m^{4+2k}e^{-(m^2-4)y}
\le\sum_{m\ge2}m^{4+2k}e^{-(m^2-4)}<\infty.
$$

These summable bounds also justify termwise differentiation. Taking the
logarithm, and extending the bounds over any remaining compact interval
by positivity and smoothness, yields

$$
\boxed{\begin{aligned}
g(u)&=\log(4\pi^2)+\tfrac92u-\pi e^{2u}+v(u),\\
|v^{(k)}(u)|&\le C_ke^{-2u}
 &&(u\ge1,\ 0\le k\le6),\\
|g^{(k)}(u)|&\le C_ke^{2|u|}
 &&(u\in\mathbb R,\ 1\le k\le6).
\end{aligned}}
\tag{W23}
$$

For the last line use evenness and compact derivative maxima.
This derives fixed-order growth bounds from the actual full series;
it does not extend the source's finite sign claims to an all-order
Laguerre or derivative-Hankel hierarchy.

Fix $D>0$, put $a=x+d$, $b=x-d$, $E=e^{-2x}$ and $|d|\le D$.
For $x>D+1$ define the exact scaled difference

$$
T(x,d)=\frac{e^{2x}L_0(x+d,x-d)}
 {x\Phi(x+d)\Phi(x-d)},
\qquad q_\infty(d)=\frac1{8\pi\cosh(2d)}.
$$

The source-specific differentiable limit is

$$
\boxed{\max_{m+n\le2}\sup_{|d|\le D}
\left|\partial_x^m\partial_d^nT(x,d)
-\mathbf1_{\{m=0\}}q_\infty^{(n)}(d)\right|
\longrightarrow0\qquad(x\to\infty).}
\tag{W24}
$$

Both complete integrals are needed to prove it. For the direct term,
$y=x+Et$ gives exactly

$$
\begin{aligned}
Q(x,d)&=\frac{e^{2x}K_0(a,b)}{x\Phi(a)\Phi(b)}
=\frac12\int_0^\infty(1+Et/x)e^{F(x,d,t)}\,dt,\\
F(x,d,t)&=\sum_{s\in\{-1,1\}}
 [g(x+sd+Et)-g(x+sd)].
\end{aligned}
$$

By (W19), $F\le-c_Dt$ with $c_D=2e^{-2D}>0$.
Writing each difference as
$Et\int_0^1g'(x+sd+vEt)\,dv$ and using $E_x=-2E$
bounds every mixed derivative of $F$ of total order at most two by
$C_Dt(1+t)^2e^{2Et}$. Here at most $g'''$ is needed, and every term
retains a factor $Et$, cancelling the $e^{2x}$ in (W23).
For all sufficiently large $x$ the direct integrand and these derivatives
are therefore bounded on the whole half-line by

$$
C_D(1+t)^7e^{-c_Dt/2}.
$$

This follows by choosing $4E\le c_D/2$ after applying the chain rule
to $e^F$. For fixed $t$, (W23) gives

$$
F=9Et-2\pi\cosh(2d)\frac{e^{2Et}-1}{E}
 +\sum_{s\in\{-1,1\}}[v(x+sd+Et)-v(x+sd)].
$$

The fraction extends smoothly to $E=0$, with value $2t$;
its first two $x$ derivatives tend to zero since
$\partial_x=-2E\partial_E$ on that factor. The remainder and its
first two derivatives vanish by (W23). Thus dominated convergence gives
$Q\to q_\infty$, uniformly with all mixed derivatives of total order
at most two, with zero limits for derivatives involving $x$.

For the reflected term put

$$
\mathscr H(x,z)=g(x+\sqrt z)+g(x-\sqrt z)\qquad(z\ge0).
$$

Its even square-root expression has continuous derivatives at $z=0$.
The integral divided-difference formula, for $j=1,2,3$, is

$$
\partial_z^j\mathscr H(x,z)
=\frac1{2^{2j-1}(j-1)!}
\int_{-1}^1(1-s^2)^{j-1}g^{(2j)}(x+s\sqrt z)\,ds.
$$

The case $j=1$ is the fundamental theorem of calculus;
differentiation and integration by parts give $j=2,3$ and their
endpoint limits. Differentiating also in $x$, (W23) gives

$$
|\partial_x^k\partial_z^j\mathscr H(x,z)|
\le C E^{-1}e^{2\sqrt z}
\qquad(2j+k\le6,\ x\ge1).
$$

There is a global favorable sign. For $z>0$,

$$
\mathscr H_z(x,z)
=\frac{g'(x+\sqrt z)-g'(x-\sqrt z)}{2\sqrt z}
\le-\frac12e^{2x}.
$$

Indeed global concavity bounds the integral of $g''$ from
$x-\sqrt z$ to $x$ by zero, and (W19) bounds its integral from
$x$ to $x+\sqrt z$ by $-e^{2x}\sqrt z$. Continuity handles $z=0$.
In particular this sign does not require $x-\sqrt z\ge0$.

Changing $y^2=d^2+Et$ in the original reflected integral gives exactly

$$
\begin{aligned}
B(x,d)&=\frac{e^{2x}K_0(a,-b)}{\Phi(a)\Phi(b)}
=\frac14\int_0^\infty e^{G(x,d,t)}\,dt,\\
G(x,d,t)&=\mathscr H(x,d^2+Et)-\mathscr H(x,d^2)\le-t/2.
\end{aligned}
$$

Write $G=Et\int_0^1\mathscr H_z(x,d^2+vEt)\,dv$.
Up to two mixed $x,d$ derivatives use only
$(j,k)=(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)$ above.
Each term retains $Et$, with at most two additional such factors;
$d$ derivatives contribute bounded factors $2d$ and $2$.
Since $\sqrt{d^2+vEt}\le D+\sqrt t$, these derivatives of $G$ are bounded by
$C_Dt(1+t)^2e^{2\sqrt t}$. Thus the reflected integrand and its
first two mixed derivatives have the integrable majorant

$$
C_D(1+t)^6e^{4\sqrt t-t/2}.
$$

Consequently $B$ and those derivatives are uniformly bounded, and
$B/x$ is $O_D(1/x)$ with all the required mixed derivatives.
This controls the full reflected exterior, including
$x-\sqrt{d^2+Et}<0$; no cutoff is introduced there.
The exact identity $T=Q-B/x$ now proves (W24).

Normalize by the actual diagonal, not a leading approximation:

$$
\begin{aligned}
r_x(d)&=\frac{L_0(x+d,x-d)}{\sqrt{J(x+d)J(x-d)}}\\
&=\frac{x}{\sqrt{x^2-d^2}}
\frac{T(x,d)}{\sqrt{T(x+d,0)T(x-d,0)}}.
\end{aligned}
$$

The mixed $x$ derivatives in (W24) control these shifted diagonal
factors. Since $T(u,0)\to1/(8\pi)>0$ and its first two $u$
derivatives tend to zero, it follows that

$$
\boxed{r_x\longrightarrow\operatorname{sech}(2d)
\quad\text{in }C^2([-D,D]),\qquad
r_x(0)=1,\quad r_x'(0)=0.}
\tag{W25}
$$

The last two equalities are exact, from normalization and symmetry.
They prevent an error independent of $d$ from obscuring the vanishing
near-diagonal margin.

Take $D=4$. Since $(\operatorname{sech}(2d))''|_{d=0}=-4$,
choose one $r\in(0,1)$ on which this derivative is at most $-2$.
For all sufficiently large $x$, (W25) then gives $r_x''\le-1$
on $[-r,r]$, whence

$$
0<r_x(d)\le1-d^2/2\qquad(|d|\le r).
$$

On $r\le|d|\le4$, uniform convergence gives
$0<r_x(d)\le(1+\operatorname{sech}(2r))/2<1$ after enlarging
the same threshold. Positivity here is (W12), reused.
For $|a-b|\ge8$, apply the already-owned two-position consumer of (W22).
Together these estimates supply one fixed $A\ge256$ such that

$$
\boxed{\begin{aligned}
\Delta(a,b)&:=J(a)J(b)-L_0(a,b)^2>0
&&\text{for all distinct }a,b\ge A,\\
\Delta(a,b)&\ge\frac{(a-b)^2}{8}J(a)J(b)
&&\text{if }a,b\ge A,\ |a-b|\le2r.
\end{aligned}}
\tag{W26}
$$

For the second line use
$1-r_x(d)^2\ge d^2-d^4/4\ge d^2/2$ with $a-b=2d$.
At $a=b$ the determinant is exactly zero. Neither $A$ nor $r$ is
numerically certified here.

This pays the high-position two-point estimate uniformly through
confluence. It does not prove positivity of dense higher-order Gram
matrices or arbitrary signed smooth profiles, and it supplies no
coupling to compact or omitted positions. The all-size result (W22)
retains its spacing restriction. Full physical positivity, the signed
Robin upper and RH remain unproved. No Jacobi-orbit or finite-curvature
identity alone is claimed to settle these outstanding estimates.

## The first actual core requires a joint correction estimate

The positive limiting $\operatorname{sech}$ kernel in (W25) does not
supply an order-uniform perturbation argument by itself. Its first
correction can be identified from the same complete physical source.
Classical Pick interpolation then excludes a finite relative lower bound
for that correction considered separately. This is a paper application of
existing interpolation theory, without a priority or Lean-verification
claim; it gives no negative minor of the actual theta kernel.

Fix a bounded nonempty open interval $I$ with
$\overline I\subset(0,\infty)$. For $u,v\in\overline I$ put
$a=A+u$, $b=A+v$, $x=(a+b)/2$, $d=(a-b)/2$ and $E=e^{-2x}$.
Define the positively congruent actual kernel and its two core terms by

$$
\begin{aligned}
\mathcal P_A(u,v)&=
 \frac{8\pi e^{a+b}L_0(a,b)}{\Phi(a)\Phi(b)},\\
S(u,v)&=\operatorname{sech}(u-v),\\
C(u,v)&=\frac{u+v}{2}\operatorname{sech}(u-v)
 -\frac{u-v}{2\sinh(u-v)}.
\end{aligned}
$$

The last quotient has its continuous diagonal value, so
$C(u,u)=u-1/2$. The source-specific expansion is

$$
\boxed{\mathcal P_A=A S+C+R_A,\qquad
 \|R_A\|_{C^2(\overline I^2)}\longrightarrow0
 \quad(A\to\infty).}
\tag{W27}
$$

The norm controls derivatives in the offsets $u,v$ of total order at
most two. To prove the stronger remainder needed here, reuse the exact
$Q,B,F,\mathscr H$ and the whole-half-line majorants from (W24).
They give $\mathcal P_A=8\pi(xQ-B)$ exactly. Set
$F_0=-4\pi t\cosh(2d)$. The exact expansion of $F$ in (W24),
Taylor's integral remainder for $e^{2Et}$ and (W23) imply, for fixed
$D>0$ and $m+n\le2$,

$$
\left|\partial_x^m\partial_d^n(F-F_0)\right|
\le C_D E t(1+t)^q e^{cEt}\qquad(|d|\le D)
$$

with fixed finite $q,c$, for all sufficiently large $x$.
For the logarithmic remainder in (W23), express its shift by $Et$ as
an integral of its first derivative; its first two mixed derivatives
are covered by the same bounds. Both $F$ and $F_0$ are at most
$-c_Dt$, where $c_D=2e^{-2D}$. The identity

$$
e^F-e^{F_0}=(F-F_0)\int_0^1e^{(1-s)F_0+sF}\,ds
$$

and its first two mixed derivatives are consequently bounded by
$C_D E(1+t)^{q'}e^{c'Et-c_Dt}$ for fixed finite $q',c'$.
Taking $c'E\le c_D/2$ gives an integrable bound proportional to $E$.
The factor $Et/x$ and its derivatives contribute $O_D(E)$ as well.
Thus, with $q_\infty$ as in (W24),

$$
\max_{m+n\le2}\sup_{|d|\le D}
\left|\partial_x^m\partial_d^n(Q-q_\infty(d))\right|
=O_D(E).
$$

In particular $x(Q-q_\infty)$ and these mixed derivatives tend to zero.
For the reflected term let $h(z)=\cosh(2\sqrt z)$, analytic at zero.
On bounded $t,d$ sets, its exact exponent is

$$
\mathscr H(x,d^2+Et)-\mathscr H(x,d^2)
=-2\pi\frac{h(d^2+Et)-h(d^2)}E
 +\text{the logarithmic remainder difference}.
$$

The quotient extends smoothly to $E=0$. It converges with two $d$
derivatives to $t h'(d^2)=t\sinh(2d)/d$; derivatives involving $x$
tend to zero, using $\partial_x=-2E\partial_E$ on this quotient.
The differentiated remainder differences tend to zero by (W23).
At $d=0$, $\sinh(2d)/d$ has value $2$.
The already established global reflected majorant
$C_D(1+t)^6e^{4\sqrt t-t/2}$ permits mixed dominated differentiation,
including the entire exterior where $x-\sqrt{d^2+Et}<0$. It gives

$$
B(x,d)\longrightarrow\frac{d}{8\pi\sinh(2d)}
$$

with two $d$ derivatives and vanishing derivatives involving $x$.
The value at $d=0$ is $1/(16\pi)$. Therefore
$8\pi(xQ-B)=x\operatorname{sech}(2d)-d/\sinh(2d)+o_{C^2}(1)$;
the linear change to $u,v$ proves (W27).

For the obstruction, reuse classical Pick interpolation as cited above
in McCarthy, Theorem 1, printed p.36. The related anti-Löwner theory is
[Audenaert, *A Characterisation of Anti-Löwner Functions*,
Theorem 2.1](https://doi.org/10.1090/S0002-9939-2011-10935-3),
[arXiv:1008.2943v2](https://arxiv.org/abs/1008.2943v2).
Its finite-order transfer requires order $2N$ for an order-$N$
conclusion; its whole-positive-axis integral representation is not a
representation on an arbitrary subinterval. Neither extension is assumed
here. The needed consequence follows directly from Pick interpolation.

On any nonempty open $J\subset(1,\infty)$, the kernel

$$
K_{\log}(z,w)=\frac{\log z+\log w}{z+w}
$$

cannot be positive semidefinite on all finite subsets. Indeed the
Cayley data $\lambda(z)=(z-1)/(z+1)$ and
$\tau(z)=(\log z-1)/(\log z+1)$ lie in $(-1,1)$. Their disk Pick
matrix is congruent to $K_{\log}$ by the positive diagonal factors
$(z+1)/(\log z+1)$. If all finite matrices were positive semidefinite,
choose distinct $z_n\in J$ accumulating at an interior point of $J$.
Pick's theorem supplies analytic disk-valued interpolants of each first
$N$ data. A normal-family subsequence converges locally uniformly to a
Schur function with every datum. Its first retained value lies strictly
inside the disk, so the maximum principle excludes a boundary constant.
Undoing both Cayley maps gives a holomorphic positive-real function
$F$ on $\operatorname{Re}z>0$ with $F(z_n)=\log z_n$.
The identity theorem forces $F=\operatorname{Log}$ on that half-plane,
contradicting $\operatorname{Log}(1/2)<0$. Thus some finite real sample
has a negative quadratic direction. This uses a classical theorem;
it is not a new general positivity criterion.

Write the unshifted first core as

$$
G(a,b)=\frac{a+b}{2}\operatorname{sech}(a-b)
 -\frac{a-b}{2\sinh(a-b)}.
$$

For $z_i=e^{2a_i}$ and $D=\operatorname{diag}(\sqrt{z_i})$,
exact algebra gives

$$
\boxed{[G(a_i,a_j)]=\frac12D[K_{\log}(z_i,z_j)
 -L_{\log}(z_i,z_j)]D,\qquad
L_{\log}(z,w)=\int_0^\infty\frac{dt}{(z+t)(w+t)}.}
\tag{W28}
$$

Here $L_{\log}=(\log z-\log w)/(z-w)$, including its continuous
diagonal, is positive semidefinite by this classical integral formula.
Subtracting it preserves a negative direction of $K_{\log}$, and
positive diagonal congruence transports that direction. Consequently
**every** nonempty open interval of positions $a>1$ contains a finite
sample on which $G$ is indefinite: it has a negative direction, whereas
$G(a,a)=a-1/2>0$. The statement is existential in the finite sample;
it does not assert that every finite sample is indefinite.

Finally $G(A+u,A+v)=A S(u,v)+C(u,v)$ exactly. On distinct nodes $S$
is strictly positive definite, since

$$
S(u,v)=\frac{2e^{u+v}}{e^{2u}+e^{2v}}
$$

is a positive diagonal congruence of the Cauchy kernel. Its integral
representation is a Gram matrix of linearly independent exponentials.
For every $M>0$ choose $A>\max(M,1)$. A negative direction for the
core on $A+I$ then gives

$$
\boxed{\text{for every }M>0\text{ there exist distinct }u_1,\ldots,u_N\in I
\text{ and }c\in\mathbb R^N\setminus\{0\}\text{ such that }
 c^{\mathsf T}C c<-M c^{\mathsf T}S c.}
\tag{W29}
$$

Thus no finite $b_I$ provides $C\succeq-b_I S$ uniformly over all
finite samples and their densities. This excludes estimating that
first correction separately in this reference form. It does **not**
exclude a source-specific joint lower bound for $C+R_A$.
If the actual $\mathcal P_A$ were positive semidefinite, the remainder
would have to satisfy
$c^{\mathsf T}R_Ac\ge-c^{\mathsf T}(A S+C)c$ on every negative core
direction. Convergence in $C^2$ in (W27) gives no order-uniform bound in
the $S$ form and does not exclude such cancellations.
The remaining target is the joint actual form, with the complete
reflected contribution and all finite coefficient vectors retained.
Neither an actual negative theta minor, full physical positivity, the
signed Robin upper nor RH is established by this core obstruction.

## A joint bound for high-window profiles with one sign change

The complete actual kernel permits an order-uniform comparison on a
restricted signed cone. Reuse (W12), the actual mixed $C^2$ limit (W24),
and the exact diagonal $J$. No positivity of the first correction $C$
in (W27) is assumed. The rectangle argument below is classical
log-supermodularity reasoning, applied to the actual kernel; it is not
an integration-closure claim about its triangular integrand support or
a new general positivity criterion. No literature-priority or
Lean-verification claim is made.

Write

$$
R(a,b)=\frac{L_0(a,b)}{\sqrt{J(a)J(b)}}\qquad(a,b>0).
$$

This is smooth, symmetric and strictly positive, with $R(a,a)=1$.
Fix a width $W>0$ and set $\kappa_W=\tfrac12\operatorname{sech}^2W$.
There is one existential $A_W$ such that

$$
\boxed{\partial_a\partial_b\log R(a,b)\ge\kappa_W>0
\quad\text{on }[c,c+W]^2\text{ for every }c\ge A_W.}
\tag{W30}
$$

Indeed, in the exact coordinates $x=(a+b)/2$, $d=(a-b)/2$,

$$
\partial_a\partial_b\log R(a,b)
=-\frac1{4x^2}
 +\frac14\left(\partial_x^2\log T(x,d)
                    -\partial_d^2\log T(x,d)\right).
$$

The factors $\Phi(a)$, $\Phi(b)$ and the diagonal normalizers have
zero mixed logarithmic derivative. For $|d|\le W/2$, (W24) makes the
right side converge uniformly to $\operatorname{sech}^2(2d)$, whose
minimum is $\operatorname{sech}^2W$. This proves (W30) after increasing
the same threshold. The complete reflected exterior remains included
through (W24); no numerical value of $A_W$ is asserted.

Fix such a window and a separator $s\in[c,c+W]$, and put
$r(a)=R(a,s)>0$. Integrate the mixed logarithmic derivative over the
rectangle from $(s,s)$ to $(a,b)$. Since $R(s,s)=1$, the result is

$$
\boxed{\begin{aligned}
R(a,b)&\ge r(a)r(b)
 \bigl(1+\kappa_W|a-s||b-s|\bigr)
 &&\text{if }a,b\text{ lie on the same side of }s,\\
R(a,b)&\le r(a)r(b)e^{-\kappa_W(s-a)(b-s)}
 \le r(a)r(b)
 &&\text{if }a\le s\le b.
\end{aligned}}
\tag{W31}
$$

For the first line the logarithmic rectangle increment is at least
$\kappa_W|a-s||b-s|$, and $e^t\ge1+t$.
For the second line one integration orientation is reversed, so that
increment is at most $-\kappa_W(s-a)(b-s)$.
These are simultaneous comparisons of the same actual $R$ and $s$.
They do not combine independently attainable extremal values.

Let $\mu$ be any finite nonzero real signed measure on this window
with at most one sign change. After multiplying by an overall minus
sign if needed, this means that its Jordan parts satisfy

$$
\operatorname{supp}\mu_+\subset[c,s],\qquad
\operatorname{supp}\mu_-\subset[s,c+W]
$$

for some separator $s$. Either part may vanish. Set
$d\nu_\pm=\sqrt J\,d\mu_\pm$ and define the nonnegative quantities

$$
\begin{aligned}
U&=\int r(a)\,d\nu_+(a),&
V&=\int r(b)\,d\nu_-(b),\\
D_+&=\int(s-a)r(a)\,d\nu_+(a),&
D_-&=\int(b-s)r(b)\,d\nu_-(b).
\end{aligned}
$$

All integrals are finite on the fixed compact window. The full joint
estimate is

$$
\boxed{\iint L_0(a,b)\,d\mu(a)d\mu(b)
\ge (U-V)^2+\kappa_W(D_+^2+D_-^2)>0.}
\tag{W32}
$$

To prove it, express the left side with kernel $R$ and signed measure
$\nu_+-\nu_-$. Apply the two within-side lower bounds in (W31) to
its positive blocks. Apply the opposite-side upper bound to its cross
block, which has a negative coefficient. The resulting bound is
$U^2+V^2-2UV+\kappa_W(D_+^2+D_-^2)$, retaining all cross terms.
If this were zero, $D_+=D_-=0$ and $r>0$ would force both Jordan
parts to be supported at the single point $s$. Their mutual singularity
allows at most one nonzero mass there; $U=V$ then forces both to vanish.
This contradicts $\mu\ne0$ and also covers atoms at the separator.

In particular (W32) applies to every nonzero finite sampled measure
$\mu=\sum_i c_i\delta_{a_i}$, after merging repeated nodes, with real
coefficients that change sign at most once in the ordered positions.
The threshold and $\kappa_W$ are independent of sample count,
spacing and coefficients. Thus arbitrarily dense samples are included.
It also applies directly to every nonzero real smooth density $h(a)da$
with the same support and sign condition. The odd physical test with
positive-half-line profile $h$ has the exact full quadratic form

$$
\iint_{\mathbb R^2}K_0(a,b)f(a)f(b)\,da\,db
=2\iint_{(0,\infty)^2}L_0(a,b)h(a)h(b)\,da\,db>0.
$$

This is a restricted signed-profile result in addition to the
one-signed cone (W14). It does not assert positivity on the linear
span of the admitted profiles: adding such profiles can introduce
further sign changes. The estimate uses the actual diagonal weights;
it gives no unweighted spectral gap. The threshold may depend on $W$.
Arbitrary sign patterns, arbitrary complex coefficients, compact
positions and coupling to omitted positions remain uncontrolled.
No bound for the separated correction $C$ is extracted, and the result
is compatible with (W29). Full physical positivity, the strict Robin
upper and RH remain unproved.


## A joint moment bound for every fixed finite sign count

The actual source permits more than the one-change comparison (W32).
For each fixed window width and each fixed finite sign count, the
following argument pays complete sampled and smooth signed quadratic
forms, with no restriction on the number or spacing of sampled nodes.
For general measures the explicit polynomial-sign condition below is
the contract; repeated roots include isolated signed atoms. The height
threshold may depend on both width and sign count. The classical Cauchy
determinant, Newton divided differences and finite Schur determinant
are reused inside this source-specific application; no new general
criterion, literature-priority claim or Lean verification is asserted.

### Keep every fixed derivative order in the complete source limit

The theta-series argument for (W23) works through any prescribed finite
order $N$. The differentiated summand majorant remains
$C_k(1+y)^km^{4+2k}e^{-(m^2-1)y}$ for $k\le N$; the summable tail
leaves a polynomial times $e^{-3y}$. Consequently, for each fixed $N$,

$$
g(u)=\log(4\pi^2)+\tfrac92u-\pi e^{2u}+v(u),\qquad
|v^{(k)}(u)|\le C_Ne^{-2u}\quad(u\ge1,\ k\le N),
$$

and $|g^{(k)}(u)|\le C_Ne^{2|u|}$ for $1\le k\le N$ on the whole
real line. This extends derivative bounds, not all-order Laguerre signs.

Fix an integer $r\ge0$ and $D>0$, and use $N=2r+2$. Retain exactly the complete
direct and reflected integrals $Q,B$ in the proof of (W24), with
$E=e^{-2x}$ and $T=Q-B/x$. In

$$
F=Et\sum_{s\in\{-1,1\}}\int_0^1g'(x+sd+vEt)\,dv,
$$

every mixed derivative through total order $r$ retains the factor
$Et$. The bounds above give
$C_{r,D}t(1+t)^re^{2Et}$. Together with $F\le-c_Dt$, the chain rule
supplies an integrable majorant
$C_{r,D}(1+t)^{M_r}e^{-c_Dt/2}$ once $x$ is sufficiently large.
The leading expression displayed in (W24) converges with all these
fixed-order derivatives; its $x$ derivatives vanish.

For the reflected term, the same even divided-difference identity
extends to every fixed $j\ge1$:

$$
\partial_z^j\mathscr H(x,z)=
\frac1{2^{2j-1}(j-1)!}
\int_{-1}^1(1-s^2)^{j-1}g^{(2j)}(x+s\sqrt z)\,ds.
$$

Integration by parts gives the identity inductively, including its
continuous value at $z=0$. Derivatives of
$G=Et\int_0^1\mathscr H_z(x,d^2+vEt)\,dv$
through order $r$ use only $2j+k\le2r+2$. They are bounded by
$C_{r,D}t(1+t)^re^{2\sqrt t}$. The same global favorable sign
$G\le-t/2$ therefore gives the integrable majorant
$C_{r,D}(1+t)^{M'_r}e^{2r\sqrt t-t/2}$. Thus $B$ has bounded
fixed-order derivatives and $B/x$ has derivatives $O_{r,D}(1/x)$.
The entire reflected exterior remains included.

Dominated convergence and the exact diagonal normalization of (W25)
now give, for every fixed finite $r$ and $W>0$,

$$
\boxed{K_A(u,v):=R(A+u,A+v)
\longrightarrow S(u,v):=\operatorname{sech}(u-v)
\quad\text{in total-order }C^r([0,W]^2).}
\tag{W33}
$$

Constants and thresholds may depend on $r,W$; there is no simultaneous
uniform assertion over derivative orders.

### Pay arbitrary confluence before taking the signed form

For distinct row and column nodes define

$$
V(u)=\prod_{i<j}(u_j-u_i),\qquad
\mathcal Q_n(K;u,v)=\frac{\det[K(u_i,v_j)]}{V(u)V(v)}.
$$

Newton row and column operations express this quotient as the
determinant of the array of bivariate divided differences with nested
prefixes of nodes. Its $(i,j)$ entry uses derivatives through orders
$i-1,j-1$. The classical integral formula in de Boor,
[*Divided Differences*, arXiv:math/0502036v1](https://arxiv.org/pdf/math/0502036v1),
equation (52), printed p.64, supplies the continuous confluent
extension and the uniform bound by the corresponding derivative norm
divided by $(i-1)!(j-1)!$. Therefore (W33) through order $2n-2$
gives uniform convergence of $\mathcal Q_n$ on the entire closed
ordered node simplexes, including coinciding boundary nodes.

The classical Cauchy determinant gives

$$
\mathcal Q_n(S;u,v)=
\frac{2^ne^{\sum_i u_i+\sum_j v_j}}
 {\prod_{i,j}(e^{2u_i}+e^{2v_j})}
\prod_{i<j}
\frac{e^{2u_j}-e^{2u_i}}{u_j-u_i}
\frac{e^{2v_j}-e^{2v_i}}{v_j-v_i}.
$$

On $[0,W]$, each difference quotient lies in $[2,2e^{2W}]$, also at
coincidence. Hence
$e^{-2n^2W}\le\mathcal Q_n(S;u,v)\le e^{2n^2W}$.
Fix an integer $m\ge1$. Taking the maximum of the finitely many
thresholds for $n\le m+1$ gives one $A_{W,m}$ such that, on every
physical window $[c,c+W]$ with $c\ge A_{W,m}$,

$$
\boxed{\tfrac12e^{-2n^2W}\le\mathcal Q_n(R;u,v)
\le2e^{2n^2W}\qquad(1\le n\le m+1).}
\tag{W34}
$$

Physical nodes are shifted by $c$ when applying (W33); Vandermonde
differences are unchanged. Permuting distinct row or column nodes
leaves their determinant quotient unchanged. The threshold in (W34)
is independent of node separation; this is stronger than convergence
at separately fixed distinct tuples.

### The sign separators pay all cross terms together

Fix a multiset $s_1\le\cdots\le s_r$ of separators in the same window,
with $1\le r\le m$. Write its distinct sites as $t_1<\cdots<t_d$,
with multiplicities $k_1+\cdots+k_d=r$, and put

$$
p(a)=\prod_{j=1}^r(a-s_j)=\prod_{\alpha=1}^d(a-t_\alpha)^{k_\alpha}.
$$

Use the normalized actual Hermite anchors, indexed first by site and
then by $0\le i<k_\alpha$:

$$
\begin{aligned}
h_{\alpha,i}(a)&=\frac{\partial_1^iR(t_\alpha,a)}{i!},\\
E_{(\alpha,i),(\beta,j)}
 &=\frac{\partial_1^i\partial_2^jR(t_\alpha,t_\beta)}{i!j!}.
\end{aligned}
$$

Let $D(s)=\prod_{\alpha<\beta}
(t_\beta-t_\alpha)^{k_\alpha k_\beta}>0$, with empty product one.
Coalescing the distinct nodes after within-cluster Newton operations
gives $\det E=D(s)^2\mathcal Q_r(R;s,s)$. Normalized jets are the
limits of these divided differences, so no additional factorials
occur. Each leading principal minor has the same formula for its
truncated site/multiplicity list. It is positive by (W34); hence $E$
is positive definite by Sylvester's criterion.

The exact Schur residual is

$$
B_s(a,b)=R(a,b)-h(a)^TE^{-1}h(b).
$$

Apply the same within-cluster operations to the bordered determinant,
leaving its final row and column unchanged. For $a,b$ off the sites,
its limit is $D(s)^2p(a)p(b)
\mathcal Q_{r+1}(R;(s,a),(s,b))$. Division by $\det E$ gives

$$
\boxed{B_s(a,b)=p(a)p(b)
\frac{\mathcal Q_{r+1}(R;(s,a),(s,b))}
 {\mathcal Q_r(R;s,s)}.}
\tag{W35}
$$

The derivatives used have total order at most $2r\le2m$, already
covered by (W33)--(W34). Directly,
$h(t_\alpha)=Ee_{\alpha,0}$, so the residual vanishes when either
argument is a separator site. Off the sites, (W34) gives
$\operatorname{sgn}(p(a)p(b))B_s(a,b)\ge c_{W,r}|p(a)p(b)|$, where

$$
c_{W,r}=\tfrac14e^{-2W((r+1)^2+r^2)}>0.
$$

Let $\mu$ be a finite nonzero real signed measure in this window and
suppose that $\epsilon p\mu$ is a nonnegative measure for some
$\epsilon\in\{-1,1\}$. Off the separators this says its signs
follow those of $\epsilon p$; atoms at its roots may have either sign. Repeated
roots are allowed: positive continuous mass minus an interior negative
atom at $t$ is covered by $p(a)=(a-t)^2$. This explicit condition
avoids relying on an unstated convention for sign variation of general
measures. Sampled or smooth profiles with fewer changes use fewer
separators; one-signed measures are already covered by (W14). Set

$$
d\nu=\sqrt J\,d\mu,\qquad z=\int h(a)\,d\nu(a).
$$

The exact decomposition and full joint lower bound are

$$
\boxed{\begin{aligned}
\iint L_0(a,b)\,d\mu(a)d\mu(b)
&=z^TE^{-1}z+\iint B_s(a,b)\,d\nu(a)d\nu(b)\\
&\ge z^TE^{-1}z+
 c_{W,r}\left(\int|p(a)|\,d|\nu|(a)\right)^2>0.
\end{aligned}}
\tag{W36}
$$

Indeed $\nu$ has sign $\epsilon\operatorname{sgn}p$ away from the
separators, so (W35) controls the complete residual integral, including
every cross block. If its displayed moment is positive, strictness is
immediate. If it is zero, $\nu=\sum_\alpha b_\alpha\delta_{t_\alpha}$.
Let $\widetilde b_{\alpha,0}=b_\alpha$ and set its higher jet
entries to zero. Then $z=E\widetilde b$ and
$z^TE^{-1}z=\widetilde b^TE\widetilde b>0$ since $\nu\ne0$.
The jets are observation functions; no derivative distributions have
been substituted for the finite measure. All integrals are finite on
the compact window; no source or independent extremal configuration
is substituted.

For each fixed $m$, this includes nonzero real sampled measures with
arbitrarily many nodes and at most $m$ sign changes, after merging
repeated nodes. It also includes real smooth densities with the same
support and sign condition. Their odd physical tests have the full
$K_0$ form equal to twice (W36). The estimate pays their full joint
form, rather than merely asserting positivity of each sign block.

The threshold depends on $m$ and $W$. There is no single threshold
covering unrestricted sign patterns, no positivity assertion for the
linear span of these cones, and no arbitrary complex-measure or
unweighted-gap claim. Compact positions and coupling to omitted
positions remain uncontrolled. Full physical positivity, the strict
all-integer Robin upper and RH remain unproved.


## Analytic transport from one complete odd window

For the actual complete kernel, all-order odd positivity on one physical
open interval is already a sufficient target for zero exclusion. The
application below transports that local hypothesis through the original
kernel; it does not prove the hypothesis. In this sufficient route a
separate comparison with compact or omitted positions is unnecessary.
The all-order requirement remains, and no finite collection of minors or
fixed sign-count bounds supplies it.

The general transport is existing mathematics: Danciger and
Rubinstein-Salzedo,
[*A Hilbert Space Approach to Bounded Analytic Interpolation*,
Theorem 4, printed p.526](https://doi.org/10.1007/s11785-007-0029-7)
([authors' published text](https://simonrs.com/AnalyticInterpolation.pdf)).
It states that a sesquianalytic kernel on $D\times D$, where
$D\subseteq\mathbb C^d$ is connected and open, is positive semidefinite
on all of $D\times D$ if it is positive semidefinite on $S\times S$;
here $S$ is a uniqueness set for a relatively compact subdomain
$D'\Subset D$. Its kernel definition uses every finite node set and
all complex coefficients. This theorem is directly reused, without a
new general extension theorem or a literature-priority claim.

### The full integral has a common complex strip

Fix $0<\eta<\pi/4$ and put
$D_\eta=\{z\in\mathbb C:|\Im z|<\eta\}$. The original theta series
for $\Phi$ converges normally there. On every closed smaller strip its
positive-real tail obeys

$$
|\Phi(u+iv)|\le C_\eta e^{9u/2}
  \exp(-c_\eta e^{2u})\qquad(u\ge0,\ |v|\le\eta),
\tag{W37}
$$

with positive constants, enlarging the containing strip within
$|\Im z|<\pi/4$ when needed. Indeed each summand is bounded using
$\Re e^{2(u+iv)}\ge e^{2u}\cos(2\eta)>0$; its $n^4$ polynomial is
summable against this same Gaussian tail. Evenness extends to the strip
by the identity theorem. Thus the tail bound also pays complex shifts in
compact sets.

For complex $a,b\in D_\eta$, keep $p=(a+b)/2$, $d=(a-b)/2$ and define

$$
\begin{aligned}
\mathcal T(d)&=\int_0^\infty
 y\Phi(y+d)\Phi(y-d)\,dy,\\
\mathcal U(p,d)&=p^2\int_0^1
 t\Phi(tp+d)\Phi(tp-d)\,dt,\\
\widetilde K_0(a,b)&=\tfrac12[\mathcal T(d)-\mathcal U(p,d)],\\
\widetilde L_0(a,b)&=\widetilde K_0(a,b)-\widetilde K_0(a,-b).
\end{aligned}
\tag{W38}
$$

The infinite integral is locally uniformly dominated by (W37).
For $0\le t\le1$,
$|\Im(tp\pm d)|\le|\Im p|+|\Im d|
=\max(|\Im a|,|\Im b|)<\eta$.
Hence the finite integral stays in the same strip and (W38) is jointly
holomorphic. On the real axis,
$y\Phi(y+d)\Phi(y-d)$ is odd in $y$, so its integral from $0$ to
$p$ is even in $p$. Consequently (W38) agrees exactly with the
$|p|$ lower limit in (W2). The complete reflected exterior remains
included. The identities of symmetry, reality and oddness extend from
the real axis; in particular
$\mathcal L(z,w)=\widetilde L_0(z,\overline w)$ is a Hermitian
sesquiholomorphic kernel on $D_\eta\times D_\eta$.

Suppose now that, on one nonempty open $I\subset(0,\infty)$,
$[L_0(a_i,a_j)]$ is positive semidefinite for every finite real sample
in $I$. Real and complex coefficients give the same positivity condition
for these real symmetric matrices. Choose $D'$ to be a small disk
centered at a point of $I$, with closure in $D_\eta$, and take $S$ to
be a nonempty real subinterval of $I\cap D'$. It is a uniqueness set
for $D'$. Apply the cited Theorem 4 directly to $\mathcal L$.
It follows that $L_0$ is positive semidefinite on the whole real axis.
No derivative-germ extension argument is required.

### The odd sector alone detects every off-real zero

Reuse the complete Fourier interface (W7) and its exponential-moment
cutoff argument. Both sides extend to arbitrary complex frequencies:
the numerator's vanishing at $\overline w=z$ removes that quotient
singularity. Define the odd projection

$$
\begin{aligned}
\mathcal B_{\rm odd}(w,z)
&=\tfrac12[\mathcal B(w,z)-\mathcal B(-w,z)]\\
&=\frac2\pi\int_{\mathbb R^2}L_0(a,b)
 e^{iza-i\overline w b}\,da\,db.
\end{aligned}
$$

Global $L_0$ positivity makes this kernel positive semidefinite on every
finite set of complex frequencies. One first uses compact cutoffs and
finite-sum approximation, then removes the cutoffs by the already owned
full exponential moments. Physical strip coordinates and complex Fourier
frequencies have different domains; the latter are unrestricted here.

Since $F$ is even and entire, write $F(z)=H(z^2)$ with $H$ entire and
real on the real axis; no global square-root branch is selected. Exact
substitution into (W7) gives

$$
\begin{aligned}
\mathcal D_H(U,V)&=
\frac{H'(V)\overline{H(U)}-H(V)\overline{H'(U)}}
 {\overline U-V},\\
\mathcal B_{\rm odd}(w,z)&=
\frac{2z\overline w}{\pi}\mathcal D_H(w^2,z^2).
\end{aligned}
\tag{W39}
$$

For $Z=z^2$ with $\Im Z>0$ and $H(Z)\ne0$, positivity implies

$$
0\le\mathcal D_H(Z,Z)
=-\frac{|H(Z)|^2}{\Im Z}\Im\frac{H'(Z)}{H(Z)}.
$$

If $H$ had a $k$-fold zero $\lambda$ in that half-plane,
$H'(\lambda-i\epsilon)/H(\lambda-i\epsilon)
=ik/\epsilon+O(1)$ as $\epsilon\downarrow0$. For sufficiently small
positive $\epsilon$, $Z=\lambda-i\epsilon$ remains in the half-plane
and is not a zero, and the displayed diagonal is negative. Conjugation
excludes lower-half-plane zeros as well. This argument never assumes
zero-free holomorphy of $H'/H$ on the half-plane in advance.

Thus every zero of $H$ would be real. The original positive density also
supplies $F(iy)=\int_{\mathbb R}\Phi(x)e^{-yx}dx>0$ for every real
$y$. Hence $H$ has no nonpositive real zero, and every zero of the actual
$F$ is real. With the fixed $\Xi$ normalization already used in (W7),
this gives the source-specific sufficient implication

$$
\boxed{\begin{gathered}
\text{complete }L_0\text{ PSD on all finite samples in one nonempty}\\
\text{open positive interval}\quad\Longrightarrow\quad\mathrm{RH}.
\end{gathered}}
\tag{W40}
$$

The compact/exterior transport in this implication is paid by (W37)--(W39)
and the existing analytic-kernel theorem. Neither local positivity,
unrestricted actual-kernel PSD, the even sector, the strict all-integer
Robin upper nor RH has been established. No identity with Suzuki's
localized Weil operator or its small-support theorem is assumed. These
are reviewed paper interfaces, not a new general criterion or Lean
verification.

In particular, (W34)--(W36) retain the quantifiers
$\forall m\,\exists A_{W,m}$; they do not supply the single-window
all-order premise in (W40). Conditionally on RH failing, every nonempty
open positive interval must contain a finite real sample with a negative
$L_0$ quadratic direction. On a width-$W$ window above $A_{W,m}$, any
such direction has more than $m$ sign changes after merging nodes.
This is the contrapositive of (W40) combined with (W36), not a located
negative theta sample or a new positivity estimate. The unpaid target
is all-order positivity of the complete actual odd kernel on one fixed
open interval, or the original same-source signed Robin upper.


## Sufficiently large theta cutoffs fail as direct PSD references

Every sufficiently large finite theta cutoff fails to supply an all-order
positive direct reference for the shifted-theta frame, even when it keeps
every center correction. This obstruction is distinct from truncating the large-center
expansion in (W27). It concerns the finite-sum direct kernel itself;
compensated truncations and the full direct-minus-reflected estimate
remain separate possibilities.

Use the original normalization $\Phi(x)=2K(x/2)$ and define

$$
\begin{aligned}
\Phi_N(x)&=\sum_{n=1}^N2\pi n^2(2\pi n^2e^{2x}-3)
 e^{5x/2-\pi n^2e^{2x}},\\
D_N(a,b)&=\frac12\int_0^\infty
 \left(t+\frac{a+b}{2}\right)\Phi_N(t+a)\Phi_N(t+b)\,dt.
\end{aligned}
\tag{W41}
$$

The finite sum is not even; no evenization is made. For positive real
$a,b$, substituting $y=t+(a+b)/2$ shows that $D_N$ is exactly the
direct kernel (W2) with $v=0$ and $\Phi$ replaced by $\Phi_N$.
For $a,b\in D_\eta$, $0<\eta<\pi/4$, the same formula defines a
symmetric jointly holomorphic kernel: its positive-real tail is locally
uniformly integrable since $\cos(2\eta)>0$. Thus
$D_N(z,\overline w)$ is Hermitian and sesquiholomorphic. At negative
positions this forward integral need not agree with the finite-sum
$|p|$-cutoff formula; it is the analytic continuation used below.

Let

$$
C_+=\int_0^\infty x\Phi(x)^2\,dx<\infty,
\qquad c_* =\frac{4\pi}{3e^6}>0.
$$

On $x\ge0$ every theta summand is positive, so
$0<\Phi_N(x)\le\Phi(x)$. On the interval
$x=-\log N-h$, $1\le h\le2$, all the first $N$ summands are negative:
$n^2e^{2x}\le e^{-2}$, $2\pi e^{-2}<1$ and $\pi e^{-2}<1$.
Consequently

$$
\begin{aligned}
-\Phi_N(-\log N-h)
&\ge\frac{4\pi}{e}N^{-5/2}e^{-5h/2}\sum_{n=1}^Nn^2\\
&\ge\frac{4\pi}{3e}\sqrt N\,e^{-5h/2}
 \ge c_*\sqrt N.
\end{aligned}
\tag{W42}
$$

For each finite $N$, the negative tail is $O_N(e^{5x/2})$ and the
positive tail is superexponential. The signed first moment exists and
satisfies

$$
\boxed{m_N:=\int_{\mathbb R}x\Phi_N(x)^2\,dx
 \le C_+-c_*^2N(\log N+1)\longrightarrow-\infty.}
\tag{W43}
$$

Indeed the positive half-line contributes at most $C_+$; the
length-one interval in (W42) contributes at most
$-c_*^2N(\log N+1)$, and the remaining negative half-line contributes
nonpositively. In particular $m_N<0$ for every sufficiently large
$N$; no assertion for every small cutoff is needed.

The analytically continued diagonal obeys

$$
D_N(a,a)=\frac12\int_a^\infty y\Phi_N(y)^2\,dy
 \longrightarrow\frac{m_N}{2}\qquad(a\to-\infty).
$$

For every $N$ with $m_N<0$, some finite negative $a$ therefore has
$D_N(a,a)<0$. If $D_N$ were positive semidefinite on all finite samples
in any nonempty positive open interval, the already cited
Danciger--Rubinstein-Salzedo Theorem 4, with the strip, compact disk and
real uniqueness interval used above, would propagate this property to
the whole real axis. The negative diagonal is a contradiction. Hence

$$
\boxed{\begin{gathered}
\text{For every sufficiently large finite }N\text{ and every nonempty}\\
I\subset(0,\infty)\text{ open, some finite real sample in }I\\
\text{has a strictly negative }D_N\text{ quadratic direction.}
\end{gathered}}
\tag{W44}
$$

Repeated nodes can be merged, and the real symmetric matrix supplies
real coefficients. This is an existential statement; no witness size,
location or cutoff threshold is claimed. The general propagation
theorem is reused directly, without a new criterion or priority claim.

Nevertheless $D_N\to K_0$ on every fixed compact real square with
every fixed finite derivative order. Normal convergence of the theta
series and the common complex-shift tail bound give locally uniform
convergence of the integrals; Cauchy estimates give these derivatives.
For complete even $\Phi$, the forward integral agrees with $K_0$
also at negative positions, since its integrand in $y$ is odd and its
primitive is even. Evenness also gives
$\int_{\mathbb R}y\Phi(y)^2\,dy=0$. Thus the iterated diagonal
limits differ:

$$
\lim_{N\to\infty}\lim_{a\to-\infty}D_N(a,a)=-\infty,
\qquad
\lim_{a\to-\infty}\lim_{N\to\infty}D_N(a,a)=0.
\tag{W45}
$$

The finite sums carry square mass toward $-\log N$, contributing
negatively to the signed first moment.
Local accuracy of the full finite-cutoff direct integral therefore does
not make that integral a positive reference at all orders, even on a
high positive window. This rules out certifying $D_N$ itself as such a
reference for sufficiently large cutoffs; it does not rule out using a
truncation with rigorously paid compensating terms. No negative sample
of the complete actual $K_0$, the actual odd $L_0$, or a truncated odd
difference is inferred. The joint omitted-theta and reflected estimate,
local all-order odd positivity, the signed Robin upper and RH remain
unproved. These are paper-level source applications, without Lean
verification or a literature-priority claim.

## An all-order remainder allowance in an independent moment metric

Retain the complete physical $L_0$ and the positive congruence
$\mathcal P_A$ of (W27). A fixed complex neighborhood supplies a
quantitative allowance for every real signed profile at once. The
allowance uses an independently specified positive metric; it does not
establish positivity in the original form. This is a source-specific
paper derivation using classical Cauchy estimates, without a
literature-priority or Lean-verification claim.

Put $M_A=\mathcal P_A/A$ and $S(u,v)=\operatorname{sech}(u-v)$.
There exist fixed $r,C,A_0>0$ such that $M_A$ is holomorphic on a
neighborhood of $\{|u|,|v|\le r\}$ and

$$
\boxed{\sup_{|u|,|v|\le r}|M_A(u,v)-S(u,v)|\le C/A
\qquad(A\ge A_0).}
\tag{W46}
$$

Here $A$ is real; the offsets in this bound are complex. For real
$u,v$, $M_A=D_A L_0 D_A$ with
$D_A(u)=\sqrt{8\pi/A}\,e^{A+u}/\Phi(A+u)>0$.
The constants and the neighborhood are independent of sampling order.

To pay the complex estimate, first reuse the actual series in (W23)
and its normal convergence in (W37). On a smaller closed strip its
right tail is

$$
\Phi(z)=4\pi^2e^{9z/2-\pi e^{2z}}
 \bigl(1+O(e^{-2\Re z})\bigr).
$$

The leading factor is nonzero. Evenness pays the left tail, and
positivity on the real axis plus compactness pays the remaining middle.
Thus $\Phi$, rather than $\xi$, is zero-free on a narrow global strip.
It has an even holomorphic logarithm $g$, real on the real axis. Cauchy
differentiation on a smaller strip gives

$$
\begin{aligned}
g(z)&=\log(4\pi^2)+\tfrac92z-\pi e^{2z}+v(z),&
 |v^{(j)}(z)|&\le C e^{-2\Re z}\quad(j\le2),\\
\Re g''(z)&\le-c e^{2|\Re z|}\quad(|\Re z|\ge T),&
 \Re g''(z)&\le C_b\quad\text{throughout the strip}.
\end{aligned}
\tag{W47}
$$

The expansion is on the right tail; the second line uses evenness on
the left and a compact maximum in the middle. Choose $r$ with ample
strip clearance, for example $4r<\delta<\pi/4$ if (W47) holds on a
neighborhood of $|\Im z|\le\delta$.

Keep $\epsilon=e^{-2A}>0$ real even for complex offsets. Write
$a=A+u$, $b=A+v$, $x=(a+b)/2$ and $d=(a-b)/2$. In the direct
forward integral put $t=\epsilon s$ and

$$
F_A=g(a+\epsilon s)+g(b+\epsilon s)-g(a)-g(b),\qquad
F_0=-2\pi(e^{2u}+e^{2v})s.
$$

The right-tail expansion and its first derivative give, uniformly for
$s\ge0$ and offsets in the closed polydisc,

$$
\Re F_A,\Re F_0\le-c_1s,\qquad
|F_A-F_0|\le C_1\epsilon(s+s^2e^{2\epsilon s}).
$$

Use $e^{F_A}-e^{F_0}=(F_A-F_0)
\int_0^1e^{(1-t)F_0+tF_A}\,dt$ and $2\epsilon<c_1/2$.
The whole-half-line integrable error is $O(\epsilon)$, hence

$$
\mathcal P_A^{\rm direct}
 =4\pi e^{u+v}\int_0^\infty(x+\epsilon s)e^{F_A}\,ds
 =xS(u,v)+O(A\epsilon).
$$

The reflected exterior requires a separate bound on the same complex
neighborhood. For $z=d^2+\epsilon s$ choose $y=\sqrt z$ with
$\Re y\ge0$. Since $|d^2+t|\le|d|^2+t$ for real $t\ge0$,
$|\Im y|\le|\Im d|$. All $x+qy$, $-1\le q\le1$, remain in
the source strip. The symmetric expression
$\mathscr H(x,z)=g(x+\sqrt z)+g(x-\sqrt z)$ has a removable
square root at zero and satisfies

$$
\mathscr H_z(x,z)=\tfrac12\int_{-1}^1g''(x+q\sqrt z)\,dq.
$$

On $0\le q\le1$ use the strong right-tail upper bound in (W47);
on $-1\le q\le0$ use its global upper bound. For all sufficiently
large $A$, uniformly for the entire half-line,

$$
\Re\mathscr H_z(x,d^2+\epsilon s)\le-c_2e^{2\Re x},\qquad
\Re[\mathscr H(x,d^2+\epsilon s)-\mathscr H(x,d^2)]\le-c_3s.
$$

In particular the region $\Re(x-\sqrt z)<0$ has not been omitted.
Define the reflected continuation by

$$
K^{\rm ref}(a,b)=\frac\epsilon4\int_0^\infty
 \Phi(x+\sqrt{d^2+\epsilon s})
 \Phi(x-\sqrt{d^2+\epsilon s})\,ds.
$$

The symmetric integrand is holomorphic in the offsets, including the
removable square root; the preceding bound gives locally uniform
integrable domination after division by $\Phi(a)\Phi(b)$.
For real offsets the substitution $y^2=d^2+\epsilon s$ identifies
it with $K_0(a,-b)$. Iterated identity theorems identify it with the
continuation already owned in (W38). No contour rotation is needed.
Its contribution to $\mathcal P_A$ is

$$
\mathcal P_A^{\rm ref}=2\pi e^{u+v}\int_0^\infty
 e^{\mathscr H(x,d^2+\epsilon s)-\mathscr H(x,d^2)}\,ds=O(1).
$$

Thus $\mathcal P_A=xS+O(1)+O(Ae^{-2A})$ on the same fixed complex
polydisc. Since $x=A+(u+v)/2$, this proves (W46).

For its signed-form consumer set $h=r/4$ and independently define

$$
G_h(u,v)=\frac1{1-uv/(4h^2)},\qquad
m_n=\int_{-h}^h(u/h)^n\,d\mu(u),\qquad
Q_G(\mu)=\sum_{n\ge0}4^{-n}m_n^2,
$$

where $\mu$ is any real finite signed Borel measure on $[-h,h]$. The geometric
series is uniformly convergent on $[-h,h]^2$, so this is exactly
$\iint G_h\,d\mu\,d\mu$. Classical bivariate Cauchy estimates
applied to (W46) give Taylor coefficients
$|e_{mn}|\le C/(Ar^{m+n})$ for $M_A-S$. Absolute convergence and
Cauchy--Schwarz then give

$$
\boxed{\begin{aligned}
|Q_{M_A-S}(\mu)|
&\le\frac CA\left(\sum_{n\ge0}4^{-n}|m_n|\right)^2\\
&\le\frac{4C}{3A}Q_G(\mu).
\end{aligned}}
\tag{W48}
$$

One $A_0$ works for every node count, density, sign count and coefficient
size. This is a joint allowance for the complete actual kernel. If
$m_0,\ldots,m_{k-1}=0$, it additionally gives
$Q_G(\mu)\le\frac43\,4^{-k}\|\mu\|_{\rm TV}^2$;
unlike a bound only by total variation, it detects moment cancellation.
For all real finite samples, (W48) equivalently says

$$
S-\frac{4C}{3A}G_h\preceq M_A
 \preceq S+\frac{4C}{3A}G_h.
$$

The two reference forms remain distinct. No comparison
$G_h\preceq cS$ or all-order positive margin for $M_A$ is asserted.
In particular (W29) cannot be bypassed by silently replacing $G_h$ by
$S$. The local all-order premise of (W40), original signed Robin upper
bound and RH remain unproved. The new consumer is the order-uniform
error estimate (W48), not a new positivity criterion.


## The complete odd kernel has a paid compact-to-remote cross block

Fix $U>0$ and keep the complete actual $\Phi$, $L_0$ and $J$ from
(W12), (W19)--(W23). The square-variable strict concavity is the
classical Csordas--Varga result already cited in (W12). The derivative
tails, high-position diagonal and sparse high-block coercivity are
reused from (W20), (W22)--(W23). This `repo-derived` paper application
adds a uniform compact-to-remote estimate and its full cross-block
allowance. It asserts no new generic Schur theorem, literature priority
or Lean verification. Constants $C_U$ below depend only on $U$ and the
fixed complete kernel, and may increase between displays.

### The actual diagonal is nondegenerate through the origin

Put $h_0(r)=\log\Phi(\sqrt r)$. Even analytic $\Phi$ makes $h_0$
smooth at zero. The exact full diagonal difference is

$$
J(a)=\frac12\int_a^\infty y\Phi(y)^2\,dy
 -\frac12\int_0^\infty y\Phi(y+a)\Phi(y-a)\,dy
\qquad(a\ge0).
$$

The derivative tails in (W23) and evenness justify differentiation,
Taylor expansion and integration by parts on the entire half-line.
They give

$$
\boxed{\begin{aligned}
J(a)&=\kappa_0a^2+O(a^4),\\
\kappa_0
&=\int_0^\infty y\Phi'(y)^2\,dy-\frac{\Phi(0)^2}{2}\\
&=-\int_0^\infty r h_0''(r)e^{2h_0(r)}\,dr>0.
\end{aligned}}
\tag{W49}
$$

Indeed, the direct diagonal has second derivative $-\Phi(0)^2/2$ at
zero; the reflected diagonal has second derivative
$\int_0^\infty y(\Phi\Phi''-\Phi'^2)\,dy
=\Phi(0)^2/2-2\int_0^\infty y\Phi'^2\,dy$.
For the final equality in (W49), substitute $r=y^2$ and integrate the
derivative of $\Phi\Phi'$. The boundary terms vanish by smoothness and
the complete superexponential tail. Strict concavity gives $h_0''\le0$
and excludes $h_0''\equiv0$; continuity supplies an interval of strict
negativity. Thus the final integral is strictly positive.

Consequently $J(a)/a^2$ extends continuously and positively to $[0,U]$.
Together with the strict diagonal positivity from (W12), compactness
gives $m_U>0$ such that $J(a)\ge m_Ua^2$ for $0\le a\le U$.
No numerical value of $m_U$ is asserted.

### Retain both endpoint cancellations before taking a norm

For $b\ge\max(U,256)$ and $0\le a\le U$, use the same forward
variable in both complete integrals:

$$
\begin{aligned}
L_0(a,b)&=\frac14\int_0^\infty\Phi(b+t)B(a,b,t)\,dt,\\
B(a,b,t)&=(a+b+2t)\Phi(t+a)-(b-a+2t)\Phi(t-a).
\end{aligned}
$$

The bracket vanishes at $a=0$. Its derivative can be grouped as

$$
\begin{aligned}
\partial_aB={}&\Phi(t+a)+\Phi(t-a)
 +a[\Phi'(t+a)-\Phi'(t-a)]\\
&+(b+2t)[\Phi'(t+a)+\Phi'(t-a)].
\end{aligned}
$$

The complete derivative tails and compactness bound the terms without
$b$ uniformly in $a,t$. Evenness makes $\Phi'$ odd, so

$$
\Phi'(a)+\Phi'(-a)=0,\qquad
|\Phi'(t+a)+\Phi'(t-a)|\le2\|\Phi''\|_\infty t.
$$

The global second-derivative norm is finite by (W23), smoothness and
evenness. Hence $|\partial_aB|\le C_U(1+bt)$ and
$|B(a,b,t)|\le C_Ua(1+bt)$ for every $t\ge0$. On the same entire
half-line, (W19) gives
$\Phi(b+t)\le\Phi(b)\exp(-e^{2b}t)$. Integrating the constant and
linear terms therefore yields

$$
|L_0(a,b)|\le C_Ua\Phi(b)[e^{-2b}+be^{-4b}]
\le C_Ua\Phi(b)e^{-2b}.
$$

Normalize using $J(a)\ge m_Ua^2$ and the actual high diagonal in
(W20). After absorbing fixed constants,

$$
\boxed{0<\frac{L_0(a,b)}{\sqrt{J(a)J(b)}}
 \le C_U\frac{e^{-b}}{\sqrt b}
\quad(0<a\le U,\ b\ge\max(U,256)).}
\tag{W50}
$$

The estimate is uniform as $a\downarrow0$. At $a=0$ the original
entry and $J(0)$ vanish; no undefined normalized value is assigned.
Both the complete reflected exterior and the infinite direct tail have
been retained. The extra decay uses the evenness cancellation at $t=0$
in addition to the cancellation at $a=0$.

### Pay the whole coupling to an arbitrary compact signed core

For any finite complex Borel measure $\mu$ supported on $[0,U]$, set

$$
\mathcal Q_L(\mu)=\iint L_0(a,b)\,d\overline\mu(a)d\mu(b),
\qquad
\mathcal M(\mu)=\int_{[0,U]}\sqrt{J(a)}\,d|\mu|(a).
$$

Let $\nu=\sum_{j=1}^Nc_j\delta_{b_j}$, where $N$ is finite,
$b_1\ge T\ge\max(U,256)$ and $b_{j+1}-b_j\ge8$. Keep
$E_\nu=\sum_jJ(b_j)|c_j|^2$ and $\kappa=17/56$ from (W22).
The normalized bound (W50), Cauchy--Schwarz and the complete geometric
sum give

$$
\begin{aligned}
\left|\iint L_0(a,b)\,d\overline\mu(a)d\nu(b)\right|
&\le C_U\mathcal M(\mu)\sqrt{E_\nu}
 \left(\sum_jb_j^{-1}e^{-2b_j}\right)^{1/2}\\
&\le C_U\frac{e^{-T}}{\sqrt T}
 \mathcal M(\mu)\sqrt{E_\nu},\\
\sum_jb_j^{-1}e^{-2b_j}
&\le\frac{e^{-2T}}{T(1-e^{-16})}.
\end{aligned}
$$

The bounds are independent of $N$, the coefficient sizes and the sign
pattern of the compact measure. Its atom at zero contributes nothing.
Reuse $\mathcal Q_L(\nu)\ge\kappa E_\nu$ from (W22) and spend
half of this same credit by Young's inequality:

$$
\boxed{\mathcal Q_L(\mu+\nu)
 \ge\mathcal Q_L(\mu)+\frac{17}{112}E_\nu
 -C_U\frac{e^{-2T}}T\mathcal M(\mu)^2.}
\tag{W51}
$$

This pays an absolute vanishing allowance for the entire compact-to-sparse-
remote cross block. It assigns no sign to $\mathcal Q_L(\mu)$ and
makes no comparison of $\mathcal M(\mu)^2$ with a nearly null compact
form. The compact size $U$ is fixed; no uniformity as $U\to\infty$,
no dense remote-sector coercivity, no full all-order positivity and no
strict all-integer Robin inequality or RH proof is supplied.


## Fixed-order decay controls arbitrarily many confluent clusters

Keep the complete actual normalized odd kernel
$R(a,b)=L_0(a,b)/\sqrt{J(a)J(b)}$. Reuse the fixed-order theta bounds
and local confluent estimates in (W23), (W33)--(W34), including their
already cited classical divided-difference formula. The new input is a
uniform derivative bound at separated escaping positions. It pays the
whole interaction between arbitrarily many bounded-size clusters.
This is a `repo-derived` paper application of the existing local results
and the classical block row-sum bound, without a literature-priority or
Lean-verification claim.

### Derivatives at separated positions

For every fixed integer $r\ge0$, there are $A_r,C_r>0$ such that

$$
\boxed{\max_{i+j\le r}|\partial_a^i\partial_b^jR(a,b)|
 \le C_r(1+|a-b|)e^{-|a-b|}
\quad(a,b\ge A_r,\ |a-b|\ge8).}
\tag{W52}
$$

The constants are independent of both positions and their distance.
There is no uniformity over $r$. To retain the entire reflected exterior,
first suppose $b\ge a+8$ and put $g=\log\Phi$, $q=e^{2b}$ and

$$
\begin{aligned}
F_+&=g(a+t)-g(a)+g(b+t)-g(b),\\
F_-&=g(a-t)-g(a)+g(b+t)-g(b),\\
\mathcal U(a,b)&=\frac{L_0(a,b)}{\Phi(a)\Phi(b)}\\
&=\frac14\int_0^\infty
 [(a+b+2t)e^{F_+}-(b-a+2t)e^{F_-}]\,dt.
\end{aligned}
$$

This is the exact common forward-variable formula, using evenness in
the reflected term. Global concavity of $g$ and (W19) give, for every
$t\ge0$,

$$
F_+\le-qt,\qquad
F_-\le-[p(b)-p(a)]t\le-qt/2,
$$

since $p(a)\le10e^{2a}$ and $10e^{-16}<1/2$. The bound remains
valid when $a-t<0$; that part of the reflected integral is not deleted.
For $1\le k\le r$, the whole-line fixed-order bounds preceding (W33)
give

$$
|\partial_a^kF_\pm|+|\partial_b^kF_\pm|
 \le C_rqt e^{2t}.
$$

Indeed each derivative is a difference of two values of $g^{(k)}$,
and its integral remainder uses $g^{(k+1)}$ on an interval of length
$t$. Mixed derivatives of the exponents vanish. Enlarge $A_r$ until
$q\ge\max(1,8r)$. The chain rule then bounds each derivative of
$e^{F_\pm}$ through total order $r$ by

$$
C_re^{-qt/4}\sum_{k=0}^r(qt)^k.
$$

These majorants justify differentiation of the full integrals. Integrating
the constant and linear factors in $t$ yields

$$
\max_{i+j\le r}|\partial_a^i\partial_b^j\mathcal U(a,b)|
 \le C_r(a+b+1)e^{-2b}.
$$

For normalization, reuse the fixed-order direct/reflected limit preceding
(W33) at its unnormalized diagonal $d_*(x)=T(x,0)$ from (W24):

$$
d_*(x)=\frac{e^{2x}J(x)}{x\Phi(x)^2}\longrightarrow\frac1{8\pi},
\qquad d_*^{(k)}(x)\longrightarrow0\quad(k\ge1\text{ fixed}).
$$

Thus $d_*$ is bounded away from zero and its fixed-order logarithmic
derivatives are bounded beyond a common start. The function
$\mathcal N(x)=e^x/(\sqrt x\sqrt{d_*(x)})$ satisfies
$|\mathcal N^{(k)}(x)|\le C_r\mathcal N(x)$ for $k\le r$ there.
Since $R(a,b)=\mathcal N(a)\mathcal N(b)\mathcal U(a,b)$, its derivatives
are bounded by
$C_r(a+b+1)e^{a-b}/\sqrt{ab}$.
For $a\ge1$, $(a+b+1)/\sqrt{ab}\le3+(b-a)$.
This proves (W52) on this half of the domain. Symmetry exchanges the
positions and derivative orders on the other half.

### The existing local estimates give one cluster metric

Fix $W>0$ and an integer $m\ge1$. A cluster consists of distinct ordered
nodes $x_{j,1}<\cdots<x_{j,n_j}$ with $1\le n_j\le m$ and hull width at most
$W$. Let $T_j$ be the real Newton map on its evaluation vectors:
its $k$th coordinate is the divided difference on
$x_{j,1},\ldots,x_{j,k}$. It is invertible; no lower bound on the internal
gaps is imposed.

The local matrix
$H_j=T_j[R(x_{j,k},x_{j,l})]_{k,l}T_j^*$ has prefix determinants
exactly equal to the quotients in (W34). For clusters beyond the existing
local threshold, those determinants are at least
$\beta_{W,m}=\tfrac12e^{-2m^2W}>0$. The derivative bounds in (W33)
and the classical integral formula bound all entries by one
$M_{W,m}\ge1$, independently of the node gaps and cluster position.
The positive prefix determinants give positive definiteness; the
operator norm is at most $mM_{W,m}$. Consequently

$$
\boxed{H_j\succeq\sigma_{W,m}I,\qquad
 \sigma_{W,m}:=\frac{\beta_{W,m}}{(mM_{W,m})^{m-1}}>0.}
\tag{W53}
$$

This reuses the already paid bounded-window confluence estimate rather
than assuming a positive budget for unrestricted local profiles.

### The entire interaction is uniform in the number of clusters

Order any finite number of clusters, and require consecutive hulls to
have distance at least $D\ge8$. Apply the same Newton maps to every
block of the complete normalized Gram matrix. The classical integral
formula and (W52) with $r=2m-2$ bound each entry of a cross block with
hull distance $\delta$ by $C_r(1+\delta)e^{-\delta}$. Its operator
norm is at most $mC_r(1+\delta)e^{-\delta}$. The $n$th next hull has
distance at least $nD$, so every block row sum is at most

$$
2mC_r\sum_{n\ge1}(1+nD)e^{-nD}
=2mC_r\left[\frac{q_D}{1-q_D}
 +\frac{Dq_D}{(1-q_D)^2}\right],\qquad q_D=e^{-D}.
$$

Choose one $D_{W,m}\ge8$ making this quantity at most
$\sigma_{W,m}/2$, and one $A_{W,m}$ covering the existing local
threshold and (W52). Both choices are independent of the total number
of clusters and nodes. The standard block row-sum estimate now leaves
$\sigma_{W,m}/2$ of the same local budget in the full matrix.

For arbitrary complex coefficient vectors $c_j$, put

$$
z_j=\operatorname{diag}(\sqrt{J(x_{j,k})})c_j,\qquad
 y_j=T_j^{-*}z_j.
$$

The block Newton congruence is exact, and therefore

$$
\boxed{\sum_{j,k}\overline{c_j}^{\,T}
 [L_0(x_{j,s},x_{k,t})]_{s,t}c_k
 \ge\frac{\sigma_{W,m}}2\sum_j\|y_j\|_2^2.}
\tag{W54}
$$

Here all nodes are at least $A_{W,m}$, each cluster has at most $m$
nodes and width at most $W$, and consecutive hull distances are at least
$D_{W,m}$. The bound covers arbitrary coefficient sizes, complex coefficients
and total sample counts. It remains uniform as internal gaps
tend to zero. Repeated physical nodes may first be merged; no derivative
distributions are substituted for the original finite samples.

Unlike the separated individual samples in (W22), these families permit
arbitrarily close nodes within each cluster and arbitrarily many sign
changes over all clusters. The metric explicitly records the coefficient
cancellation at confluence; no unweighted lower eigenvalue is asserted.
The local size $m$ and width $W$ are fixed. Their thresholds and cluster
gaps need not be uniform as $m\to\infty$, and the families are not dense
in the unrestricted physical test space. Positivity on one fixed window
at all orders, the complete compact signed form, the strict all-integer
Robin upper and RH remain unproved.


## A linearly growing sign count has a paid actual positive margin

Reuse the complete actual complex remainder (W46), rather than deriving
another fixed-order limit. The following source-specific paper
application pays that remainder relative to the positive hyperbolic
kernel on profiles whose sign count may grow linearly with the
center. Polynomial division, Cauchy coefficients and the scalar Hardy
moment identity are classical tools. No standalone generic identity,
literature priority or Lean verification is asserted.

### Put the actual remainder in the exact hyperbolic coordinate

Keep $M_A=\mathcal P_A/A=D_A L_0D_A$ and the constants $r,C,A_0$ of
(W46). Shrink that offset neighborhood once as in (W56), then choose one
$0<R<1/2$ so small that the principal map
$u=\operatorname{arctanh}z$ sends a neighborhood of $|z|\le R$
inside $|u|<r$. Put $h=R/4$, $q=2/R$, and

$$
\begin{aligned}
\mathcal K_A(z,w)
 &=\cosh(u)\cosh(v)M_A(u,v),\\
H(z,w)&=\frac1{1-zw},\qquad
\mathcal E_A=\mathcal K_A-H,
\qquad v=\operatorname{arctanh}w.
\end{aligned}
$$

The identity $\cosh(u)\cosh(v)\operatorname{sech}(u-v)
=1/(1-\tanh u\tanh v)$ is exact. Thus (W46) gives a holomorphic
remainder bounded by $C_1/A$ on $|z|,|w|\le R$, with
$C_1=C/(1-R^2)$. All constants are independent of sign count.
For a real finite signed Borel measure $\nu$ on $[-h,h]$, write

$$
a_k=\int z^k\,d\nu(z),\qquad
Q_H(\nu)=\sum_{k\ge0}a_k^2.
$$

Uniform convergence of the geometric series identifies this with the
$H$ form. Cauchy coefficients and Cauchy--Schwarz give

$$
|Q_{\mathcal E_A}(\nu)|
\le\frac{C_1}{A}\left(\sum_{k\ge0}R^{-k}|a_k|\right)^2
\le\frac{4C_1}{3A}\sum_{k\ge0}q^{2k}a_k^2.
$$

This still has a different moment radius from $Q_H$. The sign condition
below supplies the missing comparison; it is not an unrestricted
comparison of the two positive kernels.

### Pay the moment-radius change using the actual sign separators

Suppose $p(z)=\prod_{j=1}^m(z-s_j)=\sum_{j=0}^mp_jz^j$ is monic,
all $s_j\in[-h,h]$, repetitions allowed, and $\epsilon p\nu\ge0$
for some $\epsilon\in\{-1,1\}$. Include $m=0$, with $p=1$.
Set $U^2=\sum_{k=0}^ma_k^2\le Q_H(\nu)$ and define, for
$|\zeta|\le q$,

$$
F(\zeta)=\int\frac{d\nu(z)}{1-\zeta z},\qquad
N(\zeta)=\int\frac{p(z)}{1-\zeta z}\,d\nu(z),\qquad
P(\zeta)=\prod_{j=1}^m(1-s_j\zeta).
$$

Here $qh=1/2$. The sign condition gives the equality
$\int|p|d|\nu|=|\int p\,d\nu|$, even when atoms lie at repeated
separator roots. Since $\sum_j|p_j|\le(1+h)^m$, it follows that

$$
|N(\zeta)|\le2(1+h)^mU\qquad(|\zeta|\le q).
$$

Finite polynomial division gives the exact identity

$$
P(\zeta)F(\zeta)=\zeta^mN(\zeta)
 +\sum_{j=1}^mp_j\sum_{k=0}^{j-1}a_k\zeta^{m-j+k}.
$$

For $|\zeta|=q$, the double sum is bounded by
$q^m(1+h)^mU/(q-1)$, while $|P(\zeta)|\ge(1-qh)^m=2^{-m}$.
Since $q>2$, including $m=0$ with an empty double sum gives

$$
\sup_{|\zeta|=q}|F(\zeta)|
 \le3[2q(1+h)]^mU.
$$

The uniformly convergent moment series for $F$ and the scalar Parseval
identity therefore yield

$$
\sum_{k\ge0}q^{2k}a_k^2
\le9[2q(1+h)]^{2m}Q_H(\nu).
$$

In particular, with constants specified independently of $m$ by

$$
\Lambda=[2q(1+h)]^2=(1+4/R)^2>1,\qquad
K=\max(1,12C_1),
$$

the complete actual relative estimate is

$$
\boxed{|Q_{\mathcal K_A-H}(\nu)|
 \le\frac{K\Lambda^m}{A}Q_H(\nu).}
\tag{W55}
$$

It holds for every $m\ge0$, every $A\ge A_0$, and every real finite
measure with the displayed polynomial-sign condition. The constants
have no hidden dependence on total sample count, density, separator
gaps, coefficient sizes or $m$. They depend on the one chosen complex
neighborhood in (W46).

### The complete first-core remainder has an exponential complex rate

The first correction in (W27) is
$$
C(u,v)=\frac{u+v}{2}S(u,v)-T(u-v),\qquad
T(t)=\frac{t}{2\sinh t},\quad T(0)=\tfrac12.
$$
On a smaller fixed complex polydisc, the same actual integrals used in
(W46) give the stronger rate
$$
\boxed{M_A=S+\frac CA+\mathcal Z_A,\qquad
 \sup|\mathcal Z_A|\le C_2e^{-2A}.}
\tag{W56}
$$
Here and below the constants are independent of $m$.

For the direct integral, reuse (W46)'s already established bound
$\mathcal P_A^{\rm direct}=xS+O(A\varepsilon)$, where
$\varepsilon=e^{-2A}$, $x=A+(u+v)/2$, $d=(u-v)/2$.
For the reflected integral retain its exact whole-half-line formula
$$
\mathcal P_A^{\rm ref}=2\pi e^{u+v}\int_0^\infty e^{G_A(s)}ds,
\qquad
G_A(s)=\mathscr H(x,d^2+\varepsilon s)-\mathscr H(x,d^2).
$$
The global estimate $\Re G_A(s)\le-cs$ is exactly the complete
reflected estimate in (W46); it includes the exterior with
$\Re(x-\sqrt{d^2+\varepsilon s})<0$.

Put $h_0(z)=\cosh(2\sqrt z)$, entire in $z$, and
$$
G_0(s)=-2\pi e^{u+v}h_0'(d^2)s .
$$
Since $h_0'(0)=2$, shrink the complex offsets once until
$\Re[2\pi e^{u+v}h_0'(d^2)]\ge c_0>0$.
On $0\le s\le\varepsilon^{-1/2}$, every square root and every
segment used in $\mathscr H_z$ stays bounded relative to $x$, so all
arguments are in the right tail. Use (W47)'s logarithmic remainder
$v$, including $|v''|\le C e^{-2A}$, on this bounded-offset region.
The linear term in $g$ cancels in the symmetric difference. Taylor's
remainder for the entire $h_0$ gives
$$
|G_A(s)-G_0(s)|\le C\varepsilon(s+s^2).
$$
In detail its leading part is
$-2\pi e^{u+v}\varepsilon^{-1}
 [h_0(d^2+\varepsilon s)-h_0(d^2)]$;
the logarithmic remainder difference is $O(\varepsilon^2s)$.
The two negative-real-part bounds and the exponential interpolation
identity used in (W46) therefore give
$$
|e^{G_A(s)}-e^{G_0(s)}|
 \le C\varepsilon(s+s^2)e^{-c_1s}
 \quad(0\le s\le\varepsilon^{-1/2}).
$$
On the remaining half-line both integrals are bounded by
$Ce^{-c_1\varepsilon^{-1/2}}=O(\varepsilon)$.
Thus no reflected exterior is removed, and
$$
\mathcal P_A^{\rm ref}
 =\frac1{h_0'(d^2)}+O(\varepsilon)
 =\frac d{\sinh(2d)}+O(\varepsilon).
$$
All removable values are included. Together with the direct bound,
this proves (W56) as a uniform complex estimate. No bound uniform in
all derivative orders is inferred without paying its Cauchy factors.

### The first correction costs only a logarithm of the sign count

Return to the measure and separators above. The radius comparison
already proved before (W55) says
$$
\sum_{k\ge0}q^{2k}a_k^2\le9\Lambda^mQ_H(\nu).
$$
Put $b_k=\int z^k\operatorname{arctanh}z\,d\nu(z)$.
Absolute convergence on the support gives
$$
b_k=\sum_{j\ge0}\frac{a_{k+2j+1}}{2j+1}.
$$
For the right shift $B(a)_k=a_{k+1}$, the same radius comparison gives
$$
\|B^\ell a\|_2\le
 \min(1,3\Lambda^{m/2}q^{-\ell})\|a\|_2 .
$$
Choose
$J=\lceil (m+1)[1+\log\Lambda/(4\log q)]\rceil$.
For $j<J$ use the first bound; its odd harmonic sum is
$O(\log(m+2))$. For $j\ge J$ use the second bound;
$\Lambda^{m/2}q^{-2J}\le q^{-2}$, and the remaining sum is uniformly
geometric. Consequently one fixed $C_3$ gives
$$
\|b\|_2\le C_3\log(m+2)\|a\|_2.
$$
The $(u+v)S/2$ part of the transported correction has form
$\sum_k a_kb_k$, so its absolute value is bounded by
$C_3\log(m+2)Q_H(\nu)$.

For the remaining term reuse the classical positive stationary kernel
$S(t)=\operatorname{sech}t$ and its Cauchy Gram representation, already
used in (W28)--(W29). The elementary convolution formula is
$T=(S*S)/4$; it follows by integrating
$\tanh x-\tanh(x-t)=\sinh t/[\cosh x\cosh(x-t)]$, including $t=0$.
For every finite real measure $\eta$, stationarity and
Cauchy--Schwarz in this Gram space give
$$
\left|\iint S(u-v-x)\,d\eta(u)d\eta(v)\right|\le Q_S(\eta).
$$
Indeed simultaneous translation is a unitary operator in this
stationary Gram space. Integrating against $S(x)/4$, and using
$\int_{\mathbb R}S(x)dx\le4$, yields
$$
|Q_T(\eta)|\le Q_S(\eta).
$$
For the transported correction take
$d\eta(u)=\cosh(u)\,d\nu(\tanh u)$; its $S$ form is exactly
$Q_H(\nu)$. Thus the complete correction, on this sign-restricted
family, satisfies
$$
|Q_{\widetilde C}(\nu)|
 \le[C_3\log(m+2)+1]Q_H(\nu),
$$
where $\widetilde C(z,w)=\cosh(u)\cosh(v)C(u,v)$.
This does not contradict (W29)'s failure of an unrestricted bound.

### Spend both actual allowances at a linearly growing sign count

After the same positive change of variables, (W56) has a remainder
bounded by $C_4e^{-2A}$ on $|z|,|w|\le R$.
Apply the already established Cauchy-coefficient and radius comparison
to this remainder. With $K_2=\max(1,12C_4)$, the full actual estimate is
$$
\boxed{
|Q_{\mathcal K_A-H}(\nu)|
\le
\left[
 \frac{C_3\log(m+2)+1}{A}
 +K_2e^{-2A}\Lambda^m
\right]Q_H(\nu).}
\tag{W57}
$$
It retains both parts of the first correction and the complete actual
error; neither allowance is replaced by a separately favorable sign.

For all sufficiently large $A$, choose
$$
m_{\rm lin}(A)=\left\lfloor\frac A{\log\Lambda}\right\rfloor.
$$
Uniformly for $0\le m\le m_{\rm lin}(A)$, the last allowance is at most
$K_2e^{-A}$, and the first tends to zero like $O(\log A/A)$.
One start $A_1$, independent of $m$, therefore gives
$$
\boxed{Q_{\mathcal K_A}(\nu)\ge\tfrac12Q_H(\nu)>0
 \quad(A\ge A_1,\ 0\le m\le m_{\rm lin}(A),\ \nu\ne0).}
\tag{W58}
$$
Strictness uses ordinary uniqueness of finite compactly supported
measures from all polynomial moments. The explicit contract is
$\epsilon p\nu\ge0$ for a displayed monic separator polynomial of
degree at most $m_{\rm lin}(A)$. Roots may repeat; no lower separator
gap or upper sample-density bound is imposed.

To state the estimate for the original physical kernel, let
$u=\operatorname{arctanh}z$ and $d_A(u)=\cosh(u)D_A(u)>0$.
For a finite real physical measure $\mu$ supported in
$[A-\operatorname{arctanh}h,A+\operatorname{arctanh}h]$, transport
$d\mu(A+u)/d_A(u)$ by $z=\tanh u$ to obtain $\nu$.
The congruence is exact:
$Q_{L_0}(\mu)=Q_{\mathcal K_A}(\nu)$.
Hence (W58) applies whenever the transported measure satisfies the
explicit polynomial-sign contract. In particular this includes
nonzero real finite sampled measures and real smooth densities with
at most $m_{\rm lin}(A)$ sign changes, with arbitrary sample count
and density.

For arbitrary complex finite samples at
$n\le m_{\rm lin}(A)+1$ distinct physical sites in the same physical
interval, each real and imaginary coefficient measure has at most
$n-1$ sign changes. Apply the real estimates separately; reality and
symmetry make their quadratic forms add. This pays the full complex
sampled form as well, without an internal node-gap restriction.
The transported Hardy moment form is the metric, not an unweighted
coefficient norm.

The linearly growing sign count strengthens the logarithmic consequence
of (W55) alone. Its additional inputs are the actual complete exponential
first-core remainder (W56) and the paid sign-restricted correction,
not a diagonal selection of fixed-order thresholds.
The interval width is one fixed small value. At any fixed $A$, the
allowed count remains finite. No unrestricted all-order positivity
on one fixed window, unrestricted complex-measure result, unconditional
premise for (W40), strict all-integer Robin inequality or RH proof is
supplied. These are repository-derived paper estimates, without a
literature-priority or Lean-verification claim.


## Arbitrarily many finite-sign profiles have a joint positive margin

Reuse the complete actual derivative decay (W52) and the single-window
margin (W58). Their additional joint consumer permits arbitrary real
finite signed measures in each cluster, with a fixed bound on local
sign complexity and no bound on local sample count or density. Every
cross term of the original $L_0$ is retained. The classical Hermite
interpolation formula and block row-sum estimate are reused inside this
source application, without a standalone generic theorem, literature
priority or Lean-verification claim.

### Use the exact local transport for every profile

Fix the one small $h$ and $\Lambda$ from (W55)--(W58), put
$w=\operatorname{arctanh}h$, and fix an integer $m\ge0$.
Let $\mu_j$, $1\le j\le N$, be real finite signed Borel measures
supported on the ordered physical windows
$I_j=[A_j-w,A_j+w]$. Transport each by exactly (W58):
$\nu_j$ is the pushforward of $d\mu_j(A_j+u)/d_{A_j}(u)$ under
$z=\tanh u$, with $d_A(u)=\cosh(u)D_A(u)>0$.
Require separately for every $j$ that

$$
\epsilon_jp_j\nu_j\ge0,\qquad
p_j(z)=\prod_{k=1}^{r_j}(z-s_{j,k}),\qquad
0\le r_j\le m,\quad s_{j,k}\in[-h,h],\quad
\epsilon_j\in\{-1,1\}.
$$

Repeated roots and atoms at roots are allowed. Put

$$
a_{j,k}=\int z^k\,d\nu_j(z),\qquad
B_j=\sum_{k=0}^m a_{j,k}^2,\qquad
Q_j=Q_H(\nu_j)=\sum_{k\ge0}a_{j,k}^2.
$$

These are finite since $h<1$ and $\nu_j$ is finite. For
$A_j\ge A_1$ and $A_j\ge m\log\Lambda$, (W58) gives
$Q_{L_0}(\mu_j)\ge Q_j/2$.

### Hermite interpolation controls integration without a density bound

Here is the interpolation step used for the actual cross terms.
For one of these measures, omit $j$ and let $f\in C^m([-h,h])$.
For $r\ge1$, interpolate $f$ at the displayed roots, including
their multiplicities. The Newton polynomial $P$ of degree at most
$r-1$ has coefficient $\ell^1$ norm at most

$$
\|P\|_{\ell^1}
\le\sum_{k=0}^{r-1}\frac{(1+h)^k}{k!}\|f\|_{C^m}
\le e^{1+h}\|f\|_{C^m}.
$$

The same classical divided-difference integral formula already used in
(W34)/(W54) writes $f=P+pg$, with a continuous remainder satisfying
$\|g\|_\infty\le\|f^{(r)}\|_\infty/r!$.
The sign contract gives
$\int|p|\,d|\nu|=|\int p\,d\nu|$ exactly, while the coefficient
norm of $p$ is at most $(1+h)^r$. Cauchy--Schwarz on the first
$m+1$ moments therefore gives inside this application

$$
\left|\int f\,d\nu\right|
\le C_h\|f\|_{C^m}\sqrt{B},\qquad C_h=2e^{1+h}.
$$

For $r=0$ the measure is one-signed and
$\|\nu\|_{\rm TV}=|a_0|$, which gives the same bound directly.
This argument does not divide by root separations. Signed atoms at
roots enter through $P$ and the retained low moments.

### Pay the complete cross form in the same moment metric

Put $J(a)=L_0(a,a)$, as in (W52), and define

$$
c_A(z)=\cosh(u)\sqrt{M_A(u,u)},\qquad
u=\operatorname{arctanh}z.
$$

The normalization in (W46) gives
$c_A(z)=\sqrt{J(A+u)}d_A(u)$ exactly. On the fixed local complex
neighborhood, (W46) gives $M_A(u,u)=1+O(A^{-1})$ uniformly.
Its positive square root thus has uniformly bounded derivatives of
every fixed order on the smaller real interval; this also follows
directly by Cauchy estimates. These are bounds on the normalized
factor, without separately bounding the large physical weights.

For $i\ne j$, the exact transported cross kernel is

$$
T_{ij}(z,v)=c_{A_i}(z)c_{A_j}(v)
 R(A_i+\operatorname{arctanh}z,
   A_j+\operatorname{arctanh}v).
$$

For all physical positions beyond (W52)'s start at order $2m$, and
hull gaps at least $8$, its mixed derivatives through order $m$ in
each variable are bounded by
$C_m(1+d_{ij})e^{-d_{ij}}$, where $d_{ij}=|A_i-A_j|$.
The chain rule uses (W52) only through total order $2m$ and the
uniform local normalizer bounds above. The bounded offsets cost a
fixed factor depending on $h$, not on either center or their ratio.

Apply the preceding interpolation estimate in each variable. Finite
total variation justifies differentiation under the other integral.
After absorbing $C_h^2$, this pays the complete actual cross form:

$$
\boxed{\begin{aligned}
\left|\iint L_0(a,b)\,d\mu_i(a)d\mu_j(b)\right|
&\le K_m(1+d_{ij})e^{-d_{ij}}\sqrt{B_iB_j}\\
&\le K_m(1+d_{ij})e^{-d_{ij}}\sqrt{Q_iQ_j}.
\end{aligned}}
\tag{W59}
$$

All constants are independent of local measure mass, sample count,
density, coefficient sizes, root multiplicities and root separations.
The complete direct and reflected infinite integrals enter through the
already paid actual derivative supplier (W52); no reference kernel or
deleted reflected exterior replaces $L_0$ here.

### One separation pays arbitrarily many interacting profiles

Choose $D_m\ge8$ so large that, with $q=e^{-D_m}$,

$$
2K_m\left[\frac q{1-q}+\frac{D_mq}{(1-q)^2}\right]\le\frac14.
$$

Choose one $A_m^*$ covering (W58), $m\log\Lambda$, the local
normalizer bounds and $A_m^*-w\ge A_{2m}$, where $A_{2m}$ is
the physical start in (W52) at order $2m$.
Require $A_j\ge A_m^*$ and consecutive hull gaps at least $D_m$.
The $n$th next center is then at distance at least $nD_m$.
Reuse (W54)'s same scalar row-sum estimate on (W59), spending the
local $Q_j/2$ budget only once. It gives

$$
\boxed{Q_{L_0}\!\left(\sum_{j=1}^N\mu_j\right)
\ge\frac14\sum_{j=1}^N Q_H(\nu_j)>0}
\tag{W60}
$$

unless every $\mu_j$ is zero. Strictness uses exactly the compact
moment uniqueness already used in (W58). The same $A_m^*,D_m$ work
for every finite $N$ and every allowed local profile.

This includes real smooth finite-sign profiles and arbitrarily dense
real samples on arbitrarily many separated windows. Each window has
bounded sign complexity, while the total sign complexity need not be
bounded. The earlier complex-sample conclusion (W54), with its bound
on local node count, remains a separate statement. No unrestricted
complex-measure positivity, raw coefficient gap, uniformity in $m$,
fixed-window all-order positivity, original strict Robin upper or RH
proof follows. The positive metric is the exact transported Hardy
moment form; the fixed small width and intervening gaps remain part
of the hypotheses.


## Any prescribed positive gap between bounded theta clusters

Keep the complete actual $L_0$, its diagonal $J$ and the normalized
kernel $R$ of (W52)--(W54). Fix $W>0$, an integer $m\ge1$ and now
**any prescribed $\delta>0$**. There are $A_*,\sigma>0$, depending
only on $(W,m,\delta)$, for which the conclusion below holds for every
finite ordered family of clusters above $A_*$, each with at most $m$
distinct nodes, hull width at most $W$ and consecutive hull gaps at
least $\delta$. No positive lower bound on internal node gaps or upper bound on total
cluster count is required. The improvement over (W54) is the prescribed gap in place of
its sufficiently large $D_{W,m}$.

This is a `repo-derived` paper application of (W33), (W34) and (W52),
using a classical Hardy model-space theorem for the reference kernel.
It asserts neither literature priority nor Lean verification.

### Verify the classical reference theorem's angle hypothesis

The external input is Vasyunin's theorem as stated in
[Treil, arXiv:math/9601211v1](https://arxiv.org/pdf/math/9601211v1),
Theorem 8.4, printed p.19. Uniformly minimal scalar Hardy model spaces
$E_j=H^2\ominus B_jH^2$ form a Riesz basis in their closed span.
Uniform minimality has the precise meaning in equation (1.3), printed
p.4:

$$
\inf_j\inf_{f\in E_j,\ \|f\|=1}
 \operatorname{dist}\!\left(f,
 \overline{\operatorname{span}}\{E_k:k\ne j\}\right)>0.
$$

Equation (8.1), printed p.18, then bounds
$\|\sum_jf_j\|^2$ below by a positive constant times
$\sum_j\|f_j\|^2$. A Cayley map transports this theorem unitarily
from the disk to the right half-plane. The following argument checks
its actual hypothesis directly; no complementary-product corona
criterion or scalar separated-node theorem replaces it.

For a physical node $a$, put $x=e^{2a}>0$. In the half-plane Hardy
norm with boundary measure $dt/(2\pi)$ the normalized kernel is
$k_x(z)=\sqrt{2x}/(z+x)$, and

$$
\langle k_x,k_y\rangle=\frac{2\sqrt{xy}}{x+y}
 =\operatorname{sech}(a-b)=:S(a,b).
$$

Let $B_j$ have the $n_j\le m$ zeros $x_{j,l}=e^{2a_{j,l}}$ and put
$E_j=K_{B_j}=\operatorname{span}\{k_{x_{j,l}}\}_l$. Normalize
Blaschke factors unimodularly when taking infinite products. Define

$$
\eta=\prod_{n\ge1}\tanh(n\delta)^{2m}>0.
$$

The product is positive since $1-\tanh(n\delta)$ is summable. At
any node of cluster $j$, every node in the $n$th other cluster on
either side has physical distance at least $n\delta$. Thus, with
$B_{\ne j}=\prod_{k\ne j}B_k$,

$$
|B_{\ne j}(x_{j,l})|\ge\eta.
$$

These products also exist for a countable ordered family above a fixed
start: cluster starts increase by at least $\delta$, so
$\sum_x x/(1+x^2)<\infty$. This is the half-plane Blaschke condition.

The adjoint Hardy multiplier
$A_j=M_{B_{\ne j}}^*|_{E_j}$ is a contraction preserving $E_j$,
because $M_h^*k_x=\overline{h(x)}k_x$. The distinct kernels form
an eigenbasis, giving

$$
|\det A_j|=\prod_l|B_{\ne j}(x_{j,l})|
 \ge\eta^{n_j}\ge\eta^m.
$$

All its singular values are at most one, so its smallest singular
value is at least $\eta^m$. This does not estimate the conditioning
of that eigenbasis. The same adjoint multiplier annihilates every
other $E_k$. For $f\in E_j$ and $g$ in their closed span,

$$
\|f-g\|\ge\|M_{B_{\ne j}}^*(f-g)\|
 =\|A_jf\|\ge\eta^m\|f\|.
$$

This verifies uniform minimality with lower bound $\eta^m$, without
dividing by an internal node gap. Apply the cited model-space theorem.

### The reference budget is uniform over finite cluster families

Use exactly the Newton maps $T_j$ of (W54). The exact Cauchy
determinant quotients in (W34), applied to $S$ itself, give local
prefix determinants at least $e^{-2m^2W}$. Fixed-order derivatives
of $S$ and the same divided-difference integral formula bound all
entries of $H_j^S=T_jS_jT_j^*$ uniformly. The determinant/norm
argument of (W53) therefore gives
$H_j^S\succeq s_{W,m}I$ for one $s_{W,m}>0$.

There is consequently one $\sigma_S(W,m,\delta)>0$ such that every
finite admissible reference family satisfies
$\widehat S\succeq\sigma_S I$, where hats denote the full block
Newton congruence. To justify uniformity using even the qualitative
model-space theorem, suppose these finite lower bounds had infimum
zero. Concatenate translated bad finite families, with gaps at least
$\delta$, into one countable family above a fixed start. Both $S$
and the physical Newton maps are invariant under common translation.
The resulting family satisfies the Blaschke condition and the same
uniform-minimality bound just proved, so its model spaces have one
Riesz lower bound $b>0$.

For $f_j=\sum_l(T_j^*y_j)_lk_{x_{j,l}}$ this bound gives

$$
y^*\widehat S y=\left\|\sum_jf_j\right\|^2
 \ge b\sum_j\|f_j\|^2
 =b\sum_jy_j^*H_j^S y_j
 \ge bs_{W,m}\sum_j\|y_j\|^2.
$$

It applies to every bad block inside that one family, a contradiction.
Thus a uniform $\sigma_S$ exists without requiring a formula for the
model-space theorem's constants. This is the classical reference
supplier for the actual estimate, rather than a replacement of $L_0$.

### Pay nearby and distant actual blocks in the same metric

Put $r=2m-2$. For hull distance $d\ge H\ge8$, (W52), the
fixed-order derivatives of $S$ and the divided-difference formula give

$$
\| (\widehat R-\widehat S)_{ij}\|_{\rm op}
 \le mC_r(1+d)e^{-d}.
$$

In a fixed block row enumerate only the hulls with distance greater
than $H$, separately on each side. Their distances are at least
$H+k\delta$, $k\ge0$. Since $(1+d)e^{-d}$ decreases, the entire
distant-block row sum is at most

$$
2mC_re^{-H}\left[\frac{1+H}{1-q}
 +\frac{\delta q}{(1-q)^2}\right],\qquad q=e^{-\delta}.
$$

Choose $H$ so this is at most $\sigma_S/4$. Each remaining pair of
hulls lies in one physical interval of length $H+2W$. By (W33), above
one height its actual-minus-reference error in total $C^r$ norm is at
most $\varepsilon$. Newton interpolation bounds each such block by
$m\varepsilon$ in operator norm. There are at most
$3+2H/\delta$ nearby blocks per row, including the diagonal. Choose
$\varepsilon$ with
$m(3+2H/\delta)\varepsilon\le\sigma_S/4$, and choose $A_*$ to
cover the corresponding (W33) start, (W52)'s order-$r$ start and
positivity of $J$.

The same Hermitian block row-sum estimate as in (W54) gives

$$
\|\widehat R-\widehat S\|_{\rm op}\le\sigma_S/2,
\qquad \widehat R\succeq\sigma_S I/2.
$$

For the original arbitrary complex coefficients $c_j$, use (W54)'s
exact $y_j=T_j^{-*}\operatorname{diag}(\sqrt{J(a_{j,l})})c_j$.
The full physical form therefore satisfies

$$
\boxed{Q_{L_0}(c)\ge\frac{\sigma_S}{2}
 \sum_j\left\|T_j^{-*}
 \operatorname{diag}(\sqrt{J(a_{j,l})})c_j\right\|_2^2.}
\tag{W61}
$$

All interactions are included. The nearby/distant split uses the
complete normalized kernel; its direct and reflected infinite
integrals remain those already controlled in (W33) and (W52).
The constants are independent of total cluster count, coefficient
sizes and internal node gaps. Repeated physical nodes are first merged,
as in (W54).

The local node cap $m$, positive hull gap $\delta$ and bounded width
$W$ remain hypotheses. Neither uniformity as $\delta\downarrow0$ or
$m\to\infty$, nor a raw coefficient-norm lower bound, is asserted.
The arbitrary-density real-profile class of (W60) still has its own
sufficiently large gap. Fixed-window all-order positivity, the original
strict all-integer Robin upper and RH remain unproved.


## Geometric windows allow linearly growing local sign counts

The local degree need not have one fixed upper bound across all windows
if their centers grow geometrically. Keep the complete actual $L_0$ and
the exact physical-to-Hardy transport in (W58)--(W60). Choose once
their fixed small complex neighborhoods with the strip clearance in
(W46)--(W47); the resulting $h,\Lambda$ and
$w=\operatorname{arctanh}h$ are fixed independently of all degrees.
For any fixed $q_{\rm geo}>1$, put

$$
\tau=\frac{q_{\rm geo}-1}{q_{\rm geo}+1},\qquad
\kappa=\frac{\tau}{\log\Lambda}>0.
$$

One start $A_*$ works for every finite family of real signed profiles
on $[A_j-w,A_j+w]$ with $A_1\ge A_*$,
$A_{j+1}\ge q_{\rm geo}A_j$ and local separator degree at most
$\lfloor\kappa A_j\rfloor$. The conclusion below pays all their
interactions. This complements (W60), whose same local degree cap is
fixed across the family, and (W61), whose prescribed fixed gap retains
a local node cap. It is a `repo-derived` paper application without a
literature-priority or Lean-verification claim.

### A fixed complex neighborhood controls the full separated kernel

There are fixed $r,A_0,D_0,C>0$ such that the actual normalized
continuation satisfies

$$
\boxed{\sup_{|u|,|v|\le r}|R(A+u,B+v)|
 \le C(1+|A-B|)e^{-|A-B|}
\quad(A,B\ge A_0,\ |A-B|\ge D_0).}
\tag{W62}
$$

Here $A,B$ are real, the offsets are complex, and diagonal square roots
continue their positive-real values. This is not obtained by assuming
uniformity over the derivative orders in (W52).

To prove it, take $B\ge A+D_0$, $a=A+u$, $b=B+v$ and use (W52)'s
exact forward expression

$$
\begin{aligned}
\mathcal U(a,b)&=\frac{L_0(a,b)}{\Phi(a)\Phi(b)}\\
 &=\frac14\int_0^\infty
 [(a+b+2t)e^{F_+}-(b-a+2t)e^{F_-}]\,dt,\\
F_+&=g(a+t)-g(a)+g(b+t)-g(b),\\
F_-&=g(a-t)-g(a)+g(b+t)-g(b).
\end{aligned}
$$

The even holomorphic logarithm $g$ and its right-tail derivative in
(W47) give $\Re g'(s+iy)\le-ce^{2s}$ for $s\ge T$, uniformly
on a smaller closed strip. Oddness of $g'$ gives
$-\Re g'(s+iy)\le0$ for $s\le-T$ after increasing $T$; the
remaining compact strip is bounded. Consequently, for high $A$,

$$
-\Re g'(s+iy)\le C_1e^{2A}
\qquad(s\le A+r,\ |y|\le r).
$$

Horizontal integration bounds
$\Re[g(a-t)-g(a)]\le C_1e^{2A}t$ and
$\Re[g(b+t)-g(b)]\le-c_1e^{2B}t$ for every $t\ge0$.
Choose $D_0$ with $C_1e^{-2D_0}\le c_1/2$.
Then $\Re F_-\le-(c_1/2)e^{2B}t$ on the entire half-line,
including $\Re(a-t)<0$. The two right-tail increments in $F_+$
give the same or stronger bound. Hence these complex forward integrals
are locally uniformly convergent and

$$
|\mathcal U(a,b)|\le C_2(A+B+1)e^{-2B}.
$$

Iterated identity theorems identify the formula with the already owned
continuation, because it agrees on positive real positions. No reflected
exterior or theta term has been deleted.

For normalization, write $z=A+u$ and reuse the exact diagonal identity

$$
d_*(z)=\frac{e^{2z}J(z)}{z\Phi(z)^2}
 =\frac{A}{8\pi z}M_A(u,u).
$$

By (W46), $M_A(u,u)=1+O(A^{-1})$ on the fixed disc, so $d_*$
is close to $1/(8\pi)$ there. Its positive-real square-root branch
is holomorphic and consistent on overlapping high discs. Therefore

$$
\mathcal N(z)=\frac{\Phi(z)}{\sqrt{J(z)}}
 =\frac{e^z}{\sqrt z\sqrt{d_*(z)}},\qquad
|\mathcal N(A+u)|\le C_3e^A/\sqrt A.
$$

Since $R(a,b)=\mathcal N(a)\mathcal N(b)\mathcal U(a,b)$,
its modulus is at most
$C(A+B+1)e^{A-B}/\sqrt{AB}$.
For $A\ge1$, $(A+B+1)/\sqrt{AB}\le3+B-A$.
Symmetry covers $A\ge B+D_0$ and proves (W62).

### Pay different local degrees in the original Hardy metric

Write $\varrho$ for the fixed complex Hardy-disc radius denoted $R$
in (W55), with $h=\varrho/4$ and $q_0=2/\varrho$.
Its $\operatorname{arctanh}$ image lies in (W62)'s offset disc.
For each finite real physical measure $\mu_j$, let $\nu_j$ be its
exact positive transport from (W58). Require

$$
\epsilon_jp_j\nu_j\ge0,\qquad
p_j(z)=\prod_{l=1}^{r_j}(z-s_{j,l}),\qquad
s_{j,l}\in[-h,h],\quad \epsilon_j\in\{-1,1\}.
$$

Include $r_j=0$; repeated roots and atoms at roots are allowed.
Put $a_{j,k}=\int z^k\,d\nu_j(z)$ and
$Q_j=Q_H(\nu_j)=\sum_{k\ge0}a_{j,k}^2$.
The exact normalizer from (W59),

$$
c_A(z)=\cosh(u)\sqrt{M_A(u,u)}
 =\sqrt{J(A+u)}d_A(u),\qquad u=\operatorname{arctanh}z,
$$

is holomorphic and uniformly bounded on this fixed disc by (W46).
Thus (W62) bounds the complete transported cross kernel

$$
c_{A_i}(z)c_{A_j}(v)
R(A_i+\operatorname{arctanh}z,A_j+\operatorname{arctanh}v)
$$

on the bidisc by $C_4(1+d_{ij})e^{-d_{ij}}$,
$d_{ij}=|A_i-A_j|\ge D_0$. Its Cauchy coefficients are bounded
by this number times $\varrho^{-k-l}$.
The sign-polynomial radius comparison already proved before (W55)
and Cauchy--Schwarz give

$$
\sum_{k\ge0}\varrho^{-k}|a_{j,k}|
 \le\sqrt{4/3}\left(\sum_{k\ge0}q_0^{2k}a_{j,k}^2\right)^{1/2}
 \le2\sqrt3\,\Lambda^{r_j/2}\sqrt{Q_j}.
$$

The cross series is absolutely convergent on the supports, so finite
total variation justifies its integration. With $K=12C_4$, independent
of all degrees and centers, the full physical bilinear form satisfies

$$
\boxed{|B_{L_0}(\mu_i,\mu_j)|
 \le K(1+d_{ij})e^{-d_{ij}}
 \Lambda^{(r_i+r_j)/2}\sqrt{Q_iQ_j}.}
\tag{W63}
$$

No root separation, local density, derivative factorial or total-
variation substitute enters this constant. The metric is the same
$Q_j$ that pays the actual local positive form.

### Geometric spacing absorbs linearly growing sign counts

For $i<j$, the center condition gives
$d_{ij}\ge\tau(A_i+A_j)$. If
$r_j\le\lfloor\kappa A_j\rfloor$, then
$\Lambda^{(r_i+r_j)/2}\le e^{d_{ij}/2}$.
Thus (W63) costs at most
$K(1+d_{ij})e^{-d_{ij}/2}\sqrt{Q_iQ_j}$.

Choose $A_*\ge\max(A_0,A_1)$, covering the starts in (W62) and
(W58), and so large that, with $D=(q_{\rm geo}-1)A_*$ and $q_D=e^{-D/2}$,

$$
D\ge\max(D_0,1,2w+1),\qquad
2K\left[\frac{q_D}{1-q_D}
 +\frac{Dq_D}{(1-q_D)^2}\right]\le\frac14.
$$

Every successive center gap is at least $D$, so the $n$th next center
on either side has distance at least $nD$.
The function $(1+d)e^{-d/2}$ decreases for $d\ge1$; hence the
display bounds the entire cross row sum independently of the number
of windows. Also $\kappa\le1/\log\Lambda$, so (W58) supplies
each local credit $Q_{L_0}(\mu_j)\ge Q_j/2$.
The same symmetric row estimate as in (W60) pays all interactions and
leaves

$$
\boxed{Q_{L_0}\!\left(\sum_{j=1}^N\mu_j\right)
 \ge\frac14\sum_{j=1}^NQ_H(\nu_j)>0}
\tag{W64}
$$

unless all profiles vanish. Strictness uses the same compact moment
uniqueness as (W58). This one $A_*$ and the one slope $\kappa$ work
for every finite $N$, arbitrary local sample counts and densities, and
the displayed different local degrees. They do not depend on the
maximum degree in the family. In particular, the permitted local sign
counts can be unbounded along the geometric windows.

Taking $q_{\rm geo}=\varphi^3$ gives $\tau=\varphi^{-1}$ and
$\kappa=1/(\varphi\log\Lambda)$. This specifies an allowed
spacing of physical windows; it supplies no identification with all
prime configurations or Robin integers. The growing complexity is
paid by growing gaps. Arbitrary-density small-gap positivity,
unrestricted complex-measure positivity and all-order positivity on
one fixed window remain unproved, as do the original strict Robin
upper and RH. This is not a diagonal choice of fixed-degree thresholds:
the additional actual input is (W62), whose fixed complex neighborhood
pays the explicit degree factors in (W63).

## A compact core has a paid coupling to growing remote profiles

The arbitrary compact core in (W51) can be coupled to the entire remote
profiles of (W64), whose local sign counts need not have a common fixed
cap. Reuse the complete actual $\Phi,L_0,J$, the exact transport in
(W58), and the fixed discs, $h,w,\Lambda$ in (W62)--(W64), with their
closed-strip clearance chosen once. The additional actual input is a
holomorphic compact-to-remote bound retaining both cancellations in
(W50). This is a `repo-derived` paper application without a
literature-priority or Lean-verification claim.

### Keep the compact cancellations on a fixed complex remote disc

Fix $U>0$. There are $A_U,C_U>0$ such that, with the same fixed small
remote offset radius $r$ and the positive-real diagonal square-root
continuation from (W62),

$$
\boxed{\sup_{\substack{0<a\le U\\|v|\le r}}
\left|\frac{L_0(a,A+v)}{\sqrt{J(a)}\sqrt{J(A+v)}}\right|
\le C_U\frac{e^{-A}}{\sqrt A}\qquad(A\ge A_U).}
\tag{W65}
$$

Only the remote variable is complex. At $a=0$ the original kernel
vanishes; no normalized value is assigned there.

To obtain the bound, put $b=A+v$ and use (W50)'s complete forward
integral with bracket

$$
B(a,b,t)=(a+b+2t)\Phi(t+a)-(b-a+2t)\Phi(t-a).
$$

Its first cancellation is $B(0,b,t)=0$. The same grouping of
$\partial_aB$ used in (W50) bounds its terms without $b$ uniformly by
compactness and the complete derivative tails. Its second cancellation
is $\Phi'(a)+\Phi'(-a)=0$, which bounds the coefficient of $b$ by
$C_Ut$. Thus $|B(a,b,t)|\le C_Ua(1+|b|t)$ for every $t\ge0$.
The already used right-strip bound for $g=\log\Phi$ gives

$$
\left|\frac{\Phi(b+t)}{\Phi(b)}\right|
\le e^{-ce^{2A}t}.
$$

These bounds give locally uniform convergence of the entire forward
integral in $b$. The identity theorem identifies its continuation with
the actual kernel, and direct integration yields

$$
\left|\frac{L_0(a,b)}{\Phi(b)}\right|
\le C_Ua(e^{-2A}+Ae^{-4A})\le C_Uae^{-2A}.
$$

No reflected part with $t-a<0$ or remote tail was removed. Divide by
$\sqrt{J(a)}\ge\sqrt{m_U}a$ from (W49), and use
$|\Phi(b)/\sqrt{J(b)}|\le Ce^A/\sqrt A$ from (W62), to prove (W65).

### Use the same Hardy metric for each complete remote profile

Let $\mu$ be any finite complex Borel measure on $[0,U]$, and retain
$\mathcal M(\mu)=\int\sqrt{J(a)}\,d|\mu|(a)$ from (W51).
For a real physical profile $\lambda$ on $[A-w,A+w]$, let $\nu$ be
its exact transport from (W58). Require an explicit monic separator
$p$ of degree $r_A$, roots in $[-h,h]$, with $\epsilon p\nu\ge0$;
repeated roots and atoms at roots remain allowed. Put $Q=Q_H(\nu)$.

For $u=\operatorname{arctanh}z$, the existing normalizer
$c_A(z)=\sqrt{J(A+u)}d_A(u)$ is holomorphic and uniformly bounded
on the fixed Hardy disc $|z|\le\varrho$. Consequently

$$
F_A(a,z)=\frac{d_A(u)L_0(a,A+u)}{\sqrt{J(a)}}
$$

is holomorphic there and bounded by $C_Ue^{-A}/\sqrt A$, uniformly
for $0<a\le U$. Its Cauchy coefficients, the already proved scalar
moment bound in (W63), and integration against the compact measure give

$$
\boxed{|B_{L_0}(\mu,\lambda)|
\le C_U\mathcal M(\mu)\frac{e^{-A}}{\sqrt A}
       \Lambda^{r_A/2}\sqrt Q.}
\tag{W66}
$$

This uses the same $Q$ that pays the local positive form; no local total
variation replaces it. For a complex remote profile, impose the explicit
separator condition separately on its transported real and imaginary
parts, each of degree at most $r_A$. Take $Q$ to be the sum of their two
Hardy forms. Splitting the bilinear form and absorbing $\sqrt2$ gives
(W66) with the same independence from degree, roots and density.

### Spend the whole remote credit once

Fix $q_{\rm geo}>1$ and retain
$\tau=(q_{\rm geo}-1)/(q_{\rm geo}+1)$ and
$\kappa=\tau/\log\Lambda$. Take any finite family of such real or
complex remote profiles $\lambda_j$, with

$$
A_1\ge T\ge T_0(U,q_{\rm geo}),\qquad
A_{j+1}\ge q_{\rm geo}A_j,\qquad
r_j\le\lfloor\kappa A_j\rfloor.
$$

The start includes that of (W64), $A_U$, $U+w+1$, and
$(q_{\rm geo}-1)T\ge1$. Write $E=\sum_jQ_j$ and keep the exact
nonnegative cross allowance

$$
\Gamma=\sum_j A_j^{-1}e^{-2A_j}\Lambda^{r_j}.
$$

Estimate (W66) and Cauchy--Schwarz give
$|B_{L_0}(\mu,\sum_j\lambda_j)|
\le C_U\mathcal M(\mu)\sqrt{E\Gamma}$.
The actual degree bounds and the center spacing imply

$$
\Gamma\le
\frac{e^{-(2-\tau)T}}
 {T[1-e^{-(2-\tau)(q_{\rm geo}-1)T}]}.
$$

Indeed $A_j\ge T+(j-1)(q_{\rm geo}-1)T$, and
$\Lambda^{r_j}\le e^{\tau A_j}$. The denominator is bounded away
from zero under the stated start. Reuse (W64), separately for real and
imaginary parts when required, to obtain
$Q_{L_0}(\sum_j\lambda_j)\ge E/4$. Young's inequality spends half
of this same credit on the full cross term and leaves

$$
\boxed{Q_{L_0}\!\left(\mu+\sum_j\lambda_j\right)
\ge Q_{L_0}(\mu)+\frac18\sum_jQ_j
  -C_U\frac{e^{-(2-\tau)T}}T\mathcal M(\mu)^2.}
\tag{W67}
$$

One start works for every finite family size, local sample density and
permitted degree; those degrees may grow without a common fixed cap.
The compact measure has no sign-count restriction. Its atom at zero
contributes nothing. This extends (W51)'s remote point block to the
entire growing-degree profiles and retains all their mutual interactions.

The compact size $U$ and $q_{\rm geo}$ are fixed; no uniformity as
$U\to\infty$ or $q_{\rm geo}\downarrow1$ is asserted. The estimate
assigns no sign to $Q_{L_0}(\mu)$ and supplies no comparison of
$\mathcal M(\mu)^2$ with a nearly null compact form. It gives neither
unrestricted remote-complexity control nor all-order positivity on a
fixed window. The strict original joint Robin upper and RH remain
unproved.


## One sign change on the complete high half-line

Keep the actual complete $L_0$, its positive diagonal $J$ and the
normalized kernel $R$. There are constants $A_*,c_*>0$ such that

$$
\boxed{\partial_a\partial_b\log R(a,b)
 \ge c_*e^{-2|a-b|}\qquad(a,b\ge A_*).}
\tag{W68}
$$

The start is independent of the distance between the positions. It
therefore pays the complete form of an arbitrarily dense real profile
with at most one global sign change on any compact subset of
$[A_*,\infty)$, without a width restriction. This complements
(W30)--(W36), whose starts may depend on width and sign degree, and
(W60)--(W61), which retain their separation or local node conditions.
The new input is the actual distant-position mixed logarithmic
derivative below. The existing local comparison and Schur-anchor
identity are reused; no new general positivity criterion,
literature-priority assertion or Lean verification is claimed.

### Differentiate an exact endpoint moment

Reuse global concavity of $g=\log\Phi$ from (W19), and the fixed-order
theta bounds preceding (W33). For $p=-g'$ they give

$$
\begin{aligned}
p(x)&=2\pi e^{2x}-\tfrac92+O(e^{-2x}),\\
p'(x)&=4\pi e^{2x}+O(e^{-2x}),\\
p''(x)&=8\pi e^{2x}+O(e^{-2x})
\qquad(x\longrightarrow\infty).
\end{aligned}
$$

The same owned bounds give $|g^{(k)}(x)|\le Ce^{2|x|}$ for
$1\le k\le3$. Beyond one start, $p\ge1$, $p'/p\to2$, and
$p(a)/p(b)$ is between fixed positive multiples of $e^{2a-2b}$ for
$b\ge a$. All constants $C$ below are independent of the two
positions, their ratio and their distance beyond that start.

Put $q=p(b)$ and retain the complete endpoint moments

$$
E_b(t)=\frac{\Phi(b+t)}{\Phi(b)},\qquad
I_k(b)=\int_0^\infty t^kE_b(t)\,dt,\qquad
\eta(b)=\frac{I_1(b)}{I_0(b)}.
$$

Global concavity gives $E_b(t)\le e^{-qt}$. After $t=z/q$, write

$$
G_b(z)=-\int_0^z\frac{p(b+v/q)}q\,dv,\qquad
M_k(b)=\int_0^\infty z^ke^{G_b(z)}\,dz,
\qquad I_k=q^{-k-1}M_k.
$$

The tail derivative bounds give, for every $z\ge0$,

$$
G_b(z)\le-z,\qquad
|G_b(z)+z|+|\partial_bG_b(z)|
 \le\frac{Cz^2}{q}e^{2z/q}.
$$

For the derivative, set $\kappa=q'/q$. Its exact integrand is

$$
\partial_b\frac{p(b+v/q)}q
 =\frac{p'(b+v/q)-\kappa p(b+v/q)}q
 -\kappa\frac vq\frac{p'(b+v/q)}q.
$$

The first numerator vanishes at $v=0$ and its derivative in $v/q$
is $O(qe^{2v/q})$; the second term has the same
$O((v/q)e^{2v/q})$ bound. Integration proves the displayed estimate,
including the dependence of the scale $q$ on $b$. The bound for
$G_b+z$ follows from the integral remainder for $p(b+u)-q$.
For $q\ge4$, the exponential difference bound and differentiation
under these integrable majorants yield
$M_k=k!+O(q^{-1})$, $M_k'=O(q^{-1})$ for $k=0,1$. Consequently

$$
\boxed{\eta=q^{-1}(1+O(q^{-1})),\qquad
 \eta'=-q'/q^2+O(q^{-2}),\qquad
 I_0'/I_0=O(1),\qquad (b\eta)'\le-b/q}
\tag{W69}
$$

at one larger start. The last sign uses $q'/q\to2$ and $b\to\infty$;
it is uniform over all larger $b$.

### The full distant remainder is smaller than its mixed curvature

Suppose $b\ge a+D$, and set $P=p(a)$,
$\rho=P/q$, $X=(b/a)\rho$. Reuse (W52)'s exact full formula:

$$
\begin{aligned}
\mathcal U(a,b)&=\frac{L_0(a,b)}{\Phi(a)\Phi(b)}
 =\frac14\int_0^\infty E_b(t)H(a,b,t)\,dt,\\
H&=(a+b+2t)f_+-(b-a+2t)f_-,\qquad
 f_\pm=\frac{\Phi(a\pm t)}{\Phi(a)}.
\end{aligned}
$$

The reflected factor retains the original even theta function also
when $t>a$. Global concavity gives $f_\pm\le e^{Pt}$ on this whole
half-line, and the owned whole-line derivatives give
$|g^{(k)}(a\pm t)|\le CPe^{2t}$ for $k\le3$.
Let $r_\pm=f_\pm-1\mp g'(a)t$. The exact integral Taylor remainder
and its first $a$ derivative satisfy

$$
|r_\pm|+|\partial_ar_\pm|
 \le CP^2t^2(1+Pt)e^{(P+6)t}.
$$

Indeed $\partial_t^2f_\pm=(g''(a\pm t)+g'(a\pm t)^2)f_\pm$,
while its $a$ derivative uses $g'''$ and
$\partial_af_\pm=[g'(a\pm t)-g'(a)]f_\pm$;
the last difference is bounded by $CPte^{2t}$. These bounds apply
to every point of the integral remainder, including negative
reflected arguments.

Keep the exact affine coefficients:

$$
\begin{aligned}
H&=2a+2bg'(a)t+H_2,\\
H_2&=4g'(a)t^2+(a+b+2t)r_+-(b-a+2t)r_-,\\
Z&=\frac{2\mathcal U(a,b)}{aI_0(b)}=1+T+F,\\
T&=\frac{g'(a)}a\,b\eta(b),\qquad
F=\frac1{2aI_0(b)}\int_0^\infty E_b(t)H_2(a,b,t)\,dt.
\end{aligned}
$$

The bound for $r_\pm$ controls $H_2$, its $a$ derivative and its
explicit $b,ab$ derivatives with the additional factor
$a+b+1+t$. Differentiating the normalized density
$E_b(t)/I_0(b)$ multiplies it by

$$
g'(b+t)-g'(b)-I_0'/I_0,
\qquad
\left|g'(b+t)-g'(b)-I_0'/I_0\right|
 \le C(1+qt e^{2t}).
$$

Choose $D$ and the start so that $q\ge2(P+8)$. Every differentiated
remainder is then dominated by a polynomial times $e^{-qt/2}$.
Division by $I_0$ costs $O(q)$, the $t^2$ integral costs $O(q^{-3})$,
and a factor $Pt$ or $qt$ costs $P/q$ or a fixed constant.
The affine $t$ term costs one further $q^{-1}$; differentiating
$1/a$ costs at most one. Since $a\ge1$ and $b\ge a$, this proves

$$
\boxed{\max_{i,j\in\{0,1\}}|\partial_a^i\partial_b^jF|
 \le C\frac ba\rho^2=CX\rho,\qquad
 T_{ab}\ge X,\qquad
 \max_{i,j\in\{0,1\}}|\partial_a^i\partial_b^jT|\le CX.}
\tag{W70}
$$

For $T_{ab}$ use (W69) and
$\partial_a(g'(a)/a)=-(p'(a)-p(a)/a)/a\le-P/a$
at the same larger start. Thus the main mixed derivative has a
positive lower bound before either remainder is estimated.

Both $\rho$ and $X$ tend uniformly to zero as $D\to\infty$, since
$X\le C(1+b-a)e^{-2(b-a)}$. Fix one $D$ so large that (W70)
gives $|Z-1|\le1/2$, $Z_{ab}\ge3X/4$ and
$|Z_aZ_b|\le X/16$. Then

$$
\partial_a\partial_b\log Z
 =Z_{ab}/Z-Z_aZ_b/Z^2\ge X/4.
$$

The normalizations from $R$ to $\mathcal U$ to $Z$ are exact positive
separable factors, so they leave this mixed logarithmic derivative
unchanged. Also $X\ge ce^{-2(b-a)}$. This proves (W68) throughout
the distant region; symmetry covers the opposite ordering.
For $|a-b|\le D$, reuse (W30) with this one fixed width $D$.
The maximum of its start and the preceding start, with a smaller
$c_*>0$, proves (W68) on the entire high half-line.

### One anchor pays every cross term of a one-change measure

Fix $s\ge A_*$. Define the nonnegative functions

$$
\begin{aligned}
\Xi_s(a,b)&=
 \int_{\min(a,s)}^{\max(a,s)}
 \int_{\min(b,s)}^{\max(b,s)}e^{-2|u-v|}\,dv\,du,\\
\Gamma_s(a,b)&=R(a,s)R(s,b)
 \bigl(1-e^{-c_*\Xi_s(a,b)}\bigr).
\end{aligned}
$$

Since $R(s,s)=1$, integration of (W68) gives

$$
\Psi_s(a,b):=\log R(a,b)-\log R(a,s)-\log R(s,b)
 =\int_s^a\int_s^b\partial_u\partial_v\log R(u,v)\,dv\,du.
$$

Its sign is that of $(a-s)(b-s)$ and
$|\Psi_s|\ge c_*\Xi_s$. For the already-owned rank-one Schur residual
$B_s=R(a,b)-R(a,s)R(s,b)$ this implies
$\operatorname{sgn}((a-s)(b-s))B_s\ge\Gamma_s$ off the anchor:
use $e^x-1\ge1-e^{-x}$ for $x\ge0$ and the exact exponential
identity for $x\le0$. Both sides vanish at the anchor.

Let $\mu\ne0$ be a real finite measure of compact support in
$[A_*,\infty)$, and suppose
$\epsilon(a-s)\mu\ge0$ for some $\epsilon\in\{-1,1\}$.
Set $d\nu=\sqrt J\,d\mu$ and $z_s=\int R(s,a)\,d\nu(a)$.
Reuse (W36)'s exact Schur decomposition to obtain

$$
\boxed{Q_{L_0}(\mu)\ge z_s^2+
 \iint\Gamma_s(a,b)\,d|\nu|(a)d|\nu|(b)>0.}
\tag{W71}
$$

The sign contract pays the complete residual double integral.
If there is mass off $s$, $\Gamma_s$ is strictly positive on its
product with itself. Otherwise the nonzero measure is an atom at
$s$ and $z_s\ne0$. The atom at $s$ has unrestricted sign and has
not been dropped. Compactness makes all integrals finite; no upper
endpoint appears in $A_*$ or $c_*$. One-signed measures were already
covered by (W14).

This pays arbitrary density and arbitrarily wide compact support for
one global sign change. It does not cover fixed degrees $r\ge2$ on
this whole half-line, arbitrary complex measures, the linear span of
the sign cones or unrestricted all-order positivity on one fixed
physical interval. No compact-core sign, strict all-integer Robin
upper or RH proof follows. The result is a repository-derived paper
estimate, not a Lean/kernel-certified theorem.


## Fixed finite sign degree on the complete high half-line

Keep the same complete actual kernel $L_0$, its positive diagonal $J$
and $R=L_0/\sqrt{J(a)J(b)}$. For every prescribed integer $m\ge3$
there is one $A_m$ such that all ordered row/column minors of $R$
through size $m$, including their Hermite-confluent versions, are
strictly positive for nodes in $[A_m,\infty)$. The start depends on
$m$ but not on support width, sample density or the upper endpoint.
The new input is a relative estimate for the actual distant mixed
jets. Fixed-width (W33), the classical Chebyshev criterion and the
existing Schur consumer are reused. This is a paper derivation, with
no literature-priority or Lean/kernel-verification claim.

### Complete endpoint moments retain their fixed jets

Fix $n\ge2$, put $g=\log\Phi$, $P=p(a)=-g'(a)$, $q=p(b)$,
$\rho=P/q$ and $r=b/a$ for $b\ge a+D$. All constants below may
depend on $n$, not on either position or their distance. The fixed-order
theta bounds preceding (W33) give, for every fixed derivative order,

$$
p(x)=2\pi e^{2x}-\tfrac92+O(e^{-2x}),\qquad
p^{(j)}(x)=2^{j+1}\pi e^{2x}+O_j(e^{-2x})\quad(j\ge1).
$$

They also give the owned whole-line bounds on derivatives of $g$.
Use (W69)'s complete moments $I_k$, now through $k=n$, and put
$\mu_k=I_k/I_0$. For $0\le k\le n$ and $0\le j\le n-1$,

$$
\boxed{\partial_b^j\mu_k(b)
 =k!(-2k)^j q^{-k}+O_n(q^{-k-1})\quad(k\ge1),\qquad
\mu_0=1.}
\tag{W72}
$$

Here and below $0^0=1$, while a positive derivative of the constant
$\mu_0$ is zero. To justify every differentiated moment, retain the
exact change $t=z/q$ from (W69). Set
$R_b(v)=p(b+v/q)/q$ and $G_b(z)=-\int_0^zR_b(v)dv$.
The identity

$$
R_b(v)-1=\int_0^v\frac{p'(b+s/q)}{q^2}\,ds
$$

and the fixed-order bounds give

$$
|\partial_b^j(G_b(z)+z)|
 \le\frac{C_nz^2}{q}(1+z/q)^{n-1}e^{2z/q}
\quad(0\le j\le n-1),\qquad G_b(z)\le-z.
$$

For $j\ge1$ the left side is just $|\partial_b^jG_b|$.
The chain rule gives integrable majorants consisting of a fixed
polynomial times $e^{-z/2}$ once $q$ exceeds one fixed constant.
The exponential difference bound and differentiation under these
majorants yield
$M_k:=\int_0^\infty z^ke^{G_b(z)}dz=k!+O_n(q^{-1})$ and
$M_k^{(j)}=O_n(q^{-1})$ for $1\le j\le n-1$.
Since $I_k=q^{-k-1}M_k$, $q'/q=2+O(q^{-1})$, and all positive
fixed derivatives of $q'/q$ are $O_n(q^{-1})$, the quotient rule
proves (W72). In particular all fixed positive derivatives of
$\log I_0$ are bounded.

### An exact finite-rank expansion with a relative remainder

Let

$$
c_k(a)=\frac{\Phi^{(k)}(a)}{k!\Phi(a)},\qquad
\epsilon_k=\begin{cases}0&k\text{ even},\\1&k\text{ odd},\end{cases}
$$

and define

$$
U_0=1,\qquad
U_k=\begin{cases}
c_k+2c_{k-1}/a,&k\ge2\text{ even},\\
c_k/a,&k\text{ odd},
\end{cases}
\qquad V_k(b)=b^{\epsilon_k}\mu_k(b).
$$

Retain (W70)'s exact positive separable normalization

$$
Z(a,b)=\frac{2L_0(a,b)}{a\Phi(a)\Phi(b)I_0(b)}.
$$

Taylor's formula inside its full forward-variable integral gives

$$
\boxed{Z(a,b)=\sum_{k=0}^{n-1}U_k(a)V_k(b)+F_n(a,b),\qquad
\max_{0\le i,j<n}|\partial_a^i\partial_b^jF_n|
 \le C_n r\rho^n.}
\tag{W73}
$$

The parity and the $2c_{k-1}/a$ term follow before any estimate:
if $f_\pm=\Phi(a\pm t)/\Phi(a)$, then

$$
\frac{(a+b+2t)f_+-(b-a+2t)f_-}{2a}
 =\sum_{k\text{ even}}c_kt^k
  +\frac ba\sum_{k\text{ odd}}c_kt^k
  +\frac2a\sum_{k\text{ odd}}c_kt^{k+1}.
$$

This line denotes the Taylor coefficients, not an interchange of an
infinite Taylor series with the improper integral. Truncate at degree
$n-1$. The omitted last term from $2t(f_+-f_-)$ is included in $F_n$.

For completeness, the integral Taylor remainder of order $n$ obeys

$$
\max_{0\le i<n}|\partial_a^i
 [f_\pm-\sum_{k<n}(\pm1)^kc_kt^k]|
 \le C_nP^nt^n(1+Pt)^{n-1}e^{(P+C_n)t}.
$$

Here $c_k$ already contains the sign of $\Phi^{(k)}$; the plus
expansion uses $c_kt^k$ and the minus expansion uses $(-1)^kc_kt^k$.
The remainder estimate follows from differentiating the integral
Taylor remainder, the owned whole-line derivative bounds, global
concavity $f_\pm\le e^{Pt}$, and
$|\partial_a^j\log f_\pm|\le C_nPt e^{2t}$ for fixed $j\ge1$.
It remains valid when $a-t<0$.
After dividing the affine coefficients by $2a$, every required
$a$ derivative is bounded by a constant times
$r(1+t)P^nt^n(1+Pt)^{n-1}e^{(P+C_n)t}$.
The explicit $b$ derivatives of those coefficients have the same bound.
Each derivative of the normalized density
$[\Phi(b+t)/\Phi(b)]/I_0(b)$ is the density times a fixed polynomial
in logarithmic derivatives bounded by $C_n(1+qt e^{2t})$.
Choose $D$ and the high start so that $q\ge2(P+C'_n)$.
Integrating the resulting bounds, including all density derivatives,
against $Ce^{-qt}q$ proves (W73). No part of either half-line integral
is removed.

### Scale the complete jet before comparing its determinant

The fixed-order theta expansion and Bell's derivative formula give
$c_k^{(i)}=(-1)^k(2k)^iP^k/k!+O_n(P^{k-1})$ for $k\ge1$.
Set

$$
\alpha_k=P^ka^{-\epsilon_k},\qquad
\beta_k=q^{-k}b^{\epsilon_k},\qquad
 d_k=\alpha_k\beta_k=r^{\epsilon_k}\rho^k.
$$

Let $\widehat U$ have entries $U_k^{(i)}/\alpha_k$ and
$\widehat V$ entries $V_k^{(j)}/\beta_k$, with $0\le i,j,k<n$.
Equations (W72)--(W73) imply

$$
\widehat U_{ik}=
 \frac{(-1)^k}{k!}(2k)^i+O_n(a^{-1}+P^{-1}),\qquad
\widehat V_{jk}=k!(-2k)^j+O_n(b^{-1}+q^{-1}).
$$

The $k=0$ columns are exactly $(1,0,\ldots,0)^T$.
These fixed Vandermonde limits are invertible, so both inverse norms
are bounded beyond a start depending only on $n$. Write the complete
mixed jet matrix $\mathcal J_nZ=[\partial_a^i\partial_b^jZ]_{i,j<n}$
as

$$
\widehat U^{-1}(\mathcal J_nZ)\widehat V^{-T}
 =\operatorname{diag}(d_0,\ldots,d_{n-1})+\mathcal E,
\qquad \|\mathcal E\|\le C_nr\rho^n.
$$

Since $r\ge1$ and $r\rho\le C(1+b-a)e^{-2(b-a)}$, choose one
$D=D_n$ so large that $r\rho<1$. Successive $d_k$ then decrease:
their ratios are $r\rho$ and $\rho/r$. Consequently

$$
\|\operatorname{diag}(d_k)^{-1}\mathcal E\|
 \le C_n\frac{r\rho^n}{r^{\epsilon_{n-1}}\rho^{n-1}}
 \le C_nr\rho.
$$

Increasing $D_n$ makes this as small as required, uniformly in both
positions. This scaling is essential: an absolute error in the
unscaled determinant would not pay its small distant main term.
The determinants of the two limiting Vandermonde matrices have
product

$$
\kappa_n=2^{n(n-1)}\prod_{k=0}^{n-1}(k!)^2>0.
$$

Choose the high start so their actual determinant product is at least
$\kappa_n/2$, and $D_n$ so the transformed relative determinant
is at least $1/2$. With $N_n=n(n-1)/2$ and
$e_n=\lfloor n/2\rfloor$, this proves

$$
\boxed{\det\mathcal J_nZ(a,b)
 \ge\frac{\kappa_n}{4}\,r^{e_n}\rho^{N_n}>0
 \qquad(b\ge a+D_n).}
\tag{W74}
$$

For $n=3$, the leading factor is
$\kappa_3r\rho^3=256(b/a)(P/q)^3$. Terms retained only through
first order have rank at most two and would lose this main term.

Multiplication by positive separable factors changes a mixed jet
determinant only by a positive factor, using triangular derivative
matrices. Thus (W74) gives the actual mixed jet sign for $R$ and
$L_0$. Symmetry treats $a\ge b+D_n$.
On $|a-b|\le D_n$, reuse (W33) through total order $2n-2$.
The confluent Cauchy determinant gives

$$
\det\mathcal J_n[\operatorname{sech}(a-b)]
 =\left(\prod_{k=0}^{n-1}(k!)^2\right)
   \operatorname{sech}^{n^2}(a-b)>0.
$$

Its minimum on this one fixed strip is positive. Uniform derivative
convergence therefore pays the same actual jet sign there after
increasing the start. Taking the maximum for $1\le n\le m$ yields
one start for all those orders, independent of distance.

### Reuse the classical Chebyshev criterion twice

Use Grau--Mañosas--Villadelprat,
[*A Chebyshev criterion for Abelian integrals*, arXiv:0805.1140v2](https://arxiv.org/pdf/0805.1140v2),
Definitions 2.1--2.2 and Lemma 2.3(a)--(b), printed pp.4--5.
It states the equivalence of nonvanishing leading Wronskians and the
extended complete Chebyshev property for analytic functions on an
open interval, as well as its ordinary collocation counterpart.
Only this classical criterion is reused, not that paper's additional
Abelian-integral hypotheses. Analyticity of the present actual kernel
is already supplied in (W37); the positive diagonal makes $R$ analytic.

For fixed $a$, apply the criterion in $b$ to
$R(a,b),\partial_aR(a,b),\ldots,\partial_a^{m-1}R(a,b)$.
Their leading Wronskians are the positive mixed jets just paid.
Their ordered Hermite collocations are nonzero by the zero-count
property and positive by coalescence and the positive local jets.
For a fixed ordered column multiset, these collocations are the
leading $a$-Wronskians of its column functions
$\partial_b^jR(a,b_\ell)$. Apply the same criterion in $a$.
It follows that every ordered row/column Hermite minor through size
$m$ is positive. Increase the reported start by one so all compact
node sets lie inside the open interval of application. In (W34)'s
normalized notation this gives

$$
\boxed{\mathcal Q_n(R;\mathbf a,\mathbf b)>0
 \quad(1\le n\le m,\quad
 \mathbf a,\mathbf b\text{ ordered in }[A_m,\infty)),}
\tag{W75}
$$

including all coincident-node limits. No uniform assertion over $m$
is made.

### Consume the same complete form for finite sign degree

Fix $r\le m-1$ and a monic separator $p$ of degree $r$ with roots
in $[A_m,T]$, allowing multiplicities. Let $\mu\ne0$ be a finite real
measure supported in $[A_m,T]$ with $\epsilon p\mu\ge0$.
Use exactly (W35)--(W36)'s Hermite anchor matrix $E$, observation
vector $h$, $d\nu=\sqrt J\,d\mu$ and $z=\int h\,d\nu$.
Equation (W75) makes $E$ positive definite and the exact quotient
$\mathcal Q_{r+1}(R;(s,a),(s,b))/\mathcal Q_r(R;s,s)$ positive
and continuous on the full compact node sets. Hence its minimum
$c_{m,r,T}>0$ can be chosen uniformly in the separator roots.
The existing exact Schur identity therefore gives

$$
\boxed{Q_{L_0}(\mu)\ge z^TE^{-1}z+
 c_{m,r,T}\left(\int|p(a)|\,d|\nu|(a)\right)^2>0.}
\tag{W76}
$$

For degree zero use already owned one-signed positivity. The root
atoms in positive degrees keep unrestricted signs; if all mass is
at the roots, the positive anchor square supplies strictness just as
in (W36). The constant in the final moment lower bound may depend on
$T$; the high start does not. Every direct/reflected contribution and
all mutual sign-block interactions remain in the actual full form.

Thus each fixed finite separator degree has a width-independent high
half-line, including arbitrary sample density and confluence. This
does not give one start for all degrees, unrestricted complex measures,
all-order positivity on one fixed interval, compact-core positivity,
the independent original Robin signed upper, or RH. The analytic
finite-degree gain is not a claim that FIB coordinate changes preserve
or improve the arithmetic form.


## An explicit growing degree range on arbitrary-width supports

There is a constant $C>0$ for the complete actual kernel such that
(W75)--(W76) hold with

$$
\boxed{A_m=\exp\!\bigl(Cm^4\log(m+1)\bigr),\qquad m\ge3.}
\tag{W77}
$$

Thus the finite separator degree may grow without bound with the
minimum support position, subject to
$Cm^4\log(m+1)\le\log A$. The support above $A$ may have arbitrary
finite width and density, and the roots may coincide. This bounds the
growth of the order-dependent start; it is not a diagonal selection of
unknown fixed-order starts. The complete endpoint expansion and Chebyshev--Schur
consumer remain (W72)--(W76). The additional estimates below pay the
order-dependent constants in that actual application. No numerical value of $C$, optimal exponent, common start for every
order, literature priority or Lean verification is claimed.

### A complex comparison whose near-strip cost is explicit

Fix small complex discs of radius $2\delta>0$ with the strip clearance
already supplied in (W46)--(W47). There are absolute $C_0,A_0$ such
that, for real $A\ge A_0$, $D\ge0$, $A\ge C_0(D+1)$ and
$|u|,|v|\le2\delta$,

$$
\boxed{|R(A+u,A+D+v)-\operatorname{sech}(u-D-v)|
 \le\frac{C_0(D+1)}A.}
\tag{W78}
$$

The discs, $C_0$ and $A_0$ do not depend on $D$. All diagonal square
roots continue the positive-real branch as in (W62).

To verify the distance dependence, use the existing congruence
$\mathcal P(a,b)=8\pi e^{a+b}L_0(a,b)/(\Phi(a)\Phi(b))$.
Put $a=A+u$, $b=A+D+v$, $x=(a+b)/2$, $d=(a-b)/2$ and
$\varepsilon=e^{-2A}$. The direct calculation in (W46), retaining
$D$ in its constants, has

$$
F_0=-2\pi(e^{2u}+e^{2(D+v)})s,\qquad
\Re F,\Re F_0\le-cs,
$$

$$
|F-F_0|\le C\varepsilon e^{2D}
 (s+s^2e^{2\varepsilon s}).
$$

The same exponential difference identity on the complete half-line
therefore gives

$$
\mathcal P^{\rm direct}(a,b)
=x\operatorname{sech}(a-b)
 +O\!\left((A+D+1)e^{-2A+3D}\right).
$$

For the reflected contribution retain exactly (W46)'s representation
with $\mathscr H(x,z)=g(x+\sqrt z)+g(x-\sqrt z)$.
For every $s\ge0$ one still has
$|\Im\sqrt{d^2+\varepsilon s}|\le|\Im d|$.
On the positive half of the $q$-segment in the formula for
$\mathscr H_z$, the real argument is at least $\Re x\ge A-O(\delta)$;
on its negative half use the same global upper bound on $\Re g''$.
Consequently, with constants independent of $D$,

$$
\Re[\mathscr H(x,d^2+\varepsilon s)-\mathscr H(x,d^2)]
 \le-ce^Ds.
$$

The reflected prefactor has size at most $Ce^D$, so its full integral
is $O(1)$, uniformly in $D$. The region where the negative argument
leaves the right tail remains included. No contour truncation is used.
Finally (W46) and (W62) supply
$\mathcal P(z,z)=z+O(1)$ on every such high diagonal disc, uniformly
in its center, and

$$
R(a,b)=\frac{\mathcal P(a,b)}
 {\sqrt{\mathcal P(a,a)\mathcal P(b,b)}}.
$$

For $A\ge C_0(D+1)$,
$x/\sqrt{ab}=1+O((D+1)/A)$ and
$(1+D/A)e^{-2A+3D}=O(A^{-1})$ after enlarging $C_0,A_0$.
These complete estimates prove (W78), including its uniform complex
neighborhood. It is not an assertion at $D$ arbitrarily large relative
to $A$; the distant account is supplied separately by (W74).

### Pay the constants in the full distant endpoint expansion

Choose one sufficiently large constant $C_1$ and set

$$
B_n=\exp\!\bigl(C_1n^2\log(n+1)\bigr)\quad(n\ge2).
$$

The moment, Taylor and finite-matrix costs in (W72)--(W74) admit the
following simultaneous bounds at $a\ge B_n^4$:

$$
\begin{aligned}
\|[\partial_a^i\partial_b^jF_n]_{i,j<n}\|_2&\le B_n r\rho^n,\\
\|\widehat U-\widehat U_\infty\|&\le B_n/a,&
\|\widehat V-\widehat V_\infty\|&\le B_n/b,\\
\|\widehat U_\infty^{-1}\|+
\|\widehat V_\infty^{-1}\|&\le B_n.
\end{aligned}
\tag{W79}
$$

The first line is used for $b-a\ge D_0$ with a fixed sufficiently
large $D_0$; the other lines use $b\ge a$. The symbols and exact
rank-$n$ expansion are unchanged from (W73)--(W74). Here is a
quantitative accounting without unknown order-dependent constants.

First, Cauchy estimates on one smaller fixed source strip give
$|g^{(j)}(z)|\le C^{j+1}j!e^{2|\Re z|}$ and the corresponding
right-tail remainder bound $C^{j+1}j!e^{-2\Re z}$.
For complex $b$ in a fixed high disc, $q=p(b)$ has
$\Re q\ge c|q|$, and horizontal integration gives

$$
\Re[g(b+t)-g(b)],\ \Re(-qt)\le-c|q|t,\qquad
|g(b+t)-g(b)+qt|\le C|q|t^2e^{2t}.
$$

The classical exponential integral and the same exponential difference
identity used above give, for every $k\ge0$,

$$
\left|I_k(b)-k!q^{-k-1}\right|
 \le C^{k+3}(k+2)!|q|^{-k-2}.
$$

In particular $I_0$ is nonzero on those high discs. Apply the ordinary
quotient and Cauchy estimates to $I_k/I_0$; compare
$p(b+w)^{-k}$ with $p(b)^{-k}e^{-2kw}$ on a smaller fixed disc.
For $k,j<n$ the resulting error constants in (W72) are bounded by
$(Cn)^{Cn}$, which is below $B_n$ after increasing $C_1$.

For the other endpoint, the finite Bell formula for
$\Phi^{(k)}/\Phi$ has leading term $(-p)^k$; all other monomials have
at most $k-1$ factors. The same fixed-disc Cauchy estimates bound
its $i<n$ parameter derivatives and the coefficient errors in
$\widehat U$ by $(Cn)^{Cn}$ times the powers already displayed in
(W73)--(W74). Differentiating $a^{-1}$ adds at most $i!$ and the
stated $a^{-1}$ loss. The analogous $b$ factor contributes $b^{-1}$.

For the complete Taylor remainder, keep its complex parameter discs
and apply the integral remainder before estimating. The Bell formula
and the whole-strip bound give
$|\partial_t^nf_\pm(t)|\le n!(CP)^ne^{(CP+Cn)t}$ there, where
$P$ denotes the real center's $p$-value. The omitted affine $2t$ term
has the same allowance. The complex normalized density is bounded by
$Cq e^{-cqt}$ with the real center's $q$-value. Choose $D_0$ fixed
so that its latter exponent dominates $CPt$, and use $a\ge B_n^4$
to dominate $Cnt$. Integration gives a remainder at most
$(Cn)^{Cn}r\rho^n$ on those discs. Cauchy differentiation through
$i,j<n$ adds $i!j!\delta^{-i-j}$ and preserves a bound of the same
$(Cn)^{Cn}$ shape. Thus the first line of (W79) includes all mixed
jets and the entire reflected exterior.

Finally apply Batenkov,
[*On the norm of inverses of confluent Vandermonde matrices*,
arXiv:1212.0172v2](https://arxiv.org/pdf/1212.0172v2),
Definition 1 and Theorem 1, equation (1.1), printed p.1.
Use its ordinary-node case with $N=n$, every multiplicity one,
$x_k=k/(n-1)$, $0\le k<n$, and $\delta=1/(n-1)$.
These auxiliary nodes lie in the unit disc and have the required
separation. The published row bound gives
$\|\widetilde V^{-1}\|_\infty\le2[2(n-1)]^n$.
For $V_{ik}=(2k)^i$, write
$V=\operatorname{diag}([2(n-1)]^i)\widetilde V$;
the inverse row-scaling factor has norm at most one.
Converting to Euclidean operator norm costs at most $\sqrt n$,
and the factorial column factors in the two limiting matrices cost
at most $(n-1)!$. Thus their inverse norms are bounded by
$(Cn)^{Cn}$. This is a direct published-theorem application, without
reproving a generic inverse formula or imposing any spacing on the
physical support nodes.

The moment and Taylor estimates above initially bound entries.
Converting an $n\times n$ entrywise bound to Euclidean operator norm
costs at most $n$. Enlarging $C_1$ once absorbs this factor as well
as the finite matrix factors, and verifies the operator-norm first
line and all other bounds in (W79) with one constant.

For $a\ge B_n^4$, these bounds and the finite Neumann estimate give
actual inverse norms at most $2B_n$ and an actual determinant-factor
product at least $\kappa_n/2$. In the transformed jet, the remainder
has norm at most $4B_n^3r\rho^n$. Choose

$$
D_n=D_0+8\log B_n.
$$

Since $r\rho\le C(1+b-a)e^{-2(b-a)}$, enlarging $C_1,D_0$ once
gives $4B_n^3r\rho\le1/(8n)$ for every $b-a\ge D_n$.
The same decreasing-diagonal comparison in (W74) therefore pays the
relative determinant, with factor at least $1/2$. Thus its complete
actual lower bound holds whenever $a\ge B_n^4$ and $b-a\ge D_n$.
In particular $D_n\le C_2n^2\log(n+1)$ with one absolute $C_2$.

### Pay the remaining strip before allowing the order to grow

Apply bivariate Cauchy estimates to (W78). For real $a,b$ with
$A=\min(a,b)\ge C_0(D+1)$ and $|a-b|\le D$, they give

$$
\max_{i,j<n}|\partial_a^i\partial_b^j(R-S)|
 \le (Cn)^{2n}\frac{C(D+1)}A,\qquad S(a,b)=\operatorname{sech}(a-b).
$$

The entries of the reference jet obey the corresponding
$(Cn)^{2n}$ bound, with no $D$ dependence. The finite determinant
multilinearity bound thus supplies

$$
|\det\mathcal J_nR-\det\mathcal J_nS|
 \le\exp\!\bigl(C_3n^2\log(n+1)\bigr)\frac{D+1}A,
$$

when the displayed entry error is at most one. Meanwhile the exact
confluent Cauchy determinant already used in (W74) gives

$$
\det\mathcal J_nS=
 \left(\prod_{k=0}^{n-1}(k!)^2\right)\operatorname{sech}^{n^2}(a-b)
 \ge e^{-n^2D}.
$$

Use $D=D_n$. Its preceding explicit bound shows that
$A\ge\exp(C_4n^4\log(n+1))$ pays half of this positive reference
minor, as well as $B_n^4$, $C_0(D_n+1)$ and the entry-error condition.
One enlargement of $C_4$ works for every $n\ge2$.
Take the maximum through $n=m$, and enlarge it once to leave the
open-interval clearance required by (W75). The same classical
Chebyshev applications and unchanged Hermite Schur consumer prove
(W77). The minor and weighted-moment constants retain their stated
support-endpoint dependence.

This gives an explicit unbounded degree range for complete real
profiles on arbitrary-width high supports. It does not give all orders
at any fixed start, positivity for unrestricted complex measures,
compact-core positivity or the original strict Robin joint upper.
The full RH and strict Robin for every integer above 5040 remain open.

## A shrinking gap pays arbitrary complex theta samples on the full high half-line

Keep the complete actual odd kernel $L_0$, its diagonal $J(a)=L_0(a,a)$ and $R(a,b)=L_0(a,b)/\sqrt{J(a)J(b)}$. Reuse the exact complete forward integral from (W52), the real restriction of the already proved theta expansion (W23)/(W47), and the classical Cauchy inverse formula for the reference in (W34)/(W61). No theta-series proof, generic interpolation theorem or numerical certificate is repeated. This is a source-specific paper application, without a literature-priority or Lean/kernel claim.

For every fixed $\kappa>\pi^2/2$, one start $A_\kappa$ works for all finite sets of distinct physical nodes $a_i\ge A\ge A_\kappa$ with minimum gap

$$
|a_i-a_j|\ge\delta_A:=\frac{\kappa}{\log A}\quad(i\ne j).
$$

There is no bound on the number of nodes or on their upper endpoint. The quantitative estimate below concerns the same actual complete kernel and arbitrary complex coefficients.

### Compare the full actual kernel uniformly over both escaping positions

There are constants $C,A_0>0$ independent of both positions such that

$$
\boxed{\left|R(a,b)-\operatorname{sech}(a-b)\right|
\le \frac CA(1+|a-b|)e^{-|a-b|}\qquad(a,b\ge A\ge A_0).}
\tag{W80}
$$

Unlike (W33), the containing interval has no fixed width. To verify it, write $b=a+d$, $d\ge0$, and $Q=e^{2a}+e^{2b}$. The owned real expansion is

$$
g(s)=\log\Phi(s)=\log(4\pi^2)+\tfrac92s-\pi e^{2s}+v(s),\qquad v(s)=O(e^{-2s})\quad(s\ge1).
$$

The same formula defines a continuous $v$ on the whole real axis. Evenness of $g$ gives $v(s)\to-\infty$ as $s\to-\infty$, so $\sup_{\mathbb R}v<\infty$. This upper bound does not assert that the right-tail expansion is a two-sided asymptotic.

In the exact forward formula put

$$
U_+=\frac14\int_0^\infty(a+b+2t)e^{g(a+t)-g(a)+g(b+t)-g(b)}\,dt,
$$

$$
U_-=\frac14\int_0^\infty(d+2t)e^{g(a-t)-g(a)+g(b+t)-g(b)}\,dt,\qquad
\frac{L_0(a,b)}{\Phi(a)\Phi(b)}=U_+-U_-.
$$

For $U_+$, the substitution $z=e^{2t}-1$ yields

$$
U_+=\frac18\int_0^\infty
[a+b+\log(1+z)](1+z)^{7/2}e^{-\pi Qz}e^{\Delta v_+(z)}\,dz.
$$

Here $|\Delta v_+(z)|\le C e^{-2a}$ uniformly for every $z\ge0$, because both shifted arguments stay on the right tail. Elementary Laplace integrals of these fixed polynomial weights give

$$
U_+=\frac{a+b}{8\pi Q}\bigl(1+O(e^{-2a})\bigr),
$$

uniformly for all $b\ge a\ge A_0$. For example,
$|(1+z)^{7/2}-1|\le C z(1+z)^3$ and $\log(1+z)\le z$ bound the relative integral error by $C/Q\le C e^{-2a}$; the constants do not depend on $a+b$ since $a+b\ge2$.

For $U_-$ the global upper bound on $v$, not a deleted reflected tail, gives

$$
e^{g(a-t)-g(a)+g(b+t)-g(b)}
\le C\exp\{-2\pi e^{a+b}[\cosh(d+2t)-\cosh d]\}\qquad(t\ge0).
$$

This remains true when $a-t<0$. The function $u/\sinh u$ decreases on $[0,\infty)$, with value $1$ at zero. Substituting $u=d+2t$, then $x=\cosh u-\cosh d$, therefore gives

$$
0\le U_-\le C e^{-(a+b)}\frac d{\sinh d},
$$

with the quotient read continuously at $d=0$. This retains the whole reflected exterior.

At $a=b$, these two bounds give the actual diagonal expansion

$$
J(a)=\frac{a\Phi(a)^2}{8\pi e^{2a}}\bigl(1+O(a^{-1})\bigr).
$$

Choose the common start so its factor is positive. Dividing the two complete terms by $\sqrt{J(a)J(b)}$ shows that the direct term is

$$
\frac{a+b}{2\sqrt{ab}}\,\operatorname{sech}d\bigl(1+O(A^{-1})\bigr),
$$

and the reflected term has modulus at most $C A^{-1}d/\sinh d$. Since
$0\le(a+b)/(2\sqrt{ab})-1\le d/(2a)$,
$\operatorname{sech}d\le2e^{-d}$ and $d/\sinh d\le C(1+d)e^{-d}$, this proves (W80). Symmetry handles $a>b$. All constants are uniform on the unbounded set of both positions.

### Reuse the exact inverse of the separated Cauchy reference

Order an arbitrary finite node set of minimum gap $0<\delta\le1$, and put $S_{ij}=\operatorname{sech}(a_i-a_j)$. With $x_i=e^{2a_i}$ this is the normalized Cauchy Gram $2\sqrt{x_ix_j}/(x_i+x_j)$. The classical inverse formula gives

$$
(S^{-1})_{ij}=S_{ij}p_i p_j,\qquad
p_i=\prod_{k\ne i}\frac{x_i+x_k}{x_i-x_k}.
$$

The $n$th node on either side is at distance at least $n\delta$, so

$$
|p_i|^2\le\prod_{n\ge1}\coth(n\delta)^4
\le\exp\!\left(\frac{\pi^2}{2\delta}\right).
$$

The last bound uses the decreasing integrable function $\log\coth t$ and its classical integral $\int_0^\infty\log\coth t\,dt=\pi^2/8$. The same ordered row sum satisfies
$\sum_j S_{ij}\le1+4/(e^\delta-1)\le5/\delta$. Applying the standard Hermitian row-sum bound directly to this inverse yields the reference estimate

$$
S\succeq \frac{\delta}{5}\exp\!\left(-\frac{\pi^2}{2\delta}\right)I.
$$

This is a reused Cauchy-matrix estimate inside the actual source comparison, not a new generic positivity criterion. No upper bound on the number or diameter of the sampled nodes enters it.

### Pay the actual error before letting the gap shrink

The function $(1+t)e^{-t}$ decreases on $[0,\infty)$ and has integral $2$. Thus (W80) on the same separated nodes gives

$$
\|[R(a_i,a_j)-S_{ij}]\|_{\rm op}
\le\frac{C}{A}\left[1+2\sum_{n\ge1}(1+n\delta)e^{-n\delta}\right]
\le\frac{5C}{A\delta}.
$$

Consequently $[R(a_i,a_j)]\succeq\tfrac12[S_{ij}]$, and hence has half the displayed reference scalar lower bound, whenever

$$
\boxed{A\delta^2\exp\!\left(-\frac{\pi^2}{2\delta}\right)\ge50C,\quad
0<\delta\le1,\quad A\ge A_0.}
\tag{W81}
$$

Take $\delta=\delta_A=\kappa/\log A$ with fixed $\kappa>\pi^2/2$, and write $\rho_\kappa=\pi^2/(2\kappa)<1$. The left side of (W81) is
$\kappa^2 A^{1-\rho_\kappa}/(\log A)^2$, which tends to infinity. One $A_\kappa$ therefore works for every $A\ge A_\kappa$ and every finite such family. For the original arbitrary complex physical coefficients $c_i$, apply the normalized estimate to $z_i=\sqrt{J(a_i)}c_i$ to get

$$
\boxed{\sum_{i,j}\overline{c_i}L_0(a_i,a_j)c_j
\ge\frac{\kappa}{10\log A}\,A^{-\rho_\kappa}\sum_i J(a_i)|c_i|^2>0\qquad(c\ne0).}
\tag{W82}
$$

All interactions and the complete actual direct/reflected theta integrals are included. The start and constants are independent of total node count, arbitrary upper endpoint and coefficient magnitudes. The new paid parameter is a minimum physical gap tending to zero like $1/\log A$, in contrast with (W61)'s prescribed fixed gap and unspecified dependence of the start on that gap.

At each fixed $A$, (W82) still imposes a positive minimum gap. It does not cover arbitrary dense sampling or arbitrary complex measures on one fixed interval, identify these samples with the actual prime/Robin source, or supply a signed strict Robin upper. The $J(a_i)$ weights are the actual diagonals, not an unweighted physical norm. Full fixed-window all-order positivity, strict Robin for every integer above5040 and RH remain unproved. The statement is paper mathematics under the owned actual-source identities; no numerical execution, Lean build, new agent or priority claim is involved.


## The complete kernel has no finite upper comparison with the stationary reference

The complete actual kernel also excludes an unrestricted two-sided
$S$-relative error estimate. This application reuses (W27), (W37)--(W38)
and the cited Danciger--Rubinstein-Salzedo Theorem 4; it does not infer
the result from the first correction in (W29).

For positive real positions define

$$
T(a,b)=\frac{\Phi(a)\Phi(b)e^{-a-b}}{8\pi}
 \operatorname{sech}(a-b),\qquad
\mathcal J(a)=\frac{8\pi e^{2a}L_0(a,a)}{\Phi(a)^2}.
$$

The diagonal consequence of (W27) is
$\mathcal J(a)=a-\tfrac12+o(1)\to+\infty$.
For $0<\eta<\pi/4$, the reference has the Hermitian extension

$$
T(z,w)=\frac{\Phi(z)\overline{\Phi(w)}e^{-z-\overline w}}{8\pi}
 \operatorname{sech}(z-\overline w)
 \qquad(z,w\in D_\eta).
$$

It is sesquiholomorphic: $|\Im(z-\overline w)|<2\eta<\pi/2$
avoids every pole of $\operatorname{sech}$. No division by complex
$\Phi$ is used. On distinct positive real nodes, $T$ is strictly
positive definite by the existing Cauchy representation of $S$ and
positive diagonal congruence.

For every nonempty open interval $I\subset(0,\infty)$ and every
finite $B>0$, there are finitely many distinct $a_i\in I$ and a
nonzero real vector $c$ such that

$$
\boxed{\sum_{i,j}c_iL_0(a_i,a_j)c_j
 >B\sum_{i,j}c_iT(a_i,a_j)c_j.}
\tag{W83}
$$

Indeed, otherwise $BT-L_0$ would be positive semidefinite on every
finite sample in $I$. Its common-strip Hermitian extension is supplied
above and by (W38). Apply the cited Theorem 4, using a real subinterval
as a uniqueness set in a relatively compact disk in $D_\eta$, exactly
as in the local transport argument. Positivity would extend to the
whole connected strip. Its large positive real diagonal is instead
$T(a,a)[B-\mathcal J(a)]<0$, a contradiction. The failed real
symmetric finite matrix admits real coefficients, and repeated nodes
can be merged. This uses the complete $L_0$, including its reflected
exterior.

In the existing coordinates $a=A+u$, $M_A=\mathcal P_A/A$, positive
diagonal congruence sends $T$ to $S(u,v)=\operatorname{sech}(u-v)$
and $L_0$ to $\mathcal P_A$. Thus, for every fixed $A>0$ and every
nonempty open offset interval $U$ with $A+U\subset(0,\infty)$,

$$
\boxed{\sup_{\substack{u_1,\ldots,u_n\in U\ \mathrm{distinct},\ n\ge1\\
 c\in\mathbb R^n\setminus\{0\}}}
 \frac{\sum_{i,j}c_iM_A(u_i,u_j)c_j}
 {\sum_{i,j}c_iS(u_i,u_j)c_j}=+\infty.}
\tag{W84}
$$

The denominator is strictly positive. Consequently no finite
$\varepsilon_A$ can bound
$|Q_{M_A-S}(c)|\le\varepsilon_A Q_S(c)$ on all such finite samples,
even when the allowance depends on $A$ and $U$.

This excludes the complete kernel's unrestricted two-sided comparison
with this stationary reference. It supplies no node-count or witness
size bound, no negative direction of $L_0$, and no failure of a
one-sided lower comparison. Other reference metrics, the separately
normalized diagonal-one correlation kernel, and the existing restricted
sign-complexity or minimum-gap estimates are outside this exclusion.
The all-order positive lower bound, full strict Robin inequality and RH
remain unproved. This is a paper application of existing results,
without a priority claim or Lean certification.


## The odd anchor also excludes a positive stationary lower comparison

There is a separate obstruction to a strictly positive lower comparison
with the same $T$. The complete odd kernel satisfies $L_0(0,0)=0$,
whereas $T(0,0)=\Phi(0)^2/(8\pi)>0$. For every nonempty open
$I\subset(0,\infty)$ and every $b>0$, some finite distinct sample
$a_i\in I$ and nonzero real vector $c$ therefore satisfy

$$
\boxed{\sum_{i,j}c_iL_0(a_i,a_j)c_j
 <b\sum_{i,j}c_iT(a_i,a_j)c_j.}
\tag{W85}
$$

Indeed, otherwise $L_0-bT$ would be positive semidefinite on all finite
samples in $I$. The same common-strip extension and cited analytic
positivity transport used for (W83) would extend this to the origin,
where its diagonal is $-b\Phi(0)^2/(8\pi)<0$. Reality and merging
repeated nodes give the stated real distinct sample. The argument
retains the full reflected exterior.

By the same positive diagonal congruence, for each fixed $A>0$ and
nonempty open $U$ with $A+U\subset(0,\infty)$,

$$
\boxed{\inf_{\substack{u_1,\ldots,u_n\in U\ \mathrm{distinct},\ n\ge1\\
 c\in\mathbb R^n\setminus\{0\}}}
 \frac{\sum_{i,j}c_iM_A(u_i,u_j)c_j}
 {\sum_{i,j}c_iS(u_i,u_j)c_j}\le0.}
\tag{W86}
$$

Thus a positive multiple of this stationary reference cannot supply
the unrestricted all-order lower margin, even on a remote positive
window. The zero lower bound required for actual kernel positivity
is not excluded: (W85)--(W86) give no negative actual direction and
do not decide whether the infimum is zero or negative. The restricted
minimum-gap and sign-complexity estimates remain intact.

This is a paper application of the already cited analytic transport,
without a new general theorem, priority claim or Lean certification.
Actual all-order positivity, full strict Robin and RH remain unproved.


## Exponentially growing sign count on one fixed complete theta window

The complete source admits a stronger fixed-window estimate than
(W58): the allowed polynomial-sign degree can grow as $e^{\kappa A}$
for some fixed $\kappa>0$. This is a repository-derived paper estimate
for the same actual odd $L_0$, including the reflected exterior.
It uses classical Taylor remainders, Stieltjes integrals, Hardy moments
and Fourier comparison inside the actual-source proof. These tools
are not proposed as new general results. Growing Laplace truncation
also has classical precedents, for example
[Paris, *On an extension of Watson's lemma due to Ursell*,
arXiv:1505.06905v1](https://arxiv.org/pdf/1505.06905v1), Theorems 2--3.
That selected-order theorem does not supply the uniform-in-order
actual-source expansion needed here; its remainder is paid below.
No literature priority or Lean verification is asserted.

### Keep an exact congruence of the complete source

Define the nonvanishing entire Gaussian leading factor and its
one-term theta correction by

$$
\Phi_{\rm g}(t)=4\pi^2e^{9t/2-\pi e^{2t}},\qquad
c_*=\frac3{2\pi},\qquad
\Phi_1(t)=\Phi_{\rm g}(t)(1-c_*e^{-2t}).
$$

For real $A>0$ put $E=e^{-2A}$ and

$$
D_A^{\rm g}(u)=\sqrt{\frac{8\pi}{A}}
 \frac{e^{A+u}}{\Phi_{\rm g}(A+u)},\qquad
M_A^{\rm g}(u,v)=D_A^{\rm g}(u)L_0(A+u,A+v)D_A^{\rm g}(v).
$$

For real offsets $D_A^{\rm g}>0$. Thus $M_A^{\rm g}$ is an exact
positive diagonal congruence of the complete $L_0$, rather than the
kernel obtained by replacing its source by $\Phi_1$.
Choose one sufficiently small fixed complex offset bidisc within the
neighborhoods of (W46)--(W56). Choose a fixed $0<R<1/2$ whose
$\operatorname{arctanh}$ image lies inside that bidisc, and put

$$
\begin{gathered}
u=\operatorname{arctanh}z,\qquad v=\operatorname{arctanh}w,\qquad
h=R/4,\qquad q=2/R,\qquad \Lambda=(1+4/R)^2,\\
\mathcal K_A^{\rm g}(z,w)=\cosh u\cosh v\,M_A^{\rm g}(u,v),\qquad
H(z,w)=\frac1{1-zw}.
\end{gathered}
$$

Keep precisely the real finite signed measures of (W55):
$\epsilon p\nu\ge0$, where $p$ is monic of degree $m$ with all
roots in $[-h,h]$ and $\epsilon\in\{-1,1\}$. Repeated roots and
atoms at roots are allowed. With $a_j=\int z^j\,d\nu(z)$, reuse

$$
Q_H(\nu)=\sum_{j\ge0}a_j^2,\qquad
\sum_{j\ge0}q^{2j}a_j^2\le9\Lambda^mQ_H(\nu).
$$

For a physical measure on the corresponding window, the exact
transport is

$$
d\nu(z)=\frac{d\mu(A+u)}{\cosh u\,D_A^{\rm g}(u)},\qquad
z=\tanh u,\qquad
Q_{L_0}(\mu)=Q_{\mathcal K_A^{\rm g}}(\nu).
$$

The positive weight and increasing coordinate preserve sign changes.
All subsequent allowances concern this same transported measure.

### Pay a complete expansion uniformly in its truncation order

There are fixed $C,c,A_0>0$ and compatible real-symmetric coefficient
kernels $B_{k,A}$, independent of the truncation order $N$, such that
for every integer $N\ge3$ and $A\ge A_0$, on the fixed complex bidisc,

$$
\boxed{
\begin{aligned}
M_A^{\rm g}
 &=S+\frac{C_{\rm core}}A
   +\sum_{1\le k<N}E^k B_{k,A}+R_{N,A},\\
\sup|R_{N,A}|
 &\le C^N N!E^N+C e^{-c e^A},\\
S(u,v)&=\operatorname{sech}(u-v),\\
C_{\rm core}(u,v)
 &=\frac{u+v}{2}S(u,v)-\frac{u-v}{2\sinh(u-v)}.
\end{aligned}}
\tag{W87}
$$

The removable values are included. In particular the remainder pays
for $N$ growing with $A$; no fixed-$N$ asymptotic is extrapolated.

First compare the full source with $\Phi_1$ inside the exact
integrals. In the reflected integral, use evenness of the complete
$\Phi$ first to obtain the product $\Phi(x+y)\Phi(x-y)$, where
$a=A+u$, $b=A+v$, $x=(a+b)/2$, $d=(a-b)/2$.
Only then compare it with the symmetric model
$\Phi_1(x+y)\Phi_1(x-y)$. Since $\Phi_1$ is not even, this is
not the raw source substitution in every occurrence of $K_0$.

On the reflected contour $y=\sqrt{d^2+Es}$ from (W46),
$|\Im y|\le|\Im d|$. When $\Re y\le A/2$, both arguments lie
in the right tail and the relative theta-series error is
$O(e^{-c e^A})$. The whole-half-line Gaussian majorant already paid
in (W46) pays its normalized integral. When $\Re y>A/2$, the
$x+y$ factor has the upper tail $e^{-c e^{3A}}$, which beats the
normalizing cost $e^{C e^{2A}}$. The other complete-$\Phi$ and
$\Phi_1$ factors are bounded on the chosen narrow strip. Integration
of that tail therefore gives the same stated error. The direct
integral has both arguments in the right tail throughout and is paid
by its corresponding majorant. This proves a full-to-model normalized
error at most $C e^{-c e^A}$ on the fixed bidisc. In particular the
region $\Re(x-y)<0$ remains included.

The model integrals make the remaining factorial allowance explicit.
Set

$$
\begin{gathered}
Q=2\pi e^{a+b},\qquad c_0=\cosh(a-b),\qquad Y=Qc_0,\\
r_a=c_*e^{-2a},\qquad r_b=c_*e^{-2b},\\
\Psi(s)=\frac{\operatorname{arcosh}s}{\sqrt{s^2-1}}
 =\int_0^\infty\frac{dt}{s+\cosh t},\qquad \Psi(1)=1.
\end{gathered}
$$

The branch of $\Psi$ is analytic for $\Re s>0$. Direct substitutions
in the symmetric model give the complete normalized terms

$$
\boxed{
\begin{aligned}
\mathcal P_{{\rm dir},1}^{\rm g}
 &=Q\int_1^\infty
 \left(x+\tfrac12\log\tau\right)\tau^{7/2}e^{-Y(\tau-1)}
 (1-r_a/\tau)(1-r_b/\tau)\,d\tau,\\
\mathcal P_{{\rm ref},1}^{\rm g}
 &=\frac Q2\int_0^\infty e^{-Qs}\Psi(c_0+s)
 \left[1-r_a-r_b-2c_*e^{-(a+b)}s
       +c_*^2e^{-2(a+b)}\right]ds.
\end{aligned}}
\tag{W88}
$$

Here $(\mathcal P_{{\rm dir},1}^{\rm g}
-\mathcal P_{{\rm ref},1}^{\rm g})/A$ is the model for
$M_A^{\rm g}$. The reflected substitution is
$s=\cosh(2y)-\cosh(2d)$. For complex offsets,
$\Re Q,\Re Y\ge c e^{2A}$ on a small enough fixed bidisc.
The displayed integrals are holomorphic there. Their equality on real
offsets and the identity-theorem argument of (W38), (W46) identify
the continuation. The actual-source comparison was paid separately
and is not inferred from these model formulas.

For the direct integral, expand the three amplitudes
$(x+\tfrac12\log\tau)\tau^{7/2-j}$, $j=0,1,2$, at $\tau=1$.
Their coefficients of order $\ell$ are bounded by
$C^\ell(|x|+1)$. Their Taylor remainders on $\tau\ge1$ are
bounded by
$C^N(\tau-1)^N(1+\tau)^5(|x|+1)$, using the integral Taylor
formula for the powers and logarithm. Integration against
$e^{-\Re Y(\tau-1)}$, with the leading $Q$ and division by $A$,
gives $C^N N!E^N$, for every $N$. The finitely many extra polynomial
powers and index shifts are absorbed by increasing $C$.

For the reflected amplitude the exact Stieltjes remainder is

$$
\begin{aligned}
\Psi(c_0+s)
 &=\sum_{j<N}(-s)^jh_j(c_0)
   +(-s)^N\int_0^\infty
    \frac{dt}{(c_0+\cosh t)^N(c_0+s+\cosh t)},\\
h_j(c_0)&=\int_0^\infty(c_0+\cosh t)^{-j-1}\,dt.
\end{aligned}
$$

Since $\Re c_0$ is bounded below positively, the remainder is
bounded by $C^N s^N$. Its Laplace integral costs $C^N N!E^N$.
The explicit prefactors in (W88) shift indices by at most two; their
fixed extra factorial factors are also absorbed into $C^N N!$.
Collecting equal powers of $E$ defines the same $B_{k,A}$ for every
$N$. The leading direct and reflected terms are respectively
$xS$ and $\Psi(c_0)/2=(a-b)/(2\sinh(a-b))$. Together with the
full-source payment, this proves (W87).

### Pay every retained coefficient polynomially in the same sign degree

For some sufficiently large fixed absolute exponent $P$ and fixed
$C_1$, the coefficients just constructed satisfy

$$
\boxed{
\left|Q_{\cosh u\cosh v\,B_{k,A}}(\nu)\right|
 \le[C_1(m+k+1)]^{P(k+1)}Q_H(\nu)
 \qquad(k\ge1,\ A\ge A_0).}
\tag{W89}
$$

Only existence of a fixed $P$ is used; no numerical value is claimed.
A fixed-radius Cauchy bound alone would lose the polynomial dependence
on $m$ and is not the coefficient estimate used here.

The reused moment-radius bound first gives

$$
\sum_{n\ge\ell}a_n^2
 \le\min(1,9\Lambda^m q^{-2\ell})Q_H(\nu),\qquad
\sum_{n\ge0}(n+1)^j a_n^2
 \le[C(m+j+1)]^jQ_H(\nu)\quad(j\ge1).
$$

Indeed, split the exponential tail at an index proportional to $m+1$
and sum its polynomially weighted remainder. For the moment shift
$B(a)_n=a_{n+1}$ and $f_r(z)=e^{-r\operatorname{arctanh}z}$,
$r\ge0$, Cauchy on the circle of radius $1-1/(j+r+2)$ bounds the
$j$th coefficient of $f_r$ by $[C(j+r+2)]^{r/2}$.
Summing against
$\|B^j a\|_2\le\min(1,3\Lambda^{m/2}q^{-j})\|a\|_2$,
again splitting at an index proportional to $m+1$, yields

$$
\|f_r(B)a\|_2\le[C(m+r+1)]^{r/2+2}\|a\|_2.
$$

Weighted versions require no independently extremal moment sequence:
$f_r(z)>0$ on the actual support, so $f_r\nu$ has the same
separator $p$. Apply the preceding weighted-moment bound directly to
that measure after paying its unweighted norm. Likewise
$(1-z)^\ell>0$ and its shift operator has norm at most $2^\ell$.
Multiplication by $\operatorname{arctanh}z$ costs the
$C\log(m+2)$ norm already paid in (W57). The resulting measure has
separator $zp$ of degree $m+1$, since
$z\operatorname{arctanh}z\ge0$; its weighted moments are paid by
the same argument.

Every direct coefficient reduces to the exact identity

$$
\cosh u\cosh v\,e^{-\ell(u+v)}
 \operatorname{sech}^{\ell+1}(u-v)
 =\frac{(1-z)^\ell(1-w)^\ell}{(1-zw)^{\ell+1}}.
$$

Its form is the sum of $\binom{n+\ell}{\ell}$ times squares of
finite moment differences. The preceding weighted bounds pay these
terms, the extra $e^{-2u}$ or $e^{-2v}$ prefactors and the affine
$x$ term. Scalar Taylor coefficients cost at most $C^\ell\ell!$.

For the reflected coefficients use the stationary factors
$h_j(\cosh t)$, $t=u-v$, $j\le k$. Put $b_0=3\pi/4$.
The elementary hyperbolic-cosine factorization gives

$$
|\cosh(t+ib_0)+\cosh s|
 \ge\cos^2(b_0/2)(\cosh t+\cosh s).
$$

The horizontal $L^1$ norm of $h_j(\cosh(t+ib_0))$ is therefore
at most $C^{j+1}$. A Fourier contour shift, with convention
$\widehat f(\xi)=\int f(t)e^{-i\xi t}dt$, gives
$|\widehat{h_j\circ\cosh}(\xi)|
\le C^{j+1}e^{-b_0|\xi|}$.
The classical transform
$\widehat{\operatorname{sech}}(\xi)
=\pi/\cosh(\pi\xi/2)$ then bounds its stationary bilinear form
by $C^{j+1}$ times the two $S$ norms. The remaining multipliers
$e^{-ru-sv}$ have $r,s\le k+2$ and are paid above.
The factors $j!$, $(j+1)!$ and the finitely specified prefactor
cases are absorbed in powers of $m+k+1$. These estimates prove
(W89) with one fixed $P$, without an exponential-in-$m$ coefficient
cost or a combination of independently attainable profiles.

### Spend the full allowance at a growing truncation order

Reuse the first-core estimate of (W57), apply (W89) to the retained
coefficients and apply (W55)'s Cauchy/moment allowance to (W87)'s
remainder. The complete actual estimate is

$$
\boxed{
\begin{aligned}
\frac{|Q_{\mathcal K_A^{\rm g}-H}(\nu)|}{Q_H(\nu)}
\le{}&\frac{C_3\log(m+2)+1}{A}\\
 &+\sum_{1\le k<N}e^{-2Ak}[C_1(m+k+1)]^{P(k+1)}\\
 &+C_2\Lambda^m
       \left[C^NN!e^{-2AN}+e^{-c e^A}\right].
\end{aligned}}
\tag{W90}
$$

This holds for nonzero $\nu$ under the same sign contract, with
constants independent of $m,N,A$. No favorable sign is assigned to
either the reflected error or the full-theta correction.

Choose fixed

$$
0<\kappa<\min\left\{\frac14,\frac1{8P},
                         \frac1{16(C_3+1)}\right\},\qquad
N=\left\lceil D\left(1+\frac{m+1}{A}\right)\right\rceil,
$$

where $D$ is a fixed sufficiently large constant depending on
$\Lambda$, increased to make $N\ge3$. For $m\le e^{\kappa A}$,
$\log N\le\kappa A+O(1)$ and
$\log(C^NN!)\le N(\kappa A+O(1))$.
Consequently the factorial remainder after multiplication by
$\Lambda^m$ is at most $e^{-c_1A-c_1m}$, on increasing $D$.
The full-theta remainder is at most $e^{-c e^A/2}$ since
$\kappa<1$. For $k<N$ one has $m+k+1\le C_D(m+1)$, so each
middle summand in (W90) is at most $e^{-Ak}$ for one common
sufficiently large start. The first allowance is at most
$C_3\kappa+o(1)$. Thus some common $A_1$ gives

$$
\boxed{Q_{\mathcal K_A^{\rm g}}(\nu)\ge\tfrac12Q_H(\nu)>0
\quad\left(A\ge A_1,\quad
0\le m\le\lfloor e^{\kappa A}\rfloor,\quad \nu\ne0\right).}
\tag{W91}
$$

Strictness uses the existing compact-moment uniqueness argument.
Through the exact positive transport this is an actual $L_0$
estimate on the one fixed physical window
$[A-\operatorname{arctanh}h,A+\operatorname{arctanh}h]$.
For arbitrary complex coefficients on at most
$\lfloor e^{\kappa A}\rfloor+1$ distinct sites there, apply the real
estimate separately to the real and imaginary coefficient measures;
each has at most one fewer sign change than its number of sites.
Reality and symmetry make the two forms add. No internal node-gap
restriction is imposed. The metric is the transported Hardy form,
not the unweighted physical coefficient norm.

The estimate strengthens (W58)'s linear sign range on a fixed small
window. It does not replace (W77)'s arbitrary-width contract.
At each fixed $A$ the allowed order remains finite, consistently with
(W83)--(W86). No unrestricted fixed-window all-order positivity,
arbitrary-width exponential range, numerical start, identification
with the original prime/Robin source, uniform strict Robin bound or
RH proof is supplied. Full RH and strict Robin for every integer
$n>5040$ remain unproved.


## A compact core couples to an exponentially complex remote profile

The exponential sign range in (W91) needs a stronger compact coupling
than (W66), whose factor $\Lambda^{m/2}$ grows too fast in that range.
The following actual mixed-source estimate replaces that factor by
$\sqrt{m+1}$. It retains a rank-one leading pairing and a remainder
uniform in the permitted cancellations. This is a repository-derived
paper application of the existing theta identities, Taylor/Laplace
remainder method and moment bounds, without a literature-priority or
Lean-verification claim.

Fix $U>0$ and the small window and Gaussian-leading transport of
(W87)--(W91). For a remote measure $\lambda$ supported in
$[B-w,B+w]$, where $w=\operatorname{arctanh}h$, put

$$
\begin{gathered}
v=\operatorname{arctanh}z,\qquad
 d_B^{\rm g}(z)=\cosh v\,D_B^{\rm g}(v),\qquad
 d\nu(z)=\frac{d\lambda(B+v)}{d_B^{\rm g}(z)},\\
 a_n=\int z^n\,d\nu(z),\qquad
 Q=Q_H(\nu)=\sum_{n\ge0}|a_n|^2,\qquad
 \ell(\nu)=\int\frac{d\nu(z)}{1+z}.
\end{gathered}
$$

For real $\nu$, require $\epsilon p\nu\ge0$ with $p$ monic of
 degree $m$, all roots in $[-h,h]$, and $\epsilon\in\{-1,1\}$.
Repeated roots and root atoms are allowed. A complex $\nu$ may instead
satisfy this condition separately on its real and imaginary parts,
each with degree at most $m$. In that case $Q$ is the sum of their
 two Hardy forms.

For any finite complex measure $\mu$ on $[0,U]$, retain
$\mathcal M(\mu)=\int\sqrt{J(a)}\,d|\mu|(a)$ from (W51), and set

$$
\mathcal C(\mu)=\int a\Phi(a)\,d\overline\mu(a),\qquad
B_{L_0}(\mu,\lambda)
 =\iint L_0(a,b)\,d\overline\mu(a)d\lambda(b).
$$

There are fixed $\kappa>0$, $B_U,C_U>0$, with $\kappa$ no larger
than the local rate in (W91), such that for every $B\ge B_U$ and
$0\le m\le\lfloor e^{\kappa B}\rfloor$,

$$
\boxed{
\begin{aligned}
\left|B_{L_0}(\mu,\lambda)
 -\frac{e^{-B}}{\sqrt{2\pi B}}
    \mathcal C(\mu)\ell(\nu)\right|
 &\le C_U\frac{e^{-2B}}{\sqrt B}\mathcal M(\mu)\sqrt Q,\\
|B_{L_0}(\mu,\lambda)|
 &\le C_Ue^{-B}\sqrt{\frac{m+1}{B}}
              \mathcal M(\mu)\sqrt Q.
\end{aligned}}
\tag{W92}
$$

The constants do not depend on the measures, roots, density, sample
count or allowed degree. The compact core has no sign restriction.
Its atom at zero contributes nothing. The compact size is fixed; no
uniformity as $U\to\infty$ is asserted.

### Keep the compact source complete in the actual Laplace integral

Reuse the whole forward identity of (W50), (W62), (W65), with
$b=B+v$ and $B>U+1$:

$$
L_0(a,b)=\frac14\int_0^\infty
 [(a+b+2t)\Phi(a+t)-(b-a+2t)\Phi(a-t)]\Phi(b+t)\,dt.
$$

Its complex continuation and domination were already paid there.
In particular the part with $t-a<0$ remains present.
Put $s=e^{2t}-1$ and $t(s)=\tfrac12\log(1+s)$. Define

$$
\begin{aligned}
F_a(s)&=(1+s)^{5/4}
 \frac{\Phi(a+t(s))-\Phi(a-t(s))}{a},\\
G_a(s)&=(1+s)^{5/4}\left[
 \Phi(a+t(s))+\Phi(a-t(s))
 +\log(1+s)\frac{\Phi(a+t(s))-\Phi(a-t(s))}{a}\right].
\end{aligned}
$$

Evenness of the complete $\Phi$ removes the quotients at $a=0$.
For real $a\in[0,U]$, these functions and their quotients by $1+s$
are analytic on one fixed complex $s$-disc, uniformly in $a$, and
$F_a(0)=0$, $G_a(0)=2\Phi(a)$.
Indeed choose the disc small enough that $t(s)$ stays strictly inside
 the source strip. On a fixed complex neighborhood of the compact
$a$ interval the source is bounded, and the odd difference divided by
$a$ is removable. Cauchy therefore bounds each Taylor coefficient of
 the four amplitudes by $C_U^{k+1}$.

For real $s\ge0$, the full source and its first derivative are bounded
on the real axis. Evenness also gives
$|[\Phi(a+t)-\Phi(a-t)]/a|\le2\|\Phi'\|_\infty$.
Consequently the four amplitudes have absolute value at most
$C_U(1+s)^4$. Their remainder after $N$ Taylor terms is at most
$C_U^{N+1}s^N(1+s)^4$, for every $N\ge1$ and every $s\ge0$.
On a smaller disc this is the Cauchy remainder. Outside its positive
radius, the polynomial growth and the coefficient bound pay the raw
amplitude and the Taylor polynomial separately, absorbing the finite
geometric sum in $C_U^{N+1}$. This is uniform in $N$.

Only the high source is approximated. Its actual theta series gives

$$
\frac{\Phi(b+t)}{\Phi_{\rm g}(b)}
 =(1+s)^{9/4}e^{-\pi e^{2b}s}
 \left[1-\frac{c_*e^{-2b}}{1+s}+\Delta_b(s)\right],\qquad
|\Delta_b(s)|\le C e^{-c e^{2B}(1+s)}.
$$

These bounds hold on the same fixed small complex offset disc, where
$\Re(\pi e^{2b})\ge c e^{2B}$. The compact factors remain the
complete $\Phi$. Thus the model with only the high theta factor
replaced has the exact formula

$$
\boxed{\frac{L_1(a,b)}{\Phi_{\rm g}(b)}
 =\frac a8\int_0^\infty e^{-\pi e^{2b}s}
 [bF_a(s)+G_a(s)]
 \left[1-\frac{c_*e^{-2b}}{1+s}\right]ds.}
\tag{W93}
$$

Integration of the displayed $\Delta_b$ bounds the complete-to-model
error, after the exact transport, by
$C_Ua e^{-B}(B+1)e^{-c e^{2B}}/\sqrt B$ on the fixed Hardy disc.
This pays the whole half-line and its reflected part; no positivity of
$L_1$ is assumed.

Integrate the Taylor terms using
$\int_0^\infty s^k e^{-Qs}ds=k!Q^{-k-1}$ for $\Re Q>0$.
For every $N\ge3$, the resulting actual expansion is

$$
\boxed{
\begin{aligned}
\frac{d_B^{\rm g}(z)L_0(a,B+v)}a
 =\frac{e^{-B}}{\sqrt B}\bigg[
 &\frac{\Phi(a)}{\sqrt{2\pi}}g_0(z)\\
 &+\sum_{1\le k<N}e^{-2kB}
     [\alpha_k(a)(B+v)+\beta_k(a)]g_k(z)
     +R_N(a,z)\bigg],\\
g_k(z)&=\cosh v\,e^{-(2k+1)v}
       =\frac{(1-z)^k}{(1+z)^{k+1}},\\
|\alpha_k(a)|+|\beta_k(a)|&\le C_U^{k+1}k!,\\
\sup_{\substack{a\in[0,U]\\|z|\le R}}|R_N(a,z)|
 &\le C_U(B+1)
       [C_U^NN!e^{-2BN}+e^{-c e^{2B}}].
\end{aligned}}
\tag{W94}
$$

At $a=0$ the quotient is interpreted removably only in this estimate;
 the original kernel still vanishes. The coefficients are independent
of $N$. The high prefactor shifts an index by at most one, giving the
same $g_k$ and an absorbed $(k-1)!$. In the remainder the fixed
polynomial growth introduces $(N+j)!$, $j\le4$, absorbed by
$C_U^NN!$. The leading term follows from $G_a(0)=2\Phi(a)$:
$L_1/\Phi_{\rm g}(b)$ starts at
$a\Phi(a)e^{-2b}/(4\pi)$, yielding exactly the constant in (W92).

### Pay polynomial degree costs before choosing the growing order

Reuse (W55)'s moment-radius comparison and its shift-tail consequence

$$
\sum_{n\ge0}q^{2n}|a_n|^2\le9\Lambda^mQ,\qquad
\|\mathsf T^\ell a\|_2
 \le\min(1,3\Lambda^{m/2}q^{-\ell})\|a\|_2.
$$

Here $\mathsf T(a)_n=a_{n+1}$ is the moment shift. Splitting $\sum(-1)^na_n$ at an index proportional to
$m+1$, Cauchy--Schwarz pays its first part and the exponential tail
pays the rest. Therefore

$$
|\ell(\nu)|\le C\sqrt{m+1}\sqrt Q.
$$

For $k\ge1$, the $n$th Taylor coefficient of $g_k$ has magnitude at
most $2^k\binom{n+k}{k}$. Sum against the same shift-tail bound,
splitting at $L=\lceil C(m+k+1)\rceil$. The first $L$ terms cost
at most $[C(m+k+1)]^{k+1}$. For $n=L+t$ the bound
$(L+t+k)^k\le(L+k)^ke^t$ and $q>4$ pay the remaining sum.
It follows that

$$
\|g_k(\mathsf T)a\|_2\le[C(m+k+1)]^{k+1}\|a\|_2.
$$

Since $g_k>0$ on the real support, the measure $g_k\nu$ retains
 the same separator. Apply the already paid logarithmic
$\operatorname{arctanh}$ multiplier bound from (W57) to that
measure. Together with the coefficient factorials in (W94), this gives,
for some fixed sufficiently large $P$,

$$
\left|\int[\alpha_k(a)(B+v)+\beta_k(a)]g_k(z)\,d\nu(z)\right|
 \le C_U(B+1)[C_U(m+k+1)]^{P(k+1)}\sqrt Q.
$$

The same measure supplies all these bounds. For the remainder use the
linear Cauchy allowance already paid in (W63), obtaining

$$
\left|\int R_N(a,z)\,d\nu(z)\right|
 \le C_U(B+1)\Lambda^{m/2}
       [C_U^NN!e^{-2BN}+e^{-c e^{2B}}]\sqrt Q.
$$

Choose fixed $0<\kappa<\min(\kappa_{\rm W91},1/4,1/(8P))$ and
$N=\lceil D(1+(m+1)/B)\rceil\ge3$, with fixed sufficiently large
$D$. For $m\le e^{\kappa B}$ one has
$\log N\le\kappa B+O(1)$ and $m+k+1\le C_D(m+1)$ for $k<N$.
The retained $k\ge1$ terms have total integral at most
$C_Ue^{-B}\sqrt Q$, absorbing $B+1$ in the unused exponential
rate. The factorial remainder has the same bound, after increasing
$D$ and then the common start, since
$\log(C_U^NN!)\le N(\kappa B+O_U(1))$ absorbs
$\Lambda^{m/2}$. The full-theta error is smaller because
$\kappa<2$. These choices are uniform over every allowed measure
and every $a\in[0,U]$.

Thus (W94), after integration in $\nu$, has remainder at most
$C_Ua e^{-2B}\sqrt{Q/B}$ in the original transported kernel.
From (W49), both $a/\sqrt{J(a)}$ and
$a\Phi(a)/\sqrt{J(a)}$ are bounded for $0<a\le U$.
Integrating against $d\overline\mu(a)$ proves (W92), including
 the compact origin. For complex remote measures, split into the two
real separator classes and absorb the fixed constant; the leading
pairing remains exactly the displayed complex one.

### Spend the same remote credit on one full attachment

For the same $\lambda$, (W91) gives $Q_{L_0}(\lambda)\ge Q/2$.
Apply Young's inequality to the full cross term in (W92), keeping one
quarter of that $Q$ as credit. The actual total form satisfies

$$
\boxed{
\begin{aligned}
Q_{L_0}(\mu+\lambda)
 &\ge Q_{L_0}(\mu)+\tfrac14Q
       -C_U\frac{(m+1)e^{-2B}}B\mathcal M(\mu)^2,\\
\mathcal C(\mu)=0\quad\Longrightarrow\quad
Q_{L_0}(\mu+\lambda)
 &\ge Q_{L_0}(\mu)+\tfrac14Q
       -C_U\frac{e^{-4B}}B\mathcal M(\mu)^2.
\end{aligned}}
\tag{W95}
$$

The first defect is at most $C_Ue^{-(2-\kappa)B}/B$ times the
compact size. The second uses cancellation of the actual compact
moment $a\Phi(a)$ and remains uniform over the permitted exponential
sign range.

This pays one compact-to-remote attachment of an arbitrarily dense
profile with exponentially growing sign degree. Joint credit for
several such remote profiles would require their mutual interactions
to be paid separately; it is not inferred from the local credits.
Neither a sign for $Q_{L_0}(\mu)$ nor a comparison of
$\mathcal M(\mu)^2$ to a nearly null compact form is supplied.
At fixed $B$ the allowed degree is finite. Fixed-window all-order
positivity, the original signed prime/Robin estimate, strict Robin
for every integer above5040 and RH remain unproved.


## Geometric windows admit exponential local sign complexity

The local margin (W91) can be combined across a geometric collection of
windows, after replacing (W63)'s exponential degree cost in the actual
cross blocks. The new input is a two-high-window endpoint expansion
uniform in its truncation order, together with polynomial coefficient
costs on the same two moment sequences. The full lower theta correction
is paid separately in the lower variable; it is not amplified by the
higher window's moment radius. This is a repository-derived paper
estimate using the already cited classical tools, without a priority
or Lean-verification claim.

Keep the fixed small support $[-h,h]$, physical half-width
$w=\operatorname{arctanh}h$, and Gaussian-leading transport of
(W87)--(W95). For each physical profile $\lambda_j$ on
$[A_j-w,A_j+w]$, let $\nu_j$ be its transport by $d_{A_j}^{\rm g}$
and set $Q_j=Q_H(\nu_j)$. Require an explicit polynomial-sign
condition of degree $m_j$ on a real $\nu_j$, or separately on its
real and imaginary parts for a complex profile. All roots lie in
$[-h,h]$; repeated roots and root atoms remain allowed.

Fix $q_{\rm geo}>1$ and put
$\tau=(q_{\rm geo}-1)/(q_{\rm geo}+1)$. There are fixed
$\kappa>0$, $A_*,C>0$ such that, whenever
$B\ge q_{\rm geo}A$, $A\ge A_*$, and the two local degrees obey
$m_A\le\lfloor e^{\kappa A}\rfloor$,
$m_B\le\lfloor e^{\kappa B}\rfloor$, the complete cross form satisfies

$$
\boxed{|B_{L_0}(\lambda_A,\lambda_B)|
 \le C(1+B-A)e^{-(B-A)/2}\sqrt{Q_AQ_B}.}
\tag{W96}
$$

The constants do not depend on the degrees, roots, local density or
sample count. This is an actual full-kernel bound in the same Hardy
metric as the local positive credit, including the reflected exterior.

### A two-high expansion keeps the truncation cost explicit

Put $a=A+u$, $b=B+v$, $\Delta=B-A$, with complex offsets in the
fixed small bidisc. Reuse the exact forward identity of (W62), set
$s=e^{2t}-1$, $t(s)=\tfrac12\log(1+s)$, and define

$$
\begin{aligned}
V_\pm(a,s)&=\frac{\Phi(a\pm t(s))}{\Phi_{\rm g}(a)},\\
\mathcal A(a,b;s)&=(1+s)^{5/4}\big[
 (a+b+\log(1+s))V_+(a,s)\\
 &\hspace{38mm}-(b-a+\log(1+s))V_-(a,s)\big].
\end{aligned}
$$

Only the higher source factor is replaced in the model integral:

$$
\frac{L_1(a,b)}{\Phi_{\rm g}(a)\Phi_{\rm g}(b)}
 =\frac18\int_0^\infty e^{-\pi e^{2b}s}
 \mathcal A(a,b;s)
 \left[1-\frac{c_*e^{-2b}}{1+s}\right]ds.
$$

The lower factors are the complete $\Phi$, including the part where
$\Re(a-t)<0$. With
$\mathcal K_{A,B}(z,\zeta)
 =d_A^{\rm g}(z)d_B^{\rm g}(\zeta)L_0(A+u,B+v)$,
where $u=\operatorname{arctanh}z$ and
$v=\operatorname{arctanh}\zeta$, there are compatible coefficient
kernels $C_{k;A,B}$, independent of $N$, such that for every
$N\ge3$, $A\ge A_0$ and $\Delta\ge D_0$,

$$
\boxed{
\begin{aligned}
\mathcal K_{A,B}
 &=\frac{e^{-\Delta}}{\sqrt{AB}}
   \sum_{0\le k<N}e^{-2k\Delta}C_{k;A,B}
   +\mathcal R_{N;A,B},\\
\sup|\mathcal R_{N;A,B}|
 &\le C\frac{A+B+1}{\sqrt{AB}}e^{-\Delta}
       [C^NN!e^{-2N\Delta}+e^{-c e^{2B}}].
\end{aligned}}
\tag{W97}
$$

The supremum is on the fixed Hardy bidisc. The constants are independent
of both centers and of $N$, and $D_0$ is one fixed sufficiently large
number. The leading coefficient is exactly

$$
C_{0;A,B}(z,\zeta)
 =2(A+u)\frac{\Phi(A+u)}{\Phi_{\rm g}(A+u)}
       \frac1{1-z}\frac1{1+\zeta}.
$$

To pay the uniform remainder, use the complete logarithm from (W47).
Its right-tail expansion, odd derivative and a compact bound give
$|g'(x+iy)|\le Ce^{2|x|}$ on a smaller global strip. The horizontal
bounds already used in (W62) imply, for all $t\ge0$,

$$
\left|\frac{\Phi(a+t)}{\Phi(a)}\right|\le C,\qquad
\left|\frac{\Phi(a-t)}{\Phi(a)}\right|\le e^{Ce^{2A}t}.
$$

Also $\Phi(a)/\Phi_{\rm g}(a)$ is uniformly bounded on the offset
disc. For real $S\ge0$, take the complex circle
$|s-S|\le\rho e^{-2A}$, with fixed sufficiently small $\rho$.
The displacement of $t$ is at most
$C\rho e^{-2A}/(1+S)$. At either endpoint $a\pm t(S)$,
$|g'|\le Ce^{2A}(1+S)$, with the same bound along this small
displacement. Its extra exponent is therefore bounded by $C\rho$.
The source arguments remain in the original strip, including negative
real arguments. On this circle,

$$
|V_+|+|V_-|\le Ce^{Ce^{2A}S},\qquad
|\mathcal A|+|\mathcal A/(1+s)|
 \le C(A+B+1)(1+S)^4e^{Ce^{2A}S}.
$$

Cauchy followed by Taylor's integral remainder gives, for every real
$s\ge0$ and every $N$,

$$
|\mathcal A(s)-\operatorname{Taylor}_{N-1}\mathcal A(s)|
 \le C(A+B+1)(Ce^{2A})^Ns^N(1+s)^4e^{Ce^{2A}s},
$$

and the same bound for the divided amplitude. For $\Delta\ge D_0$,
$\Re(\pi e^{2b})-Ce^{2A}\ge c e^{2B}$. Laplace integration
therefore pays $C^NN!e^{-2(B-A)N}$ after normalization. The fixed
extra factorial factors from $(1+s)^4$ are absorbed in $C^NN!$.
The exact high theta residual from (W94) is bounded by
$Ce^{-c e^{2B}(1+s)}$. Integrating it against the same complete
lower amplitude gives the other term in (W97), without removing any
reflected region. The existing identity-theorem interface identifies
the continuations.

Collecting Taylor terms in powers of $e^{-2b}$, including the high
prefactor's shift by at most one, and factoring out $e^{2kA}$ gives
the same $C_{k;A,B}$ for every $N$. At order zero the lower bracket
is $2a\Phi(a)/\Phi_{\rm g}(a)$; this verifies the displayed leading
coefficient and normalization.

### Pay the lower theta correction on its own moment sequence

For all sufficiently large $A$, all $k\ge0$ and local sign degrees
with $m_A\le e^A$, the coefficient forms satisfy, for some fixed
sufficiently large $P$,

$$
\boxed{|B_{C_{k;A,B}}(\nu_A,\nu_B)|
 \le (A+B+1)[C(m_A+m_B+k+1)]^{P(k+1)}\sqrt{Q_AQ_B}.}
\tag{W98}
$$

No numerical value of $P$ is asserted. To obtain this bound, split the
lower Taylor coefficients into their one-mode part and their paid full
source correction. Put $T=\pi e^{2a}$, $r_a=c_*e^{-2a}$. The
one-mode ratios, used only for coefficients near $s=0$, are

$$
\begin{aligned}
V_{+,1}&=(1+s)^{9/4}e^{-Ts}[1-r_a/(1+s)],\\
V_{-,1}&=(1+s)^{-9/4}e^{Ts/(1+s)}[1-r_a(1+s)].
\end{aligned}
$$

Their order-$k$ coefficients are polynomials in $T$ of degree at most
$k$. Expanding the exponentials and the binomial/logarithm factors
bounds their scalar coefficients by $C^{k+1}(k!)^r$ for a fixed
$r$. There are at most $k+1$ powers of $T$ in each prefactor case.
After the factor $e^{2kA}$ in (W97), the lower coordinate multipliers
are bounded scalar factors times
$\cosh u\,e^{(2\ell+1)u}$, $-1\le\ell\le k$, with an optional
$u$ or $v$. For $\ell\ge0$ these are
$g_\ell(-z)=(1+z)^\ell/(1-z)^{\ell+1}$; for $\ell=-1$ the
factor is $g_0(z)=1/(1+z)$. The upper multiplier is
$g_k(\zeta)=(1-\zeta)^k/(1+\zeta)^{k+1}$.

The shift-tail norm estimate paid in (W92)--(W94) gives
$[C(m+k+1)]^{k+1}$ for each $g_k$, and the same estimate holds for
its reflected version. These multipliers are positive on the actual
support and retain the same separator. Thus (W57) pays the optional
$\operatorname{arctanh}$ multiplier at its logarithmic cost.
Factorials, the number of monomials and the two measure costs are all
absorbed in the fixed exponent $P(k+1)$ in (W98).

For the full lower correction, use the small circle
$|s|\le\rho e^{-2A}$. Both lower arguments remain in the high tail,
so their exact theta series give, uniformly on the fixed lower offset
disc,

$$
\left|\frac{(\Phi-\Phi_1)(a\pm t(s))}{\Phi_{\rm g}(a)}\right|
 \le Ce^{-c e^{2A}}.
$$

The ratios $\Phi_{\rm g}(a\pm t(s))/\Phi_{\rm g}(a)$ are bounded
there. Its order-$k$ Taylor coefficient costs at most
$C^{k+1}e^{2Ak}e^{-c e^{2A}}$.
After the normalization in (W97), this yields a fixed finite sum of
lower holomorphic factors bounded by
$C^{k+1}k!(A+B+1)e^{-c e^{2A}}$, times upper $g_k$ or $vg_k$.
The lower integral uses (W63)'s linear Cauchy allowance and costs

$$
C\Lambda^{m_A/2}e^{-c e^{2A}}\sqrt{Q_A}.
$$

The upper integral keeps its polynomial cost. Since $m_A\le e^A$,
this lower source error absorbs $\Lambda^{m_A/2}$ at one common
large start. This proves (W98) for the actual coefficients as well.
In particular no $\Lambda^{m_B/2}$ is charged to a source error
controlled only by the lower center. The lower one-mode expression
was not substituted on the reflected exterior of the actual integral.

### Spend the growing order before adding the windows

Choose

$$
0<\kappa<\min\left\{\kappa_{\rm W91},\frac14,
                         \frac{\tau}{16P},\frac{\tau}{16}\right\},
\qquad
N=\left\lceil D\left(1+
          \frac{m_A+m_B+1}{\Delta}\right)\right\rceil\ge3,
$$

with fixed sufficiently large $D$. For $B\ge q_{\rm geo}A$,
$\Delta\ge\tau(A+B)\ge\tau B$. Let $M=m_A+m_B$.
Then $\log N\le\kappa B+O(1)$ and
$M+k+1\le C_D(M+1)$ for $k<N$. At one common large start,
$P\log[C(M+k+1)]\le\Delta/8$. The retained coefficient forms in
(W97) are therefore bounded by

$$
C\frac{A+B+1}{\sqrt{AB}}e^{-\Delta}
 \sum_{k<N}e^{-2k\Delta}[C(M+k+1)]^{P(k+1)}\sqrt{Q_AQ_B},
$$

where the sum is at most $Ce^{\Delta/8}$.
The ratio $(A+B+1)/\sqrt{AB}\le3+\Delta$ is harmless at the
scale in (W96).

Apply the two-variable Cauchy/moment allowance only to the actual
remainder in (W97). It costs $\Lambda^{M/2}$.
Since $\log(C^NN!)\le N(\kappa B+O(1))\le N\Delta/4$,
increase $D$ until

$$
\Lambda^{M/2}C^NN!e^{-2N\Delta}
 \le e^{-c\Delta-cM}.
$$

The high theta error times $\Lambda^{M/2}$ is still smaller, because
$\kappa<2$. All estimates concern the same two profiles. This proves
(W96), including every complete-source contribution, for one common
high start independent of the allowed degrees.

Now take any finite family with $A_{j+1}\ge q_{\rm geo}A_j$,
$A_1\ge A_*$ and $m_j\le\lfloor e^{\kappa A_j}\rfloor$.
The local credits from (W91) are $Q_{L_0}(\lambda_j)\ge Q_j/2$.
Every successive center gap is at least
$D_{\rm gap}=(q_{\rm geo}-1)A_*$. The common start includes that
of (W91). Increase it also until
$D_{\rm gap}\ge\max(D_0,1,2w+1)$ and, with
$q_D=e^{-D_{\rm gap}/2}$, the same row allowance used in (W64) obeys

$$
2C\left[\frac{q_D}{1-q_D}
       +\frac{D_{\rm gap}q_D}{(1-q_D)^2}\right]\le\frac14.
$$

Estimate (W96) then pays the entire finite cross form, leaving

$$
\boxed{Q_{L_0}\!\left(\sum_{j=1}^N\lambda_j\right)
 \ge\frac14\sum_{j=1}^NQ_j>0}
\tag{W99}
$$

unless all profiles vanish. Complex profiles use the two explicit real
separator classes; reality and symmetry add their forms. There is no
internal node-gap restriction, upper sample density or bound on the
finite number of windows. This extends (W64)'s linear local degree
range to exponential degrees; it uses the new actual inputs
(W97)--(W98), rather than inserting (W91) into the old cross bound.

### Attach a fixed compact core after paying every remote interaction

Fix $U>0$ and, if needed, reduce $\kappa$ further to the rate of
(W92) for that $U$. This preserves (W96)--(W99). Let $\mu$ be any
finite complex measure on $[0,U]$ and use the same $\mathcal M(\mu)$
and $\mathcal C(\mu)$ as in (W92). For a remote family as above with
$A_1\ge T$ sufficiently large, that estimate and Cauchy--Schwarz give
 the compact cross allowance with

$$
\Gamma=\sum_j\frac{(m_j+1)e^{-2A_j}}{A_j}
 \le C\frac{e^{-(2-\kappa)T}}T.
$$

The geometric-series denominator is bounded after fixing
$q_{\rm geo}$ and the start. Spend half of the same total remote
credit (W99) by Young's inequality, as in (W67), to obtain

$$
\boxed{
\begin{aligned}
Q_{L_0}\!\left(\mu+\sum_j\lambda_j\right)
 &\ge Q_{L_0}(\mu)+\frac18\sum_jQ_j
       -C_{U,q_{\rm geo}}\frac{e^{-(2-\kappa)T}}T
            \mathcal M(\mu)^2,\\
\mathcal C(\mu)=0\quad\Longrightarrow\quad
Q_{L_0}\!\left(\mu+\sum_j\lambda_j\right)
 &\ge Q_{L_0}(\mu)+\frac18\sum_jQ_j
       -C_{U,q_{\rm geo}}\frac{e^{-4T}}T\mathcal M(\mu)^2.
\end{aligned}}
\tag{W100}
$$

The second line uses (W92)'s exact rank-one remainder on each window,
so its sum uses $\sum_j A_j^{-1}e^{-4A_j}$ instead. Every remote
interaction was already paid in (W99); no local credit is spent twice.

These estimates retain fixed small widths, geometric center spacing,
finite degree at each fixed center, and the explicit real separator
conditions. The compact size is fixed and its own form remains
unsigned; no comparison of $\mathcal M(\mu)^2$ with a nearly null
compact form is supplied. No all-order positivity on one fixed window,
original signed prime/Robin estimate, strict Robin for every integer
above5040, numerical start or RH proof follows.

## Finite remote-window horizons for negative actual theta witnesses

The qualitative transport (W40) can be made quantitative for the complete
actual odd kernel. A fixed negative physical seed yields a finite-site
negative witness in every remote window, with an explicit count and
reconstruction. This supplies a cofinal finite-order positivity target;
the required positivity is not established. The argument uses classical
Gaussian summation, conformal coordinates, Cauchy coefficients and
Lagrange interpolation, with the actual full source retained. It is a
repository-derived paper estimate without a priority or Lean-verification
claim. The Fourier and zero-exclusion interface (W37)--(W40) is reused.

### Bound the complete source as the strip approaches its boundary

For the source's normalization,

$$
\Phi(z)=\sum_{n\ge1}(4\pi^2n^4e^{9z/2}-6\pi n^2e^{5z/2})
 e^{-\pi n^2e^{2z}},\qquad \Phi(-z)=\Phi(z).
$$

For every $0<\eta<\pi/4$, put $c_\eta=\cos(2\eta)$. Elementary Gaussian summation gives, for every $y>0$ and $k=2,4$,

$$
\sum_{n\ge1}n^k e^{-yn^2}\le C_k y^{-(k+1)/2}.
$$

For example bound $(n\sqrt y)^k e^{-yn^2/2}$ by its real maximum and sum the remaining decreasing Gaussian by its integral. It follows directly from the actual full theta series, for $x\ge0$ and $|v|\le\eta$, that

$$
|\Phi(x+iv)|\le C c_\eta^{-5/2}e^{-x/2}.
$$

Evenness gives the same bound with $e^{-|x|/2}$ for every real $x$. Here and below $C$ is a fixed absolute constant for this fixed source normalization; its value can be enlarged, but has no dependence on $\eta$ or any window center. No positivity or zero-free logarithm of Phi is used.

Reuse the exact holomorphic extension W38, with $p=(a+b)/2$, $d=(a-b)/2$:

$$
\widetilde K_0(a,b)=\frac12\left[\int_0^\infty y\Phi(y+d)\Phi(y-d)dy
 -\int_0^p y\Phi(y+d)\Phi(y-d)dy\right],
\quad \widetilde L_0(a,b)=\widetilde K_0(a,b)-\widetilde K_0(a,-b).
$$

The finite integral is the W38 path integral, not a changed lower endpoint. Write $x=\Re p$, $s=\Re d$. On the positive real $y$ line the absolute product is bounded by

$$
C c_\eta^{-5}e^{-(|y+s|+|y-s|)/2}
 =C c_\eta^{-5}e^{-\max(y,|s|)}.
$$

Thus the infinite integral and the horizontal part of the finite integral are uniformly bounded: $\int_0^\infty y e^{-\max(y,|s|)}dy\le C$. Negative real $p$ gives the same absolute bound by evenness of the product and oddness of $y$ times the product. Deform the finite path to $0\to x\to p$. All shifted source arguments along it remain in the original strip: their imaginary parts are between the real-path values $\pm\Im d$ and the endpoint values $\Im a,\Im b$. Its vertical part is at most

$$
C c_\eta^{-5}\eta(|x|+\eta)e^{-\max(|x|,|s|)}\le Cc_\eta^{-5}.
$$

The same argument applies to $b\mapsto-b$. Consequently there is one absolute $D\ge1$ such that

$$
\sup_{a,b\in D_\eta}|\widetilde L_0(a,b)|\le D[\cos(2\eta)]^{-5}.
\tag{W101}
$$

This is a bound for the complete actual kernel on the full strip product, not just on a compact substrip square. It retains the reflected term and needs no source replacement.

### Keep a bounded exact disc kernel at a moving center

For $A\ge2$ set

$$
q_A=\frac{A+1}{A},\qquad \eta_A=\frac{\pi}{4q_A},\qquad
\chi_A(t)=A+q_A^{-1}\operatorname{arctanh}t.
$$

The map $\chi_A$ takes the unit disc to $D_{\eta_A}$. Also

$$
\cos(2\eta_A)=\sin\frac{\pi}{2(A+1)}\ge\frac1{A+1}.
$$

Thus the exact two-variable pullback

$$
\mathscr L_A(t,s)=\widetilde L_0(\chi_A(t),\chi_A(s))
 =\sum_{p,q\ge0}c_{pq}^{(A)}t^ps^q
$$

is bounded by $M_A=D(A+1)^5$ on the unit bidisc. Cauchy, with radii increasing to1, gives $|c_{pq}^{(A)}|\le M_A$. The coefficients are real and symmetric. There is no Gaussian-leading approximation and no change to the actual physical quadratic form.

Suppose a fixed actual finite real seed, at points $a_\ell\in(1,2)$ and with coefficients $b_\ell$, satisfies

$$
\sum_\ell|b_\ell|=1,\qquad
\sum_{\ell,k}b_\ell b_kL_0(a_\ell,a_k)=-\varepsilon<0.
\tag{W102}
$$

Let $t_\ell=\tanh(q_A(a_\ell-A))$, $r_A=\max_\ell|t_\ell|$ and $\beta_p=\sum_\ell b_\ell t_\ell^p$. For $A\ge2$ we have $0<r_A<1$, $r_A\le\tanh A$, and hence $1-r_A\ge e^{-2A}$. All full series converge absolutely on this finite seed. For the $n$-by-$n$ coefficient block,

$$
Q_{A,n}=\sum_{0\le p,q<n}c_{pq}^{(A)}\beta_p\beta_q,
\qquad
|Q_{A,n}+\varepsilon|\le\frac{2M_A r_A^n}{(1-r_A)^2}.
\tag{W103}
$$

This is simply the omitted double geometric sum, applied to the complete kernel and the same actual seed. A sufficient explicit integer is

$$
n\ge2+\left\lceil\frac{\log\left(1+\frac{8M_A}{\varepsilon(1-r_A)^2}\right)}{1-r_A}\right\rceil.
\tag{W104}
$$

It makes the error in W103 at most $\varepsilon/4$, so $Q_{A,n}\le-3\varepsilon/4$. W104 is an upper horizon, not a test of all possible negative directions or a numeric value without the seed/margin.

### Reconstruct the negative block on explicit physical nodes

Fix any $w>0$ and any $n\ge2$ for which the error in W103 is at most $\varepsilon/4$. Put $E_A=(1-r_A)^{-1}$ and choose

$$
h=\min\left\{\frac12,\frac12\tanh(q_Aw),
 10^{-(n-1)}\min\left(\frac12,\frac{\varepsilon}{16M_A(E_A+1)}\right)\right\}>0.
$$

Use the $n$ distinct real disc nodes $x_j=jh/(n-1)$, $0\le j<n$, with Lagrange polynomials $\ell_j$ and weights

$$
\alpha_j=\sum_\ell b_\ell\ell_j(t_\ell),\qquad \nu_A=\sum_{j=0}^{n-1}\alpha_j\delta_{\chi_A(x_j)}.
\tag{W105}
$$

These are actual physical points in $[A,A+w)\subset(A-w,A+w)$. Real polynomial interpolation gives $\sum_j\alpha_jx_j^p=\beta_p$ for every $p<n$. Moreover

$$
\sum_j|\alpha_j|\le(10/h)^{n-1}.
$$

Indeed $|t_\ell-x_k|\le1+h\le3/2$ and the denominators are $(h/(n-1))^{n-1}j!(n-1-j)!$ in absolute value. Sum their inverses and use $(n-1)!\ge((n-1)/e)^{n-1}$.

If $\gamma_p=\sum_j\alpha_jx_j^p$, its high tail obeys

$$
H:=\sum_{p\ge n}|\gamma_p|
 \le2\,10^{n-1}h
 \le\min\left(1,\frac{\varepsilon}{8M_A(E_A+1)}\right).
$$

The low tail satisfies $\sum_{p<n}|\gamma_p|\le E_A$. The complete actual coefficient series therefore gives

$$
|Q_{L_0}(\nu_A)-Q_{A,n}|
 \le M_A(2E_AH+H^2)\le\varepsilon/4.
$$

Consequently

$$
Q_{L_0}(\nu_A)\le-\varepsilon/2<0,
\qquad \#\operatorname{supp}\nu_A\le n.
\tag{W106}
$$

This proves the finite-site realization, including every mixed high coefficient. It is not an inference from a negative derivative matrix without a remainder. The weights can be enormous and gaps extremely small; neither stable recovery nor a finite precision certificate is claimed. The explicit formulas are mathematical constructions, not executed solvers.

### Consume a common finite-order schedule on cofinal centers

Set

$$
n_A=\left\lceil8(A+1)e^{2A}\right\rceil.
$$

Because $r_A\le1-e^{-2A}$, W103 for $n=n_A$ is at most

$$
2D(A+1)^5e^{4A}e^{-8(A+1)}
 =2D(A+1)^5e^{-4A-8}\longrightarrow0.
\tag{W107}
$$

For every fixed actual seed W102, the construction W105 therefore yields a negative physical sample on at most $n_A$ sites in every window $(A-w,A+w)$ beyond a single seed-dependent start. The count has no width dependence; the stencil's resolution does depend on $w$. No optimality of the exponent2 or the factor8 is asserted.

If RH fails, the already-owned W40 applied to the fixed interval $(1,2)$ supplies precisely a finite negative seed W102: the kernel is real symmetric, so real coefficients suffice, and they may be normalized by total variation. Therefore

$$
\begin{gathered}
\mathrm{RH\ false}\quad\Longrightarrow\quad
\exists A_\varepsilon\ \forall A\ge A_\varepsilon:\\
\text{a real negative }L_0\text{ sample exists in }(A-w,A+w)
\text{ on at most }\lceil8(A+1)e^{2A}\rceil\text{ sites}.
\end{gathered}
\tag{W108}
$$

Here $w>0$ is arbitrary and fixed. This is conditional source-specific witness localization with a quantitative count, not a found negative theta sample. No off-line zero, negative seed, numerical start or actual counterexample has been supplied.

An immediate actual consumer is now available: if, for some fixed $w>0$ and an unbounded set of centers $A$, the complete actual $L_0$ is PSD on every real sample of at most $n_A$ sites in $(A-w,A+w)$, then RH follows. The hypothesis quantifies over every location and coefficient on each admitted sample, not one grid or a finite scan. It only requires finite order at each center and a cofinal collection of centers. In particular a local sign-degree estimate valid up to $e^{\kappa A}$ with any fixed $\kappa>2$ on an unbounded sequence of large centers would suffice, because any real $n$-point measure has a polynomial sign separator of degree at most $n-1$, and complex coefficients split into real and imaginary parts.

Existing W91 has a small fixed $\kappa$, not $\kappa>2$, and does not meet this target. Under RH failure, combining its positivity with W108 bounds the minimum number of sites needed for a negative local witness from below and above; this supplies neither sign nor a contradiction. W96--W100 and their geometric interaction estimates are reused unchanged. The new input is the actual near-boundary strip bound and complete finite-node reconstruction making the qualitative W40 obstruction quantitative. No identity with Suzuki's physical Weil operator, original prime form or Robin functional is asserted. Full RH and strict Robin for every integer above5040 remain unproved.
