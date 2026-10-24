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


The [Conrey–Li source](conreyli1998positivity.md) records an existing obstruction to two specified global imaginary-translation positivity conditions in reproducing-kernel function spaces. Their operators and translation domains require separate identification with the actual theta source. Their reported failure neither replaces the complete Weil criterion nor determines the sign on the selected physical-source class.


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

## A larger positive sign range for the complete theta kernel

On the fixed small physical window of (W87)--(W91), a fixed positive
$c_{\rm deg}$ permits polynomial-sign degree up to
$c_{\rm deg}e^{2A}\log A/A$, with Hardy margin $\log A/(8A)$.
For each fixed $0<\delta<2$, a stronger fixed margin $\delta/4$ is
available up to $e^{(2-\delta)A}$. These are estimates for the same
complete actual odd kernel and exact Gaussian-leading transport,
including the reflected exterior. The required common starts are
specified by the corresponding fixed parameters.

The proof reuses the actual model formulas, all-order factorial
remainder, moment-radius inequality, logarithmic multiplier norm and
stationary comparison in (W55), (W57), (W87)--(W89). It sharpens the
one-sided core allowance, pays the multiplier denominators before
spending the factorials, and strengthens the full-source comparison.
The methods are classical Hardy, Gaussian and Laplace estimates;
this source-specific paper derivation carries no priority or
Lean-verification claim.

For each fixed $0<\delta<2$ there is $A_\delta$ so every nonzero real measure in the existing degree-$m$ polynomial-sign class satisfies

$$
Q_{\mathcal K_A^{\rm g}}(\nu)\ge\frac{\delta}{4}Q_H(\nu)>0,
\qquad A\ge A_\delta,\quad 0\le m\le\lfloor e^{(2-\delta)A}\rfloor.
\tag{W109}
$$

Complex finite samples are then admitted up to $\lfloor e^{(2-\delta)A}\rfloor+1$ sites by real/imaginary splitting, exactly as in W91. Here $\delta$ is fixed before the common start; no uniform $\delta$ tending to zero is asserted. The same actual Hardy metric and positive congruence are retained.

### Keep the sharp one-sided logarithmic coefficient

Write

$$
a=(a_n),\qquad Q=\|a\|_2^2=Q_H(\nu),\qquad (Ba)_n=a_{n+1}.
$$

The reused tail allowance gives

$$
\|B^j a\|_2\le\min(1,L_mq^{-j})\|a\|_2,\quad
L_m=3\Lambda^{m/2},\quad q>4.
$$

Choose an integer J between c(m+1) and C(m+1) with L_m q^{-J}<=1. Cauchy--Schwarz on n<J and the geometric tail show

$$
\|a\|_1\le C\sqrt{m+1}\|a\|_2.
$$

For the actual generating function F_a(e^{it})=sum a_n e^{int}, the probability density |F_a|^2/Q on the circle is therefore bounded by C(m+1). With normalized circle measure, the set |1+e^{it}|<e^{-s} has length at most Ce^{-s}. Layer-cake integration gives

$$
\int\log|1+e^{it}|\frac{|F_a(e^{it})|^2}{Q}\frac{dt}{2\pi}
 \ge-\log(m+1)-C.
$$

The other logarithm is bounded above by log2. Actual compact support inside(-1,1) gives absolute convergence of the moment series and its logarithmic boundary integrals. Thus the Hardy shift identity for this same sequence yields

$$
\begin{aligned}
\Re\langle a,\operatorname{arctanh}(B)a\rangle
&=\frac12\int\log\left|\frac{1+e^{it}}{1-e^{it}}\right|
 |F_a(e^{it})|^2\frac{dt}{2\pi}\\
&\ge-\left[\frac12\log(m+1)+C\right]Q.
\end{aligned}
\tag{W110}
$$

No favorable sign for the whole correction is assumed. The stationary T(t)=t/(2sinh t) contribution is bounded in absolute form by Q_H using the already-owned W57 comparison. Hence the exact first core satisfies

$$
Q_{H+\widetilde C_{\rm core}/A}(\nu)
 \ge\left[1-\frac{\log(m+1)}{2A}-\frac CA\right]Q.
\tag{W111}
$$

For m<=exp((2-delta)A), the bracket is at least delta/2-O(1/A). The coefficient1/2 comes from the actual logarithmic form and is not an unspecified log-norm constant.

### Retain the denominator of each growing multiplier order

For positive integer r, put f_r(z)=exp(-r atanh z). Its reflected series g_r(z)=f_r(-z)=exp(r atanh z)=sum c_{rj}z^j has nonnegative coefficients. Set

$$
\rho=1-\frac r{2(J+r)}\in[1/2,1).
$$

For all j>=0,

$$
\min(1,L_mq^{-j})\le\rho^{j-J}.
$$

For j<=J the right side is at least1; for j>J use q^{-1}<rho and L_mq^{-J}<=1. Therefore

$$
\begin{aligned}
\|f_r(B)a\|_2/\|a\|_2
&\le\sum_j c_{rj}\min(1,L_mq^{-j})\\
&\le\rho^{-J}\left(\frac{1+\rho}{1-\rho}\right)^{r/2}
 \le\left[\frac{C(m+r+1)}r\right]^{r/2}.
\end{aligned}
\tag{W112}
$$

Here rho^{-J}<=exp(r/2) and (1+rho)/(1-rho)<4(J+r)/r. The case r=0 is the identity, kept separate. This bound is uniform in m and r and applies to the same actual moment sequence; no extremal profile is changed.

Also reuse the weighted moment tail on every measure sigma with the same sign separator:

$$
\sum_{n\ge0}\binom{n+\ell}{\ell}|a_n(\sigma)|^2
 \le\frac{[C(m+\ell+1)]^\ell}{\ell!}Q_H(\sigma),
\qquad \ell\ge0.
\tag{W113}
$$

This follows from binom(n+ell,ell)<=(n+ell)^ell/ell! and the existing weighted tail bound, using (n+ell)^ell<=2^(ell-1)[(n+1)^ell+(ell-1)^ell] when ell>=1. Positive multipliers f_r and (1-z)^ell preserve the same separator, including root atoms. Multiplication by atanh z has separator zp of degree m+1 and the already-owned C log(m+2) norm cost; this is used only where an actual factor1/A accompanies it.

### Strengthen the full-source error on the complete reflected contour

Keep exactly the fixed complex offset bidisc and model Phi1 of W87--W88. The full-to-model comparison can be paid by

$$
\sup|M_A^{\rm g}-M_{A,1}^{\rm g}|
 \le Ce^{-c e^{2A}},
\tag{W114}
$$

in place of W87's coarser exp(-c exp A), without changing its model coefficients or all-N factorial remainder.

Here is the whole-half-line payment. In the direct integral, both source arguments are in the right tail, at least A-O(1), throughout. Their full theta errors relative to the Gaussian factor are bounded by exp(-c exp2A), and the normalized Gaussian integral is already uniformly integrable in W46/W87.

In the reflected integral use the SAME contour y=sqrt(d^2+E s), E=exp(-2A), with the complete even-source product Phi(x+y)Phi(x-y), x=A+(u+v)/2, as in W87. Choose a fixed large Y0 independently of A. On Re y<=Y0, the imaginary part of y is bounded by |Im d|, and both source arguments have real part at least A-O(1)-Y0. The full theta comparison there is exp(-c_Y0 exp2A); its Gaussian product is paid by the existing complete normalized majorant.

On Re y>=Y0, both full Phi and the chosen narrow-strip Phi1 are uniformly bounded for all real source arguments. The x+y factor has bound

$$
C e^{C(A+\Re y)}\exp[-c_0e^{2A+2\Re y}].
$$

The Gaussian congruence costs at most e^{C_0 exp2A+CA}. Fix Y0 large enough that c0 exp(2Y0)>2C0+2. On this part of the curve, |y dy|<=C(1+Re y)d Re y. Integrating the resulting bound, and absorbing fixed exponential/polynomial prefactors, gives Ce^{-c exp2A}. This pays even the region Re(x-y)<0 for both complete and model factors; Phi1 is never treated as even. The other model/source difference term is paid by the same high x+y bound. Thus no reflected exterior is discarded.

Together with the reused scalar Taylor/Stieltjes proof of W87, W114 gives, for every N>=3 with the SAME compatible B_{k,A},

$$
M_A^{\rm g}=S+C_{\rm core}/A+\sum_{1\le k<N}E^kB_{k,A}+R_{N,A},
\quad
\sup|R_{N,A}|\le C^NN!E^N+Ce^{-c e^{2A}}.
\tag{W115}
$$

No finite theta cutoff is declared PSD. The model is only an algebraic expansion device, with its full-source error paid.

### Pay each actual coefficient at its own order

The exact W88 coefficient formulas together with W112--W113 give, for k>=1,

$$
|Q_{\cosh u\cosh v B_{k,A}}(\nu)|
 \le[C(m+k+2)]^k\left(1+\frac{\log(m+k+2)}A\right)Q.
\tag{W116}
$$

All constants are independent of A,k,m. The factorial cancellation has two different payments in the direct and reflected pieces.

For the direct term, choose p,q in{0,1} from the r_a,r_b prefactors, put j=p+q, and let ell be the Taylor order in tau-1. Its E-order is k=ell+j. The Laplace integral contributes ell!, while the exact kernel identity is

$$
\cosh u\cosh v e^{-\ell(u+v)}\operatorname{sech}^{\ell+1}(u-v)
 =\frac{(1-z)^\ell(1-w)^\ell}{(1-zw)^{\ell+1}}.
$$

Use the two actual measures sigma_p=(1-z)^ell f_{2p}(z)nu and sigma_q=(1-z)^ell f_{2q}(z)nu. For p=0 use the identity; for p=1, W112 with r=2 gives norm at most C(m+1). The polynomial multiplier has shift norm at most2^ell. Weighted Cauchy--Schwarz and W113 therefore pay the bilinear coefficient by [C(m+k+2)]^k/ell! times Q. The ell! from integration cancels this denominator.

The three scalar amplitudes (x+0.5log tau)tau^(7/2-j) from W88 have order-ell Taylor coefficients bounded by C^(ell+1)(|x|+1), without an additional ell!. The affine x/A part contributes1 and atanh(z)/(2A),atanh(w)/(2A). The latter use the existing logarithmic norm and the degree-(m+1) separator after multiplication, at cost1+log(m+k+2)/A, not a new fixed power of m. The scalar log tau term has factor1/A and needs no extra moment multiplier. At fixed k only the finitely many prefactor cases occur: ell=k,k-1,k-2.

For the reflected term, reuse precisely W89's stationary bilinear comparison

$$
|B_{h_j\circ\cosh}(\sigma,\tau)|
 \le C^{j+1}\sqrt{Q_S(\sigma)Q_S(\tau)}.
$$

The exact prefactors in W88 produce only these cases (r,s are the exponents in exp(-ru-sv)):

| W88 prefactor | E-order k | (r,s) | scalar factorial |
|---|---:|---|---|
| 1 | j | (j,j) | j! |
| -r_a or -r_b | j+1 | (j+2,j) or (j,j+2) | j! |
| c_*^2 exp(-2(a+b)) | j+2 | (j+2,j+2) | j! |
| -2c_* exp(-(a+b)) s | j+2 | (j+2,j+2) | (j+1)! |

The j=0,k=0 term is the already-separated first core. In every remaining case r+s=2k, |r-k|,|s-k|<=1 and the factorial is at most k!. For k>=2, the denominator from the two W112 bounds is at least (k-1)^k; k!<=(2(k-1))^k cancels it at an exponential-in-k cost. For k=1 the finite cases are checked by their displayed formulas, with r=0 the identity. The numerator is bounded by [C(m+k+2)]^k. The overall1/A from W88 is harmless. This pays the whole reflected coefficient, with no independently optimized measure and no leftover factorial in k. It proves W116 for the existing actual expansion coefficients.

### Pay every fixed exponent below two

For nonzero nu the sharp core and the same Cauchy/moment allowance as W90 give

$$
\begin{aligned}
\frac{Q_{\mathcal K_A^{\rm g}}(\nu)}{Q}
\ge{}&1-\frac{\log(m+1)}{2A}-\frac CA\\
&-\sum_{1\le k<N}e^{-2Ak}[C(m+k+2)]^k
 \left(1+\frac{\log(m+k+2)}A\right)\\
&-C\Lambda^m\left[C^NN!e^{-2AN}+e^{-c e^{2A}}\right].
\end{aligned}
\tag{W117}
$$

Fix delta in(0,2), assume m<=exp((2-delta)A), and choose a fixed sufficiently large D_delta with

$$
N=\left\lceil D_\delta\left(1+\frac{m+1}{A}\right)\right\rceil\ge3.
$$

For k<N, m+k+2<=C_delta(m+1). At a common large A_delta, log[C(m+k+2)]<=(2-delta/2)A; the retained sum is therefore O_delta(exp(-delta A/2)). Its logarithmic factor is uniformly bounded. Likewise log(C^N N!)<=(2-delta/2)AN. Increasing D_delta pays Lambda^m and gives a factorial remainder at most exp(-c_delta A-c_delta m). Finally m=o(exp2A), so Lambda^m exp(-c exp2A)<=exp(-c exp2A/2) at the same common start.

The first line of W117 is at least delta/2-O(1/A). Spend at most delta/4 on all the remaining terms to obtain W109. All estimates concern the SAME actual measure and full kernel. The start depends on fixed delta and fixed support; no quantitative numerical start is supplied.


### One fixed start admits the larger moving sign count

Let C>=1 dominate the fixed constants in W116--W117, and keep the positive source-error constant c separate. There exist fixed c_deg>0 and A_* such that, for every A>=A_* and every real measure in the same polynomial-sign class,

$$
0\le m\le\left\lfloor c_{\rm deg}\frac{e^{2A}\log A}{A}\right\rfloor
\quad\Longrightarrow\quad
Q_{\mathcal K_A^{\rm g}}(\nu)
 \ge\frac{\log A}{8A}Q_H(\nu)>0
\quad(\nu\ne0).
\tag{W118}
$$

The constant c_deg is new notation, distinct from the source's c_*=3/(2pi). All source, support, norm and sign-separator contracts are unchanged. There is no assertion that the source count or the rate is optimal.

To pay the growing-order terms directly, put L=log A, M_A=c_deg exp2A L/A and choose

$$
N=\left\lceil D\,\frac{A+m+1}{L}\right\rceil,
\qquad D\ge\max(4,2\log\Lambda+4).
$$

D is fixed. Increase one A_* so L>=2D, M_A>=1, N>=3 and, for every m<=M_A,

$$
m+N+2\le2M_A,\qquad
\log(CN)\le2A-L/2.
\tag{W119}
$$

These bounds are uniform in the admitted m: the maximum of N is O(D M_A/L+D A/L), so log(CN)<=2A-L+O(1), and (m+N+2)/M_A<=1+D/L+o(1). Their constants depend only on fixed D,c_deg and source constants.

The logarithmic coefficient factor in W117 is at most4. Set

$$
\theta_A=C e^{-2A}(m+N+2)
 \le2C c_{\rm deg}L/A.
$$

For a fixed choice 0<c_deg<=min(1,1/(256C)) and sufficiently large A_*, theta_A<=1/2. Thus every retained coefficient and its log factor are paid by

$$
\sum_{1\le k<N} e^{-2Ak}[C(m+k+2)]^k
 \left(1+\frac{\log(m+k+2)}A\right)
 \le\frac{4\theta_A}{1-\theta_A}
 \le\frac{L}{16A}.
\tag{W120}
$$

The first core in W117 is bounded below by

$$
1-\frac{\log(m+1)}{2A}-\frac CA
 \ge\frac{L-\log L-\log(2c_{\rm deg})-2C}{2A}
 \ge\frac{L}{4A}.
\tag{W121}
$$

Here m+1<=2M_A at the same fixed start.

For the factorial remainder, W119 and log(N!)<=N logN give

$$
\log\left(\Lambda^m C^NN!e^{-2AN}\right)
 \le m\log\Lambda-\frac{L}{2}N
 \le-\frac D2 A-\left(\frac D2-\log\Lambda\right)m-\frac D2
 \le-2(A+m).
$$

Any fixed multiplicative constants in W117 are absorbed by increasing A_*. The complete-source error obeys

$$
\Lambda^m e^{-c e^{2A}}
 \le e^{-c e^{2A}/2},
$$

because m/e^{2A}<=c_deg L/A tends to0. The sum of these two actual remainders is at most L/(16A). Insert W120--W121 into the SAME W117 for the SAME measure to obtain L/(4A)-L/(16A)-L/(16A)=L/(8A), proving W118.

No estimate uniform in a varying delta has been silently assumed. All quantities are directly paid from W117 with one fixed start and explicit moving N. No model is asserted positive independently of the full-source error.


### Sample counts and the remaining sufficient target

For arbitrary complex coefficients on at most
$\lfloor c_{\rm deg}e^{2A}\log A/A\rfloor+1$ distinct sites in the same
physical window, apply the real estimate separately to the real and
imaginary parts. Each measure has a polynomial sign separator of
degree at most one fewer than the site count, and the exact positive
Gaussian transport preserves its signs. There is no internal gap or
density restriction; repeated roots and root atoms remain in the real
measure class. The margin is in the transported Hardy norm. Strictness for a nonzero real measure uses the same compact-moment uniqueness argument as (W91).

For every fixed $\delta\in(0,2)$, the fixed-$\delta$ statement above
retains the stronger margin $\delta/4$. The moving-count proof was
paid directly from the uniform estimate, with one fixed
$c_{\rm deg}$ and start; it was not inferred by substituting a
varying $\delta$.

Conditionally on RH failing, combine the new positive count with
(W108), without changing that theorem's seed-dependent eventual
start. The minimum number of sites required for a local negative
witness exceeds the new admitted count and is at most
$\lceil8(A+1)e^{2A}\rceil$ eventually. The upper bracket bound divided by the lower is $O(A^2/\log A)$. This is a comparison of
bounds, not a measured value or an optimality claim. It supplies no
contradiction.

The complete all-sample sufficient count in (W108), all orders on
one fixed window, and the original signed Robin upper remain unpaid.
The existing geometric-family estimates retain their stated smaller
rate; a larger-rate joint extension is not supplied here. No actual
negative seed or sample, numerical start, effective finite RH test,
identity with the original prime/Robin operator or RH proof is
provided. Full RH and strict Robin for every integer $n>5040$
remain unproved.


## Fewer sites suffice for remote negative theta witnesses

The complete actual source in (W101)--(W108) admits a smaller
conditional negative-witness count. The improvement applies the
classical logarithmic norm of analytic Taylor sections before
evaluating the same negative seed. The complete strip bound,
conformal coordinates and physical stencil are reused. This is a
repository-derived paper application, without a priority or
Lean-verification claim.

Keep exactly the notation of (W101)--(W103): for $A\ge2$,

$$
\begin{gathered}
q_A=(A+1)/A,\qquad
\chi_A(t)=A+q_A^{-1}\operatorname{arctanh}t,\\
F_A(t,s)=\widetilde L_0(\chi_A(t),\chi_A(s)),\qquad
\|F_A\|_{\infty,\mathbb D^2}\le M_A=D(A+1)^5.
\end{gathered}
$$

The fixed real negative seed remains in $(1,2)$, has total
variation one and actual margin $-\varepsilon<0$. Its disc points,
moments $\beta_p$, radius $r_A\le1-e^{-2A}$ and principal form
$Q_{A,n}$ are unchanged. No model replaces the complete source.

### Bound Taylor sections before evaluating near the disc boundary

Let $P_n$ retain the first $n$ Taylor terms in one variable. Use the
classical analytic projection bound

$$
\begin{gathered}
\|P_nf\|_\infty\le\mathsf L_n\|f\|_\infty,\qquad
\mathsf L_n=\int_{-\pi}^{\pi}
 \left|\sum_{j=0}^{n-1}e^{ij\theta}\right|\frac{d\theta}{2\pi}
 \le C\log(n+1),\\
\left\|\frac{f-P_nf}{z^n}\right\|_\infty
 \le(1+\mathsf L_n)\|f\|_\infty.
\end{gathered}
\tag{W122}
$$

The quotient is removable at zero. The finite geometric sum is
bounded by $\min(n,C/|\theta|)$; its integral gives the logarithmic
allowance. For bounded analytic functions on the open disc, use
$f(\rho z)$ with $\rho<1$ and then let $\rho\uparrow1$ to obtain
the projection estimate. On $|z|=\rho$, the quotient is bounded by
$(1+\mathsf L_n)\|f\|_\infty\rho^{-n}$; the maximum principle
followed by $\rho\uparrow1$ proves its full-disc bound. There is
no hidden dependence on an evaluation radius tending to one.
These are classical scalar facts used inside the actual application,
not new generic mathematical declarations.

Apply them sectionwise to $F_A$, and write
$T_n=P_n^{(t)}P_n^{(s)}$. The exact decomposition is

$$
F_A-T_nF_A
 =(I-P_n^{(t)})F_A+P_n^{(t)}(I-P_n^{(s)})F_A.
$$

In the second term, factor out $s^n$ first; it commutes with the
projection in $t$. The two resulting bounds are respectively
$(1+\mathsf L_n)M_Ar^n$ and
$\mathsf L_n(1+\mathsf L_n)M_Ar^n$ on $|t|,|s|\le r<1$.
Consequently

$$
\begin{aligned}
\sup_{|t|,|s|\le r}|F_A-T_nF_A|
 &\le(1+\mathsf L_n)^2M_Ar^n,\\
|Q_{A,n}+\varepsilon|
 &\le C M_A\log^2(n+1)r_A^n.
\end{aligned}
\tag{W123}
$$

The second line uses only the same seed's total variation one.
The unweighted section $T_nF_A$ is exactly the original principal
Taylor block. No filtered block, nonlinear predictor or positivity
assumption is introduced. Unlike the coefficientwise bound in
(W103), this estimate spends no factor $(1-r_A)^{-1}$.

### Reuse the actual physical reconstruction at the smaller count

Set

$$
\widetilde n_A=\left\lceil12e^{2A}\log(A+1)\right\rceil.
\tag{W124}
$$

For $A\ge2$ one has $\log(\widetilde n_A+1)\le C(A+1)$ and
$r_A^{\widetilde n_A}\le(A+1)^{-12}$. Thus

$$
|Q_{A,\widetilde n_A}+\varepsilon|
 \le CD(A+1)^7(A+1)^{-12}
 =CD(A+1)^{-5}\longrightarrow0.
\tag{W125}
$$

After one seed-dependent start this is at most $\varepsilon/4$,
so the same principal block has form at most $-3\varepsilon/4$.
The constant twelve is a sufficient choice, without an optimality
claim or a numerical start.

The reconstruction in (W105)--(W106) uses this actual block margin,
the unchanged coefficient bound $M_A$ and polynomial moment
matching. It does not require the older coefficientwise sufficient
upper bound itself to be small. Insert $n=\widetilde n_A$ in its
same positive stencil scale, real Lagrange weights and complete
high-coefficient allowance. The resulting actual physical form is
at most $-\varepsilon/2$ on at most $\widetilde n_A$ sites in
$(A-w,A+w)$, for any fixed $w>0$. Every mixed high coefficient is
paid as in (W106). The site count is independent of $w$; the
stencil spacing and precision are not. This is the existing
construction, not an executed solver or a stable finite-precision
certificate.

By (W40), RH failure supplies the required fixed real negative seed
in $(1,2)$. Therefore

$$
\begin{gathered}
\mathrm{RH\ false}\quad\Longrightarrow\quad
\exists A_\varepsilon\ \forall A\ge A_\varepsilon:\\
\text{a real negative actual }L_0\text{ sample exists in }(A-w,A+w)
\text{ on at most }\left\lceil12e^{2A}\log(A+1)\right\rceil
\text{ sites}.
\end{gathered}
\tag{W126}
$$

No actual negative seed or sample is provided. This reduces the
conditional count from $O(Ae^{2A})$ to $O(e^{2A}\log A)$ and
preserves the same source and quantifiers.

If for some fixed $w>0$ and an unbounded set of centers $A$, the
complete actual kernel is PSD on every real sample of at most
$\widetilde n_A$ sites in $(A-w,A+w)$, then RH follows. This is
the existing cofinal consumer of (W108) with the smaller actual
count; its positivity hypothesis is not established. The
quantifiers still include every location and coefficient at each
admitted count. It is not a finite RH test.

For the same fixed small window as (W118), the already established
positive count is

$$
\mathsf L_A=
 \left\lfloor c_{\rm deg}e^{2A}\frac{\log A}{A}\right\rfloor+1.
$$

Conditionally on RH failing, beyond the maximum of the relevant
starts the minimum local negative-witness site count is greater
than $\mathsf L_A$ and at most $\widetilde n_A$. The upper
bracket bound divided by the lower is now $O(A)$. This compares
bounds, without determining the actual minimum, an optimum or a
contradiction. The existing positive range (W118) has not been
extended or reproved.

The smaller sufficient all-sample positivity range remains unpaid,
as do fixed-window all-order positivity and the original signed
Robin upper. No original prime/Robin operator identity, actual
negative zero, numerical start or RH proof is supplied. Full RH
and strict Robin for every integer $n>5040$ remain unproved.


## A larger positive range from the exact first prefactor

On the same fixed small physical window and real polynomial-sign
class as (W118), one fixed $c_{\rm pref}>0$ and one common high
start admit degrees up to
$c_{\rm pref}e^{2A}\sqrt{\log A/A}$, with lower margin
$\log A/(128A)$ in the original Gaussian Hardy metric. The proof
keeps the actual first correction's sign after an exact positive
normalization of the complete kernel.

Full RH and strict Robin for every integer $n>5040$ remain unproved. Reuse actual W88, W110--W116, W118 and W126. This is not an all-order positivity claim for a first-mode reference. The actual full theta kernel and full reflected exterior remain; only an exact positive diagonal normalization changes inside the proof.

### Exact positive normalization of the COMPLETE source

Keep $E=e^{-2A}$, $u=\operatorname{arctanh}z$, $v=\operatorname{arctanh}w$, the same fixed support $[-h,h]$, $c_*=3/(2\pi)$, original $\mathcal K_A^{\rm g}$ and original Gaussian Hardy metric $Q_H$. Write
$$
r_E(z)=c_*E e^{-2u},\quad h_E(z)=(1-r_E(z))^{-1},\qquad
\mathcal K_A^1(z,w)=h_E(z)\mathcal K_A^g(z,w)h_E(w).
$$
On the fixed complex Hardy bidisc, h_E is holomorphic and uniformly bounded at one sufficiently high start. On the real support it is positive. This is a congruence of the COMPLETE actual kernel; Phi1 is not substituted for its source. In physical coordinates it corresponds to D_A^1(u)=D_A^g(u)/(1-c_*e^{-2(A+u)}).

The real degree-m sign contract epsilon p nu>=0 is unchanged for every positive weight used below, including root atoms. If nu_g is the original physical transport and nu_1=(1-r_E)nu_g, then
$$
Q_{\mathcal K_A^g}(\nu_g)=Q_{\mathcal K_A^1}(\nu_1).
\tag{W127}
$$

### An actual weighted logarithmic payment

For $\sigma=(1-z)\nu$, put $b_n=\int z^n\,d\sigma(z)$, and
$$
\mathcal R(\nu)=\sum_{n\ge0}(n+1)b_n^2,
\quad F(w)=\sum_{n\ge0}(n+1)b_n w^n.
$$
The positive factor1-z preserves the same separator degree. The owned moment-radius allowance gives
$$
\sum q^{2n}b_n^2\le9\Lambda^m Q_H(\sigma)\le9\Lambda^m\mathcal R(\nu).
$$
Choose an integer $J$ proportional to $m+1$ with sufficiently large fixed proportionality constant. Split $\sum(n+1)|b_n|$ at $J$. Cauchy--Schwarz against weights $n+1$ bounds the first part by $CJ\sqrt{\mathcal R(\nu)}$. Applying it with weights $q^n$ bounds the tail by $C\Lambda^{m/2}(J+1)q^{-J}\sqrt{\mathcal R(\nu)}$, which has the same allowance. Thus
$$
\sup_{\mathbb D}|F|\le C(m+1)\sqrt{\mathcal R(\nu)},
\qquad \int_{\mathbb D}|F|^2\frac{d\mathcal A}{\pi}=\mathcal R(\nu).
\tag{W128}
$$
The area normalization is explicit. For nonzero $\sigma$, the density $|F|^2/\mathcal R(\nu)$ is a probability density bounded by $C(m+1)^2$. The area of $|1+w|<e^{-s}$ in the disc is at most $\pi e^{-2s}$. The logarithmic layer-cake allowance is therefore
$$
\int_{\mathbb D}\log|1+w|\frac{|F|^2}{\mathcal R}\frac{d\mathcal A}{\pi}
\ge-\log(m+1)-C.
$$
Since $\log|1-w|\le\log2$,
$$
\int_{\mathbb D}\Re\operatorname{arctanh}(w)|F(w)|^2\frac{d\mathcal A}{\pi}
\ge-[\tfrac12\log(m+1)+C]\mathcal R(\nu).
\tag{W129}
$$
This uses the standard Bergman moment identity and elementary area bound inside the actual coefficient payment; it is not delivered as a separate generic theorem.

The identity needed for the source coefficient is exact:
$$
\int_{\mathbb D}\Re\operatorname{arctanh}(w)|F(w)|^2\frac{d\mathcal A}{\pi}
=\sum_{n\ge0}(n+1)b_n\int z^n\operatorname{arctanh}(z)\,d\sigma(z).
\tag{W130}
$$
Integrating $w^j$ against $|F|^2\,d\mathcal A/\pi$ gives $\sum(n+1)b_nb_{n+j}$. Sum over positive odd $j$ with coefficient $1/j$. Actual compact support strictly inside $(-1,1)$ gives absolute moment convergence and justifies the identity and logarithmic integral. With $x=A+(u+v)/2$ and
$$
R(z,w)=\frac{(1-z)(1-w)}{(1-zw)^2},
$$
W129--W130 imply the ACTUAL joint lower bound
$$
Q_{xR/A}(\nu)\ge
[1-\tfrac{\log(m+1)}{2A}-C/A]\mathcal R(\nu).
\tag{W131}
$$
No independently selected profile is used. Degenerate zero measures contribute zero; strictness is only claimed for nonzero final measures.

### Identify the whole first coefficient after congruence

Let
$$
S(u,v)=\operatorname{sech}(u-v),\qquad
h_1(c)=\int_0^\infty(c+\cosh t)^{-2}dt.
$$
From the SAME W88 formulas, the normalized expansion has first correction
$$
\mathcal K_A^1=H+\widetilde C_{\rm core}/A+E\mathcal D_{1,A}
 +\sum_{2\le k<N}E^k\mathcal D_{k,A}+\widetilde R_{N,A},
$$
where the EXACT order-one coefficient is
$$
\mathcal D_{1,A}(z,w)=
\frac{\cosh u\cosh v\,e^{-(u+v)}}{4\pi A}
\left[(7x+1)\operatorname{sech}^2(u-v)+h_1(\cosh(u-v))\right].
\tag{W132}
$$
Detailed order check: the direct tau-amplitude has derivative (7x+1)/2 at tau=1; Q/Y²=(Q cosh²(u-v))^-1 supplies E exp[-(u+v)]/(2pi). Its order-one prefactor term is -(r_a+r_b)xS/A. Expanding h_E(z)h_E(w) cancels exactly this piece. The reflected leading prefactor is (1-r_a)(1-r_b), so its order-one prefactor cancels as well, INCLUDING the first-core T/A part. Its next Stieltjes term is -h_1/(2A Q); subtracting the reflected integral gives the positive sign in W132. The special -2c_*exp[-(a+b)]s prefactor starts only at order E². This is exact coefficient algebra from the full paid expansion, not reference PSD.

The direct part of W132 is
$$
\frac7{4\pi}Q_{xR/A}(\nu)+\frac1{4\pi A}\mathcal R(\nu).
$$
Thus it is nonnegative whenever A>=0.5log(m+1)+C, by W131. Do not assume any sign for the h_1 stationary form. The owned W89 stationary comparison and W112 with r=1 give
$$
\left|Q_{\cosh u\cosh v e^{-(u+v)}h_1(\cosh(u-v))}(\nu)\right|
\le C Q_H(e^{-u}\nu)\le C(m+1)Q_H(\nu).
$$
Therefore the WHOLE first correction satisfies
$$
E Q_{\mathcal D_{1,A}}(\nu)\ge-\frac{CE(m+1)}A Q_H(\nu)
\quad\text{if }A\ge\tfrac12\log(m+1)+C.
\tag{W133}
$$
The O(Em) loss has become O(Em/A) by keeping its actual direct sign and the exact prefactor cancellation; no sign of the full reflected source is postulated.

### Higher coefficients and complete all-order remainder survive

Put barB_0=H+tildeC_core/A and barB_j=cosh u cosh v B_{j,A} for j>=1, as owned in W115--W116. On the fixed complex bidisc their direct W88 coefficients have scalar sup bound C^(j+1)j!, uniform A>=A0. Also
$$
h_E(z)h_E(w)=\sum_{p,q\ge0}(c_*E)^{p+q}f_{2p}(z)f_{2q}(w),
\qquad f_r=e^{-r\operatorname{arctanh}z}.
$$
Collect equal E orders; coefficients D_k are independent of N. Their forms obey
$$
|Q_{\mathcal D_{k,A}}(\nu)|\le[C(m+k+2)]^k
 [1+\log(m+k+2)/A]Q_H(\nu)\quad(k\ge2).
\tag{W134}
$$
Here are the joint/bilinear and remainder payments, so multiplication of an asymptotic series is not silently assumed.

- For each original barB_j, use W116, or the owned absolute logarithmic first-core allowance for j=0. A real symmetric form bounded by D Q_H on the same separator cone has bilinear bound3D sqrt(Q_H(sigma)Q_H(tau)) on any sigma=f nu,tau=g nu with f,g>0: sigma+t tau stays in that cone for t>0, and polarization of Q(sigma+t tau), choosing t=||sigma||_H/||tau||_H, yields the constant3. Zero norm cases are trivial by compact moment uniqueness. This does not apply a full-space operator bound or combine independently attainable sequences.
- W112 pays ||f_{2p}nu||_H<=[C(m+p+1)]^p||nu||_H for p>=1; p=0 is identity. Each convolution term has p+q+j=k, so the total polynomial degree is k. The O((k+1)²) cases and c_* powers are absorbed in C^k. Optional logarithms still carry1/A and preserve the same final bound.
- On the fixed complex bidisc, geometric tails of h_E(z)h_E(w) have bound C^(i+1)E^i. Multiplying the N-term original expansion and truncating the product at order N leaves at most E^N C^N sum_{j<N}j! <=C'^N N!E^N. Multiplying the owned R_N by the uniformly bounded h_E factors preserves its complete source bound.

Consequently for EVERY N>=3 at the SAME high start,
$$
\sup|\widetilde R_{N,A}|\le C^NN!e^{-2AN}+Ce^{-c e^{2A}}.
\tag{W135}
$$
Both coefficient kernels and remainder concern the actual full source. The reflected exterior is paid by unchanged W114, not dropped or evenized. The existing Cauchy/moment allowance on this remainder is C Lambda^m times the displayed sup, in the SAME Hardy metric as W133--W134.

### Spend one common start at the square-root scale

Let $L=\log A$ and let $C\ge1$ dominate all fixed bounds. Choose fixed $c_{\rm pref}>0$ sufficiently small, for example $c_{\rm pref}\le1/(64C)$ after increasing $C$ as necessary. Put
$$
M_A=c_{\rm pref}e^{2A}\sqrt{L/A},\qquad
N=\left\lceil D\frac{A+m+1}L\right\rceil,
\quad D\ge6+3\log\Lambda.
$$
For all $0\le m\le\lfloor M_A\rfloor$, one common high $A_*$ ensures
$$
N\ge3,\quad m+N+2\le2M_A,\quad
\log(CN)\le2A-L/3.
\tag{W136}
$$
Indeed the largest N is O(DM_A/L+DA/L), and log(CN)<=2A-L/2-(log L)/2+O(1). Also (m+N+2)/M_A<=1+D/L+o(1). These statements are uniform over the admitted degrees.

Since m+1<=2M_A, the owned sharp first core gives
$$
1-\frac{\log(m+1)}{2A}-\frac CA
\ge\frac{L-\log L-2\log(2c_{\rm pref})-4C}{4A}
\ge\frac{L}{8A}.
\tag{W137}
$$
At the same start, $A-\tfrac12\log(m+1)-C\ge0$, so the direct first coefficient is nonnegative by W131. W133's remaining reflected allowance is at most L/(32A), uniformly in m, because E(m+1)<=2c_pref sqrt(L/A).

For k>=2 set theta=C E(m+N+2)<=2C c_pref sqrt(L/A). The logarithmic factor in W134 is at most4. At one common high start theta<=1/2; hence
$$
\sum_{2\le k<N}E^k |Q_{\mathcal D_{k,A}}(\nu)|/Q_H(\nu)
\le\frac{4\theta^2}{1-\theta}
\le32C^2c_{\rm pref}^2 L/A\le L/(32A).
\tag{W138}
$$
The fixed c_pref choice above is sufficient, with slack.

For the factorial remainder, W136 and log(N!)<=N log N give
$$
\log(\Lambda^m C^NN!e^{-2AN})
\le m\log\Lambda-\tfrac L3 N
\le-2(A+m).
$$
Since m/e^{2A}<=c_pref sqrt(L/A) tends to0, the complete-source error obeys Lambda^m exp(-c exp2A)<=exp(-c exp2A/2). With all fixed factors restored, the sum of the two remainders is at most L/(32A) at the same start.

Combining W137, W133, W138 and W135 yields
$$
Q_{\mathcal K_A^1}(\nu)\ge\frac{\log A}{32A}Q_H(\nu)>0
\quad(A\ge A_*,\ 0\le m\le\lfloor M_A\rfloor,\ \nu\ne0).
\tag{W139}
$$
There is one fixed c_pref and start, not a varying-delta substitution.

### Return to the ORIGINAL Gaussian Hardy metric and actual sample class

For original nu_g, nu_1=(1-r_E)nu_g preserves the same separator. The norm identity and W112 with r=2 give
$$
\|\nu_1-\nu_g\|_H\le CE(m+1)\|\nu_g\|_H=o(1)\|\nu_g\|_H
$$
uniformly in the admitted range. Increase the SAME fixed start until ||nu_1||_H>=||nu_g||_H/2. By exact W127 and W139,
$$
Q_{\mathcal K_A^g}(\nu_g)\ge\frac{\log A}{128A}Q_H(\nu_g)>0
\quad\left(m\le\left\lfloor c_{\rm pref}e^{2A}\sqrt{\log A/A}\right\rfloor,\ \nu_g\ne0\right).
\tag{W140}
$$
Thus both the source and final metric are unchanged. Repeated roots and atoms at roots, arbitrary density and confluence remain in scope. For arbitrary complex coefficients on at most floor M_A+1 distinct sites in the SAME fixed small physical window, apply W140 separately to the real/imaginary transported measures, each with a separator of degree at most one fewer than its site count. Positive diagonal factors and monotone coordinate changes preserve signs and sites. Nonzero moment norm uses the owned compact moment uniqueness.

This is a genuine range enlargement over W118: M_A/[c_deg e2A logA/A] tends to infinity like a fixed constant sqrt(A/logA). The margin's constant is smaller, explicitly stated. It uses exact first-coefficient signs plus the new weighted logarithmic payment, not an improvement of numerical constants in an old absolute allowance.

Conditionally on RH failing, on this SAME fixed small window, beyond all relevant starts combine W140's admitted positive count with W126's upper ceil12 exp2A log(A+1). The minimum local negative-witness site count lies above the new positive count and below that conditional upper; the upper bracket bound divided by the lower is O(sqrt(A logA)). This compares bounds only, gives no actual minimum/optimum or contradiction, and does not establish the smaller sufficient count's positivity.

No larger-rate multiwindow coupling, full sample schedule positivity, all-order fixed-window PSD, original signed prime/Robin upper or operator identification follows. No actual negative seed/sample/zero, numerical start, finite RH test or Lean/CI/merge certification. Full RH and strict Robin for every integer $n>5040$ remain unproved. Classical Bergman/area/moment tools are reused; this is a repository-derived paper application with no literature-priority claim.


## A second signed correction enlarges the actual theta range

On the same fixed small physical window and real polynomial-sign class as W118 and W140, there are fixed $c_{\rm cub}>0$ and one common sufficiently high start such that degrees up to $c_{\rm cub}e^{2A}(\log A/A)^{1/3}$ have lower margin $\log A/(192A)$ in the original Gaussian Hardy metric. This keeps the complete actual theta source and its reflected exterior. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse W88, W89, W110--W112 and W127--W135. Put $E=e^{-2A}$, $u=\operatorname{arctanh}z$, $v=\operatorname{arctanh}w$, $x=A+(u+v)/2$, $c_0=\cosh(u-v)$ and $c_*=3/(2\pi)$. Keep the exact normalized kernel $\mathcal K_A^1$ of W127, and set
$$
f_r(z)=e^{-r\operatorname{arctanh}z},\qquad
\mathcal J_2(z,w)=\frac{(1-z)^2(1-w)^2}{(1-zw)^3},\qquad
\mathcal J_0(z,w)=f_2(z)f_2(w)H(z,w),
$$
$$
h_j(c)=\int_0^\infty(c+\cosh t)^{-j-1}\,dt.
$$
Here $h_0$ is the function $\Psi$ from W88. Constants below depend only on the already fixed window and source bounds, not on the admitted degree or the truncation order.

### The complete second coefficient after the exact normalization

The whole order-two coefficient in the same expansion as W132--W135 is
$$
\begin{aligned}
\mathcal D_{2,A}(z,w)={}&
\frac{35x+12}{16\pi^2A}\mathcal J_2(z,w)
+\frac{c_*x}{\pi A}\mathcal J_0(z,w)\\
&+\frac{\cosh u\cosh v\,e^{-2(u+v)}}A
\left[\frac{c_*}{2\pi}h_0(c_0)-\frac1{4\pi^2}h_2(c_0)\right].
\end{aligned}
\tag{W141}
$$
To identify it from the exact W88 amplitudes, write $\tau=1+t$, $s_a=r_a/(1-r_a)$ and $s_b=r_b/(1-r_b)$. The normalized direct amplitude is
$$
(x+\tfrac12\log\tau)
\left[\tau^{7/2}+(s_a+s_b)t\tau^{5/2}+s_as_b t^2\tau^{3/2}\right].
$$
The main $t^2$ coefficient is $35x/8+3/2$. Integration supplies $2!Q^{-2}c_0^{-3}$, where $Q=2\pi e^{a+b}$, and
$$
\cosh u\cosh v\,e^{-2(u+v)}\operatorname{sech}^3(u-v)=\mathcal J_2(z,w).
$$
This gives the first term of W141. The leading $xt$ term in the second summand uses $s_a+s_b=r_a+r_b+O(E^2)$ and
$$
r_a+r_b=2c_*E e^{-(u+v)}c_0.
$$
Its factor $Q^{-1}c_0^{-2}$ gives $(c_*/\pi)(x/A)\mathcal J_0$. Higher terms from $s_a+s_b$ start at order $E^3$ after integration; $s_as_b t^2$ starts at order $E^4$.

For the reflected integral, the normalized exact prefactor is
$$
1-\frac{2c_*e^{-(a+b)}s}{(1-r_a)(1-r_b)}.
$$
The unmodified Stieltjes term with $j=2$, after subtraction, gives $-h_2/(AQ^2)$. The special $s$ prefactor first contributes at this same order, with positive sign after subtraction, giving $c_*e^{-2(u+v)}h_0/(2\pi A)$. Its denominator correction and higher Stieltjes terms start at order $E^3$. Thus W141 retains both reflected contributions and all normalization terms of order two; it assumes no positivity of a first-mode reference.

### The weighted logarithmic payment for the second direct term

For $\sigma=(1-z)^2\nu$, define
$$
b_n=\int z^n\,d\sigma(z),\qquad
d_n=\binom{n+2}{2},\qquad
\mathcal E_2=Q_{\mathcal J_2}(\nu)=\sum_{n\ge0}d_nb_n^2,\qquad
G(w)=\sum_{n\ge0}d_nb_nw^n.
$$
The positive multiplier preserves the same separator degree, including repeated roots and atoms at roots. Use the probability measure
$$
d\mu_2(w)=2(1-|w|^2)\frac{d\mathcal A(w)}\pi,\qquad
\int_{\mathbb D}|w|^{2n}\,d\mu_2(w)=\frac1{d_n}.
$$
The existing moment-radius bound supplies $\sum q^{2n}b_n^2\le9\Lambda^m Q_H(\sigma)\le9\Lambda^m\mathcal E_2$. Split $\sum d_n|b_n|$ at an integer $J$ proportional to $m+1$. Cauchy--Schwarz bounds its first part by $CJ^{3/2}\sqrt{\mathcal E_2}$, since $\sum_{n<J}d_n\le CJ^3$, and its tail by
$$
C\Lambda^{m/2}(J+1)^2q^{-J}\sqrt{\mathcal E_2}.
$$
Choose the fixed proportionality constant large enough that $\Lambda^{m/2}(J+1)^{1/2}q^{-J}$ stays bounded uniformly for $m\ge0$. Consequently
$$
\int_{\mathbb D}|G|^2\,d\mu_2=\mathcal E_2,\qquad
\sup_{\mathbb D}|G|^2\le C(m+1)^3\mathcal E_2.
\tag{W142}
$$
For $0<\varepsilon\le1$, the region $|1+w|<\varepsilon$ has $\mu_2$-mass at most $4\varepsilon^3$: on it $1-|w|^2\le2\varepsilon$ and its Euclidean area is at most $\pi\varepsilon^2$. For nonzero $\sigma$, the probability bound in the logarithmic layer-cake argument is therefore $\min(1,C(m+1)^3e^{-3s})$. As in W129 this gives
$$
\int_{\mathbb D}\Re\operatorname{arctanh}(w)|G(w)|^2\,d\mu_2(w)
\ge-[\tfrac12\log(m+1)+C]\mathcal E_2.
$$
Indeed $\log|1-w|\le\log2$, while the negative part of $\log|1+w|$ costs at most $\log(m+1)+C$. Orthogonality gives
$$
\int_{\mathbb D}w^j|G(w)|^2\,d\mu_2(w)
=\sum_{n\ge0}d_nb_nb_{n+j}.
$$
Thus the moment identity used in W130 applies with weights $d_n$. Compact real support strictly inside $(-1,1)$ gives absolute convergence. The actual joint lower bound is
$$
Q_{x\mathcal J_2/A}(\nu)\ge
\left[1-\frac{\log(m+1)}{2A}-\frac CA\right]Q_{\mathcal J_2}(\nu).
\tag{W143}
$$
For $\mathcal J_0$, apply the existing W110 Hardy logarithmic allowance directly to $f_2\nu$, with the same separator. It supplies the same bracket times $Q_H(f_2\nu)$, after increasing $C$. Zero measures contribute zero. These classical weighted moments and endpoint-volume bounds are used inside the source-specific second-coefficient payment, rather than introduced as an unused generic criterion.

### Keep both direct signs and pay the reflected parts

If $A\ge\tfrac12\log(m+1)+C$, W143 and the preceding $\mathcal J_0$ allowance make the entire direct part of W141 nonnegative. Its $12\mathcal J_2$ term is also nonnegative. The first direct correction is already nonnegative by W131--W133.

No sign is assigned to the stationary forms involving $h_0$ or $h_2$. The existing W89 comparison bounds each reflected form in W141 by $CQ_H(f_2\nu)$ in absolute value. W112 with $r=2$ pays this by $C(m+1)^2Q_H(\nu)$. Together with W133,
$$
E Q_{\mathcal D_{1,A}}(\nu)+E^2Q_{\mathcal D_{2,A}}(\nu)
\ge-\frac CA\left[E(m+1)+E^2(m+1)^2\right]Q_H(\nu).
$$
Under the same condition $A\ge\tfrac12\log(m+1)+C$, combining this with W111, W134 and W135 gives, for every $N\ge3$ at the same start and every nonzero measure in the stated sign class,
$$
\begin{aligned}
\frac{Q_{\mathcal K_A^1}(\nu)}{Q_H(\nu)}\ge{}&
1-\frac{\log(m+1)}{2A}-\frac CA
-\frac CA\left[E(m+1)+E^2(m+1)^2\right]\\
&-\sum_{3\le k<N}E^k[C(m+k+2)]^k
\left[1+\frac{\log(m+k+2)}A\right]\\
&-C\Lambda^m\left[C^NN!E^N+e^{-c e^{2A}}\right].
\end{aligned}
\tag{W144}
$$
All terms concern the same actual measure. The uniform suppliers W134--W135 hold before the former degree cap is selected; their coefficient, all-$N$ remainder and complete reflected-exterior bounds are reused unchanged.

### One common start for the cube-root range

Put $L=\log A$ and fix $C\ge1$ dominating the preceding bounds. Choose a fixed sufficiently small $c_{\rm cub}>0$, for example $c_{\rm cub}\le1/(64C)$ after increasing $C$, and set
$$
M_A=c_{\rm cub}e^{2A}(L/A)^{1/3},\qquad
N=\left\lceil D\frac{A+m+1}L\right\rceil,\qquad D\ge8+4\log\Lambda.
$$
For all $0\le m\le\lfloor M_A\rfloor$, one common high start ensures
$$
N\ge3,\qquad m+N+2\le2M_A,\qquad
\log(CN)\le2A-L/4.
\tag{W145}
$$
The largest $N$ is $O(DM_A/L+DA/L)$, so $\log(CN)\le2A-L/3-(2/3)\log L+O(1)$, while $(m+N+2)/M_A\le1+D/L+o(1)$. These estimates are uniform over the admitted degrees. Since $m+1\le2M_A$,
$$
1-\frac{\log(m+1)}{2A}-\frac CA
\ge\frac{L-\log L-3\log(2c_{\rm cub})-6C}{6A}
\ge\frac{L}{12A}.
\tag{W146}
$$
In particular both direct-sign thresholds hold. Write $\xi=E(m+1)\le2c_{\rm cub}(L/A)^{1/3}$. At the same start the reflected loss $C(\xi+\xi^2)/A$ is at most $L/(48A)$. For $\vartheta=CE(m+N+2)\le2Cc_{\rm cub}(L/A)^{1/3}$, the logarithmic coefficient factor in W144 is at most $4$ and $\vartheta\le1/2$. Hence
$$
\sum_{3\le k<N}E^k[C(m+k+2)]^k
\left[1+\frac{\log(m+k+2)}A\right]
\le\frac{4\vartheta^3}{1-\vartheta}
\le64C^3c_{\rm cub}^3\frac LA\le\frac{L}{48A}.
$$
For the factorial remainder, W145 gives
$$
\log(\Lambda^m C^NN!e^{-2AN})
\le m\log\Lambda-\tfrac L4N\le-2(A+m).
$$
Also $m/e^{2A}\le c_{\rm cub}(L/A)^{1/3}\to0$, so $\Lambda^m e^{-c e^{2A}}\le e^{-c e^{2A}/2}$ at the same start. With all fixed factors restored, the two remainders together cost at most $L/(48A)$. Inserting the three allowances in W144 yields
$$
Q_{\mathcal K_A^1}(\nu)\ge\frac{\log A}{48A}Q_H(\nu)>0
\quad(A\ge A_*,\ 0\le m\le\lfloor M_A\rfloor,\ \nu\ne0).
\tag{W147}
$$
This uses one fixed constant and common start in the uniform estimate.

### Return to the original metric and actual sample class

Use the exact W127 transport $\nu_1=(1-r_E)\nu_g$ and the existing W140 norm-return argument. W112 with $r=2$ gives
$$
\|\nu_1-\nu_g\|_H\le CE(m+1)\|\nu_g\|_H=o(1)\|\nu_g\|_H
$$
uniformly in the new range. Increase the same fixed start until $Q_H(\nu_1)\ge Q_H(\nu_g)/4$. Equations W127 and W147 then give
$$
Q_{\mathcal K_A^g}(\nu_g)\ge\frac{\log A}{192A}Q_H(\nu_g)>0,
\qquad
0\le m\le\left\lfloor c_{\rm cub}e^{2A}\left(\frac{\log A}{A}\right)^{1/3}\right\rfloor,
\quad A\ge A_*,\quad\nu_g\ne0.
\tag{W148}
$$
Both the complete actual source and the final original Gaussian Hardy metric are unchanged. Repeated roots, atoms at roots, arbitrary density and confluence remain included. For arbitrary complex coefficients on at most $\lfloor M_A\rfloor+1$ distinct sites in this same fixed small physical window, apply W148 to the real and imaginary transported measures, whose separator degrees are at most one fewer than the site count. No internal gap is required. Strictness uses the existing compact moment uniqueness for nonzero measures.

Compared with W140, the admitted degree increases by a factor of order $(A/\log A)^{1/6}$, which tends to infinity; the margin constant is smaller. The additional input is the whole actual second coefficient and its weighted logarithmic payment. The first correction, higher coefficient bounds, complete remainders and norm return are reused.

If RH fails, on this same fixed small window beyond all relevant starts, W126 and W148 put the minimum local negative-witness site count between the new positive count and the conditional upper count $\lceil12e^{2A}\log(A+1)\rceil$. The ratio of these bracket bounds is $O(A^{1/3}(\log A)^{2/3})$. This compares bounds only; it supplies no actual minimum, optimum, contradiction or negative seed/sample. Positivity for the sufficient full count, a larger-rate multiwindow estimate, all-order positivity and the original signed Robin upper remain unproved. No numerical start, effective finite RH test or Lean certification is supplied. Classical weighted moment and logarithmic tools are reused in this repository-derived paper application, with no literature-priority claim. Full RH and strict Robin for every integer $n>5040$ remain unproved.


## Localized filtering gives a smaller actual negative-witness horizon

For each fixed real negative seed of the complete actual theta kernel in $(1,2)$, with total variation one and margin $-\varepsilon<0$, there is a fixed $C_\varepsilon>0$ such that every center $A\ge2$ admits a real negative sample in any fixed window $(A-w,A+w)$ on at most $\lceil C_\varepsilon e^{2A}\rceil$ sites. The count improves W126 by a factor of order $\log A$ for the same fixed seed. Its constant depends on the unknown seed margin; no universal fixed constant is asserted. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse W40, the complete strip bound W101, the exact moving pullback and seed W102, and the real physical reconstruction W105--W106. The additional estimate uses local angular growth and classical localized Jackson filtering. The actual kernel, both direct and reflected terms, and its original quadratic form remain unchanged.

### Local angular control from the complete source

Keep $q_A=(A+1)/A$, $\chi_A(t)=A+q_A^{-1}\operatorname{arctanh}t$ and $F_A(t,s)=\widetilde L_0(\chi_A(t),\chi_A(s))$. For real $a,b\in[1,2]$, write $t_a=\tanh(q_A(a-A))$ and define $t_b$ similarly. Their radii are at most $\tanh A$. Put $K=e^{2A}$ and $\Delta=K(|\theta|+|\phi|)$ for $\theta,\phi\in[-\pi,\pi]$.

For $z=t_ae^{i\theta}$ and $r=|t_a|$, the exact Cayley identity gives
$$
\cos(2\Im\operatorname{arctanh}z)
=\frac{1-r^2}{|1-z^2|}
\ge\frac1{1+2r^2|\sin\theta|/(1-r^2)}
\ge\frac1{1+K|\theta|}.
$$
Here $2r^2/(1-r^2)\le2\sinh^2 A\le K$. Dividing the imaginary part by $q_A\ge1$ increases the cosine. Apply W101 with $\eta$ the larger absolute imaginary part of the two physical arguments, using continuity when $\eta=0$. It follows that
$$
|F_A(t_ae^{i\theta},t_be^{i\phi})|\le D(1+\Delta)^5.
\tag{W149}
$$
This is a local angular bound for the complete kernel, uniform in $A,a,b$ and both angles. It does not spend the larger global bidisc bound $D(A+1)^5$.

Along the same angular curve,
$$
\left|\frac{d}{d\theta}\chi_A(t_ae^{i\theta})\right|
\le\frac{r}{q_A(1-r^2)}\le K.
$$
For $\Delta\le1/8$, the physical arguments stay in a fixed compact neighborhood of $[1,2]$ strictly inside the original holomorphic strip. Its fixed derivative bound gives a Lipschitz allowance $C\Delta$. For $\Delta\ge1/8$, use W149 and $|L_0(a,b)|\le D$. Thus one fixed source constant gives
$$
|F_A(t_ae^{i\theta},t_be^{i\phi})-L_0(a,b)|
\le C(\Delta+\Delta^5).
\tag{W150}
$$
The constants have no dependence on $A$, seed size or margin.

### A classical localized filter and its actual-source consumer

For an integer $N\ge2$, use the normalized eighth-power Jackson kernel
$$
J_N(\theta)=c_N\left|\sum_{j=0}^{N-1}e^{ij\theta}\right|^8,
\qquad \int_{-\pi}^{\pi}J_N(\theta)\frac{d\theta}{2\pi}=1.
$$
It is real, even and nonnegative, of trigonometric degree $d=4(N-1)$. Its standard localization and moment bounds are
$$
J_N(\theta)\le CN(1+N|\theta|)^{-8},\qquad
\int_{-\pi}^{\pi}|\theta|^jJ_N(\theta)\frac{d\theta}{2\pi}
\le C_jN^{-j}\quad(j=1,5).
\tag{W151}
$$
Reuse [D. Leviatan, O. V. Motorna and I. A. Shevchuk, *Fast Decreasing Trigonometric Polynomials and Applications*, J. Fourier Anal. Appl. 30, article 28 (2024), p. 2, equations (1.1)--(1.5)](https://doi.org/10.1007/s00041-024-10080-4), with $n=N$, $\beta=4$ and derivative order $\nu=0$. Their normalization is $\pi^{-1}\int J_{N,4}=1$; the present kernel is $2J_{N,4}$ so that its mass relative to $d\theta/(2\pi)$ is one. The first and fifth moment bounds follow by integrating their pointwise bounds. These classical scalar inputs are reused without a priority claim.

Let $\lambda_p=\int J_N(\theta)e^{ip\theta}\,d\theta/(2\pi)$. Then $\lambda_p$ is real, $|\lambda_p|\le1$, and $\lambda_p=0$ for $|p|>d$. Convolving the actual series $F_A(t,s)=\sum c_{pq}^{(A)}t^ps^q$ in both angular variables gives the finite polynomial
$$
F_{A,N}^{J}(t,s)=\sum_{0\le p,q\le d}
c_{pq}^{(A)}\lambda_p\lambda_qt^ps^q.
$$
Absolute convergence on each seed radius justifies termwise integration. This is a diagonal congruence of the original principal coefficient block. It is not a replacement kernel assumed positive. Integrate W150 against the two probability kernels, using W151 and $(x+y)^5\le16(x^5+y^5)$:
$$
\sup_{a,b\in[1,2]}
|F_{A,N}^{J}(t_a,t_b)-L_0(a,b)|
\le C\left[\frac{e^{2A}}N+\left(\frac{e^{2A}}N\right)^5\right].
\tag{W152}
$$
The local source bound is essential here. A bounded projection norm applied only to $D(A+1)^5$ would not give this estimate.

### A finite filtered block retains an actual negative margin

Fix the real seed W102, with $a_\ell\in(1,2)$, $\sum_\ell|b_\ell|=1$ and actual form $-\varepsilon<0$. Set
$$
\beta_p=\sum_\ell b_\ell t_\ell^p,\qquad
\widehat\beta_p=\lambda_p\beta_p,\qquad n=d+1=4N-3.
$$
Equation W152 gives
$$
Q_{A,N}^{J}=\sum_{p,q<n}c_{pq}^{(A)}\widehat\beta_p\widehat\beta_q,
\qquad |Q_{A,N}^{J}+\varepsilon|
\le C\left[\frac{e^{2A}}N+\left(\frac{e^{2A}}N\right)^5\right].
\tag{W153}
$$
Choose a fixed $B_\varepsilon\ge\max(2,8C/\varepsilon)$ and $N=\lceil B_\varepsilon e^{2A}\rceil$. Then $Q_{A,N}^{J}\le-3\varepsilon/4$ for every $A\ge2$, and
$$
n=4N-3\le(4B_\varepsilon+1)e^{2A}.
\tag{W154}
$$
Only the witness vector has been filtered; the principal matrix is the original actual one. No actual seed or numerical margin has been supplied.

### Real physical reconstruction of the filtered vector

Adapt only the moment input of W105--W106. On real polynomials define
$$
\mathcal T_N(P)=\sum_\ell b_\ell\int_{-\pi}^{\pi}
J_N(\theta)P(t_\ell e^{i\theta})\frac{d\theta}{2\pi}.
$$
Evenness makes this functional real. It satisfies $\mathcal T_N(z^p)=\widehat\beta_p$ and
$$
|\mathcal T_N(P)|\le\sup_{|z|\le r_A}|P(z)|.
$$
The interpolation estimate needs this bound; it does not need positive real support for the functional.

Keep $M_A=D(A+1)^5$, $E_A=(1-r_A)^{-1}$, and any fixed $w>0$. Use exactly W105's positive stencil scale $h$ with this $n$ and $\varepsilon$, real nodes $x_j=jh/(n-1)$, and real Lagrange polynomials $\ell_j$. Set
$$
\alpha_j=\mathcal T_N(\ell_j)
=\sum_{p<n}\lambda_p\beta_p[z^p]\ell_j(z).
$$
These weights are real and match $\widehat\beta_p$ for $p<n$. The same W105 mass bound holds on the complex disc: each numerator factor is at most $1+h\le3/2$, while the real denominators and factorial estimate are unchanged. Thus $\sum_j|\alpha_j|\le(10/h)^{n-1}$. Since $|\widehat\beta_p|\le r_A^p$, the low absolute moment sum is at most $E_A$. The existing high-tail estimate gives
$$
H\le2\,10^{n-1}h\le
\min\left(1,\frac{\varepsilon}{8M_A(E_A+1)}\right).
$$
For the actual physical measure $\nu_A=\sum_j\alpha_j\delta_{\chi_A(x_j)}$, W106's complete coefficient allowance therefore yields
$$
|Q_{L_0}(\nu_A)-Q_{A,N}^{J}|
\le M_A(2E_AH+H^2)\le\varepsilon/4,
\qquad Q_{L_0}(\nu_A)\le-\varepsilon/2<0.
\tag{W155}
$$
Every node lies in $[A,A+w)\subset(A-w,A+w)$ and the site count is at most $n$. Every mixed high coefficient remains paid. Tiny gaps and enormous weights are allowed as in the existing reconstruction; no solver execution or stable finite-precision certificate is asserted.

### The conditional horizon and the remaining positive-range gap

Under RH failure, W40 supplies the fixed seed in $(1,2)$. With $C_\varepsilon=4B_\varepsilon+1$, W154--W155 imply
$$
\begin{gathered}
\mathrm{RH\ false}\ \Longrightarrow\ \exists C_\varepsilon>0\ \forall A\ge2\ \forall w>0:\\
\text{a real negative actual }L_0\text{ sample exists in }(A-w,A+w)
\text{ on at most }\lceil C_\varepsilon e^{2A}\rceil\text{ sites}.
\end{gathered}
\tag{W156}
$$
The sample may depend on $A,w$ and the seed. The constant depends on the seed margin but not on $A$ or $w$; spacing and weights depend on $w$. This reduces the fixed-seed horizon from W126's $O(e^{2A}\log A)$ to $O_\varepsilon(e^{2A})$ without asserting a universal margin or count constant.

For any fixed $w>0$, suppose $A_j\to\infty$ and the actual kernel is PSD for every real sample of at most $n_j$ sites in $(A_j-w,A_j+w)$, with $n_je^{-2A_j}\to\infty$. Then RH follows: if it failed, the one fixed seed would give a fixed $C_\varepsilon$, eventually below $n_je^{-2A_j}$. Thus any predetermined divergent factor $g(A)$ in $n_A=\lceil e^{2A}g(A)\rceil$ gives a sufficient cofinal all-sample positivity schedule. Its positivity is unproved. A fixed universal constant times $e^{2A}$ is not shown sufficient by this argument.

On the same fixed small window as W148, conditional on RH failure and beyond that theorem's common start, the minimum negative-witness count is greater than $\lfloor c_{\rm cub}e^{2A}(\log A/A)^{1/3}\rfloor+1$ and at most $\lceil C_\varepsilon e^{2A}\rceil$. The ratio of these bounds is $O_\varepsilon((A/\log A)^{1/3})$. This improves the preceding bracket comparison by a factor $\log A$, and compares bounds only. It determines neither an actual minimum nor an optimum or contradiction. W148's positive range is unchanged; the sufficient full count, all-order and larger-rate multiwindow positivity, original signed prime/Robin upper and full RH remain unproved. No actual negative seed/sample, numerical negative margin, numerical $C_\varepsilon$ or W148 positive start, effective finite RH test, Lean certification or literature-priority claim is supplied. Classical Jackson localization, the complete-source strip bound and the physical reconstruction are reused; W149--W155 supply their actual-source interface.


## Logarithmic centering pays the actual third theta correction

On the same fixed small physical window and real polynomial-sign class as W148, there are a fixed $c_4>0$ and one common sufficiently high start such that degrees up to $c_4e^{2A}(\log A/A)^{1/4}$ have positive margin $\log A/(256A)$ in the original Gaussian Hardy metric. The additional payment controls an indefinite rank-one term in the actual third coefficient; that term is not assumed nonnegative. The complete actual theta source and its reflected exterior remain. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse W88, W89, W110--W112, W127, W131, W134--W135 and W141--W144. Keep $E=e^{-2A}$, $u=\operatorname{arctanh}z$, $v=\operatorname{arctanh}w$, $x=A+(u+v)/2$, $c_0=\cosh(u-v)$ and $f_r=e^{-r\operatorname{arctanh}z}$. Put
$$
R(z,w)=\frac{(1-z)(1-w)}{(1-zw)^2},\quad
R_2(z,w)=f_2(z)f_2(w)R(z,w),\quad
J_3(z,w)=\frac{(1-z)^3(1-w)^3}{(1-zw)^4},
$$
$$
g(z)=\cosh u\,e^{-3u}=\frac{1-z}{(1+z)^2},\qquad
h_j(c)=\int_0^\infty(c+\cosh t)^{-j-1}\,dt.
$$

### Identify the whole normalized third coefficient

In the same compatible complete-source expansion of $\mathcal K_A^1$, the whole third coefficient is
$$
\begin{aligned}
\mathcal D_{3,A}(z,w)={}&
\frac{105x+71}{64\pi^3A}J_3(z,w)
+\frac{3(2x+1)}{4\pi^3A}R_2(z,w)
+\frac{9x}{2\pi^3A}g(z)g(w)\\
&+\frac{g(z)g(w)}{8\pi^3A}
\left[3h_3(c_0)-6h_1(c_0)+18c_0h_0(c_0)\right].
\end{aligned}
\tag{W157}
$$
Use the normalized W141 amplitude with $\tau=1+t$ and $s_a=r_a/(1-r_a)$. The main cubic coefficient of $(x+\tfrac12\log\tau)\tau^{7/2}$ is $35x/16+71/48$; its factor $3!/(2\pi)^3$ gives the first term of W157. The first $s_a+s_b$ term at Taylor order two contributes $c_*(5x+1)R_2/(2\pi^2A)$. Its second geometric term $r_a^2+r_b^2$, at Taylor order one, contributes
$$
\frac{c_*^2x}{\pi A}[2g(z)g(w)-R_2(z,w)],\qquad c_*=\frac3{2\pi},
$$
using $\cosh(2(u-v))=2c_0^2-1$. Combining these two contributions gives the displayed $R_2$ and rank-one terms. The product $s_as_bt^2$ starts at order $E^4$.

For the reflected part, the unmodified Stieltjes term with $j=3$ contributes $3h_3g(z)g(w)/(8\pi^3A)$ after subtraction. The special $s$ prefactor contributes $-c_*h_1g(z)g(w)/(2\pi^2A)$ through $j=1$, and $c_*^2c_0h_0g(z)g(w)/(\pi A)$ through its first denominator correction $r_a+r_b$. These are all the reflected contributions of order three. The complete-source error is still paid by W135.

### Center the actual scalar rank observable

Write $T=m+1$, $\eta_m=A-\tfrac12\log T$, $a_n=\int z^n\,d\nu$ and $Q=Q_H(\nu)$. The existing actual moment-radius bound gives $\sum q^{2n}a_n^2\le9\Lambda^mQ$. Exact coefficients are
$$
[z^n]g=(-1)^n(2n+1),\qquad
[z^n](ug)=(-1)^n[-(2n+1)S_n+2\lceil n/2\rceil],
\qquad S_n=\sum_{\substack{1\le j\le n\\j\text{ odd}}}\frac1j.
$$
Here $S_0=0$ and $S_n=\tfrac12\log(n+1)+O(1)$. For classical logarithmic coefficient background, see [P. Flajolet and R. Sedgewick, *Analytic Combinatorics* (2009), p. 385, Theorem VI.2, equation (21)](https://algo.inria.fr/flajolet/Publications/book.pdf). The uniform estimate below uses the exact harmonic coefficients, without importing asymptotic uniformity in a moving parameter. Thus the coefficient $v_{T,n}$ of $(u+\tfrac12\log T)g$ obeys
$$
|v_{T,n}|\le C(n+1)[1+|\log((n+1)/T)|].
$$
For $J=\lceil C_0T\rceil$ with fixed sufficiently large $C_0$, the squared coefficient sum for $n<J$ is at most $CT^3$. This uses the integrability of $y^2(1+|\log y|)^2$ near zero. Weighted Cauchy--Schwarz and the same moment tail bound the remaining scalar pairing by
$$
C\Lambda^{m/2}q^{-J}(J+1)
[1+|\log((J+1)/T)|]\sqrt Q\le CT^{3/2}\sqrt Q.
$$
The fixed choice of $C_0$ absorbs the exponential factor uniformly in $m\ge0$. All series pairings converge absolutely on the actual compact support. Consequently the same measure satisfies
$$
V_T=\int(u+\tfrac12\log T)g\,d\nu,
\qquad |V_T|\le CT^{3/2}\sqrt{Q_H(\nu)}.
\tag{W158}
$$
For $G=\int g\,d\nu$ and $\eta_m>0$, the actual troublesome form is exactly
$$
Q_{xgg/A}(\nu)=\frac{\eta_mG^2+GV_T}{A}
\ge-\frac{V_T^2}{4A\eta_m}
\ge-\frac{CT^3}{A\eta_m}Q_H(\nu).
\tag{W159}
$$
This completes a square on jointly realized observables. Bounding $ug$ and $g$ separately would retain an unnecessary logarithmic loss. The rank term itself is not declared positive, and no independently optimized profile is substituted.

### Pay the other direct terms and the full reflected coefficient

Apply W131 directly to $f_2\nu$ to obtain the bracket $1-\log T/(2A)-C/A$ for $xR_2/A$. For $J_3$, the concrete weighted-log input is
$$
\sigma=(1-z)^3\nu,\quad b_n=\int z^n\,d\sigma,\quad
d_n=\binom{n+3}{3},\quad
G_3(w)=\sum_{n\ge0}d_nb_nw^n,\quad
d\mu_3=3(1-|w|^2)^2\frac{d\mathcal A}{\pi}.
$$
The radial moments are $1/d_n$. The same split as W142 gives $\int|G_3|^2d\mu_3=Q_{J_3}(\nu)$ and $\sup|G_3|^2\le CT^4Q_{J_3}(\nu)$, since $\sum_{n<J}d_n=O(J^4)$. Its tail before absorption is $C\Lambda^{m/2}(J+1)^3q^{-J}\sqrt{Q_{J_3}(\nu)}$, absorbed into $CT^2\sqrt{Q_{J_3}(\nu)}$ at $J=\lceil C_0T\rceil$. Endpoint balls $|1+w|<\varepsilon$ have $\mu_3$-mass at most $12\varepsilon^4$. The existing layer-cake argument therefore uses $\min(1,CT^4e^{-4s})$ and retains exactly the coefficient $1/2$ before $\log T$. The same weighted moment identity gives
$$
Q_{xJ_3/A}(\nu)\ge
\left[1-\frac{\log T}{2A}-\frac CA\right]Q_{J_3}(\nu).
\tag{W160}
$$
When $\eta_m\ge C$, both these direct pieces, including their positive constant parts in W157, are nonnegative. The classical weighted-moment mechanism is used inside the actual coefficient payment. No unused generic statement is introduced, and positive multipliers preserve the same separator, including repeated roots and root atoms.

For the reflected terms, W89 bounds the $h_3$ and $h_1$ forms by $CQ_H(f_3\nu)$. Express the $c_0h_0$ term as the average of the $h_0$ stationary bilinear forms on the two actual weighted measures $f_2\nu$ and $f_4\nu$, with the same cosh transports. W89 bounds it by $C\sqrt{Q_H(f_2\nu)Q_H(f_4\nu)}$. W112 with $r=2,3,4$ pays all of these by $CT^3Q$. The whole reflected third loss is therefore at most $CT^3Q/A$; no stationary sign is assumed.

Combining W157--W160 with W144 and the unchanged coefficient and remainder suppliers gives, for every nonzero measure in the stated sign class, every $N\ge4$, $\eta_m\ge C$ and the same high source start,
$$
\begin{aligned}
\frac{Q_{\mathcal K_A^1}(\nu)}Q\ge{}&
1-\frac{\log T}{2A}-\frac CA
-\frac CA[\xi+\xi^2+\xi^3]-\frac{C\xi^3}{A\eta_m}\\
&-\sum_{4\le k<N}E^k[C(m+k+2)]^k
\left[1+\frac{\log(m+k+2)}A\right]\\
&-C\Lambda^m[C^NN!E^N+e^{-c e^{2A}}],\qquad\xi=ET.
\end{aligned}
\tag{W161}
$$
Every term concerns the same actual measure and complete kernel. The uniform suppliers hold before any degree cap is selected.

### One common start at the fourth-root scale

Let $L=\log A$, fix $C\ge1$ dominating the bounds, choose a fixed sufficiently small $c_4>0$, for example $c_4\le1/(64C)$ after increasing $C$, and take $D\ge10+5\log\Lambda$. Set
$$
M_A=c_4e^{2A}(L/A)^{1/4},\qquad
N=\left\lceil D\frac{A+m+1}L\right\rceil.
$$
Uniformly for $0\le m\le\lfloor M_A\rfloor$, one common high start ensures
$$
N\ge4,\quad m+N+2\le2M_A,\quad\log(CN)\le2A-L/5,
\qquad 1-\frac{\log T}{2A}-\frac CA\ge\frac{L}{16A}.
\tag{W162}
$$
The largest $\log(CN)$ is at most $2A-L/4-(3/4)\log L+O(1)$. The core is at least $[L-\log L-4\log(2c_4)-8C]/(8A)$. Thus $\eta_m\ge L/16$ and all direct-sign thresholds hold at the same start.

The reflected and centered-rank allowances in W161 together are at most $L/(64A)$: $\xi\le2c_4(L/A)^{1/4}\to0$ and $\eta_m\ge L/16$. Put $\vartheta=CE(m+N+2)\le2Cc_4(L/A)^{1/4}$. Its logarithmic coefficient factor is at most $4$ and $\vartheta\le1/2$. The remaining coefficient sum is at most
$$
\frac{4\vartheta^4}{1-\vartheta}
\le128C^4c_4^4\frac LA\le\frac{L}{64A}.
$$
For the factorial remainder,
$$
\log(\Lambda^m C^NN!e^{-2AN})
\le m\log\Lambda-(L/5)N\le-2(A+m).
$$
The complete-source remainder obeys $\Lambda^me^{-c e^{2A}}\le e^{-c e^{2A}/2}$ at the same start because $m/e^{2A}\to0$. Both remainders together cost at most $L/(64A)$. Hence
$$
Q_{\mathcal K_A^1}(\nu)\ge\frac{\log A}{64A}Q_H(\nu)>0
\quad(A\ge A_*,\ 0\le m\le\lfloor M_A\rfloor,\ \nu\ne0).
\tag{W163}
$$
Use the exact W127 transport $\nu_1=(1-r_E)\nu_g$ and the existing W140 norm return. Since $CE(m+1)\to0$ uniformly in this new range, the same common start gives $Q_H(\nu_1)\ge Q_H(\nu_g)/4$. Therefore
$$
Q_{\mathcal K_A^g}(\nu_g)\ge\frac{\log A}{256A}Q_H(\nu_g)>0,
\quad 0\le m\le\left\lfloor c_4e^{2A}(\log A/A)^{1/4}\right\rfloor,
\quad A\ge A_*,\quad\nu_g\ne0.
\tag{W164}
$$
The source and final original Gaussian Hardy metric are unchanged. Repeated roots, root atoms, arbitrary density and confluence remain included. Existing real/imaginary splitting admits arbitrary complex coefficients on at most $\lfloor M_A\rfloor+1$ distinct sites in the same fixed small physical window, without an internal gap assumption.

The degree cap increases over W148 by a factor of order $(A/\log A)^{1/12}$, with the stated smaller margin constant. This uses the actual indefinite rank observable and its logarithmic centering; it does not assert that higher direct coefficients are all nonnegative. Under RH failure, on this same fixed small window beyond all positive starts, W156 and W164 give an upper/lower bracket ratio $O_\varepsilon((A/\log A)^{1/4})$ for the minimum negative-witness site count. This compares bounds only and determines neither an actual minimum nor an optimum or contradiction. The sufficient full count, all-order or larger-rate multiwindow positivity, original signed prime/Robin upper and full RH remain unproved. No actual negative seed/sample, numerical negative margin, numerical $C_\varepsilon$ or positive start, effective finite RH test, Lean certification or literature-priority claim is supplied. Classical logarithmic and weighted-moment tools, complete remainders and exact norm transport are reused in this source-specific paper application.


## Complete direct logarithmic control admits a fixed exponential fraction

On the same fixed small physical window and original real polynomial-sign class as W164, there are a fixed $c_{\rm frac}>0$ and one common sufficiently high start such that degree $m\le\lfloor c_{\rm frac}e^{2A}\rfloor$ has lower margin $1/(8A)$ in the original Gaussian Hardy metric. This keeps the complete actual theta source, the reflected exterior and arbitrary confluence. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse W55, W88--W89, W112--W116, W127, W134--W135 and W156--W164. The complete direct integral is kept unexpanded. Its logarithmic observable is controlled by right shifts in an increasing weighted norm, including the correction from its time-dependent amplitude. The scalar logarithm representation is classical: [N. Merhav and I. Sason, *An Integral Representation of the Logarithmic Function with Applications in Information Theory*, Entropy 22(1), Article 51 (2020), author version p. 2, equation (1)](https://arxiv.org/pdf/1912.05812v2), with stated domain $p>0$. That reference supplies the scalar formula; the complete-source estimates below are its paper application, without a literature-priority or Lean-certification claim.

### Keep an exact feature of the whole direct model

Put $E=e^{-2A}$, $\varepsilon=E/\pi$, $T=m+1$, $Q=Q_H(\nu)$ and
$$
p(z)=e^{2u}=\frac{1+z}{1-z},\qquad u=\operatorname{arctanh}z,\qquad
B_E(z)=\left(1-\frac{c_*E}{p(z)}\right)^{-1},\quad c_*=\frac3{2\pi}.
$$
At one fixed high start, $B_E$ is positive on the actual real support and holomorphic and uniformly bounded on the fixed complex disc. For an actual signed measure $\sigma$, define
$$
F_\sigma(t)=\int\frac{p(z)+1}{\sqrt2}e^{-p(z)t}\,d\sigma(z),\qquad t\ge0.
$$
The identity $[(p+1)(q+1)/2]/(p+q)=1/(1-zw)$ gives $\int_0^\infty F_\sigma^2dt=Q_H(\sigma)$. Set
$$
\begin{gathered}
F(t)=F_\nu(t)+\varepsilon tF_{B_E\nu}(t),\qquad
U(t)=F_{u\nu}(t)+\varepsilon tF_{B_Eu\nu}(t),\\
W(t)=(1+\varepsilon t)^{3/2},\qquad
\mathscr S=\int_0^\infty W(t)F(t)^2\,dt.
\end{gathered}
$$
In W88 use $\tau=1+\varepsilon t$ and the exact W127 normalization. Then $Q_{\rm physical}\,d\tau=2\sqrt{pq}\,dt$, $Y(\tau-1)=(p+q)t$, and its normalized amplitude is
$$
\frac{\tau^{7/2}(1-r_a/\tau)(1-r_b/\tau)}{(1-r_a)(1-r_b)}
=\tau^{3/2}[1+\varepsilon tB_E(z)][1+\varepsilon tB_E(w)].
$$
Consequently the entire normalized direct model form is exactly
$$
Q_{{\rm dir},1}(\nu)=\frac1A\int_0^\infty W(t)
\left\{\left[A+\frac12\log(1+\varepsilon t)\right]F(t)^2+F(t)U(t)\right\}dt.
\tag{W165}
$$
The displayed logarithm contributes a nonnegative form. The $FU$ term retains the actual $x=A+(u+v)/2$ cross term. Reflection and the complete-source error are paid separately below; this is not a PSD assertion for a theta truncation.

### Reuse the moment costs before taking a logarithm

W112 with $r=2j$ gives, uniformly for every integer $j\ge1$,
$$
\|p^{-j}\nu\|_H\le
\left[\frac{C(T+j)}j\right]^j\sqrt Q\le(CT)^j\sqrt Q.
$$
Here $(T+j)/j\le T+1\le2T$, so this bound may be summed over all $j$. If $CET\le1/4$, the actual multiplier series for $B_E$ converges in Hardy moment norm and on the compact support, giving
$$
\|B_E\nu\|_H\le C\sqrt Q,\qquad
\|(B_E/p)\nu\|_H\le CT\sqrt Q.
$$
Both positive multipliers preserve the same degree-$m$ separator. Exact time moments are
$$
\int_0^\infty t^{2j}F_\sigma(t)^2dt
=\frac{(2j)!}{2^{2j}}
Q_{(1-z)^{2j}(1-w)^{2j}/(1-zw)^{2j+1}}(\sigma).
$$
For the fixed orders $j=0,1,2$, W113 and the bounded polynomial multiplier therefore yield $\|t^jF_\sigma\|_2\le C_jT^j\|\sigma\|_H$ on the same sign class. Since $1\le W\le(1+\varepsilon t)^2$, these bounds give, for a fixed sufficiently small $\delta>0$ and $ET\le\delta$,
$$
\frac12\sqrt Q\le\sqrt{\mathscr S}\le C\sqrt Q,\qquad
\|F_{(B_E/p)\nu}\|_W\le CT\sqrt Q.
\tag{W166}
$$
The lower bound is a norm comparison: $\|F\|_W\ge\|F_\nu\|_W-\varepsilon\|tF_{B_E\nu}\|_W\ge[1-C\varepsilon T(1+\varepsilon T)]\sqrt Q$, after the fixed geometric multiplier bound. No pointwise ordering of signed Laplace transforms is used.

On the fixed complex disc $|z|\le R$, $\Re p(z)\ge c>0$. Cauchy coefficient pairing with W55, using $Rq=2$, gives the actual tail
$$
|F(t)|\le C\Lambda^{m/2}(1+\varepsilon t)e^{-ct}\sqrt Q.
\tag{W167}
$$
This uses neither a total-variation bound nor a bound on the number or separation of atoms.

### Right shifts pay the complete logarithmic observable

For $p>0$, the classical scalar formula is $\log p=\int_0^\infty(e^{-s}-e^{-ps})\,ds/s$. It gives the exact feature identity
$$
U(t)=\frac12\int_0^\infty\frac{e^{-s}F(t)-F(t+s)}s\,ds
+\frac{\varepsilon}{2}F_{(B_E/p)\nu}(t).
\tag{W168}
$$
The final term is essential: $F(t+s)$ contains $\varepsilon(t+s)F_{B_E\nu}(t+s)$, whereas multiplying the source by $e^{-ps}$ retains $\varepsilon t$. Their difference is $\varepsilon sF_{B_E\nu}(t+s)$, whose integral is $\varepsilon F_{(B_E/p)\nu}(t)$.

Right shifts contract the increasing weighted norm:
$$
\|F(\cdot+s)\|_W^2=\int_s^\infty W(r-s)F(r)^2dr\le\mathscr S.
$$
Thus $\mathscr C(s)=\int_0^\infty W(t)F(t)F(t+s)dt\le\mathscr S$. Equations W166--W167 also imply
$$
\frac{|\mathscr C(s)|}{\mathscr S}\le C\Lambda^{m/2}(1+s)e^{-cs}.
$$
Choose $J=\lceil C_0T\rceil$ with fixed sufficiently large $C_0$. The tail $\int_J^\infty|\mathscr C(s)|\,ds/s$ is at most $C\mathscr S$, uniformly in $m,A$. For $0<s<1$, use $e^{-s}\mathscr S-\mathscr C(s)\ge-s\mathscr S$; for $1\le s\le J$, use $-\mathscr C(s)\ge-\mathscr S$. Therefore the integral in W168, paired with $F$, is at least $-[\tfrac12\log T+C]\mathscr S$. Its correction term costs at most $CET\mathscr S$ by W166, absorbed in a fixed constant. It follows that
$$
\int_0^\infty WFU\,dt\ge-[\tfrac12\log T+C_{\rm dir}]\mathscr S,
\qquad
Q_{{\rm dir},1}(\nu)\ge
\left[1-\frac{\log T}{2A}-\frac{C_{\rm dir}}A\right]\mathscr S.
\tag{W169}
$$
All pairings refer to the same measure. Compact support with $p$ bounded positively gives exponential time decay and the $O(s)$ cancellation at zero needed for Fubini. The sharp coefficient $1/2$ is retained without declaring each asymptotic direct coefficient nonnegative.

### The full reflected integral retains its inverse-size factor

The reflected part of W88, after W127, has no $x$ factor and carries $1/A$ throughout. Keep that factor in the existing W116 and W134--W135 payments. Its compatible expansion and analytic remainder satisfy, for every $N\ge3$,
$$
\begin{gathered}
K_{{\rm ref},1}=\frac1A\sum_{0\le k<N}E^kR_k+R_{{\rm ref},N},\\
|Q_{R_0}(\nu)|\le CQ,\qquad
|Q_{R_k}(\nu)|\le[C(T+k+1)]^kQ\quad(k\ge1),\\
\sup|R_{{\rm ref},N}|\le\frac{C^NN!E^N}A.
\end{gathered}
\tag{W170}
$$
These are the reflected portions of the owned proofs: W89 bounds the stationary $h_j$ bilinear forms, W112's multiplier-order denominators cancel the factorials, and the geometric normalization convolution has total degree $k$. Its polynomially many terms are absorbed in $C^k$. No $x$ or logarithmic observable occurs in that convolution. The old Stieltjes and geometric remainders retain the same $1/A$ and the whole reflected half-line.

Fix $D\ge\log\Lambda+4$ and take $N=\lceil D(T+A)\rceil$. If $c_{\rm frac}>0$ is fixed sufficiently small and $m\le c_{\rm frac}/E$, one common high start ensures
$$
CE(T+N+2)\le\tfrac12,\qquad CEN\le e^{-3},\qquad ET\le\delta.
$$
The coefficient sum in W170 is bounded by a fixed constant times $Q/A$. Its remainder form is at most
$$
\frac CA\Lambda^m(CEN)^NQ
\le\frac CAe^{m\log\Lambda-3N}Q
\le\frac CAe^{-2(A+m)}Q.
$$
Hence, for a fixed $C_{\rm ref}$,
$$
|Q_{{\rm ref},1}(\nu)|\le\frac{C_{\rm ref}}A Q.
\tag{W171}
$$
The complete actual-source comparison from W114, multiplied by the bounded W127 factors, costs at most $C\Lambda^me^{-\kappa/E}Q$. Shrink $c_{\rm frac}$ so $c_{\rm frac}\log\Lambda<\kappa/2$; this error is at most $Q/A$ at the same high start. Every theta mode and the reflected exterior remain paid.

### One fixed fraction and one common start

Choose the same fixed $c_{\rm frac}>0$ small enough for all preceding restrictions and
$$
-\frac12\log(2c_{\rm frac})-C_{\rm dir}\ge4C_{\rm ref}+8.
$$
For all $0\le m\le\lfloor c_{\rm frac}e^{2A}\rfloor$ at one common high start, $T\le2c_{\rm frac}/E$. W169 and $\mathscr S\ge Q/4$ give $Q_{{\rm dir},1}\ge(C_{\rm ref}+2)Q/A$. Subtract W171 and the complete-source error to obtain
$$
Q_{\mathcal K_A^1}(\nu)\ge\frac1A Q_H(\nu)>0\qquad(\nu\ne0).
\tag{W172}
$$
Use the exact W127 transport $\nu_1=(1-r_E)\nu_g$. W112 with $r=2$ gives $\|\nu_1-\nu_g\|_H\le CET\|\nu_g\|_H$. Shrink the fixed $c_{\rm frac}$ again so this is at most half the original norm. Thus $Q_H(\nu_1)\ge Q_H(\nu_g)/4$. In particular, with slack,
$$
Q_{\mathcal K_A^g}(\nu_g)\ge\frac1{8A}Q_H(\nu_g)>0,
\quad A\ge A_*,\quad
0\le m\le\lfloor c_{\rm frac}e^{2A}\rfloor,\quad\nu_g\ne0.
\tag{W173}
$$
The complete source, fixed window, original sign contract and original Gaussian Hardy metric are unchanged. Repeated roots and root atoms, arbitrary density and confluence remain included. The existing real/imaginary split admits arbitrary complex coefficients on at most $\lfloor c_{\rm frac}e^{2A}\rfloor+1$ distinct sites, without an internal gap. Nonzero moment norm uses the owned compact moment uniqueness; the zero measure contributes zero.

The cap exceeds W164 by a factor of order $(A/\log A)^{1/4}$, with the stated smaller margin. Under RH failure, on this same small window beyond all positive starts, W156 and W173 put the minimum negative-witness count strictly above $\lfloor c_{\rm frac}e^{2A}\rfloor+1$ and at most $\lceil C_\varepsilon e^{2A}\rceil$. The ratio of these bracket bounds is $O_\varepsilon(1)$. This compares bounds only; no actual seed, negative margin, numerical count constant, exact minimum or contradiction is supplied. Positivity for the sufficient cofinal count $e^{2A}g(A)$ with $g(A)\to\infty$, all-order PSD, larger-rate multiwindow positivity, the original signed prime/Robin upper and full RH remain unproved. No numerical $c_{\rm frac}$ or start, effective finite RH test, Lean/CI/merge certification or literature-priority claim is supplied. Classical logarithm, shift, moment and complete-source estimates are reused in this source-specific paper application.


## Exact Carleman channels for the whole reflected model

The whole W88 reflected model, with the exact W127 normalization, admits a two-channel identity before any expansion or sign-degree cap. Its first channel is nonnegative; the second is controlled in an explicit inverse-$p$ weighted norm. The model statement allows arbitrary compact finite complex profiles and arbitrary support width. Its consumer for the complete actual theta kernel retains the original local sign class and the full source-comparison error. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse W88, W114, W127 and W165--W173. The classical transform input is [NIST DLMF 10.22.51](https://dlmf.nist.gov/10.22.E51), specialized to Bessel order zero, with its stated conditions $\Re\nu>-1$ and $\Re(p^2)>0$. Its substitutions below have positive real Gaussian parameter and real nonnegative Bessel argument. The bound $|J_0(x)|\le1$ for real $x$ is [DLMF 10.14.1](https://dlmf.nist.gov/10.14.E1). The classical Carleman bound is reused through the [existing weighted Schur criterion](../Fourier/teschl2009mathematical.md#schur-criterion-for-the-local-frequency-kernel), as in the complete adjacent-row estimate T40. These are scalar transform and operator-norm suppliers; the reflected-source interface below is their paper application, without a priority or Lean-certification claim.

### Retain the exact reflected prefactor

Put $E=e^{-2A}$, $\varepsilon=E/\pi$, $c_*=3/(2\pi)$, and
$$
p=e^{2u}=\frac{1+z}{1-z},\qquad
B_E(p)=\left(1-\frac{c_*E}p\right)^{-1},\qquad
M_E(p)=\frac{B_E(p)}p=\frac1{p-c_*E},\qquad
\omega_E=\frac{c_*E^2}\pi.
$$
For the model identity, let $\nu$ be any finite complex measure with compact real $p$-support inside $(c_*E,\infty)$. This keeps the normalization positive and away from its pole. Define, on this same pushed-forward source,
$$
a(p)=\frac{p+1}{\sqrt2},\qquad
F_\sigma(t)=\int a(p)e^{-pt}\,d\sigma(p),\qquad
F_0=F_\nu,\quad F_1=F_{M_E\nu}.
$$
As in W165, $\|F_\sigma\|_2^2=Q_H(\sigma)$. There is no model sign-degree, density, gap or width condition.

In W88 set $\sigma=\mathcal Qs$, where $\mathcal Q=2\pi E^{-1}\sqrt{pq}$ and $c_0=(p+q)/(2\sqrt{pq})$. The entire normalized reflected kernel is exactly
$$
R_A^1(z,w)=\frac{\cosh u\cosh v}{2A}
\int_0^\infty e^{-\sigma}
\Psi\left(c_0+\frac{\varepsilon\sigma}{2\sqrt{pq}}\right)
[1-\omega_E\sigma M_E(p)M_E(q)]\,d\sigma.
\tag{W174}
$$
Indeed the normalized special prefactor is $1-2c_*e^{-(a+b)}s/[(1-r_a)(1-r_b)]$, and $e^{-(a+b)}s=E^2\sigma/(2\pi pq)$. Thus every denominator correction is retained. This is the folded symmetric W88 model obtained after using evenness of the complete source; it is not a literal substitution of the noneven $\Phi_1$ in negative source arguments.

### Transform the complete Stieltjes integral

A variable change $r=\sqrt{pq}e^t$ in the owned integral for $\Psi$ gives, for $p,q>0$ and $d\ge0$,
$$
\Psi\left(\frac{p+q+d}{2\sqrt{pq}}\right)
=\sqrt{pq}\int_0^\infty\frac{\,dr}{(p+r)(q+r)+d\,r}.
$$
DLMF 10.22.51, with $\nu=0$ and the squared Gaussian variable replaced by $\sigma$, gives
$$
\int_0^\infty e^{-\lambda\sigma}J_0(2\sqrt{b\sigma})\,d\sigma
=\lambda^{-1}e^{-b/\lambda},\qquad \lambda>0,\ b\ge0.
$$
It implies the double-Laplace identity
$$
\frac1{ab+k}=\int_0^\infty\int_0^\infty
 e^{-as-bt}J_0(2\sqrt{kst})\,ds\,dt
\quad(a,b>0,\ k\ge0).
$$
Apply this with $a=p+r$, $b=q+r$, $k=\varepsilon\sigma r$. Integrating $\sigma$ with weight $e^{-\sigma}$ gives $e^{-\varepsilon rst}$; the remaining $r$ integral gives the first kernel below. Differentiating the scalar transform once in $\lambda$ at $1$ gives $(1-b)e^{-b}$ for the $\sigma e^{-\sigma}$ weight, and hence the second kernel:
$$
C_\varepsilon(s,t)=\frac1{s+t+\varepsilon st},\qquad
D_\varepsilon(s,t)=\frac{s+t}{(s+t+\varepsilon st)^2}.
\tag{W175}
$$
The latter calculation is $\int_0^\infty e^{-r(s+t+\varepsilon st)}(1-\varepsilon rst)dr=D_\varepsilon(s,t)$.

For $f\in L^2(0,\infty)$ write $\mathscr C_\varepsilon(f)=\iint\overline{f(s)}f(t)C_\varepsilon(s,t)\,dsdt$, and similarly $\mathscr D_\varepsilon$. Since $\cosh u\cosh v\sqrt{pq}/2=a(p)a(q)/4$, the untruncated reflected model form is exactly
$$
Q_{R_A^1}(\nu)=\frac1{4A}
\left[\mathscr C_\varepsilon(F_0)-\omega_E\mathscr D_\varepsilon(F_1)\right].
\tag{W176}
$$
Both features come from the same measure. For finite compact sources the transforms decay exponentially. Using $|J_0|\le1$ before integrating $\sigma$, its two weights have finite integrals, and integration in $r$ gives $1/(s+t)$. This kernel is locally integrable at the corner and integrable against these exponentially decaying features. Thus all exchanges, including the complex sesquilinear pairing, are absolute; no asymptotic series is exchanged with an integral.

### Keep one channel positive and bound the other

The unitary inversion $(\mathcal If)(x)=f(1/x)/x$ on $L^2(0,\infty)$ gives
$$
\mathscr C_\varepsilon(f)=
\int_0^\infty\int_0^\infty
\frac{\overline{\mathcal If(x)}\mathcal If(y)}{x+y+\varepsilon}\,dxdy.
$$
The shifted Carleman kernel on the right is nonnegative as a form, by its positive Laplace representation. Both kernels in W175 are pointwise nonnegative and at most $1/(s+t)$. Direct application of the classical Carleman bound gives
$$
0\le\mathscr C_\varepsilon(f)\le\pi\|f\|_2^2,
\qquad
|\mathscr D_\varepsilon(f)|\le\pi\|f\|_2^2.
\tag{W177}
$$
No nonnegative-form assertion is made for $D_\varepsilon$; its absolute norm is the input. In particular,
$$
-\frac{c_*E^2}{4A}Q_H(M_E\nu)
\le Q_{R_A^1}(\nu)
\le\frac\pi{4A}Q_H(\nu)+\frac{c_*E^2}{4A}Q_H(M_E\nu).
\tag{W178}
$$
These model bounds have no sign-degree or support-width restriction. The positive first channel remains available exactly, rather than being replaced throughout by its maximum norm allowance.

### A two-sided budget for the complete actual local kernel

Return to the fixed small W87/W173 window, the real degree-$m$ sign class and the same high source start. W114 and the bounded W127 normalization give
$$
\left|Q_{\mathcal K_A^1}(\nu)-Q_{{\rm dir},1}(\nu)+Q_{R_A^1}(\nu)\right|
\le C\Lambda^me^{-\kappa/E}Q_H(\nu).
$$
Here $Q_{{\rm dir},1}$ is the exact unexpanded direct model form W165; $\mathcal K_A^1$ retains the complete actual theta source and its reflected exterior. Combining this with W176--W177 yields
$$
\left|Q_{\mathcal K_A^1}(\nu)-Q_{{\rm dir},1}(\nu)
 +\frac1{4A}\mathscr C_\varepsilon(F_\nu)\right|
\le\frac{c_*E^2}{4A}Q_H(M_E\nu)
 +C\Lambda^me^{-\kappa/E}Q_H(\nu).
\tag{W179}
$$
In particular the signed lower budget is
$$
Q_{\mathcal K_A^1}(\nu)\ge Q_{{\rm dir},1}(\nu)
-\frac\pi{4A}Q_H(\nu)-\frac{c_*E^2}{4A}Q_H(M_E\nu)
-C\Lambda^me^{-\kappa/E}Q_H(\nu).
\tag{W180}
$$
This budget holds before selecting a degree cap or a truncation order. It keeps the actual positive channel, the inverse-$p$ response and the complete-source error on one jointly realized measure. The reflected factorial expansion and its truncation are absent from this estimate.

For $E(m+1)$ sufficiently small, the reused W112/W166 multiplier estimate gives $Q_H(M_E\nu)\le C(m+1)^2Q_H(\nu)$. The second debit is then only $C[E(m+1)]^2Q_H(\nu)/A$. Together with W169 this recovers a fixed-fraction schedule of W173's form, with suitable fixed constants and the existing exact metric return. That recovery is reuse, not a further degree-cap result. The added interface is the exact unrestricted model identity and W179's retained actual positive channel.

The arbitrary-width and arbitrary-profile scope belongs to W176--W178 for the model. The actual kernel estimates W179--W180 retain their local sign class and nonzero source-comparison error. They supply neither an unrestricted actual global operator bound nor the sufficient cofinal positivity schedule. No numerical constant/start, actual negative seed, effective finite RH test, Lean/CI/merge certification or literature-priority claim is supplied. RH and strict Robin for every integer $n>5040$ remain unproved.

## The complete direct theta component admits width-free finite samples

There are fixed $c>0$ and $A_*>0$ such that the Gaussian-normalized **direct** kernel has Hardy margin $1/(8A)$ on arbitrary finite complex samples at $a_j\ge A$, provided their number $N\le\lfloor ce^{2A}\rfloor$ and $A\ge A_*$. No upper endpoint or minimum separation is imposed. This statement retains the complete theta source. It concerns the direct $K_0$ component only; it supplies neither a width-free actual reflected comparison nor positivity of the odd difference $L_0$. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse the complete theta series, W87, W127 and W165--W180. The classical model-space conjugation is supplied by [M. C. Câmara and J. R. Partington, *Asymmetric truncated Toeplitz operators and Toeplitz operators with matrix symbol*, J. Operator Theory 77(2) (2017), pp. 456--458, equations (0.1), (1.8) and the isometry statement immediately after (1.8)](https://jot.theta.ro/jot/archive/2017-077-002/2017-077-002-008.pdf), with Hardy exponent $2$. Their upper-half-plane coordinate is changed to the right half-plane by $\zeta=is$. The interior-line contraction and boundary norm are supplied by [J. E. Galé, V. Matache, P. J. Miana and L. Sánchez-Lajusticia, *Hilbertian Hardy-Sobolev spaces on a half-plane*, arXiv:2401.16091v1, p. 2, equation (1.1), and p. 9, opening paragraph of Section 3](https://arxiv.org/pdf/2401.16091v1). These classical inputs are used with the finite-pole parameters below; the source-specific application is not supplied by either reference. Frullani is reused from the primary cited at W168. The additional result is the complete-source direct application on the whole half-line, without a literature-priority or Lean-certification claim.

### Use the actual finite pole set instead of a fixed window

Put $E=e^{-2A}$, $\varepsilon=E/\pi$, $c_*=3/(2\pi)$ and
$$
u_j=a_j-A\ge0,\qquad p_j=e^{2u_j}\ge1,\qquad
z_j=\frac{p_j-1}{p_j+1}\in[0,1).
$$
Equal sites are merged before counting $N$. All coefficients may be complex. Define
$$
F_\sigma(t)=\sum_{j=1}^N\frac{p_j+1}{\sqrt2}\sigma_j e^{-p_jt},
\qquad Q_H(\sigma)=\|F_\sigma\|_2^2.
$$
The isometry is the same identity $[(p+1)(q+1)/2]/(p+q)=1/(1-zw)$ used at W165.

For clarity write $f(s)=\mathcal L F_\sigma(s)$ and
$$
\beta(s)=\prod_{j=1}^N\frac{s-p_j}{s+p_j},\qquad
g(s)=\beta(s)\overline{f(-\overline s)}.
$$
The factors cancel all poles in the right half-plane; $g$ is rational, decays at infinity and has only the possible poles $-p_j$. On the imaginary axis $|\beta|=1$, so $g$ and $f$ have the same $H^2$ boundary norm. On $\Re s=1/2$, $|\beta|\ge3^{-N}$. The classical Hardy interior-line contraction, followed by Plancherel, therefore gives
$$
\|e^{t/2}F_\sigma\|_2\le3^N\|F_\sigma\|_2,\qquad
\|F_\sigma(\cdot+s)\|_2
\le\min(1,3^Ne^{-s/2})\|F_\sigma\|_2.
\tag{W181}
$$
Neither the largest pole nor pole separation enters. With zero coefficients or fewer active poles the same upper bound remains valid.

The tail mass beyond $s$ is at most $\min(1,9^Ne^{-s})\|F_\sigma\|_2^2$. Splitting the time-moment integral at $2N\log3$, and using the ordinary gamma tail, gives for every integer $j\ge1$
$$
\|t^jF_\sigma\|_2\le[C(N+j)]^j\|F_\sigma\|_2.
$$
Also
$$
F_{p^{-j}\sigma}(t)=\frac1{\Gamma(j)}\int_0^\infty s^{j-1}F_\sigma(t+s)\,ds.
$$
Applying W181 and Minkowski, with the same split, yields
$$
\|p^{-j}\sigma\|_H
\le\left[\frac{C(N+j)}j\right]^j\|\sigma\|_H
\le(CN)^j\|\sigma\|_H.
\tag{W182}
$$
All constants are absolute. These are classical finite-pole tools consumed below, rather than a separate generic theorem or a polynomial-sign hypothesis.

Set $Q=Q_H(\nu)$, $B_E=(1-c_*E/p)^{-1}$ and $M_E=B_E/p$. When $EN\le\delta$ for one sufficiently small fixed $\delta$, W182 sums their geometric multiplier series in Hardy norm. Thus
$$
\|B_E\nu\|_H\le C\sqrt Q,\qquad
\|M_E\nu\|_H\le CN\sqrt Q.
\tag{W183}
$$
The series also converge pointwise on the finite support. Fixed-order time moments apply to both weighted measures on the same pole set.

### Keep every theta mode in one exact direct feature

Write $\tau=1+\varepsilon t$ and $S_\ell=\pi(\ell^2-1)/E$. The complete source is
$$
\Phi(x)=\sum_{\ell\ge1}4\pi^2\ell^4
 e^{9x/2-\pi\ell^2e^{2x}}
 (1-c_*\ell^{-2}e^{-2x}).
$$
Define
$$
\begin{aligned}
F_\ell(t)&=\ell^4\tau F_{B_E\nu}(\ell^2t+S_\ell)
-c_*E\ell^2F_{M_E\nu}(\ell^2t+S_\ell),\\
F^\Theta(t)&=\sum_{\ell\ge1}F_\ell(t),\qquad
U^\Theta(t)=F^\Theta_{u\nu}(t),\qquad W(t)=\tau^{3/2}.
\end{aligned}
\tag{W184}
$$
In $U^\Theta$, replacing $\nu$ by $u\nu$ acts in each modal formula. Since $B_E-c_*EM_E=1$, the first mode is exactly $F_1=F_\nu+\varepsilon tF_{B_E\nu}$ from W165.

Let $\mathcal D_A^1$ denote the congruence of the complete actual **direct** kernel
$$
K_0(a,b)=\frac14\int_0^\infty(a+b+2r)\Phi(a+r)\Phi(b+r)\,dr
$$
by $\cosh u\,D_A^1(u)$ from W127; define $\mathcal D_A^g$ using $D_A^g$. Direct substitution of $\tau=e^{2r}$ gives
$$
Q_{\mathcal D_A^1}(\nu)=\frac1A\int_0^\infty W(t)
\left\{\left[A+\frac12\log\tau\right]|F^\Theta(t)|^2
+\Re\bigl(\overline{F^\Theta(t)}U^\Theta(t)\bigr)\right\}dt.
\tag{W185}
$$
The normalization is checked by $d\tau=\varepsilon dt$ and $2e^{u+v}\cosh u\cosh v=(p+1)(q+1)/2$. Extracting the affine amplitude from each complete source ratio leaves $\tau^{3/2}$, as at W165. The denominator uses $\Phi_1$ at the sites, whereas both numerator sources remain complete. There is no theta cutoff or local full-to-model error here. Every direct source argument is positive.

### Pay all higher modes uniformly in the furthest site

Use $\|\cdot\|_W$ for the weighted $L^2$ norm. W182--W183 give $\|F_1\|_W\le C\sqrt Q$ and, by a norm comparison, $\|F_1\|_W\ge3\sqrt Q/4$ after decreasing $\delta$. For each fixed integer $k\ge0$, W181 also gives
$$
\|\tau^kF_\sigma(\ell^2\cdot+S_\ell)\|_2
\le C_k3^N\ell^{-1}e^{-S_\ell/4}\|F_\sigma\|_2,
\qquad \ell\ge2.
\tag{W186}
$$
To see the uniform constants, set $x=\ell^2t+S_\ell$, retain a fixed portion of the exponential decay in W181, and absorb the fixed polynomial $[1+\varepsilon(x-S_\ell)/\ell^2]^k$ in the remaining portion. Only fixed $k\le2$ is needed for W184 and $W$. The factors $\ell^4$, $\ell^2$ and $\log\ell$ are summable against this Gaussian in $\ell$. Since $EN$ is bounded, for some fixed $\kappa>0$,
$$
\left\|\sum_{\ell\ge2}F_\ell\right\|_W
+\left\|\sum_{\ell\ge2}(\log\ell)F_\ell\right\|_W
\le C3^Ne^{-\kappa/E}\sqrt Q.
\tag{W187}
$$
Choose a fixed $c>0$ with $c\log3<\kappa/2$ and $N\le c/E$. At one common high start the modal tail is exponentially small. Therefore
$$
\frac12\sqrt Q\le\sqrt{\mathscr S}:=\|F^\Theta\|_W\le C\sqrt Q.
\tag{W188}
$$
Applying the same decay estimates after an additional right shift gives
$$
\frac{\|F^\Theta(\cdot+s)\|_W}{\sqrt{\mathscr S}}
\le C3^N(1+s)^2e^{-s/4},\qquad s\ge0.
\tag{W189}
$$
For the first mode use W181--W183 and $\tau(t+s)\le(1+\varepsilon s)\tau(t)$; for higher modes retain also $e^{-S_\ell/4}$. Every right shift is additionally a contraction in this increasing weighted norm.

### Retain the arithmetic log-mode charge

Apply the owned scalar Frullani formula with eigenvalue $\ell^2p$ in each mode. The time-dependent affine amplitude and the identity $\tfrac12\log(\ell^2p)=u+\log\ell$ give the exact relation
$$
\begin{aligned}
U^\Theta(t)={}&\frac12\int_0^\infty
\frac{e^{-s}F^\Theta(t)-F^\Theta(t+s)}s\,ds\\
&+\frac\varepsilon2\sum_{\ell\ge1}\ell^2
 F_{M_E\nu}(\ell^2t+S_\ell)
-\sum_{\ell\ge1}(\log\ell)F_\ell(t).
\end{aligned}
\tag{W190}
$$
Both corrections are essential. In the amplitude correction $\tau(t+s)-\tau(t)=\varepsilon s$, and integration of $F_{B_E\nu}(\ell^2t+S_\ell+\ell^2s)$ in $s$ supplies $\ell^{-2}F_{M_E\nu}$; together with $\ell^4$ this leaves $\ell^2$. The last term has the displayed negative sign; $\log1=0$.

For each finite profile all interchanges hold by exponential time decay, absolute modal convergence and the $O(s)$ cancellation at zero. The uniform bound does not estimate $u\nu$ separately; arbitrarily large $u_j$ are handled through W190 before absolute values are taken.

Pair W190 with $F^\Theta$ in $W$, and write $\mathscr C(s)=\int W\overline{F^\Theta(t)}F^\Theta(t+s)dt$. Shift contraction bounds $|\mathscr C(s)|\le\mathscr S$. With $J=\lceil C_0(N+1)\rceil$ and fixed large $C_0$, W189 pays $\int_J^\infty|\mathscr C(s)|ds/s\le C\mathscr S$. On $(0,1)$ use $e^{-s}\mathscr S-\Re\mathscr C(s)\ge-s\mathscr S$; on $(1,J)$ use the lower bound $-\mathscr S$. This retains the coefficient $1/2$ in the logarithmic cost. W182--W183 pay the first modal amplitude correction by $CEN\sqrt Q$ in weighted norm; W186 pays its higher modes and W187 pays the log-mode charge. Thus
$$
\Re\int_0^\infty W\overline{F^\Theta}U^\Theta dt
\ge-\left[\frac12\log(N+1)+C_{\rm dir}\right]\mathscr S.
\tag{W191}
$$
All estimates concern the same actual finite measure.

### A common start for a fixed fraction on the entire half-line

The $\log\tau$ contribution in W185 is nonnegative. Consequently
$$
Q_{\mathcal D_A^1}(\nu)
\ge\left[1-\frac{\log(N+1)}{2A}-\frac{C_{\rm dir}}A\right]\mathscr S.
\tag{W192}
$$
Shrink the same fixed $c$ so that $EN\le\delta$, the preceding modal-tail restriction holds, and $-\tfrac12\log(2c)-C_{\rm dir}\ge4$. For all $1\le N\le\lfloor ce^{2A}\rfloor$ at one common high start, $N+1\le2c/E$. W188--W192 yield $Q_{\mathcal D_A^1}(\nu)\ge Q_H(\nu)/A$.

The exact Gaussian return is $\nu_1=(1-c_*E/p)\nu_g$, with $Q_{\mathcal D_A^g}(\nu_g)=Q_{\mathcal D_A^1}(\nu_1)$. W182 gives $\|\nu_1-\nu_g\|_H\le CEN\|\nu_g\|_H$. Shrink $c$ once more so this is at most half the original norm. With slack,
$$
Q_{\mathcal D_A^g}(\nu_g)\ge\frac1{8A}Q_H(\nu_g)>0,
\quad A\ge A_*,\quad
1\le N\le\lfloor ce^{2A}\rfloor,\quad\nu_g\ne0.
\tag{W193}
$$
Distinct finite exponentials are linearly independent, so the merged nonzero measure has positive Hardy norm. The zero measure contributes zero.

The additional scope is the complete actual **direct** component on arbitrary finite sites in $[A,\infty)$, including complex coefficients, with no local analytic source remainder. The old fixed-window full odd-kernel result W173 is reused unchanged and is not improved here. W176--W177 concern the folded reflected model; they do not supply the missing width-free complete actual reflected comparison. There is no claim about arbitrary infinite measures or derivative distributions, full-real-line $K_0$ positivity, the sufficient cofinal $e^{2A}g(A)$ count, fixed-start all-order positivity, RH, strict all-integer Robin, numerical constants/start, Lean/CI/merge certification or literature priority.

## A sector contour pays the complete reflected source on the half-line

There are fixed $c>0$ and $A_*>0$ such that the complete actual odd kernel $L_0$ has original Gaussian Hardy margin $1/(8A)$ on arbitrary finite complex samples at $a_j\ge A$, when $A\ge A_*$ and their number $N\le\lfloor ce^{2A}\rfloor$. No upper endpoint or minimum separation is imposed. This extends the full-kernel finite-site domain beyond W173's fixed small window. It retains every theta mode and the reflected exterior. The count rate is still a fixed fraction of $e^{2A}$; full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse W174--W193 and their cited classical Hardy, Carleman, Frullani and Cauchy inputs. W75--W77 already give width-independent fixed-order conclusions and explicit growing-order starts; they are not reproved here. The additional ingredient is a complete reflected-source error in a fixed complex sector, paired through the actual finite-pole space. The elementary matrix and contour estimates below are consumed in that actual source comparison, rather than retained as separate generic statements. This is paper mathematics, without a literature-priority or Lean-certification claim.

### Keep both source parameters in one sector

Put $E=e^{-2A}$, $\varepsilon=E/\pi$, $c_*=3/(2\pi)$ and $a(p)=(p+1)/\sqrt2$. On the real physical sites use $u_j=a_j-A\ge0$, $p_j=e^{2u_j}\ge1$, $z_j=(p_j-1)/(p_j+1)$. Equal sites are merged before counting $N$; coefficients may be complex. Keep $Q=Q_H(\nu)=\|F_\nu\|_2^2$ and the exact W127 Gaussian/first-mode normalizations.

Fix $0<\vartheta<\pi/8$, $r_0=1/2$ and the exterior sector $\Omega=\{p:|\arg p|<\vartheta,\ |p|>r_0\}$. Principal logarithms and square roots are used. Boundary estimates follow by first working in a slightly larger fixed sector. For $p,q\in\Omega$ and $\rho\ge0$, let $P_+,P_-$ be the unordered roots of
$$
P^2-(1+\rho)(p+q)P+pq=0.
$$
Write $m=\min(|p|,|q|)$, $M=\max(|p|,|q|)$. Then
$$
|\arg P_\pm|\le\vartheta,\qquad
\frac{m}{2(1+\rho)}\le|P_\pm|\le2(1+\rho)M.
\tag{W194}
$$
Indeed the roots are eigenvalues of $\operatorname{diag}(p,q)B_\rho$, where
$$
B_\rho=\begin{pmatrix}1+\rho&\sqrt{\rho(\rho+2)}\\
\sqrt{\rho(\rho+2)}&1+\rho\end{pmatrix}.
$$
This real positive definite matrix has determinant one and largest eigenvalue at most $2(1+\rho)$. Its product with the diagonal matrix is similar to $B_\rho^{1/2}\operatorname{diag}(p,q)B_\rho^{1/2}$. For an eigenvector the numerical value of that congruence is a nonnegative real combination of $p,q$, placing the eigenvalue in the same sector. The upper modulus bound follows from the operator norm; the product $P_+P_-=pq$ gives the lower one. In particular $\Re P_\pm\ge\cos\vartheta\,m/[2(1+\rho)]$.

### Retain the complete theta multiplier, including its small argument

For $\Re v>0$ define
$$
T_E(v)=\sum_{\ell\ge1}\ell^4e^{-\pi(\ell^2-1)v/E}
 \left(1-\frac{c_*E}{\ell^2v}\right),\qquad
t_E(v)=1-\frac{c_*E}{v}.
$$
The owned complete source gives $\Phi(A+\tfrac12\log v)=\Phi_g(A+\tfrac12\log v)T_E(v)$. On the fixed sector its ordinary Gaussian fourth- and second-moment sums imply
$$
|T_E(v)|\le C\left[1+\left(\frac E{|v|}\right)^{5/2}\right].
\tag{W195}
$$
For $|v|/E\ge1$, split off the first mode and use $\Re v\ge\cos\vartheta|v|$ on the tail. For $|v|/E\le1$, the two Gaussian sums give the displayed power. Thus W195 also handles a negative real physical source coordinate; no evenness is imposed on $\Phi_1$.

Set
$$
\begin{gathered}
c_0=\frac{p+q}{2\sqrt{pq}},\qquad Y=\frac{\pi(p+q)}E,\qquad
\mathrm{den}=t_E(p)t_E(q),\\
\mathcal A_E=\frac{T_E(P_+)T_E(P_-)}{\mathrm{den}},\qquad
\mathcal A_1=\frac{t_E(P_+)t_E(P_-)}{\mathrm{den}}.
\end{gathered}
\tag{W196}
$$
At one high start the denominator is bounded away from zero throughout $\Omega^2$. Symmetric analytic functions of the two roots remain holomorphic at root collisions; neither root reaches zero or a logarithmic cut. The bounds below give locally uniform integral domination.

### An exact contour for the actual reflected component

For real $p,q>r_0$, put $x=A+\tfrac14\log(pq)$ and $d=\tfrac14\log(p/q)$. Complete-source evenness gives $K_0(a,-b)=\tfrac12\int_{|d|}^\infty y\Phi(x+y)\Phi(x-y)dy$. Substitute $\cosh2y=c_0(1+\rho)$, so the exponential source parameters are $P_+,P_-$. Since $y\,dy=\Psi(c)dc/4$, its exact W127-normalized reflected kernel satisfies
$$
\frac{R_A^{\rm act}(p,q)}{a(p)a(q)}
=\frac1{4A\sqrt{pq}}\int_0^\infty
 Y e^{-Y\rho}\Psi(c_0(1+\rho))\mathcal A_E(p,q,\rho)\,d\rho.
\tag{W197}
$$
The raw reflected integral has factor $\Phi_g(a)\Phi_g(b)/8$ in front of its $c$ integral. Multiplying by $\cosh u\cosh v\,D_A^1(u)D_A^1(v)$ and using $dc=c_0d\rho$ gives precisely W197. Here $\Re c_0\ge\cos\vartheta>0$, so the owned branch of $\Psi$ applies.

Replacing $\mathcal A_E$ by $\mathcal A_1$ gives exactly the W174--W178 model, because $P_++P_-=(1+\rho)(p+q)$ and $P_+P_-=pq$ reproduce its entire prefactor. This is the folded model, rather than a raw negative-argument substitution of $\Phi_1$. W194--W196 continue W197 holomorphically to $\Omega^2$; agreement on positive real parameters suffices for the Cauchy application below. As $\rho\to\infty$ one source parameter tends to zero, and W195 retains the complete exterior where $x-y<0$.

### A uniform error controlled by the Loewner logarithm kernel

For $r,s>0$ write
$$
\mathcal L(r,s)=\int_0^\infty\frac{dh}{(r+h)(s+h)}.
$$
Its $L^2(dr)$ operator norm is at most $\pi^2$: it is the square of the classical Carleman operator already used at W177. The Stieltjes identity at W175 gives
$$
\frac{\Psi(c_0(1+\rho))}{\sqrt{pq}}
=\int_0^\infty\frac{dh}{(p+h)(q+h)+(p+q)\rho h},\qquad
\left|\frac{\Psi(c_0(1+\rho))}{\sqrt{pq}}\right|
\le C\mathcal L(|p|,|q|).
\tag{W198}
$$
Every summand in that denominator has argument in the fixed sector of half-angle $2\vartheta<\pi/2$, so taking its real part proves the inequality uniformly in $\rho$.

For $0\le\rho\le1$, W194 bounds both real parts below by $\cos\vartheta\,m/4$. Since $m\ge r_0$, the ordinary higher-mode theta tail yields $|\mathcal A_E-\mathcal A_1|\le Ce^{-\kappa/E}$. All first-mode factors are bounded there. For $\rho\ge1$, W194--W195 instead give the complete bound $|\mathcal A_E-\mathcal A_1|\le C(1+\rho)^5$. Also $\Re Y\ge\cos\vartheta|Y|$ and $|Y|\ge C/E$. Integration against $|Y|e^{-\Re Y\rho}$ pays both the central error and the entire polynomial exterior by $Ce^{-\kappa/E}$, after decreasing $\kappa$. Therefore, with $\Delta_A=R_A^{\rm act}-R_A^1$,
$$
\left|\frac{\Delta_A(p,q)}{a(p)a(q)}\right|
\le\frac CA e^{-\kappa/E}\mathcal L(|p|,|q|),\qquad p,q\in\Omega.
\tag{W199}
$$
The constants do not depend on the largest pole, width or separation.

### Pair the error through the same finite-pole space

Let $\Gamma$ be the positively oriented boundary of $\Omega$, with its two rays and inner arc. For a finite profile set
$$
f_\sigma(s)=\sum_j\frac{a(p_j)\sigma_j}{s+p_j},\qquad
\mathscr R_\sigma(\zeta)=\sum_j\frac{a(p_j)\sigma_j}{\zeta-p_j}=-f_\sigma(-\zeta).
$$
Reuse W181's rational conjugate $g(s)=\beta(s)\overline{f_\sigma(-\bar s)}$, $\beta(s)=\prod_j(s-p_j)/(s+p_j)$, and its boundary Hardy norm $\|g\|_{H^2}^2=Q_H(\sigma)$ in the owned Paley--Wiener normalization. Along either ray $|\beta|\ge\tan(\vartheta/2)^N$; on the inner arc $|\beta|\ge3^{-N}$. With $b=\min(\tan(\vartheta/2),1/3)>0$,
$$
\|\mathscr R_\sigma\|_{L^2(\Gamma)}
\le b^{-N}\|g\|_{L^2(\Gamma)}
\le Cb^{-N}\sqrt{Q_H(\sigma)}.
\tag{W200}
$$
For the last bound write $g=\mathcal LG$ with $\|G\|_2^2=Q_H(\sigma)$. The paired Laplace kernel on a ray is $[e^{i\vartheta}t+e^{-i\vartheta}s]^{-1}$, whose absolute value is at most $[\cos\vartheta(t+s)]^{-1}$. The owned Carleman bound gives $\int_0^\infty|g(re^{i\vartheta})|^2dr\le\pi\sec\vartheta\|G\|_2^2$, and similarly for the other ray. On the finite arc use $|g(\zeta)|\le\|G\|_2/\sqrt{2\Re\zeta}$ and $\Re\zeta\ge r_0\cos\vartheta$.

The kernel $\mathcal L(|\zeta|,|\eta|)$ is bounded on $L^2(\Gamma,|d\zeta|)$. Ray-ray pieces use the $\pi^2$ bound; arc-arc is finite; arc-ray pieces use $\mathcal L(r_0,s)\in L^2([r_0,\infty))$, since it is $O(\log s/s)$ at infinity.

Apply Cauchy in both variables to $\Delta_A(p,q)/(a(p)a(q))$. The two rational factors for the complex pairing are $\mathscr R_{\bar\nu}$ and $\mathscr R_\nu$, with the same Hardy norm. W199--W200 make the resulting double boundary integral absolute. The outer closing arcs vanish: for a fixed second parameter the kernel is $O(\log|\zeta|/|\zeta|)$, whereas the rational factor is $O(1/|\zeta|)$. Constants needed for this limiting justification may depend on the fixed finite profile; the resulting norm bound does not. Iterated Cauchy and Fubini give
$$
|Q_{\Delta_A}(\nu)|
\le\frac CA b^{-2N}e^{-\kappa/E}Q_H(\nu).
\tag{W201}
$$
No coefficient total variation, determinant or gap estimate replaces the Hardy norm.

### Consume the complete reflection in the actual odd kernel

On real $p_j\ge1$, W178 and W183 give $Q_{R_A^1}(\nu)\le[\pi/4+C(EN)^2]Q/A$. Thus the complete actual kernel satisfies
$$
Q_{\mathcal K_A^1}(\nu)\ge Q_{\mathcal D_A^1}(\nu)
-\frac1A\left[\frac\pi4+C(EN)^2+Cb^{-2N}e^{-\kappa/E}\right]Q.
\tag{W202}
$$
The direct component is the complete actual W185/W192 feature, not its first mode. In particular $Q_{\mathcal D_A^1}\ge[A-\tfrac12\log(N+1)-C_{\rm dir}]\mathscr S/A$, with $\mathscr S\ge Q/4$ under the owned small-$EN$ and modal-tail conditions.

Choose fixed $c>0$ small enough for those conditions, $c\log(b^{-2})<\kappa/2$, and a direct coefficient $-\tfrac12\log(2c)-C_{\rm dir}$ larger than four times the fixed reflected budget plus eight. Decreasing $c$ achieves all requirements. For $1\le N\le\lfloor c/E\rfloor$ at one common high start, $N+1\le2c/E$, the error in W201 is exponentially small and $EN$ is small. W202 therefore yields, with fixed slack,
$$
Q_{\mathcal K_A^1}(\nu)\ge\frac1A Q_H(\nu).
\tag{W203}
$$
The exact W127 return is $\nu_1=(1-c_*E/p)\nu_g$. W182 gives $\|\nu_1-\nu_g\|_H\le CEN\|\nu_g\|_H$. Shrink the same $c$ so this is at most half the original norm. With slack,
$$
Q_{\mathcal K_A^g}(\nu_g)\ge\frac1{8A}Q_H(\nu_g)>0,
\quad A\ge A_*,\quad
1\le N\le\lfloor ce^{2A}\rfloor,\quad a_j\ge A,\quad\nu_g\ne0.
\tag{W204}
$$
Distinct finite exponentials are independent, so the merged nonzero measure has positive Hardy norm. The zero measure contributes zero. Every direct/reflected contribution and theta mode is retained on this same source.

W204 supplies the width-free full actual finite-site consumer absent from W173 and W193. It does not enlarge the exponential count rate, extend to arbitrary infinite measures or derivative distributions, or give a common start for all orders. The sufficient cofinal $e^{2A}g(A)$ schedule with $g(A)\to\infty$, full-real-line $K_0$ positivity, RH and strict all-integer Robin remain unproved. No numerical constant/start, actual negative witness, Lean/CI/merge certification or literature priority is supplied. The classical tools and previously accepted estimates are reused; the added content is their complete reflected-source comparison and full-kernel half-line application.

## The half-line estimate counts sign changes rather than support points

The complete actual odd-kernel estimate extends to compact finite signed measures with no bound on their number of atoms or density. There are fixed $c>0,A_*>0$ such that, for every $A\ge A_*$ and separator degree $0\le m\le\lfloor ce^{2A}\rfloor$, the same original Gaussian Hardy margin $1/(8A)$ holds on the half-line $[A,\infty)$. The real measure must have the stated degree-$m$ separator; for a complex measure the condition is imposed separately on its real and imaginary parts. No upper support width or minimum gap is required. The support of each measure is compact, and derivative distributions are excluded. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse W174--W204 and the classical model-space decomposition in [Câmara--Partington, pp. 456--458, equations (0.1), (1.1), (1.8)](https://jot.theta.ro/jot/archive/2017-077-002/2017-077-002-008.pdf), together with the reproducing kernels, Hardy norm and Paley--Wiener normalization from the Galé et al. primary cited at W181. The orthogonal decomposition is classical. The additional interface is its use on the same signed Stieltjes source to replace atom count by separator degree in both the time and sector estimates; its consumer is the complete actual theta form below. W75--W77 and the fixed-window W173 are reused, without a repeated proof or a literature-priority or Lean-certification claim.

### Construct the positive remainder from the same source

Let $\sigma$ be a compactly supported finite real signed measure on $p\ge1$, with
$$
a(p)=\frac{p+1}{\sqrt2},\qquad
F_\sigma(t)=\int a(p)e^{-pt}d\sigma(p),\qquad
f_\sigma(s)=\int\frac{a(p)}{s+p}d\sigma(p).
$$
Keep $Q_H(\sigma)=\|F_\sigma\|_2^2=\|f_\sigma\|_{H^2}^2$ in the owned normalization. Suppose $\epsilon_0\prod_{k=1}^m(p-r_k)\,d\sigma\ge0$ for $r_k\ge1$ and $\epsilon_0\in\{-1,1\}$. Multiplicities and unrestricted signs of atoms at roots are allowed. Define
$$
b(s)=\prod_{k=1}^m\frac{s-r_k}{s+r_k},\qquad
\tau=\epsilon_0b(p)\sigma\ge0.
\tag{W205}
$$
Flipping the global sign leaves every quadratic norm unchanged, so take $\epsilon_0=1$ in the proof. The empty product is one when $m=0$.

For the reproducing kernel $k_p(s)=1/(s+p)$, multiplication by the real inner function $b$ obeys $M_b^*k_p=b(p)k_p$. Passing this bounded operator through the compact Bochner integral gives $f_\tau=M_b^*f_\sigma$. Thus the classical orthogonal decomposition $H^2=K_b\oplus bH^2$ gives
$$
f_\sigma=h+bf_\tau,\qquad h\in K_b,\qquad
\|h\|_{H^2}^2+\|f_\tau\|_{H^2}^2=Q_H(\sigma).
\tag{W206}
$$
The positive measure and the finite-dimensional part are both constructed from $\sigma$.

The function $h$ has poles only at the $-r_k$, with total order at most $m$, even for a continuum source. Indeed
$$
h(s)=\int a(p)\frac{1-b(s)b(p)}{s+p}\,d\sigma(p).
$$
For a nonanchor $p$, $b(-p)b(p)=1$ cancels the possible pole at $-p$; at an anchor the remaining pole is an allowed anchor pole. The common denominator is $\prod_k(s+r_k)$, with numerator degree less than $m$. This retains all root-atom mass. When $m=0$, $h=0$. Multiple poles occur only in this auxiliary model-space function, and do not introduce physical derivative distributions.

### The shifted-line allowance depends only on the separator

Apply the owned model-space conjugation to $h$ with its $m$ anchors counted with multiplicity. The W181 argument gives $\|e^{t/2}H\|_2\le3^m\|H\|_2$ for $H=\operatorname{Lap}^{-1}h$. On $\Re s=-1/2$, $|b(s)|\le3^m$. Positivity of $\tau$ gives the separate bound
$$
\|e^{t/2}F_\tau\|_2^2
=\iint\frac{a(p)a(q)}{p+q-1}\,d\tau(p)d\tau(q)
\le2Q_H(\tau),
$$
since $p,q\ge1$. The identity W206 continues to that line, with all Stieltjes singularities and anchor poles at real part at most $-1$. Triangle inequality followed by the orthogonal norm identity yields
$$
\|e^{t/2}F_\sigma\|_2\le\sqrt3\,3^m\|F_\sigma\|_2,\qquad
\|F_\sigma(\cdot+s)\|_2
\le\min(1,\sqrt3\,3^me^{-s/2})\|F_\sigma\|_2.
\tag{W207}
$$
There is no atom-count, maximum-pole or separation constant.

Put $T=m+1$. Reusing W182's tail integration and right fractional integral gives, for every integer $j\ge1$,
$$
\|t^jF_\sigma\|_2\le[C(T+j)]^j\|\sigma\|_H,\qquad
\|p^{-j}\sigma\|_H
\le\left[\frac{C(T+j)}j\right]^j\|\sigma\|_H
\le(CT)^j\|\sigma\|_H.
\tag{W208}
$$
Every nonnegative multiplier preserves the same separator, so W207 also applies to each weighted measure before its norm is estimated. With $E=e^{-2A}$, $B_E=(1-c_*E/p)^{-1}$ and $M_E=B_E/p$, the geometric series at sufficiently small $ET$ therefore gives
$$
\|B_E\sigma\|_H\le C\|\sigma\|_H,\qquad
\|M_E\sigma\|_H\le CT\|\sigma\|_H.
\tag{W209}
$$
These are the time and multiplier inputs for the unchanged complete source feature.

### Control the sector Cauchy transform without counting its support

Use the same fixed $\Omega,\Gamma,\vartheta,r_0=1/2$ as W194--W201, and define
$$
\mathscr R_\sigma(\zeta)=\int\frac{a(p)}{\zeta-p}d\sigma(p)
=-f_\sigma(-\zeta),\qquad
b_0=\min(\tan(\vartheta/2),1/3)>0.
$$
The model-space part of W206 obeys $\|h(-\cdot)\|_{L^2(\Gamma)}\le Cb_0^{-m}\|h\|_{H^2}$ by W200's conjugation and ray calculation, now with the anchor product. Also $|b(-\zeta)|=|b(\zeta)|^{-1}\le b_0^{-m}$ on $\Gamma$.

For the positive remainder, on either ray $|re^{\pm i\vartheta}-p|\ge\sin(\vartheta/2)(r+p)$, whence $|\mathscr R_\tau(re^{\pm i\vartheta})|\le C_\vartheta f_\tau(r)$. The owned Carleman bound gives $\int_0^\infty|f_\tau(r)|^2dr\le\pi Q_H(\tau)$. On the inner arc,
$$
|\mathscr R_\tau(\zeta)|\le2\int\frac{a(p)}p d\tau(p),\qquad
\left(\int\frac{a(p)}p d\tau(p)\right)^2\le2Q_H(\tau),
$$
using $(p+q)/(pq)\le2$ and positivity. Combining these estimates with the orthogonal identity W206 gives
$$
\|\mathscr R_\sigma\|_{L^2(\Gamma)}
\le Cb_0^{-m}\sqrt{Q_H(\sigma)}.
\tag{W210}
$$
The continuation of W206 to $-\Gamma$ stays outside the negative real Stieltjes cut and the anchor poles. Compact finite sources justify Cauchy and Fubini on finite contours; their total variation is not used in the final norm bound. Finite sign changes are not identified with a finite Nevanlinna negative index.

### Consume the complete direct and reflected estimates on this source

The exact W184--W185 feature and W190 Frullani identity extend to a compact finite measure by normal absolute convergence and finite-measure integration. In W186--W192 replace the finite-site inputs by W207--W209. Their time tails and modal errors now cost $C3^me^{-\kappa/E}$. The amplitude correction and arithmetic log-mode charge remain paid on the same measure. For $T\le c_0/E$ with a sufficiently small fixed $c_0$, this yields
$$
\mathscr S=\|F^\Theta\|_W^2\ge Q/4,\qquad
Q_{\mathcal D_A^1}(\sigma)
\ge\left[1-\frac{\log T}{2A}-\frac{C_{\rm dir}}A\right]\mathscr S,
\qquad Q=Q_H(\sigma).
\tag{W211}
$$
The tail split is $J=\lceil C_0T\rceil$; the change in logarithmic notation only changes the fixed constant. No theta cutoff or uncharged logarithmic observable is introduced.

W199's complete reflected-sector pointwise error had no point-count assumption. Pair it through W210 instead of finite-node W200. The same Carleman-square kernel bounds the double boundary integral absolutely. Outer arcs vanish since a fixed compact Stieltjes source has $\mathscr R_\sigma(\zeta)=O(1/\zeta)$ outside its support and the pointwise error kernel is $O(\log|\zeta|/|\zeta|)$. Thus
$$
|Q_{\Delta_A}(\sigma)|
\le\frac CA b_0^{-2m}e^{-\kappa/E}Q,
\qquad\Delta_A=R_A^{\rm act}-R_A^1.
\tag{W212}
$$
W178 and W209 also give $Q_{R_A^1}(\sigma)\le[\pi/4+C(ET)^2]Q/A$. Consequently the full actual odd kernel satisfies
$$
Q_{\mathcal K_A^1}(\sigma)\ge
\left[1-\frac{\log T}{2A}-\frac{C_{\rm dir}}A\right]\mathscr S
-\frac1A\left[\frac\pi4+C(ET)^2+Cb_0^{-2m}e^{-\kappa/E}\right]Q.
\tag{W213}
$$
Every theta mode, reflected exterior and direct contribution remains on the same source.

### One common start for exponential sign degree on arbitrary compact supports

Choose fixed $c>0$ with $2c\le c_0$, small enough for the preceding moment/modal conditions, for the costs $c\log3$ and $c\log(b_0^{-2})$ to fit within the paid source exponents, and for $-\tfrac12\log(2c)-C_{\rm dir}$ to exceed four times the fixed reflected budget plus eight. At one common high start, $0\le m\le\lfloor ce^{2A}\rfloor$ implies $T=m+1\le2c/E$ and W213 gives $Q_{\mathcal K_A^1}(\sigma)\ge Q_H(\sigma)/A$.

For the exact Gaussian return $\sigma_1=(1-c_*E/p)\sigma_g$, the multiplier is positive and preserves the same separator. W208 gives $\|\sigma_1-\sigma_g\|_H\le CET\|\sigma_g\|_H$. Shrink $c$ once more so this is at most half the original norm. With slack,
$$
Q_{\mathcal K_A^g}(\sigma_g)\ge\frac1{8A}Q_H(\sigma_g)>0,
\qquad A\ge A_*,\quad
0\le m\le\lfloor ce^{2A}\rfloor,\quad\sigma_g\ne0.
\tag{W214}
$$
Strictness uses the owned compact moment uniqueness; the zero measure contributes zero.

In physical coordinates this applies to a real compact finite measure $\mu$ on $[A,\infty)$ satisfying $\epsilon_0\prod_{k=1}^m(a-t_k)\,d\mu\ge0$ with $t_k\ge A$. Use exactly $d\sigma_g=d\mu/(\cosh uD_A^g(u))$ and $p=e^{2u}$. The anchor factor is $b(p)=\prod_k\tanh(a-t_k)$, so the positive transport preserves the separator signs and the exact equality $Q_{L_0}(\mu)=Q_{\mathcal K_A^g}(\sigma_g)$.

For a complex measure, impose this real separator condition separately on its real and imaginary parts, allowing different anchors and global signs and degrees at most the cap. Both actual and Hardy kernels are real symmetric, so their Hermitian quadratic forms are the sums of the two real forms. W214 applies to each; a nonzero complex measure has at least one strictly positive component. This does not define an order on complex coefficients or assert unrestricted complex continuum positivity.

W204 bounded the number of support points. W214 instead permits arbitrarily many atoms and continuum measures at the stated sign degree, on compact supports of arbitrary width and density. W77's width-free start $\exp(Cm^4\log(m+1))$ is not repeated; the new growing-degree schedule is $\lfloor ce^{2A}\rfloor$ at one common start in the same physical separator class and original Gaussian metric. The sufficient cofinal arbitrary-sign complexity $e^{2A}g(A)$ with $g(A)\to\infty$, common-start all-order positivity, RH and the original strict all-integer Robin bound remain unproved. No numerical constant/start, experiment, Lean/CI/merge certification or literature priority is supplied.

## Remote sign separators have a smaller cost in the complete direct theta source

The complete actual direct component admits a pole-sensitive extension of W193 and W211. There are fixed $c>0,A_*>0$ such that its original Gaussian Hardy margin $1/(8A)$ holds for compact finite real signed measures on $[A,\infty)$ with a real-root separator satisfying
$$
\epsilon_0\prod_{k=1}^m(a-t_k)\,d\mu(a)\ge0,
\qquad t_k\ge A,\quad\epsilon_0\in\{-1,1\},\qquad
\Xi_A=1+\sum_{k=1}^m e^{-2(t_k-A)}\le ce^{2A},
\quad A\ge A_*.
\tag{W215}
$$
The number $m$ is finite but has no separate bound. Repeated roots and root atoms are allowed. A complex measure requires this condition separately on its real and imaginary parts, with possibly different roots and global signs. Every measure has compact support; its upper endpoint, density and atom count are unrestricted. This concerns the complete actual direct kernel $K_0(a,b)$ from W185. It does not assert positivity of the full odd difference $L_0$ on this larger class. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse the classical model-space conjugation and Hardy normalization cited at W181, the same-source decomposition W205--W206, and the complete direct feature W184--W191. The orthogonal decomposition and interior-line contraction are classical. The additional content is the position-sensitive cost in that complete-source application, including its arithmetic log-mode charge and exact Gaussian return. There is no separate generic theorem or literature-priority claim.

### Retain the anchor positions in the shifted-line product

Use $p=e^{2(a-A)}\ge1$, $r_k=e^{2(t_k-A)}\ge1$, $E=e^{-2A}$, and the same $a(p)=(p+1)/\sqrt2$, $F_\sigma$, $f_\sigma$ and $Q_H(\sigma)$ as W205. After the harmless global sign, let
$$
b(s)=\prod_{k=1}^m\frac{s-r_k}{s+r_k},\qquad
\tau=b(p)\sigma\ge0,\qquad
f_\sigma=h+bf_\tau,\quad h\in K_b.
$$
The orthogonal norm identity W206 remains exact, including root atoms and repeated anchors. Put $S=\sum_k r_k^{-1}$ and $\Xi=1+S$. For $r\ge1$,
$$
\log\frac{r+1/2}{r-1/2}\le\frac{\log3}{r}.
$$
Indeed the convergent expansion is $2\sum_{j\ge0}(2r)^{-(2j+1)}/(2j+1)$, and multiplication by $r$ leaves a decreasing function of $r\ge1$, with value $\log3$ at one. Consequently
$$
|b(1/2+iy)|\ge3^{-S},\qquad
|b(-1/2+iy)|\le3^S.
$$
Apply the owned conjugation to $h$, retaining these exact anchor factors before the Hardy interior-line contraction. If $H=\operatorname{Lap}^{-1}h$, it gives $\|e^{t/2}H\|_2\le3^S\|H\|_2$. Positivity gives $\|e^{t/2}F_\tau\|_2\le\sqrt2\|F_\tau\|_2$, as in W207. The triangle inequality and orthogonal identity therefore yield
$$
\|e^{t/2}F_\sigma\|_2\le\sqrt3\,3^S\|F_\sigma\|_2,
\qquad
\|F_\sigma(\cdot+s)\|_2
\le\min(1,\sqrt3\,3^Se^{-s/2})\|F_\sigma\|_2.
\tag{W216}
$$
All constants depend on $S$, rather than on the dimension $m$ of the auxiliary model space. For $m=0$, $h=0$, $S=0$, and the same bound holds.

### Pay the complete feature and its arithmetic charge in the same weighted complexity

The W182/W208 tail integration and fractional-integral argument now split at $C\Xi$. For every integer $j\ge1$ they give
$$
\|t^jF_\sigma\|_2\le[C(\Xi+j)]^j\|\sigma\|_H,
\qquad
\|p^{-j}\sigma\|_H
\le\left[\frac{C(\Xi+j)}j\right]^j\|\sigma\|_H
\le(C\Xi)^j\|\sigma\|_H.
\tag{W217}
$$
Every nonnegative multiplier retains the same roots and the same $S$. Thus, for sufficiently small $E\Xi$, the geometric-series argument W183 gives $\|B_E\sigma\|_H\le C\|\sigma\|_H$ and $\|M_E\sigma\|_H\le C\Xi\|\sigma\|_H$.

Keep the complete actual $F^\Theta$, increasing weight $W$, and both corrections in W190 unchanged. W216 replaces $3^N$ in W186--W189 by $\sqrt3\,3^S$. The modal tail and its log-mode charge are bounded by $C3^Se^{-\kappa/E}\sqrt{Q_H(\sigma)}$. Choosing a fixed sufficiently small cap $E\Xi\le c_0$ pays this tail at one common high start, and
$$
\mathscr S=\|F^\Theta\|_W^2\ge Q_H(\sigma)/4.
$$
The complete shifted feature obeys $\|F^\Theta(\cdot+s)\|_W\le C3^S(1+s)^2e^{-s/4}\sqrt{\mathscr S}$, as well as the unchanged shift contraction. In the exact W190 pairing, split its scalar logarithm integral at $J=\lceil C_0\Xi\rceil$. The tail is paid by W216, the interval $[1,J]$ costs $\log\Xi+C$, and W217 pays the amplitude correction. The arithmetic term $-\sum_{\ell\ge1}(\log\ell)F_\ell$ is retained and paid by the same modal tail. Hence
$$
Q_{\mathcal D_A^1}(\sigma)\ge
\left[1-\frac{\log\Xi}{2A}-\frac{C_{\rm dir}}A\right]\mathscr S,
\qquad E\Xi\le c_0.
\tag{W218}
$$
No estimate of the unbounded position multiplier $u\sigma$ is substituted for the joint W190 identity. Compact finite support justifies its integrals exactly as at W211, without using total variation in any final norm bound.

Choose fixed $c>0$ small enough for these modal and multiplier conditions and for $-\tfrac12\log c-C_{\rm dir}\ge8$. Under $\Xi\le c/E$, W218 gives $Q_{\mathcal D_A^1}(\sigma)\ge2Q_H(\sigma)/A$. The exact original Gaussian return is $\sigma_1=(1-c_*E/p)\sigma_g$. This positive multiplier preserves the same weighted separator, and W217 gives $\|\sigma_1-\sigma_g\|_H\le CE\Xi\|\sigma_g\|_H$. Shrink $c$ once more to make this at most half the original norm. With slack,
$$
Q_{\mathcal D_A^g}(\sigma_g)\ge\frac1{8A}Q_H(\sigma_g)>0,
\quad A\ge A_*,\quad\Xi\le ce^{2A},\quad\sigma_g\ne0.
\tag{W219}
$$
The physical transport is the same positive $d\sigma_g=d\mu/(\cosh uD_A^g(u))$ as W214. Since $p=e^{2u}$ is increasing and $b(p)=\prod_k\tanh(a-t_k)$, the separator signs are exactly those in W215. Real symmetric kernels split the complex Hermitian form into its real and imaginary measures, so W219 holds under their separate W215 conditions. The zero measure contributes zero; strictness for a nonzero compact measure uses the owned moment uniqueness.

### The larger direct class is not a change of the lower support endpoint

At a fixed admitted $A$ with $ce^{2A}>2$, retain a positive atom at $a=A$. For arbitrarily large even $m$, choose $R$ so large that $m/R\le ce^{2A}-1$, take $m$ distinct separator roots in $[R,2R]$, and place alternating-sign atoms in the $m+1$ complementary intervals of that block. Their signs can be chosen so that $\prod_k(p-r_k)\,d\sigma\ge0$, including the retained atom at $p=1$. Then $\Xi\le1+m/R\le ce^{2A}$. There are $m$ actual sign changes, so no smaller-degree polynomial separates these alternating atoms. The lower support endpoint is still $A$, and $m$ has no bound as $R$ grows. Thus neither the old global $m\le ce^{2A}$ contract nor moving the entire support to a higher start supplies this fixed-$A$ direct conclusion. This is an admissible family construction, not an executed numerical experiment.

For the complete actual odd kernel, the W212 reflected-source estimate still contains $b_0^{-2m}$. W215 controls $\sum_k r_k^{-1}$ and does not control that factor. No reciprocal-root replacement for the actual reflected error is established here. The new complete-direct estimate, the old full odd-kernel estimate W214, and their different source classes must remain distinct. There is no full odd-kernel positivity claim on W215, unrestricted sign or unbounded-support theorem, sufficient cofinal positivity, numerical constant/start, Lean certification or literature-priority claim. Full RH and the original strict all-integer Robin bound remain unproved.

## Pairing the logarithmic theta dilations pays the complete reflection

The complete actual reflected error admits a uniform bound in an exponentially weighted norm of the same source, without a support-count or sign condition. Its consumer extends the full odd-kernel conclusion W214 to the position-weighted separator class W215. There are fixed $c>0,A_*>0$ such that every compact finite real signed measure on $[A,\infty)$ satisfying W215, with $A\ge A_*$ and $\Xi_A\le ce^{2A}$, has original Gaussian Hardy margin $1/(8A)$ for the complete actual $L_0$. Complex measures require the separator condition separately on their real and imaginary parts. No upper support endpoint, atom-count or internal-gap restriction is added. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse the exact complete theta series, folded model W174--W178, direct feature W184--W191, source decomposition W205--W206, and position-sensitive shifts and Gaussian return W215--W219. The classical Hardy and Carleman suppliers are unchanged. The additional interface pairs the two exchanged logarithmic modes before bounding their finite-interval correction. It does not replace the old sector Cauchy norm by a reciprocal-root bound, or assert that the noneven first-mode source is even. This is paper mathematics, without a Lean-certification or literature-priority claim.

### Keep every finite modal push-forward on the same source

Write $\phi=\Phi_1$, $E=e^{-2A}$, $\varepsilon=E/\pi$, $c_*=3/(2\pi)$, $p=e^{2(a-A)}\ge1$, and $a(p)=(p+1)/\sqrt2$. Keep $B_E=(1-c_*E/p)^{-1}$, $M_E=(p-c_*E)^{-1}$ and the first-mode normalization
$$
w_A(a)=\cosh(a-A)D_A^1(a-A),\qquad
w_A(a)\phi(a)=C_Aa(p),\qquad C_A^2=\frac{4\pi}{AE}.
$$
For a compact finite complex measure $\sigma$ on $p\ge1$, let $d\mu(a)=w_A(a)d\sigma(p)$. The complete source identity is
$$
\Phi(x)=\sum_{\ell\ge1}\ell^{-1/2}\phi(x+\log\ell),\qquad x\in\mathbb R.
$$
For a finite cutoff $L$, push $\ell^{-1/2}\mu$ forward by $a\mapsto a+\log\ell$, and divide there by $w_A$. Call the resulting normalized measure $\sigma_\ell$, and put $\sigma_{\le L}=\sum_{\ell\le L}\sigma_\ell$. Its new parameter is $p'=\ell^2p$. With $S_\ell=\pi(\ell^2-1)/E$, direct substitution gives
$$
\begin{aligned}
F_{\sigma_\ell}(t)
&=\ell^4F_{B_E\sigma}(\ell^2t+S_\ell)
 -c_*E\ell^2F_{M_E\sigma}(\ell^2t+S_\ell),\\
F_{M_E\sigma_\ell}(t)
&=\ell^2F_{M_E\sigma}(\ell^2t+S_\ell),\qquad \sigma_1=\sigma.
\end{aligned}
\tag{W220}
$$
Indeed the pushed mass satisfies
$a(p')d\sigma_\ell(p')=a(p)\ell^4e^{-S_\ell p}(1-c_*E/(\ell^2p))B_E(p)d\sigma(p)$.
Every finite push-forward is a compact finite measure. No finite total-variation claim is made for the infinite unnormalized physical sum $\sum\ell^{-1/2}T_{\log\ell}\mu$; only the normalized feature limits below are used.

### Pair the two exchanged modes before taking absolute values

For any source function $\varphi$, define its folded reflection by
$$
R_\varphi^{\rm fold}(a,b)=\frac12\int_{|(a-b)/2|}^\infty
y\varphi((a+b)/2+y)\varphi((a+b)/2-y)\,dy.
$$
For the complete even $\Phi$ this is the actual reflected component. For $\phi$, it is precisely the owned folded model, rather than a claim about an even extension of $\phi$.

Let $\ell<k$, $H_{\ell k}=\tfrac12\log(k/\ell)>0$, $d=(a-b)/2$ and $z=(a+b)/2+\tfrac12\log(\ell k)$. Pair the $(\ell,k)$ and $(k,\ell)$ products in the finite source expansion. Their sum is even in the original integration variable $y$, so its weighted integral can start at the signed $d$. Opposite changes of variables turn the new integrands into $g(v)=\phi(z+v)\phi(z-v)$, which is even regardless of whether $\phi$ is even. Thus the paired raw contribution, before the coefficient $(\ell k)^{-1/2}$, is
$$
\begin{aligned}
&R_\phi^{\rm fold}(a+\log\ell,b+\log k)
 +R_\phi^{\rm fold}(a+\log k,b+\log\ell)\\
&\hspace{8mm}+\frac{H_{\ell k}}2\int_\ell^k
 \phi(a+\log s)\phi(b+\log(\ell k/s))\frac{ds}s.
\end{aligned}
\tag{W221}
$$
To check the correction, the two shifted integrals have weights $v-H$ and $v+H$ and lower limits $d+H$ and $d-H$. Their difference of unweighted tails is $H\int_{d-H}^{d+H}g(v)dv$; the original factor $1/2$ is retained. On this finite interval both physical arguments are at least $\min(a,b)+\log\ell\ge A$.

Put $G_s=\int\phi(a+\log s)d\mu(a)$. If $R_{A,L}^{\rm act}$ denotes the same folded integral with the finite theta sum, W221 gives the exact finite identity
$$
Q_{R_{A,L}^{\rm act}}(\sigma)
=Q_{R_A^1}(\sigma_{\le L})
 +\sum_{\ell<k\le L}\frac{H_{\ell k}}{2\sqrt{\ell k}}
 \int_\ell^k\overline{G_s}G_{\ell k/s}\frac{ds}s.
\tag{W222}
$$
The finite-interval integral is real, since $s\mapsto\ell k/s$ preserves $ds/s$ and exchanges the two factors. It is bounded in absolute value below; no positive-form assertion for this correction is needed.

### The modal norm limits require no sign separator

For the original compact source define $Q_+=\|e^{t/2}F_\sigma\|_2^2$. This is finite because $p\ge1$. In this norm a right shift contracts by $e^{-s/2}$. The owned right-integral formula for $p^{-j}$ therefore gives norm at most $2^j$, without a sign condition. For sufficiently small fixed $E$, the geometric series yields
$\|e^{t/2}F_{B_E\sigma}\|_2+\|e^{t/2}F_{M_E\sigma}\|_2\le C\sqrt{Q_+}$.
Changing variables in W220 now gives
$$
\|\sigma_\ell\|_H\le C\ell^3e^{-S_\ell/2}\sqrt{Q_+},\qquad
\|M_E\sigma_\ell\|_H\le C\ell e^{-S_\ell/2}\sqrt{Q_+}.
\tag{W223}
$$
In particular the feature sums converge in $L^2$, and their differences from $F_\sigma,F_{M_E\sigma}$ are at most $Ce^{-\kappa_0/E}\sqrt{Q_+}$ for some fixed $\kappa_0>0$. Applying the two bounded model operators W176--W178 to the finite sums and passing to their norm limits gives
$|\lim_LQ_{R_A^1}(\sigma_{\le L})-Q_{R_A^1}(\sigma)|\le Ce^{-\kappa_0/E}Q_+/A$.
The model's second channel is still used only in absolute norm.

### The finite interval keeps the joint Gaussian time gap

For $s\ge1$ set $S_s=\pi(s^2-1)/E$ and
$$
V(t)=F_{B_E\sigma}(t)-\frac{c_*E}{1+\varepsilon t}F_{M_E\sigma}(t).
$$
The same-source normalization above gives exactly
$$
G_s=C_As^{9/2}V(S_s),\qquad
\|e^{t/2}V\|_2^2\le CQ_+.
\tag{W224}
$$
For every $s\in[\ell,k]$,
$$
S_s+S_{\ell k/s}\ge\frac{2\pi(\ell k-1)}E.
$$
Keep this joint damping before taking absolute values. With $V_+(t)=e^{t/2}V(t)$, Cauchy--Schwarz and the measure-preserving involution $s\mapsto\ell k/s$ give
$$
\begin{aligned}
\left|\int_\ell^k\overline{V(S_s)}V(S_{\ell k/s})\frac{ds}s\right|
&\le e^{-\pi(\ell k-1)/E}
 \int_\ell^k|V_+(S_s)|^2\frac{ds}s\\
&\le\frac{E}{2\pi\ell^2}e^{-\pi(\ell k-1)/E}\|V_+\|_2^2.
\end{aligned}
\tag{W225}
$$
Here $ds/s=E\,dS_s/(2\pi s^2)$. In W222 the powers from W224 combine to $(\ell k)^4$ after its $(\ell k)^{-1/2}$ coefficient. Since $C_A^2=4\pi/(AE)$, the absolute value of that pair's correction is at most
$C H_{\ell k}(\ell k)^4\ell^{-2}e^{-\pi(\ell k-1)/E}Q_+/A$.
The full double sum is at most $Ce^{-\kappa_1/E}Q_+/A$ for a fixed $\kappa_1>0$, since $\ell k\ge2$ and the remaining factors grow polynomially with a logarithm.

For each fixed compact physical source, the complete modal expansion may also be passed through the folded integral. The absolute Gaussian fourth- and second-moment sums used at W195 control the small argument by a fixed power of its inverse; the other source argument tends to $+\infty$ and has double exponential decay. This is an integrable bound uniform on the compact pair of source sites. Finite total variation then justifies the limit of W222. These domination constants justify the identity only; they do not enter the uniform final norm estimate.

Consequently the complete actual error, including all mixed modes and the full small-argument exterior, satisfies
$$
|Q_{\Delta_A}(\sigma)|
\le\frac CAe^{-\kappa/E}Q_+,
\qquad \Delta_A=R_A^{\rm act}-R_A^1,
\quad Q_+=\|e^{t/2}F_\sigma\|_2^2.
\tag{W226}
$$
This bound holds for every compact finite complex measure on $p\ge1$ at one common high start, without a separator, count, width or gap condition. It is a weighted-norm comparison; it does not give an unrestricted comparison in $Q_H$.

### Consume the complete reflection at reciprocal separator cost

Return to a real signed source with the W215 separator, $S=\sum r_k^{-1}$ and $\Xi=1+S$. W216 gives $Q_+\le3\cdot9^SQ_H(\sigma)$. W217 and W178 bound the folded model above by $[\pi/4+C(E\Xi)^2]Q_H(\sigma)/A$. Combining W226 with the complete actual direct lower W218, on the same measure and with $\mathscr S\ge Q_H(\sigma)/4$, gives
$$
\begin{aligned}
Q_{\mathcal K_A^1}(\sigma)\ge{}&
\left[1-\frac{\log\Xi}{2A}-\frac{C_{\rm dir}}A\right]\mathscr S\\
&-\frac1A\left[\frac\pi4+C(E\Xi)^2
 +Ce^{-\kappa/E+2(\log3)S}\right]Q_H(\sigma).
\end{aligned}
\tag{W227}
$$
Choose fixed $c>0$ sufficiently small for the existing direct/modal conditions, for $2c\log3<\kappa/2$, and for $-\tfrac12\log c-C_{\rm dir}$ to exceed four times the fixed reflected budget plus eight. At one common high start, $\Xi\le c/E$ then gives $Q_{\mathcal K_A^1}(\sigma)\ge Q_H(\sigma)/A$.

The exact positive Gaussian return $\sigma_1=(1-c_*E/p)\sigma_g$ retains the same separator and reciprocal mass. W217 gives $\|\sigma_1-\sigma_g\|_H\le CE\Xi\|\sigma_g\|_H$. Shrink $c$ once more to make this at most half the original norm. With slack,
$$
Q_{\mathcal K_A^g}(\sigma_g)\ge\frac1{8A}Q_H(\sigma_g)>0,
\qquad A\ge A_*,\quad\Xi\le ce^{2A},\quad\sigma_g\ne0.
\tag{W228}
$$
The original physical transport and separator signs are exactly those in W215/W219, with $\Xi=\Xi_A$. Both kernels are real symmetric, so the separate real/imaginary contracts give the same Hermitian bound for a complex measure. Nonzero compact moment uniqueness supplies strictness; the zero measure contributes zero.

This pays the actual reflection missing from W219 and extends W214 from total separator degree to reciprocal separator mass. The fixed-low-support, arbitrarily-many-remote-sign-changes family described after W219 remains admitted for the smaller fixed $c$ once the common start is high enough. The proof keeps all theta modes and exterior terms jointly; it does not contradict the failure of a reciprocal-mass bound for the unrestricted old sector Cauchy norm. At each fixed compact window the weighted cap still restricts the number of local changes. Sufficient cofinal arbitrary-sign positivity, common-start all-order positivity, RH and the original strict all-integer Robin bound remain unproved. No unbounded-support physical source, derivative distribution, numerical constant/start, Lean/CI/merge certification or literature priority is supplied.


## The folded first-mode model has negative local samples at exponential order

There are fixed $C,A_*>0$ such that, for every $A\ge A_*$ and every $w>0$, one finite real source $\mu$ on at most $\lceil Ce^{2A}\rceil$ distinct sites in $[A,A+w)$ satisfies
$$
Q_{D_\phi}(\mu)<0,\qquad
Q_{D_\phi-R_\phi^{\rm fold}}(\mu)<0,
\qquad \phi=\Phi_1.
\tag{W229}
$$
Here $D_\phi$ is the first-mode direct kernel obtained by replacing both sources in W185 by $\phi$, and $R_\phi^{\rm fold}$ is exactly the folded model in W221. The first mode is not even. This is a statement about that model, not a negative sample of the complete actual theta kernel. The full-source result W228 is unchanged. Full RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse the scalar Frullani formula at W168/W190, the complete folded model and its absolute operator bounds W176--W177, and the classical quarter-Gamma multiplier already used in the [actual Weil normalization](frankliebseiringer2006hardy.md#common-test-and-normalization). The weighted approximation reuses [B. R. Draganov, *Strong converse inequalities for the weighted simultaneous approximation by the Szász--Mirakjan operator*, Serdica Math. J. 46 (2020), 261--286, pp.261--262, operator definition, weight (1.1) and the unnumbered direct estimate attributed there to [8, Theorem 1.2]](https://serdica.math.bas.bg/index.php/serdica/article/download/188/110/362). That direct supplier is Draganov, *Direct estimates of the weighted simultaneous approximation by the Szász--Mirakjan operator*, Period. Math. Hungar. 83 (2021), 88--109, [DOI 10.1007/s10998-020-00370-x](https://doi.org/10.1007/s10998-020-00370-x). The additional interface keeps the first-mode polynomial and logarithm commutator, pays the whole folded reflection, and transports one smooth negative profile to finite real sources with the count in W229. No new general Gamma, approximation or Carleman theorem, Lean certification or literature priority is claimed.

### Keep the physical feature and its logarithm in the correct order

For a finite physical source, put $p_j=e^{2a_j}$ and
$$
F(x)=\sum_j\mu_j e^{9a_j/2}e^{-p_jx},\qquad
(IF)(x)=\int_x^\infty F(y)dy,\qquad
(LF)(x)=\sum_j(\log p_j)\mu_j e^{9a_j/2}e^{-p_jx}.
$$
The owned Frullani formula writes $LF=\int_0^\infty(e^{-s}F-F(\cdot+s))ds/s$. Use it also to define $L$ on the smooth decaying profiles below. Set $BF=F-3IF/(2x)$. With $x=\pi e^{2r}$, the first-mode feature is $4\pi^2(x/\pi)^{9/4}BF(x)$. Multiplication of the original source by $a=(\log p)/2$ gives $BLF/2$, rather than $LBF/2$. Direct substitution therefore gives the exact physical form
$$
\mathcal D_\pi(F)=\frac2{\sqrt\pi}\int_\pi^\infty x^{7/2}
\left[\log(x/\pi)|BF|^2+
\Re\bigl(\overline{BF}\,BLF\bigr)\right]dx
=Q_{D_\phi}(\mu).
\tag{W230}
$$

### The homogeneous feature has the existing negative Gamma baseline

Let $\mathcal D_0$ be W230 with lower limit zero. For real $F\in C_c^\infty(0,\infty)$, put $g(u)=e^{9u/4}F(e^u)$ and use the unitary Fourier convention $g(u)=(2\pi)^{-1/2}\int\widehat g(\xi)e^{-i\xi u}d\xi$. Write
$$
z=\frac94+i\xi,\qquad
h(z)=1-\frac3{2(z-1)}=\frac{z-5/2}{z-1}.
$$
Right integration and the classical [digamma integral](https://dlmf.nist.gov/5.9.E16), with the owned Frullani formula, give
$I x^{-z}=x^{1-z}/(z-1)$ and $Lx^{-z}=(\operatorname{digamma}(z)-\log x)x^{-z}$. Consequently
$$
BLx^{-z}=\left[h(z)(\operatorname{digamma}(z)-\log x)+h'(z)\right]x^{-z}.
$$
The $h'$ term is retained. Digamma recurrence gives
$$
\operatorname{digamma}(z)+\frac{h'(z)}{h(z)}
=\operatorname{digamma}(z-2)+\frac1{z-2}+\frac1{z-5/2}.
$$
The last two reciprocals have zero real sum on this line. Mellin Plancherel yields
$$
\mathcal D_0(F)=\frac2{\sqrt\pi}\int_{\mathbb R}
|\widehat g(\xi)|^2|h(9/4+i\xi)|^2
\left[\Re\operatorname{digamma}(1/4+i\xi)-\log\pi\right]d\xi.
\tag{W231}
$$
Compact logarithmic support gives rapidly decaying Fourier coefficients. The right-integral tails at zero, multiplied by $x^{7/2}$, are integrable; the digamma multiplier grows only logarithmically. Truncation and Plancherel thus justify this identity on the displayed profile class. It reuses the quarter-Gamma multiplier at Fourier frequency $2\xi$. At zero its value is $[\operatorname{digamma}(1/4)-\log\pi]/25<0$. For nonzero real $\eta\in C_c^\infty(\mathbb R)$, take $g_T(u)=T^{-1/2}\eta(u/T)$. Its Fourier mass concentrates at zero, so one fixed sufficiently large $T$ gives a real compact smooth $F$ with $\mathcal D_0(F)<0$.

### Pay the cutoff and the whole folded reflection

Put $F_R(x)=R^{-9/4}F(x/R)$. Its homogeneous form is unchanged: the $-\log R$ in $L$ cancels the scale term in $\log x$. In W230 the lower limit becomes $\pi/R$, whence $\mathcal D_\pi(F_R)\to\mathcal D_0(F)<0$.

To pay the reflection, write $P=e^{2A}$, $E=1/P$, and retain the owned normalization $d\mu=w_A\,d\sigma$, $w_A=\cosh(a-A)D_A^1(a-A)$, $C_A^2=4\pi P/A$. With the normalized parameter $p=e^{2(a-A)}$, W220's identity $w_A\phi(a)=C_A(p+1)/\sqrt2$ gives exactly, at $x=\pi+t/P$,
$$
F_\sigma(t)=\frac{4\pi^2}{C_A}[F(x)-c_*IF(x)],\qquad
F_{M_E\sigma}(t)=\frac{4\pi^2P}{C_A}IF(x),\qquad c_*=\frac3{2\pi}.
$$
The second equality cancels the original site factor $1-c_*/(Pp)$; no small inverse-multiplier norm is assumed. W176--W177 give the physical bound
$$
|Q_{R_\phi^{\rm fold}}(\mu)|\le
\pi^4\int_\pi^\infty|F-c_*IF|^2dx
+c_*\pi^3\int_\pi^\infty|IF|^2dx
=:\mathcal B_\pi(F).
\tag{W232}
$$
The second model channel is used only in absolute norm. For $F_R$, the right side is $O_F(R^{-7/2}+R^{-3/2})$, since the squared norms of $F_R$ and $IF_R$ have those respective scales. Choose and fix $R$ large enough. The resulting one fixed real $f\in C_c^\infty(0,\infty)$, supported in some $[r,M]$ with $0<r<M$, satisfies
$$
\mathcal D_\pi(f)+\mathcal B_\pi(f)<-\delta
\quad\text{for some fixed }\delta>0.
\tag{W233}
$$
This smooth feature is not yet a finite source.

### Approximate in the physical form domain before returning to finite sites

Use $\|v\|_j=\|(1+x)^jv\|_2$ and $\|v\|_X=\|v\|_8+\|v'\|_8$. Right shifts satisfy $\|v(\cdot+s)\|_j\le(1+s)^{-k}\|v\|_{j+k}$. Thus $I$ maps norm $j+2$ to norm $j$. In Frullani, on $0<s<1$ write
$e^{-s}v-v(\cdot+s)=(e^{-s}-1)v-\int_0^s v'(\cdot+u)du$; on $s>1$ use the shift bound with $k=1$. This gives
$$
\|Lv\|_j\le C_j(\|v\|_{j+1}+\|v'\|_j).
\tag{W234}
$$
On $x\ge\pi$, multiplication by $x^{-1}$ is bounded. These estimates control $Bv,BLv$ in norm $3$ by $\|v\|_X$. The weight $x^{7/2}(1+|\log(x/\pi)|)$ is bounded by a constant times $(1+x)^6$ there. Cauchy proves continuity of $\mathcal D_\pi$ and $\mathcal B_\pi$ in $X$.

For real $P\ge1$ use the classical Poisson polynomial approximation
$$
f_P(x)=e^{-Px}\sum_{k\ge0}f(k/P)\frac{(Px)^k}{k!},
\qquad \deg(e^{Px}f_P)\le\lfloor PM\rfloor.
\tag{W235}
$$
The cited primary explicitly permits noninteger $P$. Apply its direct derivative estimate with $r=1$, $\gamma_0=0$, $\gamma_\infty=10$ and weight $\mathfrak w(x)=(1+x)^{10}$. Its conditions $0\le\gamma_0<r$ and $\gamma_\infty\ne r$ hold. Our compact smooth $f$ satisfies all its continuity, local absolute-continuity and weighted derivative requirements. In its $K$-functional choose the competitor to be $f$ itself. The published inequality gives
$$
\|(1+x)^{10}(f_P-f)'\|_\infty
\le\frac{C_f}P,\qquad
C_f=C\|(1+x)^{10}(xf'')'\|_\infty<\infty.
$$
Both $f_P$ and $f$ vanish at infinity, since W235 is a finite polynomial times $e^{-Px}$. Integrating the derivative bound from infinity gives
$|f_P(x)-f(x)|\le C_f(1+x)^{-9}/(9P)$.
Thus $\|f_P-f\|_X=O_f(P^{-1})\to0$, by integrating $(1+x)^{-2}$ for the function and $(1+x)^{-4}$ for its derivative. This is the parameter and norm conversion of the published stronger estimate, rather than a new approximation theorem. W233 remains strictly negative for every sufficiently large $P$.

Write $f_P=e^{-Px}\sum_{k=0}^{n_P}c_{k,P}x^k$, $n_P\le PM$, and deconflate by
$$
f_{P,h}(x)=e^{-Px}\sum_{k=0}^{n_P}c_{k,P}
\left(\frac{1-e^{-hx}}h\right)^k.
\tag{W236}
$$
At fixed $P,n_P$ this converges to $f_P$ in $X$: use $(1-e^{-hx})/h\le x$, its derivative $e^{-hx}\le1$, and polynomial times $e^{-Px}$ domination. It is a real sum of at most $n_P+1$ exponentials with distinct poles $P+jh$. Choose $h>0$ small enough to preserve the strict negative allowance and satisfy $n_Ph<P(e^{2w}-1)$. With $P=e^{2A}$ set $a_j=\tfrac12\log(P+jh)$ and multiply each exponential coefficient by $e^{-9a_j/2}$ to obtain the physical mass $\mu_j$. Every site is in $[A,A+w)$, the count is at most $PM+1\le\lceil Ce^{2A}\rceil$, and W230--W233 give W229. Zero coefficients are removed. Strict negativity excludes the zero measure. The common start and $C$ are independent of $w$; coefficients and gaps are not controlled.

This application excludes the folded first-mode model as a positive proxy on all samples in any sufficient cofinal schedule $e^{2A}g(A)$ with $g(A)\to\infty$: its negative sources already occur at a fixed constant multiple of $e^{2A}$. It neither supplies a negative sample of the complete actual kernel nor proves that a better joint complete-source estimate is impossible. Higher theta modes and the actual model difference cannot simply be dropped on this family. The known negative Gamma baseline, scalar approximation and model operators are reused; the finite physical source/count/window bridge is the additional application. No sharp constant, numerical witness, stable coefficient bound, Lean/kernel or CI/merge certification, exhaustive bibliography or literature priority is supplied. RH and the original strict all-integer Robin bound remain unproved.


## A polynomial tail budget pays the complete reflection on a cofinal sample schedule

Use the original Gaussian normalization of W127 on the whole physical half-line $a\ge A$. Put $E=e^{-2A}$, $\tau(t)=1+Et/\pi$ and retain its source feature $F_\sigma(t)=\int(p+1)e^{-pt}d\sigma(p)/\sqrt2$, $p=e^{2(a-A)}\ge1$. Define
$$
Q_{6,A}(\sigma)=\int_0^\infty\tau(t)^6|F_\sigma(t)|^2dt,\qquad
T_{6,A}(\sigma)=\int_{\pi/E}^\infty\tau(t)^6|F_\sigma(t)|^2dt.
$$
There are fixed $C,A_*>0$ such that, for every $A\ge A_*$ and every compact finite complex source on this half-line,
$$
\begin{aligned}
|Q_{R_A^{g,\rm act}-R_A^{g,1}}(\sigma)|
&\le\frac CA\sqrt{Q_{6,A}(\sigma)T_{6,A}(\sigma)},\\
|Q_{R_A^{g,\rm act}}(\sigma)|&\le\frac CA Q_{6,A}(\sigma).
\end{aligned}
\tag{W237}
$$
The first reflected kernel is complete; the second in its difference is the entire folded first-mode model, both in the same original Gaussian normalization. There is no sign, support-count, width or gap restriction in W237. On finite samples it will pay the complete actual reflected debit at a sufficient cofinal count. It supplies no sign for the complete actual direct component, RH or strict Robin for every integer $n>5040$.

Reuse the exact finite modal pairing W221--W222, its complete-source limiting justification, the two model operators W176--W177, the physical model bound W232, and the existing fixed-order time moments W181--W182. The new estimate retains the joint physical time threshold of the paired correction and uses polynomial weighted source norms. It does not replace the old sector Cauchy norm, reprove a Carleman or Hardy theorem, or extend the first-mode positive-proxy route excluded by W229. This is a paper application without Lean certification or a literature-priority claim.

### Use the physical Gaussian source before estimating any modal tail

Write $P=e^{2A}$, $d\mu(a)=w_A^g(a)d\sigma(p)$ with $w_A^g=\cosh(a-A)D_A^g(a-A)$, and introduce the physical feature
$$
\mathscr F(x)=\int e^{9a/2}e^{-e^{2a}x}d\mu(a),\qquad
I\mathscr F(x)=\int_x^\infty\mathscr F(y)dy,\qquad
B\mathscr F=\mathscr F-\frac3{2x}I\mathscr F.
$$
For $b\ge\pi$ let $N_b(\mathscr F)=\|x^3\mathscr F\|_{L^2(b,\infty)}$. The owned right-integral and dilation calculation gives
$$
N_b(B\mathscr F)\le\frac85N_b(\mathscr F),\qquad
N_\pi\bigl(\ell^4\mathscr F(\ell^2\cdot)\bigr)
=\ell^{-3}N_{\pi\ell^2}(\mathscr F).
\tag{W238}
$$
For the first inequality, $I\mathscr F(x)/x=\int_1^\infty\mathscr F(vx)dv$, and Minkowski costs $\int_1^\infty v^{-7/2}dv=2/5$ in this norm. It preserves the tail domain because $vx\ge b$ when $x\ge b$. In particular, with
$\mathscr T_L\mathscr F=\sum_{\ell\le L}\ell^4\mathscr F(\ell^2\cdot)$,
$$
N_\pi(\mathscr T_L\mathscr F)\le C N_\pi(\mathscr F),\qquad
N_\pi(\mathscr T_L\mathscr F-\mathscr F)\le C N_{4\pi}(\mathscr F),
$$
and the feature series converges in $N_\pi$ as $L\to\infty$.

The physical bound W232 and its underlying two bounded Hermitian model operators give a continuous sesquilinear form satisfying
$|\mathscr R_\phi(U,V)|\le C N_\pi(U)N_\pi(V)$.
Here $\phi=\Phi_1$, and only the absolute norm of its second channel is used. The right integrals in W232 are bounded by the same norm: for example, the ordinary right Hardy inequality $\|IU\|_2\le2\|xU\|_2$ applies after extension by zero below $\pi$. Thus
$$
\left|\mathscr R_\phi(\mathscr T_L\mathscr F,\mathscr T_L\mathscr F)
-\mathscr R_\phi(\mathscr F,\mathscr F)\right|
\le C N_\pi(\mathscr F)N_{4\pi}(\mathscr F).
\tag{W239}
$$
This uses finite physical push-forwards first, followed by their feature-norm limit; no finite total variation is asserted for an infinite unnormalized physical sum.

### The paired finite interval forces at least one feature into the tail

For $s\ge1$ the exact first-mode feature is
$$
G_s=\int\phi(a+\log s)d\mu(a)
=4\pi^2s^{9/2}(B\mathscr F)(\pi s^2).
$$
In W222 the original physical feature of the $\ell$-th shifted source is $\ell^4\mathscr F(\ell^2x)$. Consequently its folded-model term is the one in W239. For $\ell<k$, put $q=\ell k$ and $H_{\ell k}=\tfrac12\log(k/\ell)$. The exact remaining pair correction is
$$
8\pi^4H_{\ell k}q^4\int_\ell^k
\overline{(B\mathscr F)(\pi s^2)}
(B\mathscr F)(\pi(q/s)^2)\frac{ds}s.
\tag{W240}
$$
Let $x=\pi s^2$, $y=\pi(q/s)^2$ and $U(x)=x^3B\mathscr F(x)$. Then $xy=\pi^2q^2$, so the integrand's two cubic weights remove $\pi^6q^6$. Split the interval at $s=\sqrt q$. The involution $s\mapsto q/s$ preserves $ds/s$ and exchanges the two halves. On one half $x\ge\pi q\ge2\pi$; Cauchy and $ds/s=dx/(2x)$ therefore give
$$
\int_\ell^k|U(x)U(y)|\frac{ds}s
\le C N_{\pi q}(B\mathscr F)N_\pi(B\mathscr F).
$$
All arguments are at least $\pi$, so its constant is absolute. By W238 the absolute value of W240 is at most
$C H_{\ell k}q^{-2}N_\pi(\mathscr F)N_{\pi q}(\mathscr F)$.
The double sum converges, since
$\sum_{\ell<k}\log(k/\ell)/(\ell k)^2<\infty$.
Thus the complete paired correction is bounded by
$C N_\pi(\mathscr F)N_{2\pi}(\mathscr F)$.

Use W222 at finite $L$. The just proved norm convergence and absolute double sum pay its right side. The owned complete Gaussian-moment domination passes its left side to the actual reflection, including the small-argument exterior where a raw first-mode substitution would be invalid. It follows that
$$
\begin{aligned}
|Q_{R_\Phi-R_\phi^{\rm fold}}(\mu)|
&\le C N_\pi(\mathscr F)N_{2\pi}(\mathscr F),\\
|Q_{R_\Phi}(\mu)|&\le C N_\pi(\mathscr F)^2.
\end{aligned}
\tag{W241}
$$
This keeps the pair before absolute values. It does not use first-mode evenness or a separator estimate for the old sector norm.

### Return exactly to the original Gaussian metric

Let $\phi_g(a)=4\pi^2e^{9a/2-\pi e^{2a}}$ and $C_A^2=4\pi P/A$. W127 and W232 give exactly
$w_A^g(a)\phi_g(a)=C_A(p+1)/\sqrt2$.
At $x=\pi+t/P$ this yields
$$
F_\sigma(t)=\frac{4\pi^2}{C_A}\mathscr F(\pi+t/P),\qquad
N_\pi(\mathscr F)^2=\frac{\pi^3}{4A}Q_{6,A}(\sigma),\qquad
N_{2\pi}(\mathscr F)^2=\frac{\pi^3}{4A}T_{6,A}(\sigma).
\tag{W242}
$$
No inverse multiplier or small-$EN$ norm-return condition is required: the Gaussian site amplitude cancels exactly in this formula. Substitution in W241 proves W237 for the same original source. Compact finite measures have finite displayed moments; their atom count may be unbounded or absent.

### Consume the whole reflected debit beyond the fixed-fraction count

Now let $\sigma$ have $N\ge1$ distinct active sites, after merging equal sites, with arbitrary complex coefficients. Reuse W182's fixed time moments for $j\le3$, with no small-$EN$ restriction. Expanding $\tau^3$ gives
$$
Q_{6,A}(\sigma)\le C(1+EN)^6Q_H(\sigma),\qquad
|Q_{R_A^{g,\rm act}}(\sigma)|
\le\frac CA(1+EN)^6Q_H(\sigma).
\tag{W243}
$$
This holds at one common high start for every finite $N$, with no support endpoint or gap condition. In particular, for
$$
n_A=\left\lceil e^{2A}A^{1/12}\right\rceil,\qquad
1\le N\le n_A,
\qquad
|Q_{R_A^{g,\rm act}}(\sigma)|\le C A^{-1/2}Q_H(\sigma).
\tag{W244}
$$
The ratio $n_Ae^{-2A}$ tends to infinity, as required by the sufficient cofinal count W156. W244 pays only the complete reflected component on that all-sample schedule. Its sign and the sign of the full odd kernel are not assumed.

Retain the complete actual direct form $Q_{\mathcal D_A^g}$ on exactly the same source, with all its modal amplitude and arithmetic logarithmic contributions. The actual full odd form satisfies
$$
Q_{\mathcal K_A^g}(\sigma)
\ge Q_{\mathcal D_A^g}(\sigma)
-\frac CA(1+EN)^6Q_H(\sigma),
\tag{W245}
$$
and the reflected debit is $C A^{-1/2}Q_H$ under W244. A sufficient direct lower margin, or another joint payment giving positivity of this complete form, is still missing. The old exponential $Q_+$ comparison W226 and small-complexity positive result W228 remain valid in their own scopes; W237--W245 add a polynomial/tail payment on a larger finite-sample range and do not enlarge W228's positive range. No actual negative complete-theta witness, common-start all-order positivity, sufficient cofinal positivity, numerical constants/start, Lean/kernel or CI/merge certification, exhaustive bibliography or literature priority is supplied. RH and the original strict Robin inequality for every integer $n>5040$ remain unproved.


## A polynomial budget bounds the complete direct and odd forms from below

The missing direct component in W245 has an unconditional lower bound in the same polynomial metric. There are fixed $C,A_*>0$ such that every $A\ge A_*$ and every compact finite complex source on $[A,\infty)$ satisfy
$$
Q_{\mathcal D_A^g}(\sigma)\ge-\frac CAQ_{6,A}(\sigma),\qquad
Q_{\mathcal K_A^g}(\sigma)\ge-\frac CAQ_{6,A}(\sigma).
\tag{W246}
$$
Here $Q_{6,A}$, the original Gaussian transport, and the complete actual direct and odd kernels are exactly those in W237--W245. Neither sign, atom count, width nor separation is restricted. This gives a full-form lower bound on the sufficient cofinal sample schedule below. Its right side is negative: it proves neither positivity on that schedule nor RH or strict Robin for every integer $n>5040$.

Reuse the owned homogeneous Gamma multiplier W231, scalar Frullani formula, complete theta source W184--W190, physical modal norm W238 and exact Gaussian return W242. The additional interface pays the finite physical cutoff and the entire arithmetic logarithmic mode term in the cubic physical source norm. The classical Mellin/Gamma lower bound is not reproved. Fixed-window semiboundedness of the Weil form is already recorded in [Connes--Consani--Moscovici, Proposition 3.3, arXiv:2511.22755v1, printed p.8](connesconsanimoscovici2026spectral.md); it has a fixed multiplicative support interval and that interval's Hilbert norm. The uniform physical-source estimate here requires the displayed cubic-norm transport and does not reprove their spectral construction. This is paper mathematics without Lean certification, exhaustive bibliography or a literature-priority claim.

### Pay the cutoff without estimating the source position multiplier

Use W230's physical first-mode form $\mathcal D_\pi$, $I$ the right integral, $L$ the forward Frullani logarithm, $c=3/2$, $B=1-cI/x$, and $N_b(F)=\|x^3F\|_{L^2(b,\infty)}$. Initially take a physical feature from a compact finite complex source. Put $F_0=\mathbf1_{[\pi,\infty)}F$ and $m=\int_\pi^\infty F(y)dy$. For $0<x<\pi$,
$$
BF_0(x)=-\frac{cm}x,\qquad
LF_0(x)=-\int_\pi^\infty\frac{F(y)}{y-x}dy,\qquad
ILF_0(x)=\int_\pi^\infty[-\gamma-\log(y-x)]F(y)dy.
$$
The last identity follows from the owned scalar Laplace logarithm formula at $x=\pi$, followed by integration of the preceding expression for $LF_0$. On $x\ge\pi$ the forward shifts and right integrals see only the original $F$, so the direct integrand is unchanged. Consequently
$$
\begin{aligned}
\mathcal D_\pi(F)&=\mathcal D_0(F_0)-\mathcal C_\pi(F),\\
\mathcal C_\pi(F)&=\frac2{\sqrt\pi}\left[
-\frac{9\pi^{5/2}}{25}|m|^2
+\Re\bigl(\overline m\,\ell_\pi(F)\bigr)\right],\\
\ell_\pi(F)&=\int_\pi^\infty k_\pi(y)F(y)dy,\\
k_\pi(y)&=\frac32\int_0^\pi\frac{x^{5/2}}{y-x}dx
-\frac94\int_0^\pi x^{3/2}[\gamma+\log(y-x)]dx.
\end{aligned}
\tag{W247}
$$
This cutoff form has rank at most two in the physical weighted space. The first integral in $k_\pi$ has at most a logarithmic singularity at $y=\pi$; the second is finite there and grows at most logarithmically at infinity. Thus $k_\pi(y)y^{-3}$ is square integrable, as is $y^{-3}$, and Cauchy--Schwarz gives $|m|+|\ell_\pi(F)|\le C N_\pi(F)$ and $|\mathcal C_\pi(F)|\le C N_\pi(F)^2$. No largest-source-position or source-coefficient norm enters.

W231's real Gamma multiplier is bounded below: its rational factor is bounded on $\Re z=9/4$, while the real digamma factor is continuous and tends to positive infinity at large frequency. Its existing Mellin identity therefore gives $\mathcal D_0(F_0)\ge-C\|x^{7/4}F_0\|_2^2$. The zero extension is in that logarithmic form domain. Indeed $g_0(u)=e^{9u/4}F_0(e^u)$ is smooth on each side of its single jump, with integrable one-sided derivative and exponential decay at the right end; its Fourier transform is $O((1+|\xi|)^{-1})$. Smooth cutoffs converge in the logarithmically weighted Fourier norm, so W231 extends to this profile. Below $\pi$ its Frullani singularity at the jump is logarithmic and its displayed $B$ tail is integrable in the physical form. The complex case follows by separate real and imaginary parts. These facts justify the identity, not a uniform derivative allowance. Since $x^{7/2}\le\pi^{-5/2}x^6$ for $x\ge\pi$, W247 yields
$$
\mathcal D_\pi(F)\ge-CN_\pi(F)^2.
\tag{W248}
$$
The logarithm itself is not bounded above in this norm; only its required signed lower form is used.

### Keep the entire theta logarithmic charge on the same physical feature

For the original physical feature $\mathscr F$ of W238 define finite modal sums
$$
\mathscr T_J\mathscr F(x)=\sum_{\ell\le J}\ell^4\mathscr F(\ell^2x),\qquad
\mathscr V_J\mathscr F(x)=\sum_{\ell\le J}(\log\ell)\ell^4\mathscr F(\ell^2x).
$$
Let $\Phi_J$ be the corresponding finite theta source. Scalar dilation gives $\mathscr T_JL=L\mathscr T_J-2\mathscr V_J$. The complete direct feature is $B\mathscr T_J\mathscr F$, whereas multiplying the ORIGINAL source by $a$ gives $B\mathscr T_JL\mathscr F/2$. W230 with this order retained gives the exact identity
$$
Q_{D_{\Phi_J}}(\mu)
=\mathcal D_\pi(\mathscr T_J\mathscr F)
-\frac4{\sqrt\pi}\Re\int_\pi^\infty x^{7/2}
\overline{B\mathscr T_J\mathscr F(x)}\,
 B\mathscr V_J\mathscr F(x)\,dx.
\tag{W249}
$$
The negative sign and factor two in the logarithmic charge are retained. This is the physical form of the arithmetic term in W190, not a source replacement or an estimate of $a\mu$ separately.

The already owned W238 dilation gives, uniformly in $J$,
$$
N_\pi(\mathscr T_J\mathscr F)+N_\pi(\mathscr V_J\mathscr F)
+N_\pi(B\mathscr T_J\mathscr F)+N_\pi(B\mathscr V_J\mathscr F)
\le C N_\pi(\mathscr F).
\tag{W250}
$$
Both feature series converge in this norm, since $\sum\ell^{-3}$ and $\sum(\log\ell)\ell^{-3}$ converge. W248 applies to each finite physical push-forward. Cauchy--Schwarz with $x^{7/2}\le\pi^{-5/2}x^6$ bounds the entire charge in W249 by $C N_\pi(\mathscr F)^2$. Hence $Q_{D_{\Phi_J}}(\mu)\ge-CN_\pi(\mathscr F)^2$, with a constant independent of $J$.

For the original compact finite physical source, normal absolute theta convergence on direct arguments $a+r\ge A$ and their Gaussian decay pass this finite-cutoff direct form to the complete actual one. Position multipliers are bounded on each original compact source; these bounds justify the limit only and do not occur in the final norm inequality. There is no assertion of finite total variation for an infinite unnormalized modal push-forward. Thus
$$
Q_{D_\Phi}(\mu)\ge-CN_\pi(\mathscr F)^2.
\tag{W251}
$$
Reuse W242's exact original Gaussian identity $N_\pi(\mathscr F)^2=\pi^3Q_{6,A}(\sigma)/(4A)$. No inverse multiplier, small $EN$ condition or first-mode metric return is used. This proves the first half of W246. W237's absolute bound for the complete ACTUAL reflection proves its second half on exactly the same source.

### Consume the lower bound on every sample of the cofinal schedule

If $\sigma$ has $N\ge1$ distinct active sites after merging equal sites, with arbitrary complex coefficients, the already owned W243 moment bound gives
$$
Q_{\mathcal D_A^g}(\sigma),\ Q_{\mathcal K_A^g}(\sigma)
\ge-\frac CA(1+e^{-2A}N)^6Q_H(\sigma).
\tag{W252}
$$
For $n_A=\lceil e^{2A}A^{1/12}\rceil$ this implies, uniformly over ALL these sources with $1\le N\le n_A$ and $A\ge A_*$,
$$
Q_{\mathcal D_A^g}(\sigma),\ Q_{\mathcal K_A^g}(\sigma)
\ge-CA^{-1/2}Q_H(\sigma).
\tag{W253}
$$
The point locations can have arbitrary width and no positive minimum separation. The zero source gives zero. The bound is on the complete actual odd form, including the direct source, every theta logarithmic charge and the reflected exterior; the count is the sufficient cofinal schedule of W156, not a fixed fraction of $e^{2A}$.

W253 gives a negative allowance tending to zero in the original Gaussian Hardy metric, not positive semidefiniteness. Negative values remain allowed, with magnitude at most $CA^{-1/2}Q_H(\sigma)$. The W156 implication requires actual positivity on its cofinal sample family; W253 does not satisfy that premise, exclude off-line zeros or bound the normalized margin of their transported witnesses. W228's exact positive range remains unchanged. A same-source positive margin or another argument eliminating the permitted negative directions is still required. No actual negative complete-theta witness, finite effective RH test, numerical constant/start, Lean/kernel or CI/merge certification, exhaustive bibliography or priority is supplied. Full RH and the original strict Robin inequality for every integer $n>5040$ remain unproved.


## Actual negative witnesses retain a fixed margin after scaling the Gaussian form by A

The negative lower allowances W246--W253 must be compared with the margin of actual witnesses in the SAME metric. Conditional on RH failure, there are fixed $c,C,K,A_*>0$ such that every $A\ge A_*$ and every $w>0$ admit a real finite original Gaussian source $\sigma_{A,w}$ with
$$
\begin{gathered}
\operatorname{supp}\sigma_{A,w}\subset[A,A+w),\qquad
\#\operatorname{supp}\sigma_{A,w}\le\lceil Ce^{2A}\rceil,\\
Q_H(\sigma_{A,w})=1,\qquad
Q_{6,A}(\sigma_{A,w})\le K,\qquad
Q_{\mathcal K_A^g}(\sigma_{A,w})\le-\frac cA.
\end{gathered}
\tag{W254}
$$
The constants can depend on the conditional actual negative seed, but not on $A$ or $w$. Support and site count are recorded in the physical $a$ coordinate. Equal sites are merged and zero coefficients removed. The kernel is the complete actual odd kernel, not the first-mode model; $Q_H$ and $Q_{6,A}$ are the original Gaussian quantities of W237--W253. No unconditional negative seed, numerical margin or stable coefficient bound is supplied.

Reuse the actual negative seed W40/W102, the complete physical direct/modal/reflected identities W239--W251, the forward logarithm bound W234, the published approximation already transported in W235--W236, and the exact original Gaussian map W242. The added interface controls the complete actual form and both source norms through that approximation. The classical approximation and the first-mode witness W229 are not reproved. This is paper mathematics without Lean certification, exhaustive bibliography or a literature-priority claim.

### The complete actual physical form is continuous in the owned approximation domain

Use the same $X$ as W234,
$\|F\|_X=\|(1+x)^8F\|_2+\|(1+x)^8F'\|_2$ on $(0,\infty)$.
Retain $B=1-3I/(2x)$, the physical dilation sum $\mathscr T$ and the forward logarithm $L$. Define the direct form on this domain by
$$
\mathfrak D_\Phi(F)=\frac2{\sqrt\pi}\int_\pi^\infty x^{7/2}
\left[\log(x/\pi)|B\mathscr TF|^2
+\Re\bigl(\overline{B\mathscr TF}\,B\mathscr TLF\bigr)\right]dx.
$$
Its logarithm remains in the source order $\mathscr TL$; equivalently W249 retains the full $-2\mathscr V$ charge after commuting it. W234 bounds $LF$ in weighted norm $3$ by $C\|F\|_X$. W238 and W250 bound $B\mathscr TF$ and $B\mathscr TLF$ in the cubic physical norm. The weights $x^{7/2}$ and $x^{7/2}\log(x/\pi)$ are bounded by $C(1+x)^6$ on this half-line. Thus the direct pairing is bounded on $X$.

Define $\mathfrak R_\Phi(F)$ by the bounded folded model on $\mathscr TF$ and the exact paired integrals W240. Their absolute convergence and sesquilinear norm bounds W239--W241 apply in the same cubic norm. In particular the complete reflection, including its small-argument exterior, is continuous on $X$. With $\mathfrak E=\mathfrak D_\Phi-\mathfrak R_\Phi$,
$$
|\mathfrak E(F)-\mathfrak E(G)|
\le C(\|F\|_X+\|G\|_X)\|F-G\|_X.
\tag{W255}
$$
For every compact finite physical source $\mu$, this form agrees with $Q_{L_0}(\mu)$ on its physical feature
$F(x)=\int e^{9a/2}e^{-e^{2a}x}d\mu(a)$, by the owned finite-modal identities and their justified limits. Each operation in the displayed definition uses only $F$ on $[\pi,\infty)$: forward shifts, right integrals, dilations by $\ell^2\ge1$ and the paired arguments in W240 never ask for a smaller physical coordinate. No infinite unnormalized modal measure or independent sign assignment is introduced.

### Reuse approximation on one fixed actual negative feature

If RH fails, take W102's fixed real actual seed $\mu_0$ on $(1,2)$. Its smooth exponentially decaying physical feature $F_0$ has $\mathfrak E(F_0)<0$. First multiply $F_0$ by a smooth cutoff that is zero near $0$ and one for $x\ge\pi$. This does not alter $\mathfrak E$, since only the right-hand physical tail is used. Then truncate at infinity. Exponential decay makes this second cutoff converge in $X$. By W255 one fixed real $f\in C_c^\infty(0,\infty)$, supported in $[r,M]$ with $0<r<M$, satisfies
$$
\mathfrak E(f)<-2\delta\quad\text{for some fixed }\delta>0,
\qquad \|f\|_{L^2(\pi,\infty)}>0.
\tag{W256}
$$
This argument does not assert that an arbitrary nonzero trace at $0$ can be approximated in the whole $H^1$ norm by functions vanishing there. The lower cutoff is legitimate because the physical form does not observe that interval.

Apply W235 directly to this $f$ with the real parameter $P=e^{2A}$. Its already established derivative estimate gives $\|f_P-f\|_X=O_f(P^{-1})$ and degree $n_P\le PM$. Use W236's deconflation with $h>0$ so small that
$\|f_{P,h}-f_P\|_X\le P^{-1}$ and $n_Ph<P(e^{2w}-1)$. Both requirements can be met for every $w>0$. The resulting physical feature is a real sum of at most $PM+1$ distinct exponentials with rates $P+jh$, hence a real physical source in $[A,A+w)$.

For all sufficiently large $P$, W255--W256 give $\mathfrak E(f_{P,h})\le-\delta$. At the same common start, its $L^2(\pi,\infty)$ norm is bounded above and away from zero, and its cubic physical norm is bounded above. These constants depend only on $f$. The choice $\|f_{P,h}-f_P\|_X\le P^{-1}$ makes the bounds independent of $w$; the coefficients and required gap may depend on it. This applies the existing approximation rather than repeating its proof.

### Return both norms exactly to the original Gaussian source

Let $\mu_{A,w}$ be that physical source and put $d\mu_{A,w}=w_A^g\,d\sigma_{A,w}^{\rm raw}$. Its original physical feature is $F=f_{P,h}$. W242 gives, with $C_A^2=4\pi P/A$,
$$
\begin{aligned}
F_{\sigma^{\rm raw}}(t)&=\frac{4\pi^2}{C_A}F(\pi+t/P),\\
Q_H(\sigma^{\rm raw})&=4\pi^3 A\|F\|_{L^2(\pi,\infty)}^2,\\
Q_{6,A}(\sigma^{\rm raw})&=\frac{4A}{\pi^3}\|x^3F\|_{L^2(\pi,\infty)}^2,\\
Q_{\mathcal K_A^g}(\sigma^{\rm raw})&=\mathfrak E(F)\le-\delta.
\end{aligned}
\tag{W257}
$$
The physical numerator stays negative by a fixed amount, while both original Gaussian norms have size at most a fixed constant times $A$ and $Q_H/A$ is bounded away from zero. Divide the source by $\sqrt{Q_H(\sigma^{\rm raw})}$. This proves W254 with fixed $c,K$ and count constant $C=M+1$, after increasing the common start and taking $K\ge1$. There is no small-$EN$ inverse-multiplier return or coefficient-mass allowance. Very small $h$ and very large physical coefficients remain permitted.

### The current negative budget is now measured against an actual witness scale

Fix $w>0$, let $A_j\to\infty$ and let positive integers $n_j$ satisfy $n_je^{-2A_j}\to\infty$. The following would suffice for RH: for EVERY fixed $K\ge1$, there are $\eta_j(K)\ge0$ with $\eta_j(K)\to0$ such that, for all sufficiently large $j$, all real finite original Gaussian sources with
$\operatorname{supp}\sigma\subset[A_j,A_j+w)$, at most $n_j$ active sites, $Q_H(\sigma)=1$ and $Q_{6,A_j}(\sigma)\le K$ obey
$$
A_jQ_{\mathcal K_{A_j}^g}(\sigma)\ge-\eta_j(K).
\tag{W258}
$$
Indeed, if RH failed, choose the ONE fixed $K$ and $c,C$ of W254. Its sources eventually fit $n_j$, and satisfy the opposite bound $A_jQ_{\mathcal K_{A_j}^g}\le-c$, contradicting $\eta_j(K)\to0$. Neither uniformity in $K$ nor a numerical value of the conditional seed constants is needed. This is a sufficient estimate, not a necessary requirement for other RH methods; W258 itself remains unproved.

W246 already gives on precisely this normalized fixed-budget class
$$
A_jQ_{\mathcal K_{A_j}^g}(\sigma)\ge-CK.
\tag{W259}
$$
It pays a fixed negative constant after scaling, not a quantity tending to zero. That allowance does not exclude W254's fixed negative margin. Consequently W253's unscaled $o(1)$ bound is not a sign conclusion. The next missing estimate in this route is a joint complete-source payment that removes this fixed scaled deficit for each fixed moment budget, or another argument eliminating the permitted negative directions. Improving the count without paying that deficit does not supply W258.

The actual kernel, complete theta modes and reflected exterior remain unchanged throughout. W254 is conditional and supplies no actual negative complete-theta example. W228's exact positive range and W246--W253's unconditional lower bounds remain valid in their stated scopes. No stable finite-precision witness, numerical constants/start, Lean/kernel or CI/merge certification, exhaustive bibliography or priority is supplied. Full RH and the original strict Robin inequality for every integer $n>5040$ remain unproved.


## A small original moment excess gives actual positivity without a point-count cap

There are fixed $\delta_0,C,A_*>0$ such that every $A\ge A_*$ and every compact finite complex original Gaussian source on $a\ge A$ with $Q_H(\sigma)>0$ and
$\varepsilon=Q_{6,A}(\sigma)/Q_H(\sigma)-1\le\delta_0$ satisfy
$$
Q_{\mathcal K_A^g}(\sigma)
\ge\frac1A\left[\frac18\log\frac1\varepsilon-C\right]Q_H(\sigma).
\tag{W260}
$$
Here $\varepsilon>0$ automatically. There is no count, sign, width or internal-gap cap. All theta modes, the arithmetic logarithmic charge and the complete actual reflection remain present. This supplies a positive sector of the intrinsic moment budgets in W258; it does not supply W258 for every fixed budget, RH or strict Robin for every integer $n>5040$.

Reuse W230/W234's forward Frullani logarithm, W238's right-integral/dilation calculation, W241's full actual reflection bound, W249's exact modal source order and W257's original Gaussian return. The additional application makes concentration near the physical endpoint pay the entire direct logarithm and both actual debits. No standalone Hardy, logarithmic-uncertainty or generic criterion is added. This is paper mathematics without Lean certification or a literature-priority claim.

### Keep the excess and every modal feature on the same source

Let $F$ be the original physical feature in W238, and use norms on $[\pi,\infty)$. W257 gives exactly
$$
\begin{aligned}
D(F)^2&:=\int_\pi^\infty(x^6-\pi^6)|F(x)|^2dx
=\pi^6\varepsilon\|F\|_2^2,\\
N_\pi(F)^2&=\pi^6(1+\varepsilon)\|F\|_2^2,\qquad
Q_H(\sigma)=4\pi^3 A\|F\|_2^2.
\end{aligned}
\tag{W261}
$$
The strictly positive weight off the single endpoint proves $\varepsilon>0$ for $Q_H>0$. Initially retain a finite modal cutoff $J\ge1$. Put
$U=\mathscr T_JF$, $V=\mathscr V_JF$, $G=BU$, $W(x)=x^{7/2}$, and write $\|h\|_W^2=\int_\pi^\infty W|h|^2$.

For $v\ge1$, changing variables gives
$D(F(v\cdot))\le v^{-7/2}D(F)$: on the changed tail,
$y^6-v^6\pi^6\le y^6-\pi^6$. Thus the W238 Minkowski calculation also gives $D(Bh)\le(8/5)D(h)$ and $D(U)\le C D(F)$, uniformly in $J$. For every higher mode, its input lies above $4\pi$, where $y^6\le C(y^6-\pi^6)$. W238 therefore gives
$N_\pi(U-F)+N_\pi(V)\le C D(F)$, by summing $\ell^{-3}$ and $(\log\ell)\ell^{-3}$.

The right-integral part of $G-F$ is small in the required weight as well. Apply integration by parts to $h=IF$ with
$R(x)=\int_\pi^x t^{3/2}dt\le(x-\pi)x^{3/2}$, followed by Cauchy--Schwarz. The endpoint term vanishes at $\pi$ because $R(\pi)=0$, and at infinity by exponential decay. It gives
$\|x^{3/4}IF\|_2\le2\|(x-\pi)x^{3/4}F\|_2\le C D(F)$.
The last comparison uses $(x-\pi)^2x^{3/2}\le C(x^6-\pi^6)$. Together with W238 on $B(U-F)$ this proves $\|G-F\|_W\le C D(F)$ and $D(G)\le C D(F)$.

Consequently, for one fixed sufficiently small $0<\delta_0\le1$, all $0<\varepsilon\le\delta_0$ satisfy, uniformly in $J$,
$$
\begin{aligned}
\tfrac14\pi^{7/2}\|F\|_2^2\le S&:=\|G\|_W^2\le C\|F\|_2^2,\\
0<r&:=\frac{\int_\pi^\infty(x-\pi)W(x)|G(x)|^2dx}{S}
\le C\varepsilon.
\end{aligned}
\tag{W262}
$$
For the second bound use $(x-\pi)x^{7/2}\le C(x^6-\pi^6)$ and the just proved excess estimate on $G$. Its numerator is positive because $S>0$ and a nonzero $L^2$ feature cannot be supported at a single endpoint. All constants are independent of source count, coefficients and the modal cutoff.

### Concentration pays the forward logarithm before any mode is discarded

For $s>0$ let
$\mathscr C(s)=\int_\pi^\infty W(x)\overline{G(x)}G(x+s)dx$.
Increasing $W$, Cauchy--Schwarz and the definition of $r$ give
$$
|\mathscr C(s)|\le S\min(1,\sqrt{r/s}),\qquad
\Re\langle G,LG\rangle_W
\ge S[-\gamma-\log r-2]
\ge S\left[\log\frac1\varepsilon-C\right].
\tag{W263}
$$
Indeed $\|G(\cdot+s)\|_W^2\le\int_{\pi+s}^\infty W|G|^2\le S\min(1,r/s)$. Insert this correlation allowance directly in the owned forward Frullani formula. Its scalar integral is
$\int_0^\infty(e^{-s}-\mathbf1_{s\le r})ds/s=-\gamma-\log r$, and the remaining tail costs
$\int_r^\infty\sqrt{r/s}\,ds/s=2$.
For each finite cutoff, the actual $G$ is smooth with exponential decay, so the pairing has the required cancellation at zero and convergence at infinity. This consumes the classical logarithm formula inside the actual-source estimate, rather than asserting positivity of an independent model.

The original source order still requires $BLU$, not $LBU$. The exact commutator is
$$
BLU=LBU+\mathscr C_BU,\qquad
(\mathscr C_BU)(x)=\frac3{2x}\int_x^\infty\log(y/x)U(y)dy,
\qquad N_\pi(\mathscr C_BU)\le\frac6{25}N_\pi(U).
\tag{W264}
$$
To obtain its sign, the forward formula gives
$[x^{-1},L]h=-x^{-1}\int_x^\infty h(y)dy/y$ and $I$ commutes with $L$. Substitute $h=IU$ and interchange the two right integrals. For the norm, write $\mathscr C_BU=(3/2)\int_1^\infty(\log v)U(vx)dv$ and reuse W238's dilation cost; $(3/2)\int_1^\infty(\log v)v^{-7/2}dv=6/25$. Only this absolute bound is used, not a positive-semidefinite claim about the commutator.

### Pay the complete arithmetic charge and reflected exterior in the original metric

With the preceding notation W249 is exactly
$$
Q_{D_{\Phi_J}}(\mu)=\frac2{\sqrt\pi}
\left[\int_\pi^\infty W\log(x/\pi)|G|^2
+\Re\langle G,LG\rangle_W
+\Re\langle G,\mathscr C_BU\rangle_W
-2\Re\langle G,BV\rangle_W\right].
$$
The first term is nonnegative. W238/W250/W264 bound the commutator debit by $C N_\pi(F)^2$ and the entire log-mode debit by $C N_\pi(F)D(F)$, since $x^{7/2}\le\pi^{-5/2}x^6$ on this half-line. W261 makes both at most $C\|F\|_2^2$ when $\varepsilon\le\delta_0\le1$. In W263 use the lower bound for $S$ only on the nonnegative factor $\log(1/\varepsilon)$; use its upper bound on the constant negative allowance. It follows that
$$
Q_{D_{\Phi_J}}(\mu)
\ge\frac{\pi^3}{2}\log\frac1\varepsilon\,\|F\|_2^2-C\|F\|_2^2.
$$
The constants are uniform in $J$. Pass to the complete actual direct form using precisely W251's compact-source theta convergence. W241 bounds the complete actual reflection, including its exterior and all paired corrections, by $C N_\pi(F)^2\le C\|F\|_2^2$. Thus the full same-source physical form satisfies
$$
\mathfrak E(F)\ge\frac{\pi^3}{2}\log\frac1\varepsilon\,\|F\|_2^2-C\|F\|_2^2.
\tag{W265}
$$
Divide by W261's exact $Q_H=4\pi^3A\|F\|_2^2$ and enlarge the fixed constant. This proves W260 for the original Gaussian source. There is no inverse-multiplier return, point-count allowance, separately optimized response or replacement by the folded first mode.

Choose a fixed $0<\delta_*\le\delta_0$ small enough that
$(1/8)\log(1/\delta_*)-C\ge1/8$. Then
$$
Q_{6,A}(\sigma)\le(1+\delta_*)Q_H(\sigma)
\quad\Longrightarrow\quad
Q_{\mathcal K_A^g}(\sigma)\ge\frac1{8A}Q_H(\sigma)>0
\quad(Q_H>0,\ A\ge A_*).
\tag{W266}
$$
This intrinsic condition imposes no finite bound on the number of active sites or local sign changes. For example, by W182's one-site moments a Gaussian atom at $a=A$ has $Q_{6,A}/Q_H-1=O(e^{-2A})$. Fix a sufficiently high $A$ and a compact window of positive width. For each arbitrarily large finite site count, append distinct atoms with alternating nonzero real coefficients sufficiently small that the strict moment condition persists by continuity of the two quadratic norms. The active count and local sign degree are unbounded at this fixed window and start. This illustrates that the intrinsic hypothesis is not the old point-count or separator cap; the theorem itself covers every source satisfying that hypothesis, including its cancellations.

Conversely, any negative actual source at the common start must have $Q_{6,A}/Q_H>1+\delta_*$. In particular W254's conditional witnesses, if RH fails, cannot lie in this small-excess sector. W258 still requires an estimate for EVERY fixed moment budget, including larger ratios; W260--W266 do not control those ratios or eliminate the conditional witnesses. Full RH and the original strict Robin inequality for every integer $n>5040$ remain unproved. No explicit numerical threshold/start, stable finite-precision decision procedure, Lean/kernel or CI/merge certification, exhaustive bibliography or literature priority is supplied.


## Short physical intervals admit complete theta positivity at arbitrarily large moment ratios

Let $\mathfrak E$ be the complete physical form defined at W255, including the full theta source, arithmetic logarithmic charge and actual reflected exterior. There is a fixed $C>0$ such that, for every $R\ge\pi$, $0<d\le1$ and complex $f\in C_c^\infty((R,R+d))$,
$$
\mathfrak E(f)\ge
\left[\frac2{\sqrt\pi}\log\frac1d-C\right]S(f),
\qquad S(f):=\|\mathscr Tf\|_{L^2([\pi,\infty),x^{7/2}dx)}^2.
\tag{W267}
$$
All constants are independent of $R,d$ and $f$. In particular one fixed sufficiently small width gives positivity at every physical location, not just near $\pi$. The original Gaussian source consumer below has moment ratios tending to values of order $(R/\pi)^6$, unbounded as $R$ grows. This does not prove positivity for every source with a given large moment budget, or pay coupling between arbitrary separate physical intervals. W258, RH and strict Robin for every integer $n>5040$ remain unproved.

Reuse the exact physical extension W255, homogeneous Gamma multiplier W231, cutoff W247, full source order W249, complete paired reflection W240--W241, original Gaussian map W257 and approximation W235--W236. The ordinary compact-logarithmic-test small-window floor in [the localization note](frankliebseiringer2006hardy.md#reuse-the-stronger-small-window-spectral-floor) is a different support condition; it is not reproved here. The estimate concerns the physical Laplace feature before all theta dilations. Classical Fourier mass, harmonic-sum and right-integral estimates are consumed in this application, with no separate generic theorem or literature-priority claim. The argument is paper mathematics without Lean certification.

### Retain all disjoint dilation intervals and their exact harmonic weights

Put $M=\|f\|_2^2$, $W=x^{7/2}$, $L=\lfloor\sqrt{(R+d)/\pi}\rfloor$ and $L_0=\lfloor\sqrt{R/\pi}\rfloor\ge1$. On $[\pi,\infty)$ write
$u_\ell(x)=\ell^4 f(\ell^2x)$, $U=\mathscr Tf=\sum_{\ell\le L}u_\ell$ and $V=\mathscr Vf=\sum_{\ell\le L}(\log\ell)u_\ell$.
The intervals $(R/\ell^2,(R+d)/\ell^2)$ are pairwise disjoint for these indices. Indeed $d\ell^2<R(2\ell+1)$ follows from $d\le1$, $R\ge\pi$ and $\ell^2\le(R+d)/\pi$. Truncation at $\pi$ preserves disjointness. Changing variables gives
$$
\begin{aligned}
S_\ell&:=\|u_\ell\|_W^2
=\frac1\ell\int_{\max(R,\pi\ell^2)}^{R+d}y^{7/2}|f(y)|^2dy,\qquad S=\sum_{\ell\le L}S_\ell,\\
cR^{7/2}\log(2+R)M&\le S\le CR^{7/2}\log(2+R)M,\\
2\Re\langle U,V\rangle_W
&=2\sum_{\ell\le L}(\log\ell)S_\ell\le(\log L+C)S.
\end{aligned}
\tag{W268}
$$
For $\ell\le L_0$, the integral is the whole common quantity $S_f=\int_R^{R+d}y^{7/2}|f|^2$. Since $d<\pi$, at most the last mode is partial: $L-L_0\le1$. Thus $S\ge H_{L_0}S_f$ and $S\le H_LS_f$. The harmonic estimates $H_n=\log n+O(1)$ and $\sum_{\ell\le n}(\log\ell)/\ell=\tfrac12\log^2n+O(1)$ prove all displayed comparisons, including the partial last mode. These weights belong to the same $f$; no separate maximizing sequence is substituted.

### The Mellin localization gain pays the whole arithmetic logarithmic loss

Extend $U$ by zero below $\pi$, writing $U_0$. Put $g(u)=e^{9u/4}U_0(e^u)$, so $\|g\|_2^2=S$. Its support has logarithmic measure $m\le L\log(1+d/R)\le Ld/R$. With the unitary Fourier convention of W231, Cauchy--Schwarz gives $|\widehat g(\xi)|^2\le mS/(2\pi)$. Consequently
$$
\int_{\mathbb R}|\widehat g(\xi)|^2\log|\xi|\,d\xi
\ge[\log(\pi/m)-1]S
\ge\left[\log\frac{R}{Ld}-C\right]S.
\tag{W269}
$$
For the first inequality, use the probability measure $|\widehat g|^2d\xi/S$ and the bound
$\Pr\{|\xi|< (\pi/m)e^{-t}\}\le e^{-t}$; integrate its negative logarithmic part. No shape, connected-support or sign assumption on $g$ is made. If $f=0$ every estimate is trivial; otherwise $m,S>0$.

The multiplier in W231 is at least $\log|\xi|-C$: it has the owned digamma asymptotic at infinity, and its difference from $\log|\xi|$ is bounded below on the remaining real line. W231 therefore bounds $\mathcal D_0(U_0)$ below by $(2/\sqrt\pi)[\log(R/(Ld))-C]S$. The zero extension has a possible single jump at $\pi$, is smooth elsewhere in its finite compact support, and has Fourier decay $O((1+|\xi|)^{-1})$ after the Mellin change. It lies in the logarithmic form domain by the same argument used at W247; no derivative-norm estimate is claimed.

W247's cutoff correction is bounded by $CS$ in this weaker weight too: $y^{-7/4}$ and $k_\pi(y)y^{-7/4}$ are square integrable. The kernel has only a logarithmic singularity at $\pi$ and at most logarithmic growth at infinity. Hence
$\mathcal D_\pi(U)\ge(2/\sqrt\pi)[\log(R/(Ld))-C]S$.

The $B$ factors in W249's arithmetic charge must still be retained. Since $|If(y)|\le\sqrt{dM}\,\mathbf1_{y<R+d}$,
$$
\begin{aligned}
\|(B-I)U\|_W&\le C\sqrt d\,R^{3/2}\sqrt M,\\
\|(B-I)V\|_W&\le C\sqrt d\,R^{3/2}\log(2+R)\sqrt M,\\
|\Re\langle BU,BV\rangle_W-\Re\langle U,V\rangle_W|&\le CS.
\end{aligned}
\tag{W270}
$$
For the first two bounds, $Iu_\ell(x)=\ell^2If(\ell^2x)$ and $\sum_{\ell\le\sqrt{(R+d)/x}}\ell^2\le C(R/x)^{3/2}$. Divide by $x$ and integrate against $x^{7/2}$ for $\pi\le x\le R+d$; $\int_\pi^{R+d}x^{-3/2}dx$ is uniformly bounded. Add the factor $\log(2+R)$ for $V$. For the third use Cauchy--Schwarz, $\|V\|_W\le(\log L)\sqrt S$, and W268. The resulting relative factors are bounded by constants times $\sqrt d R^{-1/4}\sqrt{\log(2+R)}+dR^{-1/2}$, uniformly on the stated range.

Substitute W268--W270 in the exact full direct identity W249. It yields
$$
\mathfrak D_\Phi(f)\ge
\frac2{\sqrt\pi}\left[\log\frac{R}{L^2d}-C\right]S
\ge\left[\frac2{\sqrt\pi}\log\frac1d-C\right]S.
\tag{W271}
$$
Here $L^2\le(R+d)/\pi$ and $R\ge\pi$, $d\le1$. The exact coefficient of both the Fourier gain and the harmonic logarithmic loss matters: estimating the log-mode charge by its largest mode separately would lose an uncancelled $\log R$. No theta mode in the direct source is dropped.

### The complete reflected exterior is uniformly bounded in this same packet metric

For the folded model on $U$, W232 and the owned right Hardy inequality give
$|\mathscr R_\phi(U,U)|\le C(\|U\|_2^2+\|IU\|_2^2)\le CS$.
For the exact remaining pair sum W240 put $Q=(R+d)/\pi$, $q=\ell k$, $H_{\ell k}=\tfrac12\log(k/\ell)$ and $Hf=(3/2)If/x$, so $Bf=f-Hf$. The bound
$|Hf(x)|\le C\sqrt{dM}/x$ holds for $\pi\le x<R+d$, and $Hf=0$ above this range. Both pair arguments must be at most $R+d$, so only $q\le Q$ contribute. This includes indices $k>L$; the direct-mode cutoff cannot be used to discard that exterior contribution.

Expand each pair into its $f$--$f$, $f$--$Hf$ and $Hf$--$Hf$ parts, keeping their actual paired arguments $x=\pi s^2$, $y=\pi(q/s)^2$ and $xy=\pi^2q^2$.

For the first part, both arguments in $(R,R+d)$ force $q\in[R/\pi,(R+d)/\pi]$, an interval of length less than one. Thus at most one integer $q$ occurs. Cauchy--Schwarz in the invariant measure $dx/x=2ds/s$ bounds its integral by $CM/R$. There are at most $\sqrt q$ divisor pairs and $\sum_{\ell k=q,\ell<k}H_{\ell k}\le C\sqrt q\log(2+q)$. The total contribution is therefore at most $CR^{7/2}\log(2+R)M\le CS$.

For either mixed part, $xy=\pi^2q^2$ and $\int|f|\le\sqrt{dM}$ give a bound $CdM q^2H_{\ell k}$ after the coefficient in W240 is included. For the two-tail part, integration over $\ell<s<k$ gives at most $CdM q^2H_{\ell k}^2$. The elementary hyperbola estimate
$\sum_{\ell<k,\ell k\le Q}(\ell k)^2[1+\log(k/\ell)]^2\le CQ^3\log^3(2+Q)$
follows by summing $k^2$ first and then $\sum_{\ell\le\sqrt Q}1/\ell$. Both remaining totals are at most $CdMR^3\log^3(2+R)\le CS$, since $d\le1$ and $R^{-1/2}\log^2(2+R)$ is bounded for $R\ge\pi$. Consequently
$$
|\mathfrak R_\Phi(f)|\le CS.
\tag{W272}
$$
This estimates the complete actual reflection defined at W255, including every paired correction and the small-argument exterior. Compact support makes the effective pair sum finite; no unnormalized infinite physical measure or first-mode substitution is used. W271--W272 prove W267.

### Transport this positive family to actual local Gaussian sources

Choose once a sufficiently small $d_*>0$, $d_*\le1$, so that W267's bracket is at least one. By W268 there is a fixed $c>0$ such that
$$
\mathfrak E(f)\ge S(f)\ge cR^{7/2}\log(2+R)\|f\|_2^2>0
\quad\text{for every }R\ge\pi,\quad0\ne f\in C_c^\infty((R,R+d_*)).
\tag{W273}
$$
This physical feature need not be a finite exponential source itself. To obtain actual sources, apply the already established W235--W236 to each such $f$, componentwise for complex $f$. With $P=e^{2A}$, choose the deconflation step to make the $X$ error at most $P^{-1}$ and all physical sites lie in $[A,A+w)$, for every $w>0$. The same selected error works uniformly in $w$; required coefficients and gaps may depend on $w$. There are at most $\lceil(R+d_*+1)P\rceil$ sites. W255 and the exact W257 Gaussian return give normalized actual sources with $Q_H=1$ such that, as $A\to\infty$, uniformly for these choices of $w$,
$$
\begin{aligned}
Q_{6,A}(\sigma_{A,w})&\longrightarrow
\frac{\int x^6|f(x)|^2dx}{\pi^6\|f\|_2^2}
\in\left[(R/\pi)^6,((R+d_*)/\pi)^6\right],\\
A Q_{\mathcal K_A^g}(\sigma_{A,w})&\longrightarrow
\frac{\mathfrak E(f)}{4\pi^3\|f\|_2^2}>0.
\end{aligned}
\tag{W274}
$$
Thus beyond a start depending on $f$, independent of $w$, these actual sources have $Q_{\mathcal K_A^g}\ge c_0R^{7/2}\log(2+R)/A$ with a fixed $c_0>0$. This is a whole positive approximation family with arbitrary packet shape, not merely a nonzero diagonal sample. W255 also supplies a genuine $X$ neighborhood of each packet on which the actual form stays positive.

For a nonnegative real nonzero $f$, the Poisson polynomial's nonzero coefficients are positive. If its degree is $n_P$, expanding W236 gives coefficients of sign $(-1)^j$, strictly nonzero for every $0\le j\le n_P$. At all large $P$, $PR<n_P\le P(R+d_*)$. The positive physical/Gaussian weights preserve these alternating signs. Hence these sources have more than $PR$ successive sign changes in the fixed local window. Any separator for that alternating atomic source needs at least $n_P$ roots there, counting multiplicity, including the possibility of roots at atoms. W215 therefore gives $\Xi_A\ge n_Pe^{-2w}>Re^{-2w}P$. For $R$ sufficiently large at fixed $w$, they lie outside W228's fixed reciprocal-mass cap as well as outside W266's small-moment sector. No stable coefficient or gap bound is asserted.

The full original kernels, source normalization and Hardy metric are unchanged. The packet estimate is uniform in its location, but the approximation start may depend on the chosen packet. It neither proves all sources of any large fixed moment budget positive nor pays joint interference between arbitrary packets. Sufficient cofinal arbitrary-source positivity, W258 for every fixed budget, full RH and the original strict Robin inequality for every integer $n>5040$ remain unproved. No numerical threshold/start, computational certificate, Lean/kernel or CI/merge certification, exhaustive bibliography or priority is supplied.


## Integer-square interval configurations admit a joint complete-source estimate

Fix any nonempty finite set $D\subset\mathbb Z_{\ge1}$. There are $R_D,C_D,c_D>0$ such that, for every $R\ge R_D$, $0<\delta\le1$ and arbitrary independent complex profiles $g_d\in C_c^\infty((R,R+\delta))$, the physical feature
$$
f(x)=\sum_{d\in D}d^4g_d(d^2x),\qquad
S=\|\mathscr Tf\|_{L^2([\pi,\infty),x^{7/2}dx)}^2
$$
satisfies
$$
\mathfrak E(f)\ge
\left[\frac2{\sqrt\pi}\log\frac1\delta-C_D\right]S,
\qquad
c_DR^{7/2}\log(2+R)\sum_d\|g_d\|_2^2
\le S\le
C_DR^{7/2}\log(2+R)\sum_d\|g_d\|_2^2.
\tag{W275}
$$
Here $\mathfrak E$ is W255's complete actual form. A sufficiently small fixed $\delta_D>0$ therefore gives a positive joint margin for all these independent profiles. Constants may depend on the fixed finite set $D$; no uniformity as $D$ grows is asserted. The physical intervals are $(R/d^2,(R+\delta)/d^2)$, whose exact integer-square relation is part of the hypothesis. This pays cross terms for this configuration, not arbitrary interval locations or all sources of a given moment budget.

Reuse W267--W274's physical support/Gamma/cutoff mechanism, the original complete modal order W249, paired reflection W240, and W255/W257's physical/source correspondence. The additional step is a matrix estimate for the actual overlapping modal profiles, rather than positivity inferred from separate intervals. Classical harmonic sums and common-divisor Gram factorizations are consumed within that estimate; no standalone GCD-matrix theorem is added. This is paper mathematics without Lean certification or a literature-priority claim.

### Keep the overlapping profiles in one exact arithmetic matrix

Increase $R_D$ so that $R_D\ge\pi(\max D)^2$. Put $L=\lfloor\sqrt{(R+\delta)/\pi}\rfloor$ and $\ell(y)=\lfloor\sqrt{y/\pi}\rfloor$. On $[\pi,\infty)$ the complete direct features are
$$
\begin{aligned}
U=\mathscr Tf&=\sum_{n\le L}n^4h_n(n^2x),&
h_n(y)&=\sum_{\substack{d\in D\\d\mid n}}g_d(y),\\
V=\mathscr Vf&=\sum_{n\le L}n^4k_n(n^2x),&
k_n(y)&=\sum_{\substack{d\in D\\d\mid n}}\log(n/d)g_d(y).
\end{aligned}
\tag{W276}
$$
Thus the original source order is retained; $V$ is not obtained by multiplying $h_n$ by $\log n$. The $n$-th intervals are disjoint by the same geometry as W268. Different $d$ within one such interval need not be orthogonal and are never separated in the estimate.

Set $H_0=J_0=0$, $H_m=\sum_{j\le m}1/j$ and $J_m=\sum_{j\le m}(\log j)/j$. For $q=\operatorname{lcm}(d,e)$ define real symmetric matrices
$$
\begin{aligned}
\mathsf M_N(d,e)&=\frac1q H_{\lfloor N/q\rfloor},\\
\mathsf A_N(d,e)&=\frac1q\left[
2J_{\lfloor N/q\rfloor}
+(2\log q-\log d-\log e)H_{\lfloor N/q\rfloor}\right].
\end{aligned}
$$
With $\mathbf g(y)=(g_d(y))_{d\in D}$, changing variables in each actual modal interval gives exactly
$$
\begin{aligned}
S&=\int_R^{R+\delta}y^{7/2}\mathbf g(y)^*\mathsf M_{\ell(y)}\mathbf g(y)dy,\\
2\Re\langle U,V\rangle_W
&=\int_R^{R+\delta}y^{7/2}\mathbf g(y)^*\mathsf A_{\ell(y)}\mathbf g(y)dy,
\qquad W=x^{7/2}.
\end{aligned}
\tag{W277}
$$
Using $\ell(y)$ handles the partial last mode without changing the profiles or their common realization.

### Common prime-power features pay the matrix logarithmic loss

Use the classical matrices
$G(d,e)=1/\operatorname{lcm}(d,e)$ and
$K(d,e)=\log\gcd(d,e)/\operatorname{lcm}(d,e)$.
The common-divisor factorization
$G(d,e)=\sum_{r\mid d,e}\varphi(r)/(de)$ gives positive definiteness on every finite set of distinct positive integers. This is the usual GCD Gram after positive diagonal scaling. In particular its smallest eigenvalue is positive for this fixed $D$. Also
$K=\sum_{p^a\mid\operatorname{lcm}(D)}(\log p)P_{p^a}GP_{p^a}\succeq0$,
where $P_{p^a}$ is the diagonal indicator of $p^a\mid d$. This consumes $\log\gcd(d,e)=\sum_{p^a\mid d,e}\log p$ on the same finite indices; it is valid for arbitrary complex vectors.

The classical harmonic expansions, with errors uniform in this fixed finite matrix, give in operator norm
$$
\begin{aligned}
\mathsf M_N&=(\log N)G+O_D(1),\\
\mathsf A_N-(\log N)\mathsf M_N
&=-(\log N)(\gamma G+K)+O_D(1).
\end{aligned}
$$
For the second line use $H_m=\log m+\gamma+O(1/m)$ and
$J_m=\tfrac12\log^2m+c_1+O(\log(2m)/m)$. At entry $(d,e)$, $\log d+\log e-\log q=\log\gcd(d,e)$. The floor errors are $O_D((\log N)/N)$ and are bounded; $c_1$ is the common constant in that classical sum. Since $G\succ0$ and $K\succeq0$, at one $D$-dependent start,
$$
\begin{aligned}
c_D\log(2+N)I&\preceq\mathsf M_N\preceq C_D\log(2+N)I,\\
\mathsf A_N&\preceq(\log N+C_D)\mathsf M_N.
\end{aligned}
\tag{W278}
$$
No bound on the individual $g_d$ relative to their sum is assumed. Increase $R_D$ to put every $\ell(y)$ beyond this common start. W277--W278 prove W275's comparison for $S$ and give
$2\Re\langle U,V\rangle_W\le(\log L+C_D)S$.
This is the paid matrix cross term. A bound for each pure profile alone would not imply it.

### Retain the physical logarithm, cutoff and both B factors

The Mellin support of $U_0=\mathbf1_{[\pi,\infty)}U$ is contained in at most $L$ intervals of logarithmic length $\log(1+\delta/R)$. Its total measure is at most $L\delta/R$, even though all the original profiles may be independent. Apply W269's Fourier-mass inequality and W231's owned Gamma multiplier to this same $U_0$. The possible jump at $\pi$ is in the logarithmic form domain as in W247. That cutoff's two functionals are bounded in $W$ norm by the square-integrability of $y^{-7/4}$ and $k_\pi(y)y^{-7/4}$. Thus
$\mathcal D_\pi(U)\ge(2/\sqrt\pi)[\log(R/(L\delta))-C]S$.

Write $M=\sum_d\|g_d\|_2^2$. The W270 right-integral estimates now give
$\|(B-I)U\|_W\le C_D\sqrt\delta R^{3/2}\sqrt M$ and
$\|(B-I)V\|_W\le C_D\sqrt\delta R^{3/2}\log(2+R)\sqrt M$.
Indeed $|\int_z^\infty h_n|\le C_D\sqrt{\delta M}$, while the same integral for $k_n$ costs at most an extra $\log(2+n)$; sum $n^2$ up to $\sqrt{(R+\delta)/x}$ exactly as in W270. Cauchy--Schwarz and W278 also give $\|V\|_W\le C_D\log(2+R)\sqrt S$. Consequently
$|\Re\langle BU,BV\rangle_W-\Re\langle U,V\rangle_W|\le C_DS$.
The relative errors are bounded by the same $R^{-1/4}\sqrt{\log(2+R)}$ and $R^{-1/2}$ factors as in W270, with constants depending only on $D$.

The exact complete direct formula W249 therefore yields
$$
\mathfrak D_\Phi(f)
\ge\frac2{\sqrt\pi}\left[\log\frac{R}{L^2\delta}-C_D\right]S
\ge\left[\frac2{\sqrt\pi}\log\frac1\delta-C_D\right]S.
\tag{W279}
$$
Here $L^2\le(R+\delta)/\pi$. All mixed components of $V$ and the coefficient $-2$ have been retained; the leading $\log R$ is paid by the joint arithmetic matrix rather than a separate coefficient bound.

### Pay every reflected cross interval on the same source

The folded model on $U$ has absolute value at most $CS$ by W232 and the right Hardy inequality. For the exact pair sum W240 write $f_d(x)=d^4g_d(d^2x)$ and $Hf=(3/2)If/x$. There is the common bound
$|Hf(x)|\le C_D\sqrt{\delta M}/x$ for $\pi\le x<R+\delta$, and $Hf=0$ above that range. Both pair arguments are at least $\pi$; only $q=\ell k\le(R+\delta)/\pi$ can contribute. As in W272, indices $k>L$ remain in this reflected sum.

For the $f_d$--$f_e$ part, $xy=\pi^2q^2$ forces
$q\in[R/(\pi de),(R+\delta)/(\pi de)]$, an interval of length less than one. At most one integer $q$ occurs for that ordered profile pair. Its invariant-measure Cauchy bound is
$C d^4e^4\|g_d\|_2\|g_e\|_2/R$.
The factor $q^4$ in W240 cancels $d^4e^4$ at this scale. Summing divisor pairs with
$\sum_{\ell k=q,\ell<k}\tfrac12\log(k/\ell)\le C\sqrt q\log(2+q)$
and then the finitely many $d,e$ gives at most
$C_DR^{7/2}\log(2+R)M\le C_DS$.

For either $f$--$Hf$ part, $\|f\|_1\le C_D\sqrt{\delta M}$ gives after the pair coefficient a bound $C_D\delta M q^2H_{\ell k}$. The two-tail part costs $C_D\delta M q^2H_{\ell k}^2$. W272's elementary hyperbola sum bounds their totals by
$C_D\delta MR^3\log^3(2+R)\le C_DS$.
Hence, including all actual exterior corrections,
$$
|\mathfrak R_\Phi(f)|\le C_DS.
\tag{W280}
$$
Every term uses the original sum $f$ and its actual paired arguments; no independent phase, coefficient law or physical source is substituted. W279--W280 prove W275.

### The joint positive space has an actual finite-source consumer

Choose $0<\delta_D\le1$ so that W275's bracket is at least one. Then the entire direct sum of independent profile spaces above satisfies
$$
\mathfrak E(f)\ge S\ge
c_DR^{7/2}\log(2+R)\sum_d\|g_d\|_2^2>0
\quad\text{unless every }g_d=0.
\tag{W281}
$$
The physical intervals are disjoint at the chosen start, so
$\|f\|_2^2=\sum_d d^6\|g_d\|_2^2$ and
$\|x^3f\|_2^2=\sum_d d^{-6}\int_R^{R+\delta_D}y^6|g_d(y)|^2dy$.
Apply the existing W235--W236 approximation to this single $f$, with $X$ error $O_f(e^{-2A})$ chosen independently of $w$. W255 and W257 give actual original Gaussian sources on $[A,A+w)$, at most $\lceil(R+\delta_D+1)e^{2A}\rceil$ sites, normalized by $Q_H=1$, such that
$$
\begin{aligned}
Q_{6,A}(\sigma_{A,w})&\longrightarrow
\frac{\sum_d d^{-6}\int_R^{R+\delta_D}y^6|g_d(y)|^2dy}
{\pi^6\sum_d d^6\|g_d\|_2^2},\\
A Q_{\mathcal K_A^g}(\sigma_{A,w})&\longrightarrow
\frac{\mathfrak E(f)}{4\pi^3\sum_d d^6\|g_d\|_2^2}>0.
\end{aligned}
\tag{W282}
$$
For each fixed nonzero profile tuple, both limits and a positive lower margin hold beyond one start independent of $w>0$, for these selected approximants. The limiting sixth-moment ratio is at least $(R/(\pi(\max D)^2))^6$ and is unbounded as $R$ grows with $D$ fixed. The complete original kernel, Gaussian normalization and Hardy metric are unchanged. No stable coefficient or gap bound is asserted.

There is a literal prime-channel example inside this joint space. If $D$ is the divisor set of a fixed squarefree $Q$ and $g_d=\mu(d)g$, then W276 has $h_n=\mathbf1_{(n,Q)=1}g$. The corresponding cancellations are caused by the chosen source; the original kernel, logarithmic charge and reflected exterior are still complete. W281 also covers arbitrary independent complex $g_d$, not only this sieve choice. Already for $D=\{1,2\}$ and $g_1=g$, $g_2=-g$ with nonnegative $g$, it pays the genuine interaction in $f=g-16g(4\cdot)$.

For that example, the Poisson polynomial has nonnegative coefficients in its outer packet and nonpositive coefficients in its inner packet. Above the inner degree $n_{\rm in}\le P(R+\delta_D)/4$, every deconflated coefficient up to the positive outer degree $n_{\rm out}>PR$ has strict sign $(-1)^j$, with $P=e^{2A}$. There are at least $n_{\rm out}-n_{\rm in}-1>PR/2$ successive alternations at all large $P$. Roots at atoms do not evade the same local root-count argument used at W274. At fixed $w$ and large $R$ these actual sources exceed W228's reciprocal-mass cap, while their limiting moment ratio lies in $[(R/(2\pi))^6,((R+\delta_D)/(2\pi))^6]$, beyond W266. This illustrates actual cancellation, rather than positivity obtained by appending negligible atoms.

The finite set $D$, common base interval and integer-square relations are essential hypotheses of this estimate. Its constants do not justify a passage to arbitrary interval sets or an unbounded-index limit. General multi-interval coupling, W258 for EVERY fixed moment budget, full RH and the original strict Robin inequality for every integer $n>5040$ remain unproved. No numerical constants/start, computational certificate, Lean/kernel or CI/merge certification, exhaustive bibliography or literature priority is supplied.


## A joint prime-power estimate allows the interval index set to grow

There are universal $R_0,C,K,c>0$ with the following property. For every $R\ge R_0$, $0<\delta\le1$, every nonempty
$D\subset\{1,\ldots,\lfloor\sqrt{R/\pi}\rfloor\}$ and arbitrary independent complex $g_d\in C_c^\infty((R,R+\delta))$, put
$$
f(x)=\sum_{d\in D}d^4g_d(d^2x),\qquad
U=\mathscr Tf,\quad V=\mathscr Vf,\quad
S=\|U\|_{L^2([\pi,\infty),x^{7/2}dx)}^2.
$$
Then the COMPLETE actual form satisfies
$$
\mathfrak E(f)\ge
\left[\frac2{\sqrt\pi}\log\frac1\delta-C\log\log(3R)\right]S.
\tag{W283}
$$
Consequently $0<\delta\le c(\log(3R))^{-K}$ gives $\mathfrak E(f)\ge S>0$ unless all profiles vanish. If $(R,R+\delta)\cap\pi\mathbb Z=\varnothing$, the loss in W283 can instead be replaced by a universal constant, so one fixed sufficiently small width gives that same joint positive margin. All constants are independent of $D$; the index set can grow up to order $\sqrt R$. The integer-square geometry and common base interval remain hypotheses. This does not prove positivity for arbitrary supports, every fixed moment budget or RH.

Consume W249's complete direct source order, W240's full paired reflection, W269's support/Gamma estimate and W255/W257's actual-source transport. Classical Dirichlet hyperbola summation, von Mangoldt convolution, Mertens, Chebyshev and weighted Schur estimates are used inside the same-source argument. No standalone classical arithmetic or operator theorem is added. W283 pays an explicit $\log\log R$ loss across resonances; the entropy refinement W291 below replaces it by a universal constant for the same source class. This is paper mathematics without Lean certification or a literature-priority claim.

### Regroup the entire paired correction, including the integral tails

First let $f$ be any smooth compact physical feature supported below $M$. Put $b=Bf$. In W240 change variables $y=\pi s^2$ and group $m=\ell k$. Its paired correction is
$4\pi^4\sum_m m^4\int\overline{b(y)}b(\pi^2m^2/y)A_m(y)dy/y$,
where
$A_m(y)=\tfrac12\sum_{\ell k=m,\,\ell<\sqrt{y/\pi}<k}\log(k/\ell)$.
The classical rectangular hyperbola identity with cutoffs
$a=\sqrt{y/\pi}$ and $b_0=m/a$ gives
$A_m(y)=\tfrac12\sum_{r<a,\,s<b_0,\,rs\mid m}\Lambda(m/(rs))$.
Indeed summing $1*\Lambda=\log$ over the full rectangle and subtracting its complement leaves $\sum_{r<a,r\mid m}\log(m/r^2)$; the reciprocal divisors between the two cutoffs cancel. Endpoint equalities have measure zero in these integrals.

Reindex $m=qrs$, $y=r^2x$. Both cutoffs become $x>\pi$ and $\pi^2q^2/x>\pi$, while $m^4=q^4r^4s^4$. The sums at both arguments restore the SAME $\mathscr Tb=BU$. Hence the exact complete correction is
$$
\mathcal P(BU)=2\pi^4\sum_{q\ge2}\Lambda(q)q^4
\int_\pi^{\pi q^2}\overline{BU(x)}
 BU(\pi^2q^2/x)\frac{dx}{x}.
\tag{W284}
$$
Only $q\le M/\pi$ contribute. The reordering is finite on this compact class. Every $Bf$ tail, mixed pair, index beyond the direct cutoff and actual exterior correction from W240 remains; $B$ commutes with all scalar dilations. The remaining folded model on $U$ has absolute value at most $CS$ by W232 and right Hardy. Thus the actual reflection equals that model plus W284. No inverse theta or Gram comparison is used.

In logarithmic coordinates $u(t)=(\pi e^t)^{9/4}BU(\pi e^t)$, W284 is
$(2/\sqrt\pi)\sum\Lambda(q)q^{-1/2}\int_0^{2\log q}\overline{u(t)}u(2\log q-t)dt$.
It is a prime-power Hankel pairing. W249's charge is the corresponding Toeplitz pairing, since $V=\sum_q\Lambda(q)D_qU$, $D_qF(x)=q^4F(q^2x)$. This representation supplies no sign on its own. In particular the $B$ image, model and cutoff terms cannot be dropped: for compact $U$, $\int_\pi^\infty x^{3/2}BU(x)dx=\pi^{3/2}IU(\pi)$.

### Use the actual modal profiles without an inverse Gram loss

Return to the common interval $I=(R,R+\delta)$ and let $L=\lfloor\sqrt{(R+\delta)/\pi}\rfloor$, $N(y)=\lfloor\sqrt{y/\pi}\rfloor$. Keep W276's
$h_n(y)=\sum_{d\mid n}g_d(y)$ and
$k_n(y)=\sum_{d\mid n}\log(n/d)g_d(y)$, with $g_d=0$ off $D$.
Classical convolution gives $k_n=\sum_{q\mid n}\Lambda(q)h_{n/q}$. Define
$$
a_n(y)=\frac{y^{9/4}}{\sqrt n}h_n(y),\qquad n\le N(y),
\qquad
S=\int_I\sum_{n\le N(y)}|a_n(y)|^2\frac{dy}{y}.
\tag{W285}
$$
The last identity includes the partial last mode. The normalized divisor matrix $\mathcal C_y(n,j)=\Lambda(n/j)/\sqrt{n/j}$ for $j\mid n$ gives the exact local charge. Its classical weighted-Schur rows and columns, with weights $n^{-1/2}$, are $\log n$ and $\sum_{q\le N(y)/n}\Lambda(q)/q$. Mertens therefore gives $\|V\|_W\le(\log L+C)\sqrt S$.

Set $H_U=(3/2)IU/x$. Cauchy in the actual profiles, using $\sum_{n\le J}n^5\le CJ^6$, gives
$$
|H_U(x)|\le C\sqrt\delta R^{-1/4}x^{-5/2}\sqrt S,
\qquad \pi\le x<R+\delta.
\tag{W286}
$$
Use the truncated profiles $h_n\mathbf1_{y\ge\pi n^2}$ in this estimate, so no full-last-mode norm is substituted. It also gives $\|H_U\|_W\le C\sqrt\delta R^{-1/4}\sqrt S$. The same argument for $V$ costs only $\log L+C$. Therefore replacing $\Re\langle BU,BV\rangle_W$ by $\Re\langle U,V\rangle_W$ costs $CS$, uniformly in $D$.

The reflection replacement $\mathcal P(BU)=\mathcal P(U)+O(S)$ is also uniform. For a mixed term in W284, $xz=\pi^2q^2$ and W286 leave
$C\sqrt\delta R^{-1/4}\sqrt S\sum_{q\le(R+\delta)/\pi}\Lambda(q)/q\int|U(x)|x^{3/2}dx$.
The actual modal support has
$\int_{\operatorname{supp}U}x^{-1/2}dx\le C\delta R^{-1/2}\log(2+R)$.
Cauchy and Mertens bound this mixed term by
$C\delta R^{-1/2}\log^{3/2}(2+R)S$.
The two-tail term is at most
$C\delta R^{-1/2}S\sum_{q\le(R+\delta)/\pi}\Lambda(q)\log(2q)/q
\le C\delta R^{-1/2}\log^2(2+R)S$.
Both are $CS$. No source $g$ norm or number of intervals enters.

### Estimate the internal and reflected prime directions jointly

In $\mathcal P(U)$, two actual modal arguments force a single integer
$m=qnk$ with $\pi m\in I$. There is at most one such integer because $\delta\le1<\pi$. If none exists, $\mathcal P(U)=0$. Otherwise put
$y^*=\pi^2m^2/y$ and extend each $a_n$ by zero off its actual domain. Formula W284 becomes
$$
\mathcal P(U)=\frac2{\sqrt\pi}\int_I
\sum_{\substack{n\le N(y),\ k\le N(y^*)\\nk\mid m}}
\frac{\Lambda(m/(nk))}{\sqrt{m/(nk)}}
\overline{a_n(y)}a_k(y^*)\frac{dy}{y}.
\tag{W287}
$$
The involution preserves $dy/y$; this is a self-adjoint pairing on the SAME profile space. Variable $N(y)$ retains square resonances and the partial last interval. No closeness of the independent profile values at $y$ and $y^*$ is assumed.

For the joint nonnegative-entry operator $\mathcal C+\mathcal C^*+\mathcal H$, where $\mathcal H$ is W287's involution kernel, choose Schur weights
$w_n(y)=n^{-1/2}(1+n/a)$, $a=\sqrt{y/\pi}$, $t=n/a\le1$.
Write $\mathcal L(v)=\sum_{q\mid v}\Lambda(q)/q$ for positive integer $v$.
The classical divisor estimate $\mathcal L(v)\le C\log\log(3v)$ is used here; it follows from the usual prime Mertens bound by separating primes at $\log(3v)$.

The lower and upper local divisor rows are bounded respectively by
$[\log n+t\mathcal L(n)]/(1+t)$ and
$[\log(a/n)+C]/(1+t)$.
For the latter use $\sum_{q\le a/n}\Lambda(q)/q\le\log(a/n)+C$ and $t\psi(a/n)\le C$.
When $n\mid m$, the reflected row is at most
$[a/\sqrt m][t\log(m/n)+\mathcal L(m/n)]/(1+t)$; otherwise it vanishes.
This follows by substituting $k=m/(nq)$ and $q>a/n$ into the paired weight $w_k(y^*)$. Since both $y$ and $\pi m$ lie in $I$,
$a/\sqrt m=1+O(\delta/R)$ and $\log(m/a^2)=O(\delta/R)$.
The leading terms sum to $\log a+O(1)$: use
$\log n+\log(a/n)=\log a$ and $-t\log t\le1/e$.
The remaining divisor sums cost only $C\log\log(3R)$.

Weighted Schur, on the direct-integral space in W285 with its measure-preserving involution, therefore gives for arbitrary complex profiles
$$
2\Re\langle U,V\rangle_W+
\frac{\sqrt\pi}{2}\mathcal P(U)
\le[\log L+C\log\log(3R)]S.
\tag{W288}
$$
This is a joint estimate, not a sum of independently optimized sources. If no resonance integer exists, ordinary divisor Schur instead gives the sharper $[\log L+C]S$.

### Keep the full direct gain and return to actual sources

W269 and W247 applied to the SAME $U_0=\mathbf1_{[\pi,\infty)}U$ give
$\mathcal D_\pi(U)\ge(2/\sqrt\pi)[\log(R/(L\delta))-C]S$.
Its Mellin support measure is at most $L\delta/R$; the possible cutoff jump is in the owned logarithmic form domain. Use W249, W286's two $B$ errors, W284's full reflection and W288 together. The model and tail allowances cost $CS$, so
$$
\mathfrak E(f)\ge\frac2{\sqrt\pi}
\left[\log\frac{R}{L^2\delta}-C\log\log(3R)\right]S.
\tag{W289}
$$
Since $L^2\le(R+\delta)/\pi$, this proves W283. In the nonresonant case the logarithmic loss is $C$. A universal sufficiently large $K$ and small $c$ make the bracket at least one when $\delta\le c(\log(3R))^{-K}$. A fixed sufficiently small width works for every nonresonant $I$. The source is zero iff $S=0$, since the divisor transform is triangular and $D\subset\{1,\ldots,N(y)\}$ throughout $I$.

For EACH fixed nonzero tuple in either positive-width class established above, consume W235--W236 ONCE on its complete $f$, with the error chosen independently of $w>0$. W255/W257 give actual original Gaussian sources in $[A,A+w)$ with $Q_H=1$, at most $\lceil(M_f+1)e^{2A}\rceil$ sites, $M_f=(R+\delta)/(\min D)^2$, and
$$
Q_{6,A}\longrightarrow\frac{\|x^3f\|_2^2}{\pi^6\|f\|_2^2},
\qquad
A Q_{\mathcal K_A^g}\longrightarrow
\frac{\mathfrak E(f)}{4\pi^3\|f\|_2^2}>0.
\tag{W290}
$$
The start may depend on $R,D$ and the complete tuple, but is independent of $w$ for those selected approximants. The full original kernel, Hardy norm and Gaussian map are unchanged; no stable coefficient or gap bound is asserted.

There is a growing-interval consumer inside one FIXED moment budget. Take
$D\subset[\lceil\sqrt{R/\pi}/2\rceil,\lfloor\sqrt{R/\pi}\rfloor]$ and $R$ large. Then $\operatorname{supp}f\subset(\pi,5\pi)$, while $|D|$ may tend to infinity. On this band $U=f+D_2f$ and $D_2^2f=0$, so $f=U-D_2U$ and
$\|f\|_2^2\le\pi^{-7/2}(1+2^{-1/2})^2S$.
For either admitted positive-width class, W290 consequently supplies selected actual sources with limiting sixth-moment ratio at most $5^6$ and a universal positive lower limit for $A Q_{\mathcal K_A^g}$. Their count is at most $\lceil(5\pi+1)e^{2A}\rceil$. This pays arbitrary joint coefficients and independent shapes on unboundedly many intervals. It does not cover every source in that budget; the approximation starts are not uniform over all tuples or $R$.

The integer-square locations and common base interval remain hypotheses; W291 below supplies a fixed positive width through all resonances. No density passage from these sparse configurations to arbitrary compact features is established. W258 for EVERY fixed moment budget, unrestricted complete positivity, full RH and the original strict Robin inequality for every integer $n>5040$ remain unproved. No numerical constants/start, computational certificate, Lean/kernel or CI/merge certification, exhaustive bibliography or literature priority is supplied.


## Modal entropy pays the full resonance at a fixed width

There are universal $R_0,C>0$ such that for EVERY $R\ge R_0$, $0<\delta\le1$, nonempty
$D\subset\{1,\ldots,\lfloor\sqrt{R/\pi}\rfloor\}$ and arbitrary independent complex $g_d\in C_c^\infty((R,R+\delta))$, the SAME complete actual form, with
$f=\sum_{d\in D}d^4g_d(d^2x)$, $U=\mathscr Tf$ and $S=\|U\|_{L^2(x^{7/2}dx)}^2$, satisfies
$$
\mathfrak E(f)\ge
\left[\frac2{\sqrt\pi}\log\frac1\delta-C\right]S.
\tag{W291}
$$
Thus one universal sufficiently small $\delta_*>0$ gives $\mathfrak E(f)\ge S>0$ for every nonzero tuple with $\delta\le\delta_*$, including ALL resonances and growing $D$. No exclusion of $\pi\mathbb Z$ and no logarithmic shrinking of the width are needed in this class. W291 uses integer-square positions and a short common base interval; W297 below permits disconnected base sets of small total measure in a containing span $W\le R^\nu$ for each $0<\nu<1/4$. This does not establish arbitrary-support positivity, every-budget W258 or RH.

Reuse W284--W287's exact complete reflection and dimension-uniform $B$ tails, W285's SAME-source normalized modes, W249's original charge order, W269's Gamma multiplier and cutoff control, and W290's actual Gaussian return. The additional input is the classical logarithmic endpoint of the sharp fractional Sobolev inequality, consumed as an entropy lower bound on this physical feature. It is not a new logarithmic Sobolev theorem. The elementary classical divisor bound and prime-power geometric sum below are also inputs, not standalone contributions. No Lean certification or literature-priority claim is made.

### Keep the modal mass in the Gamma estimate

Use the classical one-dimensional logarithmic Sobolev inequality
$$
\int_{\mathbb R}\log|\xi|\,|\widehat v(\xi)|^2d\xi
\ge\int_{\mathbb R}|v(t)|^2\log|v(t)|^2dt-C_{\mathrm{LS}},
\qquad \|v\|_2=1,
\tag{W292}
$$
with a unitary Fourier transform. The supplier is [W. Beckner, *Pitt’s inequality and the fractional Laplacian: sharp error estimates*, arXiv:math/0701939v6, Section 2, printed page 5, equation (13)](https://arxiv.org/pdf/math/0701939v6), with its Fourier convention on printed page 2. Specialize its $L^2$ entropy form to dimension one; its $\log|v|$ becomes $\tfrac12\log|v|^2$, giving exactly the coefficient in W292. Changing the fixed Fourier convention changes only $C_{\mathrm{LS}}$. The source states the Schwartz class. For a complex profile the usual real/imaginary decomposition changes the universal constant by at most $\log2$. For our compact piecewise smooth cutoff profiles, the $O((1+|\xi|)^{-1})$ Fourier decay gives absolute integrability with the logarithmic weight. Bounded mollifications in a fixed compact set converge both in that weighted Fourier norm and in entropy, so the supplier applies by passage to the limit. This consumes the known endpoint and checks its interface with W247/W269, rather than adding a new logarithmic Sobolev theorem.

Let $I=(R,R+\delta)$, $L=\lfloor\sqrt{(R+\delta)/\pi}\rfloor$ and keep the zero-extended actual $a_n(y)$ of W285, including its variable last mode. For $S>0$ set
$$
p_n=\frac1S\int_I|a_n(y)|^2\frac{dy}{y},\qquad
\sum_{n\le L}p_n=1,\qquad
H(p)=-\sum_{n\le L}p_n\log p_n.
$$
Put $u(t)=(\pi e^t)^{9/4}U(\pi e^t)$ for $t\ge0$ and zero otherwise. Its disjoint modal intervals have logarithmic length at most $\delta/R$, and on the $n$th interval it equals $a_n(y)$ with $t=\log(y/(\pi n^2))$. Thus $\|u\|_2^2=S$. Jensen on each actual interval, omitting zero-mass intervals, gives
$\int |u|^2S^{-1}\log(|u|^2/S)dt\ge\log(R/\delta)-H(p)$.
Apply W292 to $u/\sqrt S$. W231's full multiplier, including its $|h|^2$ factor, is at least $\log|\xi|-C$, as used in W269. The rank-two cutoff correction is bounded by $CS$ in the same weight. Hence
$$
\mathcal D_\pi(U)\ge\frac2{\sqrt\pi}
\left[\log\frac R\delta-H(p)-C\right]S.
\tag{W293}
$$
There is no derivative-norm allowance or replacement of a partial last mode by a full interval. All $p_n$ come from the original independent complex profiles after their actual divisor transform.

### Charge the reflection only to its own divisor coordinates

If $I\cap\pi\mathbb Z=\varnothing$, W287 vanishes and $H(p)\le\log L$ already proves W291 by the owned direct charge estimate. Otherwise there is exactly one integer $m$ with $\pi m\in I$. Put
$$
J_m=\{n\le L:n\mid m\},\qquad
r=\sum_{n\in J_m}p_n,\qquad
T(m)=\sum_{\substack{q\mid m\\q\ge2}}\frac{\Lambda(q)}{\sqrt q}.
$$
In W287 each prime-power $q\mid m$ acts by the partial involution
$(n,y)\mapsto(m/(qn),\pi^2m^2/y)$ on the ACTUAL modal domain. It preserves counting measure times $dy/y$ on its domain, and its square is the identity there. Extension by zero makes its operator norm at most one. Both its input and output indices lie in $J_m$. Thus the entire prime-Hankel pairing, with all independent phases and reflected profile values retained, satisfies
$$
\frac{\sqrt\pi}{2}\,|\mathcal P(U)|\le T(m)\,rS.
\tag{W294}
$$
This is not a bound using a separate source norm. W286 and the mixed/two-tail estimates following it continue to pay $\mathcal P(BU)-\mathcal P(U)$ by $CS$, uniformly in $D$.

The same $r$ improves W293. Since $|J_m|\le\tau(m)$, grouping modal probabilities into $J_m$ and its complement gives
$$
H(p)\le\log L-r\log\frac L{\tau(m)}+\log2.
$$
Here $0\log0=0$, so $r=0$ and $r=1$ are included. The bound uses the full distribution of the same actual modes; it does not assume their amplitudes or phases are equal.

The classical divisor bound gives $\log\tau(m)\le\varepsilon\log m+C_\varepsilon$ for each fixed $\varepsilon>0$. Also
$T(m)\le\sum_{p\mid m}\log p/(\sqrt p-1)$.
Separating a fixed finite set of small primes from the rest gives
$T(m)\le\varepsilon\log m+C'_{\varepsilon}$, because $\sum_{p\mid m}\log p\le\log m$.
Since $\pi m\in I$ and $\delta\le1$, one has $L\ge\sqrt m/2$ for $R$ large. Fixing $\varepsilon=1/8$ therefore yields
$$
\log\frac L{\tau(m)}-T(m)\ge\frac14\log m-C.
\tag{W295}
$$
Increase the universal $R_0$ so the right side is nonnegative. No quantitative prime number theorem, inverse divisor matrix or growing-dimensional norm comparison is needed.

### Combine the gains before discarding their common mass

The original local charge still has
$2\Re\langle U,V\rangle_W\le(\log L+C)S$, by W285's ordinary divisor Schur estimate. Combine this with W293, W294, W249 and ALL owned $B$, cutoff and folded-model allowances. For the resonant case this gives
$$
\mathfrak E(f)\ge\frac2{\sqrt\pi}
\left[\log\frac R{L^2\delta}-C
+r\left(\log\frac L{\tau(m)}-T(m)\right)\right]S.
\tag{W296}
$$
W295 makes its final term nonnegative. In the nonresonant case it is absent. Since $L^2\le(R+\delta)/\pi$, both cases prove W291. The $S=0$ case is zero, and W289's triangularity gives $S>0$ for every nonzero tuple. Choose a universal $\delta_*$ so the bracket in W291 is at least one.

For EACH fixed nonzero tuple in this fixed-width positive class, apply the already owned W290 to its COMPLETE $f$. It returns actual original Gaussian finite-source families with $Q_H=1$,
$Q_{6,A}\to\|x^3f\|_2^2/(\pi^6\|f\|_2^2)$ and
$AQ_{\mathcal K_A^g}\to\mathfrak E(f)/(4\pi^3\|f\|_2^2)>0$.
The count is at most $\lceil(M_f+1)e^{2A}\rceil$, $M_f=(R+\delta)/(\min D)^2$. The start remains tuple-dependent and independent of every $w>0$ for the selected approximants. On W290's upper-half index sets, interval count can tend to infinity while the limiting sixth-moment ratio is at most $5^6$ and the lower limit for $AQ_{\mathcal K_A^g}$ is uniformly positive. This now holds at a single fixed sufficiently small width through every resonance.

The result removes the resonance-dependent width loss for these actual sources. It does not exhaust all features in that moment budget, and supplies neither a common approximation start over all tuples nor stable coefficient/gap bounds. No density passage from integer-square interval configurations to arbitrary compact features is established. Every-budget W258, unrestricted complete positivity, RH and strict Robin for EVERY integer $n>5040$ remain unproved. No numerical constants/start, computational certificate or exhaustive literature/priority claim is supplied.


## Separate shared low indices from distinct resonance blocks

There are universal $C>0$ and $\mu_*>0$ with the following property. For EACH $0<\nu<1/4$ there is $R_0(\nu)$ such that for EVERY $R\ge R_0(\nu)$, $0<W\le R^\nu$, open $E\subset(R,R+W)$ with $0<\mu=|E|\le1$, nonempty
$D\subset\{1,\ldots,\lfloor\sqrt{R/\pi}\rfloor\}$ and arbitrary independent complex $g_d\in C_c^\infty(E)$, put
$f(x)=\sum_{d\in D}d^4g_d(d^2x)$, $U=\mathscr Tf$ and $S=\|U\|_{L^2([\pi,\infty),x^{7/2}dx)}^2$. The COMPLETE actual form satisfies
$$
\mathfrak E(f)\ge
\left[\frac2{\sqrt\pi}\log\frac1\mu-C\right]S.
\tag{W297}
$$
For $0<\mu\le\mu_*$, $\mathfrak E(f)\ge S>0$ for every nonzero tuple. The constant and positive measure threshold are independent of $\nu$, component count, $D$, amplitudes and phases; the starting scale $R_0(\nu)$ may depend on $\nu$. The containing span and number of resonance cuts may grow as a power of $R$. All interactions between components are included. Integer-square positions, the restricted containing span and small TOTAL base measure remain hypotheses. This does not establish arbitrary-support positivity, every-budget W258 or RH.

Consume W284's COMPLETE prime-Hankel regrouping, W285--W286's actual modal and right-integral method, W249's original source order, the classical Beckner endpoint already supplied at W292, W293's entropy interface, W295's classical divisor inputs and W290's actual Gaussian return. The source-specific addition is a block estimate for the full collection of interacting resonance cuts. Classical divisor and prime-power identities are reused, without adding a standalone classical theorem, Lean certification or literature-priority claim.

### Use total base measure in the owned entropy and tail bounds

Set $I=(R,R+W)$, $L=\lfloor\sqrt{(R+W)/\pi}\rfloor$ and $N(y)=\lfloor\sqrt{y/\pi}\rfloor$. Keep W285's actual $h_n$, $k_n$ and $a_n=y^{9/4}h_n/\sqrt n$, zero-extended off $E$ and off $n\le N(y)$. Since $W\le R^{1/4}\ll\sqrt R$, the containing shells $I/n^2$ are disjoint for the admitted starting scale. Consequently
$S=\int_E\sum_{n\le N(y)}|a_n(y)|^2dy/y$ is exact, including the partial last mode.
For $S>0$ put $p_n=S^{-1}\int_E|a_n|^2dy/y$. Each modal Mellin support has measure at most $\mu/R$, regardless of its number of components. Jensen and the already supplied W292, applied to the SAME normalized feature with the same complex/cutoff interface, give
$$
\mathcal D_\pi(U)\ge\frac2{\sqrt\pi}
\left[\log\frac R\mu-H(p)-C\right]S.
\tag{W298}
$$
The profiles are smooth and compact even when their containing set is disconnected. Only the original cutoff can introduce a jump, and its logarithmic form domain and rank-two correction are those checked at W292--W293.

The right-integral proof W286 depends on measure rather than connectedness. In that proof use
$\int_{E\cap[n^2x,\infty)}y^{-7/2}dy\le\mu R^{-7/2}$ and
$\sum_{n\le\sqrt{(R+W)/x}}n^5\le C(R/x)^3$.
It gives
$|H_U(x)|\le C\sqrt\mu R^{-1/4}x^{-5/2}\sqrt S$ and
$\|H_U\|_W\le C\sqrt\mu R^{-1/4}\sqrt S$,
with universal constants since $R+W\le2R$. The same estimate for $V$ has the owned $\log L+C$ factor, so the direct $B$ replacement costs $CS$.
Also
$\int_{\operatorname{supp}U}x^{-1/2}dx\le C\mu R^{-1/2}\log(2+R)$.
The mixed and two-tail terms in W284 are bounded by
$C\mu R^{-1/2}\log^{3/2}(2+R)S$ and
$C\mu R^{-1/2}\log^2(2+R)S$. They cost $CS$ uniformly for $\mu\le1$. All exterior indices and the folded-model allowance remain included.

### Express every cross-component resonance on one profile space

Let $\mathcal M=\{m\ge1:\pi m\in I\}$ and $M=|\mathcal M|\le W/\pi+1$. These integers are consecutive. W284 and the actual modal supports give the COMPLETE compact-profile correction
$$
\mathcal P(U)=\frac2{\sqrt\pi}\langle a,\mathcal H a\rangle,
\qquad
(\mathcal H a)_n(y)=
\sum_{m\in\mathcal M}\sum_{\substack{k\le N(y_m^*)\\nk\mid m}}
\frac{\Lambda(m/(nk))}{\sqrt{m/(nk)}}a_k(y_m^*),
\quad y_m^*=\frac{\pi^2m^2}{y}.
\tag{W299}
$$
The space has counting measure in $n$ and $dy/y$ on each actual modal domain. Zero extension keeps precisely the pairs with $y,y_m^*\in E$. Thus components at different base positions, arbitrary complex phases and the partial last mode are retained.
For each $(m,q)$, its coordinate map $(n,y)\mapsto(m/(qn),\pi^2m^2/y)$ is a partial measure-preserving involution of norm at most one, as at W294. Put
$J=\{n\le L:n\mid m\text{ for some }m\in\mathcal M\}$,
$b=\max(1,|J|)$ and $r=\sum_{n\in J}p_n$. Both ends of every summand lie in $J$, so
$(\sqrt\pi/2)|\mathcal P(U)|\le\|\mathcal H\|\,rS$.
The reflected loss and entropy gain will therefore use the SAME actual mass $r$.

### Bound high, low and mixed index blocks

Put $B=\max(1,M)$ and split indices into $n\le B$ and $n>B$. A high index divides at most one $m\in\mathcal M$, because two such multiples would differ by at least $n>M-1$. Hence the high--high block is an orthogonal direct sum over $m$, and
$\|\mathcal H_{hh}\|\le\max_{m\in\mathcal M}T(m)$, with $T$ from W294 and empty maximum zero.

For low indices $n,k\le B$, each entry has operator norm bounded by
$C\log(3R)\sqrt{nk/R}\,[M/(nk)+1]$: there are at most $M/(nk)+1$ multiples $m$ of $nk$, and $m\asymp R$. Summing this finite symmetric numerical matrix by rows gives
$\|\mathcal H_{ll}\|\le C B^2R^{-1/2}\log(3R)$.

For $n\le B<k$, $nk>M-1$, so there is at most ONE relevant $m$ for each pair $(n,k)$. Apply the finite numerical matrix bound to the entry operator norms, followed by its Frobenius bound. The $L^2(E)$ maps themselves remain partial isometries. For any fixed $\epsilon>0$ this gives
$$
\begin{aligned}
\|\mathcal H_{lh}\|^2
&\le\sum_{m\in\mathcal M}\sum_{\substack{n\le B<k\le L\\nk\mid m}}
\frac{\Lambda(m/(nk))^2}{m/(nk)}\\
&\le C_\epsilon B^2 R^{-1/2+\epsilon}\log^2(3R).
\end{aligned}
\tag{W300}
$$
Indeed $q=m/(nk)\ge c\sqrt R/B$. For each $m,q$ there are at most $\tau(m)$ pairs. The classical bound $\tau(m)\le C_\epsilon R^\epsilon$ and the exact identity $\sum_{q\mid m}\Lambda(q)=\log m$ give
$\sum_{q\mid m,\ q\ge c\sqrt R/B}\Lambda(q)^2/q\le C B R^{-1/2}\log^2(3R)$.
Finally $M\le B$. This uses a finite matrix of operator-entry norms and retains the common profile space throughout.

Choose $\epsilon=1/4-\nu>0$. Since $B\le C R^\nu$, the low--low norm is at most $C R^{-2\epsilon}\log(3R)$ and the mixed norm at most $C_\epsilon R^{-\epsilon/2}\log(3R)$. Both are at most one after increasing $R_0(\nu)$. W295's already owned bound $T(m)\le\eta\log m+C_\eta$, with one fixed sufficiently small $\eta>0$, now gives $\|\mathcal H\|\le(1/8)\log R$ at that scale, using self-adjointness for the other mixed block.

The SAME divisor bound gives
$b\le1+C_\epsilon M R^\epsilon\le C_\nu R^{1/4}$.
As $L\ge c\sqrt R$, a further increase of $R_0(\nu)$ yields
$$
\log\frac Lb-\|\mathcal H\|\ge\frac1{16}\log R\ge0.
\tag{W301}
$$
If $M=0$, $J$ is empty, $r=0$, $\mathcal H=0$ and the same inequality holds. Constants from the divisor bound enter the starting scale; no dependence on $\nu$ is added to the final constant in W297.

### Consume the joint gain in the full form and original sources

Entropy grouping gives
$H(p)\le\log L-r\log(L/b)+\log2$, including $r=0,1$.
The original local divisor Schur bound remains
$2\Re\langle U,V\rangle_W\le(\log L+C)S$.
Combine W298--W301 with W249's ORIGINAL negative charge coefficient and ALL paid $B$, cutoff, exterior and folded-model terms. It follows that
$$
\mathfrak E(f)\ge\frac2{\sqrt\pi}
\left[\log\frac R{L^2\mu}-C
+r\left(\log\frac Lb-\|\mathcal H\|\right)\right]S.
\tag{W302}
$$
W301 pays the entire reflection on its own actual modal mass. Since $L^2\le(R+W)/\pi\le2R/\pi$, this proves W297 with universal $C$. The zero case is exact; W289's triangularity gives $S>0$ for every nonzero tuple. Choose one universal $\mu_*$ so W297 is at least $S$.

For EACH fixed nonzero tuple with $\mu\le\mu_*$, consume W290 ONCE on its COMPLETE $f$. The original Gaussian finite-source families have $Q_H=1$,
$Q_{6,A}\to\|x^3f\|_2^2/(\pi^6\|f\|_2^2)$ and
$AQ_{\mathcal K_A^g}\to\mathfrak E(f)/(4\pi^3\|f\|_2^2)>0$.
The count is at most $\lceil(M_f+1)e^{2A}\rceil$, $M_f=(R+W)/(\min D)^2$. Starts may depend on $\nu,R,W,E,D$ and the tuple, but remain independent of EVERY $w>0$ for the selected approximants. No common start or stable coefficient/gap bound is asserted.

For upper-half index sets as at W290, $\operatorname{supp}f\subset(\pi,5\pi)$ at the admitted starting scale. The existing $f=U-D_2U$ estimate gives
$\|f\|_2^2\le\pi^{-7/2}(1+2^{-1/2})^2S$.
Thus selected original-source families have limiting sixth-moment ratio at most $5^6$, a universal positive lower limit for $AQ_{\mathcal K_A^g}$ and at most $\lceil(5\pi+1)e^{2A}\rceil$ sites. The containing span, resonance count, number of base components and integer-square index count may all grow; every cross term is estimated together in this same fixed moment budget.

W297 retains small total measure and the containing span $W\le R^\nu$, $\nu<1/4$. W303--W309 below remove the total-measure restriction on full windows for each $\nu<(3-\sqrt5)/4$. These classes do not exhaust the moment budget and supply no density passage or estimate for unrestricted interacting windows. The endpoint $\nu=1/4$, every-budget W258, unrestricted complete positivity, full RH and strict Robin for EVERY integer $n>5040$ remain unproved. This is paper mathematics without Lean/kernel or computational certification and without exhaustive bibliography or literature-priority claims.


## Pay modal entropy and arithmetic charge before separating them

Put $\varphi=(1+\sqrt5)/2$ and $\kappa_0=1-\varphi/2=(3-\sqrt5)/4$. There is a universal $C>0$ with the following property. For EACH $0<\nu<1/4$ and $\eta>0$ there is $R_0(\nu,\eta)$ such that, for EVERY $R\ge R_0(\nu,\eta)$, $0<W\le R^\nu$, open $E\subset(R,R+W)$ with $0<\mu=|E|\le W$, nonempty
$D\subset\{1,\ldots,\lfloor\sqrt{R/\pi}\rfloor\}$ and arbitrary independent complex $g_d\in C_c^\infty(E)$, the SAME complete actual form satisfies
$$
\mathfrak E(f)\ge\frac2{\sqrt\pi}
\left[(\kappa_0-\eta)\log R-\log\mu-\log\log(3R)-C\right]S,
\quad
f(x)=\sum_{d\in D}d^4g_d(d^2x),\quad
S=\|\mathscr Tf\|_{L^2([\pi,\infty),x^{7/2}dx)}^2.
\tag{W303}
$$
In particular, for EACH $0<\nu<\kappa_0$ there is $R_1(\nu)$ such that EVERY $R\ge R_1(\nu)$, $0<W\le R^\nu$, admissible $D$ and arbitrary independent complex $g_d\in C_c^\infty((R,R+W))$ obey
$$
\mathfrak E(f)\ge
\frac{\kappa_0-\nu}{\sqrt\pi}\,\log R\,S>0
\quad\text{unless all }g_d=0.
\tag{W304}
$$
The small TOTAL base measure assumption is absent in W304: the profiles can fill the entire containing interval, whose length may tend to infinity. All interactions, independent phases, partial last mode and actual exterior terms remain. The integer-square geometry and containing span still restrict the source class. This does not exhaust a fixed moment budget or establish arbitrary-support positivity, every-budget W258, RH or strict Robin for every integer $n>5040$.

Reuse W249's ORIGINAL charge order, W284--W286's complete reflection and actual modes, W292/W298's already supplied Beckner entropy interface, W299--W300's full reflection blocks and W290's original Gaussian return. The classical generalized divisor coefficients, their logarithmic-derivative identity, weighted Schur, prime Mertens and Gibbs entropy bound are inputs, not new standalone results. The additional application couples entropy and the arithmetic charge through the SAME actual modal distribution, before paying the complete reflected loss. This is paper mathematics without Lean certification or a literature-priority claim.

### Use one classical weight for the actual charge and entropy

Keep $L=\lfloor\sqrt{(R+W)/\pi}\rfloor$, $N(y)=\lfloor\sqrt{y/\pi}\rfloor$ and W285's zero-extended actual profiles $a_n(y)=y^{9/4}h_n(y)/\sqrt n$. The containing shells remain disjoint because $W\ll\sqrt R$. For $S>0$ put
$p_n=S^{-1}\int_E|a_n(y)|^2dy/y$ and $m_p=\sum_{n\le L}p_n\log n$.

Use the classical generalized divisor function $d_k$ defined by $\zeta(s)^k=\sum_n d_k(n)n^{-s}$ for real $k\ge1$ and $\Re s>1$. Its positive prime-power coefficients are $d_k(p^j)=(k)_j/j!$. Consume its standard identities
$$
\sum_{q\mid n}\Lambda(q)d_k(n/q)
=\frac{\log n}{k}d_k(n),
\qquad
d_k(nq)\le d_k(n)d_k(q).
$$
Here the second inequality holds for $k\ge1$, including shared prime factors. The prime-power coefficients and the already owned prime Mertens estimate also give
$\sum_{q\le X}\Lambda(q)d_k(q)/q\le k\log X+C_k$ for $X\ge1$; prime powers of exponent at least two contribute a bounded sum for fixed $k$.

The divisor suppliers are [Bondarenko, Brevig, Saksman, Seip and Zhao, *Pseudomoments of the Riemann zeta function*, arXiv:1701.06842v3, Section 2, printed page 5, equations (8), (10)--(11)](https://arxiv.org/pdf/1701.06842v3) for the real-parameter coefficients and submultiplicativity, and [Granville, Harper and Soundararajan, *A new proof of Halász’s theorem, and its consequences*, arXiv:1706.03749v1, Section 2.2, proof of Lemma 2.5, printed page 11](https://arxiv.org/pdf/1706.03749v1) for the displayed convolution identity. These are classical inputs to the actual-source application below.

In the actual local charge matrix $\mathcal C_y$ of W285 choose the positive weights $w_n=d_\varphi(n)/\sqrt n$. Its lower and upper weighted row sums satisfy, on every actual domain,
$$
\frac{(\mathcal C_yw)_n}{w_n}=\frac{\log n}{\varphi},
\qquad
\frac{(\mathcal C_y^*w)_n}{w_n}
\le\varphi\log\frac Ln+C.
$$
The first equality retains every divisor of $n\le N(y)$; the second is an upper bound after enlarging $q\le N(y)/n$ to $q\le L/n$. The symmetric weighted-Schur quadratic bound applies pointwise to arbitrary complex $a(y)$. Since $\varphi-\varphi^{-1}=1$, integration on the SAME actual profile space gives
$$
\frac{2\Re\langle U,V\rangle_W}{S}
\le\varphi\log L-m_p+C,
\quad U=\mathscr Tf,\quad V=\mathscr Vf.
\tag{W305}
$$
This is a form bound with a retained diagonal observable; it is not an operator-norm estimate obtained by discarding that observable.

Let $\mathcal H_L=\sum_{n\le L}1/n$. The classical finite Gibbs bound relative to probabilities $1/(n\mathcal H_L)$ is
$H(p)\le m_p+\log\mathcal H_L$, including zero modal masses. Combine it with W305 before estimating either term separately:
$$
H(p)+\frac{2\Re\langle U,V\rangle_W}{S}
\le\varphi\log L+\log\mathcal H_L+C.
\tag{W306}
$$
Both occurrences of $m_p$ refer to the original independent profiles AFTER their actual divisor transform. There is no independently optimized entropy, replacement probability law or equality assumption on the amplitudes. The golden ratio enters because it solves $k-k^{-1}=1$ for this cancellation. This scalar balance does not identify these weights with a Zeckendorf address, establish an optimal exponent, or supply an unproved FIB-to-zeta implication.

### Pay every remaining term when the base measure grows

W298's Jensen/Beckner argument still gives
$\mathcal D_\pi(U)\ge(2/\sqrt\pi)[\log(R/\mu)-H(p)-C]S$ for $0<\mu\le W$; it never required $\mu\le1$. Its complex-profile, cutoff and logarithmic-form-domain interfaces are unchanged. Only the subsequent tail bounds used that upper restriction.

In W286/W298 replace the unit measure bound by the ACTUAL $\mu\le R^\nu$. The same proof gives
$|H_U(x)|\le C\sqrt\mu R^{-1/4}x^{-5/2}\sqrt S$ and
$\|H_U\|_W\le C\sqrt\mu R^{-1/4}\sqrt S$.
The analogous estimate for $V$ retains the old $\log L+C$ factor. Thus the direct $B$ replacement costs at most
$C[\sqrt\mu R^{-1/4}\log(3R)+\mu R^{-1/2}\log(3R)]S$.
The mixed and two-tail reflection bounds remain
$C\mu R^{-1/2}\log^{3/2}(3R)S$ and
$C\mu R^{-1/2}\log^2(3R)S$.
All four are at most $CS$ at an admitted $\nu$-dependent start, since $\nu<1/4<1/2$. The partial last mode is still zero-extended, and the cutoff and folded-model allowances are still bounded by $CS$.

Keep W299's COMPLETE self-adjoint reflection operator $\mathcal H$ on the same actual modal domains, including every cross-component involution. Its high, low and mixed estimates W300 give, for EACH fixed $\nu<1/4$,
$$
\|\mathcal H\|=o_\nu(\log R).
\tag{W307}
$$
Indeed the low--low and mixed norms tend to zero with the same choice $\epsilon=1/4-\nu$, while the high--high norm is at most $\max_{m\in\mathcal M}T(m)$. The already owned W295 bound $T(m)\le\rho\log m+C_\rho$ holds for EVERY fixed $\rho>0$, uniformly over $m\asymp R$. This gives W307 with no restriction on $\mu$, component count or phases. For any prescribed $\eta>0$, increasing $R_0(\nu,\eta)$ therefore makes the entire normalized reflected loss at most $\eta\log R$. No Hilbert--Schmidt claim about the infinite-dimensional partial involutions is used.

Now use W249's full negative charge coefficient, W306, the entropy lower bound and ALL the preceding actual allowances. They give
$$
\mathfrak E(f)\ge\frac2{\sqrt\pi}
\left[\log\frac R\mu-\varphi\log L-\log\mathcal H_L
-\|\mathcal H\|-C\right]S.
\tag{W308}
$$
Since $\log L\le\tfrac12\log R+C$ and $\log\mathcal H_L\le\log\log(3R)+C$, this proves W303. For $\nu<\kappa_0$, choose $\eta=(\kappa_0-\nu)/4$, use $\mu\le W\le R^\nu$, and increase the start so
$\log\log(3R)+C\le(\kappa_0-\nu)\log R/4$.
The resulting bracket is at least $(\kappa_0-\nu)\log R/2$, proving W304. The zero case is exact. W289's triangularity, with $D\subset\{1,\ldots,N(y)\}$ throughout the base interval, gives $S>0$ for every nonzero tuple.

### Return the full-width positive space to original finite sources

For EACH fixed nonzero tuple admitted by W304, consume W290 ONCE on its COMPLETE $f$. The original Gaussian finite-source families have $Q_H=1$ and
$$
Q_{6,A}\longrightarrow\frac{\|x^3f\|_2^2}{\pi^6\|f\|_2^2},
\qquad
A Q_{\mathcal K_A^g}\longrightarrow
\frac{\mathfrak E(f)}{4\pi^3\|f\|_2^2}>0.
\tag{W309}
$$
Their count is at most $\lceil(M_f+1)e^{2A}\rceil$, $M_f=(R+W)/(\min D)^2$. The approximation starts can depend on $\nu,R,W,D$ and the complete tuple; they remain independent of EVERY $w>0$ for the selected approximants. The original kernel, Gaussian normalization and Hardy metric are unchanged. No stable coefficient or gap bound is asserted.

On W290's upper-half index sets, $\operatorname{supp}f\subset(\pi,5\pi)$ and the existing bound
$\|f\|_2^2\le\pi^{-7/2}(1+2^{-1/2})^2S$ applies. Thus W304 supplies selected actual source families with limiting sixth-moment ratio at most $5^6$, a positive lower limit for $A Q_{\mathcal K_A^g}$ bounded below by a fixed positive multiple of $(\kappa_0-\nu)\log R$, and at most $\lceil(5\pi+1)e^{2A}\rceil$ sites. Both the number of physical intervals and the FULL occupied base width may grow. Positivity is proved for arbitrary joint shapes on that entire base window, without a small-total-measure or separate-component positivity premise.

W303--W309 do not prove positivity on arbitrary physical supports or unrestricted interacting base windows. W310--W316 below control the complete debit and its tail uniformly over every moment-budget source, while retaining the full Gamma term. The positive full-width spaces still do not exhaust the fixed moment budget, and no density passage or common approximation start over all tuples is supplied. The endpoint $\nu=\kappa_0$ is not proved and is not asserted to be optimal. Every-budget W258, unrestricted complete positivity, full RH and strict Robin for EVERY integer $n>5040$ remain unproved. No numerical constants/start, computational certificate, Lean/kernel or CI/merge certification, exhaustive bibliography or literature-priority claim is supplied.


## Localize the complete debit uniformly over every moment-budget source

Define, for $z\ge1$,
$$
\ell(z)=(1+\log z)^3[\log(e+\log z)]^2,
\qquad
\mathcal N(F)^2=\int_\pi^\infty (x/\pi)^4\ell(x/\pi)|F(x)|^2dx.
$$
On the owned compact smooth physical features and original Gaussian physical features put $U=\mathscr TF$, $V=\mathscr VF$. Let $\mathfrak A$ denote the Hermitian sesquilinear extension of the COMPLETE debit
$$
\mathfrak A(F,F)=\frac4{\sqrt\pi}\Re\langle BU,BV\rangle_W
+\mathfrak R_\Phi(F),
\qquad
\mathfrak E(F)=\mathcal D_\pi(\mathscr TF)-\mathfrak A(F,F).
$$
Here $\langle\cdot,\cdot\rangle_W$ uses $x^{7/2}dx$, and $\mathfrak R_\Phi$ includes both folded model channels and W284's full prime-power Hankel correction. There is a universal $C>0$ such that
$$
|\mathfrak A(F,G)|\le C\mathcal N(F)\mathcal N(G),
\qquad
\|\mathscr TF\|_W\le C\mathcal N(F).
\tag{W310}
$$
In particular the debit, but not necessarily the unbounded Gamma form, extends continuously to this fourth-moment space with its displayed logarithmic weights. No integer-square packet support, sign, atom-count, width or gap condition is used.

Fix a smooth $0\le\chi\le1$ on $[0,\infty)$, equal to one on $[0,1]$ and zero on $[2,\infty)$, and put $\chi_T(x)=\chi(x/(\pi T))$. For EVERY $K\ge1$, $T\ge2$, every $A$ beyond W246's fixed admitted start and every compact finite complex ORIGINAL Gaussian source on $[A,\infty)$ with $Q_H(\sigma)=1$ and $Q_{6,A}(\sigma)\le K$, let $F$ be its actual physical feature and $\psi=F/\|F\|_{L^2(\pi,\infty)}$. Then
$$
\left|A Q_{\mathcal K_A^g}(\sigma)
-\frac{\mathcal D_\pi(\mathscr T\psi)
-\mathfrak A(\chi_T\psi,\chi_T\psi)}{4\pi^3}\right|
\le C K\,\frac{\sqrt{\ell(T)}}T.
\tag{W311}
$$
This controls ALL cross terms between the retained physical core and its complement, uniformly over the ENTIRE original fixed-budget source class. The original full Gamma term $\mathcal D_\pi(\mathscr T\psi)$ is left intact; it is not replaced by the Gamma form of the truncated core. The right side tends to zero as $T\to\infty$ for each fixed $K$, independently of $A$, source coefficients and source count.

The same source class also has the unconditional lower floor
$$
A Q_{\mathcal K_A^g}(\sigma)
\ge-C K^{2/3}\ell(K).
\tag{W312}
$$
Its growth for large $K$ is smaller than W259's linear allowance. It is still a fixed negative allowance at fixed $K$, not W258's vanishing negative margin. W311 supplies a uniform localization of the complete debit; it supplies neither a sign for the remaining core nor a truncation of the unbounded Gamma term. Full RH and strict Robin for EVERY integer $n>5040$ remain unproved.

Reuse W231/W247's actual Gamma/cutoff interface, W232's two bounded folded channels, W249's ORIGINAL charge, W284's COMPLETE prime-power reflection and W242/W257's exact original Gaussian return. The classical Chebyshev, harmonic-sum and positive-kernel Schur/Hardy estimates below are consumed inside the physical-source transport. No standalone classical theorem, positive subclass, replacement kernel, Lean certification or literature-priority claim is added.

### Keep the entire prime Toeplitz and Hankel pairing

For a compact physical feature set $u(t)=(\pi e^t)^{9/4}B\mathscr TF(\pi e^t)$, $t\ge0$. By W249 and W284 the charge plus complete nonmodel reflection is
$(2/\sqrt\pi)\langle u,(C+C^*+H)u\rangle$, where
$$
(Cu)(t)=\sum_{q\ge2}\frac{\Lambda(q)}{\sqrt q}\,u(t+2\log q),
\qquad
(Hu)(t)=\sum_{\substack{q\ge2\\2\log q\ge t}}
\frac{\Lambda(q)}{\sqrt q}\,u(2\log q-t).
$$
These are the SAME actual $B$ image and prime-power coefficients at both arguments. The paired variable in $H$ is retained before taking absolute values. Initially all relevant sums are finite on compact physical supports.

Write $a(t)=(1+t)[\log(e+t)]^2$ and choose the positive Schur weight
$w(t)=e^{-t/4}/a(t)$. The three weighted row sums are
$$
\begin{aligned}
\frac{(Cw)(t)}{w(t)}
&=a(t)\sum_{q\ge2}\frac{\Lambda(q)}{q\,a(t+2\log q)},\\
\frac{(C^*w)(t)}{w(t)}
&=a(t)\sum_{2\log q\le t}\frac{\Lambda(q)}{a(t-2\log q)},\\
\frac{(Hw)(t)}{w(t)}
&=e^{t/2}a(t)\sum_{2\log q\ge t}
\frac{\Lambda(q)}{q\,a(2\log q-t)}.
\end{aligned}
$$
Chebyshev gives a uniformly bounded $\Lambda(q)/q$ mass on each interval of unit length in $2\log q$. Since $\sum_{j\ge0}a(j)^{-1}<\infty$, the first sum is uniformly bounded after its factor $a(t)$ is removed, and the same holds for the last sum after its displayed factor is removed. The middle row is at most $C e^{t/2}a(t)$ by $a\ge1$ and $\sum_{q\le X}\Lambda(q)\le CX$. Thus the classical symmetric weighted-Schur form bound gives
$$
|\langle u,(C+C^*+H)u\rangle|
\le C\int_0^\infty e^{t/2}a(t)|u(t)|^2dt
= C\pi^{-1/2}\int_\pi^\infty x^4a(\log(x/\pi))
|B\mathscr TF(x)|^2dx,
\tag{W313}
$$
where the constant absorbs the fixed coordinate conversion. Equivalently this Hermitian pairing is bounded bilinearly in the indicated weighted norm. This is a positive-kernel row estimate, not a Hilbert--Schmidt assertion about translation or reflection maps on $L^2$.

### Pay the critical theta sum before returning to the source

Let $g(t)=(\pi e^t)^{5/2}F(\pi e^t)$. Then exactly
$(\pi e^t)^{5/2}\mathscr TF(\pi e^t)=\sum_{n\ge1}n^{-1}g(t+2\log n)$.
Consume the classical weighted tail-Hardy estimate through Schur on this actual harmonic translation measure. After normalizing input weight $(1+t)^2a(t)$ and output weight $a(t)$, use the auxiliary Schur weight $(1+t)^{-1/2}$. The logarithmic factor's ratio is at most one along every forward shift. The row and column sums are respectively bounded by
$$
(1+t)\sum_{n\ge1}\frac1{n(1+t+2\log n)^2}\le C,
\qquad
\frac1{1+s}\sum_{n\le e^{s/2}}\frac1n\le C.
$$
These are the ordinary harmonic-sum bounds; they apply to the positive translation measure, hence to arbitrary complex profiles. Since $(1+t)^2a(t)=\ell(e^t)$, they give
$$
\int_\pi^\infty x^4a(\log(x/\pi))|\mathscr TF(x)|^2dx
\le C\int_\pi^\infty x^4\ell(x/\pi)|F(x)|^2dx.
\tag{W314}
$$
No upper support endpoint enters. Right integration in these coordinates is
$x^{5/2}(IU/x)(x)=\int_0^\infty e^{-3s/2}g_U(t+s)ds$.
The weight $a$ is increasing, so Minkowski bounds $B=1-3I/(2x)$ in the output norm of W314, with an absolute constant. That output norm also bounds $\|\mathscr TF\|_W$, since $x^{7/2}\le Cx^4a(\log(x/\pi))$.

Use W313--W314 for the complete charge and prime-power reflection, and W232/right Hardy for BOTH folded-model channels, bounded by $C\|\mathscr TF\|_W^2$. Polarization yields W310 including every cross term. Compact approximation in the displayed weighted source norm extends the debit continuously. For original Gaussian features, the already owned compact-feature convergence in W255 identifies that extension with the actual original form. Absolute positive-kernel domination also justifies the full prime-power limit; no strong $V$-domain claim on an arbitrary weighted-$L^2$ completion is needed.

The cutoff functionals in W247 are bounded in $\|\cdot\|_W$: both $y^{-7/4}$ and $k_\pi(y)y^{-7/4}$ are square integrable. The already supplied bounded-below Gamma multiplier therefore gives
$\mathcal D_\pi(\mathscr TF)\ge-C\|\mathscr TF\|_W^2$ on the owned form domain. W310 proves $\mathfrak E(F)\ge-C\mathcal N(F)^2$. This is a signed lower form bound, not an upper bound or continuity assertion for the unbounded Gamma form.

### Control every actual core-tail pair in the original budget

For $\|\psi\|_2=1$ with $\int (x/\pi)^6|\psi(x)|^2dx\le K$, elementary moment interpolation and the displayed increasing logarithmic factors give
$$
\mathcal N(\psi)^2\le C\min\{K,K^{2/3}\ell(K)\},
\qquad
\mathcal N((1-\chi_T)\psi)^2
\le CK\frac{\ell(T)}{T^2}.
\tag{W315}
$$
For the first bound, put $Y=(x/\pi)^6\ge1$, split at $Y=K$, and use
$Y^{2/3}\ell(Y^{1/6})\le C K^{2/3}\ell(K)(1+Y/K)$.
For the simpler $CK$ comparison, use directly $z^4\ell(z)\le Cz^6$. For the tail use
$\sup_{z\ge T}\ell(z)/z^2\le C\ell(T)/T^2$, for $T\ge2$. All constants are universal for this fixed weight.

Set $\psi_c=\chi_T\psi$ and $\psi_t=\psi-\psi_c$. W310 pays their complete mutual debit and the tail's own debit on the SAME realization:
$$
|\mathfrak A(\psi,\psi)-\mathfrak A(\psi_c,\psi_c)|
\le C[\mathcal N(\psi)+\mathcal N(\psi_c)]\mathcal N(\psi_t)
\le CK\frac{\sqrt{\ell(T)}}T.
\tag{W316}
$$
The cutoff core is an actual truncation of the original feature; it need not be a Gaussian finite source. Its debit is defined by the owned physical form and W310's continuous extension, rather than by assigning independent source coefficients.

For every ORIGINAL Gaussian source in the statement, W257 gives exactly
$A Q_{\mathcal K_A^g}(\sigma)=\mathfrak E(\psi)/(4\pi^3)$ and
$\int(x/\pi)^6|\psi|^2dx=Q_{6,A}(\sigma)/Q_H(\sigma)\le K$.
Apply W316 inside the exact complete form, leaving $\mathcal D_\pi(\mathscr T\psi)$ unchanged. This proves W311 uniformly over all coefficients, counts and supports in the original budget. Apply the preceding signed Gamma floor and the first bound of W315 instead to obtain W312. No selected-approximant family, density passage, source-dependent starting scale or additional sign assumption is used in these all-source conclusions.

The debit's physical tail is now uniformly small on EVERY fixed moment budget, including all core-tail interactions, while the full Gamma component remains in place. Controlling the remaining compact debit against that same Gamma component, or otherwise removing W258's fixed scaled negative deficit, is still required. The improved large-$K$ floor does not tend to zero as $A\to\infty$ at fixed $K$. Unrestricted complete positivity, every-budget W258, full RH and strict Robin for EVERY integer $n>5040$ remain unproved. This is paper mathematics without numerical constants, computational/Lean/kernel certification, exhaustive bibliography or literature-priority claims.
## Prevent bounded-energy sources from escaping a fixed physical moment budget

The complete debit has the continuous critical-moment extension W310, while the Gamma component remains unbounded. Together they give compactness for ALL bounded-above-energy sources in each fixed sixth-moment budget. The source-specific step is a finite Möbius reconstruction of the original physical feature from its COMPLETE theta image. Classical compactness and closed-form theorems are reused as suppliers, not added as new results.

Work in $H=L^2(\pi,\infty)$, with the W310 norm $\mathcal N$, and put
$$
M(F)=\int_\pi^\infty (x/\pi)^6|F(x)|^2dx,
\qquad H_6=\{F\in H:M(F)<\infty\}.
$$
All theta transforms below are the same $\mathscr TF=\sum_{n\ge1}n^4F(n^2x)$, extended by W310. Use the Gamma profile WITHOUT $B$:
$$
u_F(t)=(\pi e^t)^{9/4}\mathscr TF(\pi e^t)\quad(t\ge0),
\qquad u_F(t)=0\quad(t<0).
$$
Thus $\|u_F\|_2=\|\mathscr TF\|_W$. By W231 its real Fourier multiplier is
$$
m_\Gamma(\xi)=\frac2{\sqrt\pi}|h(9/4+i\xi)|^2
\left[\Re\operatorname{digamma}(1/4+i\xi)-\log\pi\right],
\qquad h(z)=\frac{z-5/2}{z-1}.
$$
Choose a fixed $c_\Gamma$ so that $p=m_\Gamma+c_\Gamma\ge1$. The owned multiplier is continuous, bounded below and asymptotic to $(2/\sqrt\pi)\log|\xi|$, so $p$ is comparable to $1+\log(2+|\xi|)$. Define the positive form and its specified domain
$$
\mathcal P(F)=\int_{\mathbb R}p(\xi)|\widehat u_F(\xi)|^2d\xi,
\qquad
\mathcal V=\{F\in H_6:\mathcal P(F)<\infty\}.
$$
This is an explicit finite-moment Gamma domain. W324--W326 below identify its finite-Gaussian form core, including cofinal narrow-source-window approximations. The compact smooth features in $C_c^\infty((\pi,\infty))$ belong to $\mathcal V$, which is consequently dense in $H$. Their theta image has only finitely many nonzero dilations, and its logarithmic zero extension is piecewise smooth with at most a single jump and Fourier decay $O((1+|\xi|)^{-1})$. The original finite Gaussian features belong by the owned W247/W255 interfaces and exponential decay.

### Keep the original Gamma, cutoff and complete debit together

Let $\mathcal C_\pi(U,V)$ be the Hermitian polarization of W247's rank-two cutoff. Define on $\mathcal V$
$$
\begin{aligned}
\mathfrak J(F,G)&=\mathfrak A(F,G)+\mathcal C_\pi(\mathscr TF,\mathscr TG)
+c_\Gamma\langle\mathscr TF,\mathscr TG\rangle_W,\\
\mathfrak E(F)&=\mathcal P(F)-\mathfrak J(F,F),\\
|\mathfrak J(F,G)|&\le C\mathcal N(F)\mathcal N(G),\\
|\mathfrak J(F,F)|&\le\varepsilon M(F)+C_\varepsilon\|F\|_2^2
\qquad(\varepsilon>0).
\end{aligned}
\tag{W317}
$$
This agrees exactly with $\mathcal D_\pi(\mathscr TF)-\mathfrak A(F,F)$ on the owned physical features. Both folded channels and the entire prime-power Hankel/exterior correction remain in $\mathfrak A$. The cutoff is bounded in $W$ by the two square-integrable functions already checked after W314. W310 therefore proves the third line. The last line follows from $z^4\ell(z)=o(z^6)$ by splitting at a fixed physical radius depending on $\varepsilon$. It is an infinitesimal moment bound, not an upper bound on Gamma or an assertion that the unconfined form is closed in $H$.

### Transfer compactness back through the actual theta transform

For $L,R\ge2$, W310 and W315 applied to the actual tail give
$$
\begin{aligned}
\|\mathbf1_{x\ge\pi L}\mathscr TF\|_W^2
&\le C M(F)\frac{\ell(L)}{L^2},\\
\int_{|\xi|>R}|\widehat u_F(\xi)|^2d\xi
&\le \frac{C\mathcal P(F)}{\log(2+R)}.
\end{aligned}
\tag{W318}
$$
For the first line, set $F_t=\mathbf1_{x>\pi L}F$. Above $\pi L$ the complete theta images of $F$ and $F_t$ agree almost everywhere: every dilation samples a point at least as far out. Bound the latter image in $W$ by $C\mathcal N(F_t)$ and use the moment tail. In logarithmic coordinates this is precisely the physical tail of $u_F$ outside $t\le\log L$. The second line follows from the positive multiplier $p$.

If $M(F)$ and $\mathcal P(F)$ are uniformly bounded, $u_F$ is bounded in $L^2(\mathbb R)$ and both its position and Fourier tails vanish uniformly. Apply the classical Fourier-tail compactness criterion [Hanche-Olsen--Holden, Corollary 7, arXiv:0906.4883v2, printed p.5](https://arxiv.org/abs/0906.4883v2). It gives precompactness of $\mathscr TF$ in $W$. It does not by itself give precompactness of $F$; the inverse interface must be paid.

Let $\mu(n)$ be the classical Möbius function and define the finite actual reconstruction
$$
(R_LG)(x)=\sum_{n\le\lfloor\sqrt L\rfloor}\mu(n)n^4G(n^2x).
$$
For $F_c=\mathbf1_{x\le\pi L}F$, the finite divisor identity $\sum_{d\mid k}\mu(d)=\mathbf1_{k=1}$ gives $R_L\mathscr TF_c=F_c$ almost everywhere on $[\pi,\infty)$. Moreover
$$
\begin{aligned}
\|R_L\|_{W\to H}&\le C L^{1/4},\\
\|F-R_L\mathscr TF\|_2
&\le C\sqrt{M(F)}
\left[L^{-3}+L^{-3/4}\sqrt{\ell(L)}\right]\longrightarrow0.
\end{aligned}
\tag{W319}
$$
Indeed a single term has norm
$\|n^4G(n^2\cdot)\|_2\le\pi^{-7/4}n^{-1/2}\|G\|_W$; summing to $\sqrt L$ proves the first bound. The reconstruction error is $F_t-R_L\mathscr TF_t$. Its first term is at most $L^{-3}\sqrt{M(F)}$, while W310 bounds the theta tail by $C\sqrt{M(F)\ell(L)}/L$. Multiplication by the finite inverse loss gives the second term in W319. The sharp cut is used solely for this finite reconstruction; no Gamma localization is inferred from it.

Thus bounded $M$ and $\mathcal P$ imply precompactness of $F$ in $H$: for each large fixed $L$, the bounded map $R_L$ takes the precompact theta images to a precompact family, and W319 approximates the original features uniformly. They are also precompact in $\mathcal N$. On a bounded physical interval its weight is bounded, so convergence follows from convergence in $H$; on the complement W315 makes the $\mathcal N$ tails uniformly small. This establishes the source-specific compact embedding needed below, rather than assuming a uniformly bounded full theta inverse.

### Every original negative budget sequence has a nonescaping limit

For EVERY $K>1$ and $B\in\mathbb R$, the set
$$
\mathcal S_{K,B}
=\{F\in\mathcal V:\|F\|_2=1,\ M(F)\le K,\ \mathfrak E(F)\le B\}
\quad\text{is compact in }\mathcal N.
\tag{W320}
$$
W317 and $\mathcal N(F)^2\le CM(F)$ give $\mathcal P(F)\le B+CK$, so the preceding argument gives precompactness. To check closure, let $F_j\to F$ in $\mathcal N$. The moment is lower semicontinuous by its weighted $L^2$ norm. W310 gives $u_{F_j}\to u_F$ in $L^2$, and multiplication by $p^{1/2}$ is closed and has a lower semicontinuous norm. Hence $\mathcal P(F)\le\liminf\mathcal P(F_j)$. The debit $\mathfrak J$ is continuous in $\mathcal N$, so $\mathfrak E(F)\le\liminf\mathfrak E(F_j)$. The norm, moment and energy constraints are preserved, proving W320. This argument uses lower semicontinuity of the FULL Gamma form, not its continuity or a discarded high-frequency tail.

In particular, for EVERY $K>1$,
$$
e_K=\min_{\substack{F\in\mathcal V,\ \|F\|_2=1\\M(F)\le K}}\mathfrak E(F)
\quad\text{is finite and attained in }\mathcal V.
\tag{W321}
$$
The feasible set is nonempty: normalize a smooth feature supported sufficiently close to $\pi$ so its moment is less than $K$. W317 gives a finite lower bound; a minimizing sequence lies eventually in one W320 sublevel. At $K=1$ the normalized feasible set is empty, since $(x/\pi)^6>1$ almost everywhere on $(\pi,\infty)$. No minimum or original Gaussian minimizer is claimed at that endpoint.

Now take ANY sequence of admitted ORIGINAL finite Gaussian sources, with arbitrary counts, complex coefficients, widths and gaps, satisfying $Q_H=1$, $Q_{6,A}\le K$ and $AQ_{\mathcal K_A^g}\le-\delta$ for one fixed $K>1$, $\delta>0$. Their ACTUAL normalized physical features obey, by W257,
$$
\psi_j=F_j/\|F_j\|_2,\quad
M(\psi_j)=Q_{6,A_j}/Q_H\le K,\quad
\mathfrak E(\psi_j)=4\pi^3A_jQ_{\mathcal K_{A_j}^g}\le-4\pi^3\delta.
$$
W320 supplies a subsequence converging in $\mathcal N$ to $\psi\in\mathcal V$ with $\|\psi\|_2=1$, $M(\psi)\le K$ and $\mathfrak E(\psi)\le-4\pi^3\delta$. All components come from the SAME actual features; an independently chosen theta or reflected profile has not been substituted. The limit need not be a finite Gaussian source. W327--W328 below identify the completed minimum with the cofinal original-source infimum at each exact fixed moment budget, with real and complex fields matched.

### Reuse closed-form theory with an arbitrarily small moment penalty

For EACH $\lambda>0$ put
$$
q_\lambda(F)=\mathfrak E(F)+\lambda M(F),\qquad
\operatorname{Dom}q_\lambda=\mathcal V,\qquad
q_\lambda(F)\ge\mathcal P(F)+\tfrac\lambda2M(F)-C_\lambda\|F\|_2^2.
\tag{W322}
$$
The positive reference form $\mathcal P+\lambda M$ is densely defined and closed in $H$. In fact a Cauchy sequence in its form norm converges in $H_6$; W310 gives convergence of the theta image in $W$, and the closed Fourier multiplier supplies convergence in $\mathcal P$. Apply the classical KLMN theorem to $-\mathfrak J$, using W317 with $\varepsilon=\lambda/2$. This gives a closed semibounded $q_\lambda$, with the displayed coercive bound. The supplier is [Teschl, *Mathematical Methods in Quantum Mechanics*, GSM 99 online edition, Theorem 6.24, printed p.150](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf); its closed-form representation is Theorem 2.13, printed pp.71--72. No new KLMN theorem is being proved.

The compact embedding just established applies to its bounded form-norm sets by W322. The standard closed-form compact-embedding consequence therefore gives compact resolvent for the self-adjoint operator represented by $q_\lambda$, and its normalized lowest level $\lambda_0(\lambda)$ is attained. This is on the WHOLE physical half-line with the displayed moment penalty. The already recorded [Connes--Consani--Moscovici, arXiv:2511.22755v1, Proposition 3.4 and Theorem 3.6](connesconsanimoscovici2026spectral.md) concern a fixed multiplicative support window; their form-core and discrete-spectrum results are not reproved. Here the additional interface is compactness in the ORIGINAL physical feature norm through W318--W319. No simplicity, positivity, evenness or finite-source realization of a lowest vector is asserted.

For an ACTUAL original normalized source with $Q_{6,A}\le K$ and $AQ_{\mathcal K_A^g}\le-\delta$, the same feature gives the concrete bound
$$
0<\lambda\le\frac{2\pi^3\delta}{K}
\quad\Longrightarrow\quad
\lambda_0(\lambda)\le q_\lambda(\psi)\le-2\pi^3\delta.
\tag{W323}
$$
This is a consumer of the actual normalization, not a positivity conclusion: a hypothetical fixed negative source margin survives every sufficiently weak moment penalty. Conversely no sign of $e_K$ or $\lambda_0(\lambda)$ has been established here. A completed minimizer is not identified with an admissible finite source. Compactness rules out escape of bounded-energy fixed-budget negative sequences; it does not remove their permitted negative sign. Every-budget W258, unrestricted complete positivity, full RH and strict Robin for EVERY integer $n>5040$ remain unproved. The argument is paper mathematics without Lean/kernel certification, numerical constants, an experiment, exhaustive literature coverage or a priority claim.
## Recover actual Gaussian sources from the completed physical extrema

The compactness result W320 and completed minima W321--W322 leave a realization obligation: a completed vector need not itself be a finite Gaussian feature. The missing interface is approximation in BOTH its sixth moment and FULL Gamma form norm, followed by a return to the SAME original Gaussian budget. This interface can be supplied without assuming a sign, weakening the exact budget, or imposing a lower source gap.

Use $\mathcal V$, $M$, $\mathcal P$ and the complete $\mathfrak E$ of W317--W323, and write
$$
\|F\|_{\mathcal V}^2=M(F)+\mathcal P(F).
$$
All scalar fields below are matched: for $\mathbb F\in\{\mathbb R,\mathbb C\}$ let $\mathcal V_{\mathbb F}$ be the corresponding real- or complex-valued features, and require the source coefficients to be in that SAME field. No equality of the real and complex constrained minima is assumed. Constants and approximation starts may depend on the target and tolerance; no uniform rate over the whole unit sphere is asserted.

### Approximate the theta image before reconstructing the source

The sixth-moment theta bound W238 allows the classical Möbius inverse on $H_6$:
$$
\begin{aligned}
(\mathscr SU)(x)&=\sum_{n\ge1}\mu(n)n^4U(n^2x),\\
\|\mathscr T\|_{H_6\to H_6},\ \|\mathscr S\|_{H_6\to H_6}&\le\zeta(3),
\qquad \mathscr S\mathscr T=\mathscr T\mathscr S=I.
\end{aligned}
\tag{W324}
$$
Indeed the single-dilation norm in W238 is at most $n^{-3}$. Both operator series converge absolutely in this norm, and the finite divisor inversion already used in W319 extends by that absolute convergence. This reuses classical Möbius inversion in the stronger sixth-moment space. It asserts no bounded full inverse on the weaker $W$ or $\mathcal N$ spaces.

For $F\in\mathcal V_{\mathbb F}$ put $U=\mathscr TF$ and retain the Gamma profile WITHOUT $B$,
$u(t)=(\pi e^t)^{9/4}U(\pi e^t)$ for $t\ge0$, extended by zero for $t<0$. Its two finite norms are
$\|p^{1/2}\widehat u\|_2$ and $\|e^{5t/4}u\|_2$; the square of the latter equals $\pi^{7/2}M(U)$.

Use ordinary approximate identities on this profile. First translate it to the right by $2\varepsilon$, then convolve with $\rho_\varepsilon(t)=\varepsilon^{-1}\rho(t/\varepsilon)$, where $\rho$ is real, nonnegative, smooth, supported in $[-1,1]$ and has integral one. The result is smooth, supported in $[\varepsilon,\infty)$, and converges to $u$ in BOTH norms. Put $b(\eta)=\int\rho(s)e^{i\eta s}ds$, so $|b|\le1$ and $b(0)=1$. For the Gamma norm, with W231's unitary Fourier convention, the multiplier is $e^{2i\varepsilon\xi}b(\varepsilon\xi)$; dominated convergence applies. For the exponential norm it is the usual strong continuity of translations and approximate identities in that weighted $L^2$ space, with bounded costs on a fixed small translation range. This step moves the whole zero-extended profile; it does not discard a boundary jump.

At a fixed smoothing scale the profile is in ordinary $H^1(\mathbb R)$. Multiply it by a smooth cutoff equal to one on $[-R,R]$ and zero outside $[-2R,2R]$, and let $R\to\infty$. The cutoff converges in $H^1$, hence in the Gamma norm since $p(\xi)\le C(1+|\xi|^2)$; dominated convergence gives the exponential norm as well. A diagonal choice gives compact smooth $u_j$ supported strictly inside $(0,\infty)$ in both norms. Reality is preserved when $\mathbb F=\mathbb R$. This consumes the classical smoothing operations inside the actual theta-image domain, not a new standalone density theorem.

Convert $u_j$ back to $U_j\in C_c^\infty((\pi,\infty))$ and apply $\mathscr S$. Each inverse is finite on $x\ge\pi$, because $U_j$ has compact upper support. That finite formula also defines a smooth compact feature $f_j\in C_c^\infty((0,\infty))$ whose restriction is $\mathscr SU_j$. W324 gives $M(f_j-F)\to0$, and $\mathscr Tf_j=U_j$ gives $\mathcal P(f_j-F)\to0$. Consequently
$$
f_j\longrightarrow F\quad\text{in }\mathcal V_{\mathbb F},
\qquad
M(H)+\mathcal P(H)\le C\|H\|_X^2
\quad\text{on the owned compact/Gaussian difference class.}
\tag{W325}
$$
For the last inequality use the SAME $X$ as W255. It bounds $M(H)$ and $\mathcal N(H)^2$; W255 with the zero feature bounds $|\mathfrak E(H)|$ by $C\|H\|_X^2$. W317 then bounds $\mathcal P(H)=\mathfrak E(H)+\mathfrak J(H,H)$. The Gamma form and every debit therefore stay on the same difference feature. All norm and energy passages below use this graph norm, not just $L^2$ convergence.

### Reuse the finite-source approximation in every sufficiently late narrow window

For EVERY $F\in\mathcal V_{\mathbb F}$ and $\eta>0$ there are $A_*,C>0$ such that EVERY $A\ge A_*$ and EVERY $w>0$ admit an actual finite physical source of field $\mathbb F$, whose physical feature $G$ satisfies
$$
\operatorname{supp}\mu\subset[A,A+w),\qquad
\#\operatorname{supp}\mu\le\lceil Ce^{2A}\rceil,
\qquad \|G-F\|_{\mathcal V}<\eta.
\tag{W326}
$$
First fix one compact smooth $f_j$ from W325. Apply the ALREADY transported Poisson/deconflation approximation W235--W236 to this fixed feature, with $P=e^{2A}$. Its $X$ error tends to zero for every sufficiently large real $P$; W325 transfers that error to $\mathcal V$. If $f_j$ is supported below $M_j$, the degree is at most $PM_j$, hence the displayed site count. At each such $P$, the deconflation gap may be made arbitrarily small to put all poles $P+kh$ inside $[P,Pe^{2w})$ without changing the degree. The common start and count constant therefore do not depend on $w$; the gap and coefficients may. This is the existing approximation's parameter transport, not a repeated proof of its polynomial estimate. Complex targets use its linear extension, and real targets keep real coefficients.

For any fixed admitted $A_0$, the linear space of finite Gaussian features with physical sources on $[A_0,\infty)$ is thus dense in $\mathcal V$. Since W322's shifted form norm for each fixed $\lambda>0$ is equivalent to this graph norm, it is a form core for $q_\lambda$. W326 is stronger in source placement: each approximant can be put in any sufficiently late window of any positive width. It does NOT assert density within a single fixed window $[A,A+w)$, or a uniform start for all target vectors.

### Preserve the exact budget even at a saturated minimum

For $K>1$ define
$$
e_K^{\mathbb F}=\min\{\mathfrak E(F):F\in\mathcal V_{\mathbb F},\ \|F\|_2=1,\ M(F)\le K\}.
$$
For $\mathbb F=\mathbb C$ this is W321's $e_K$; the same compactness argument applies to the closed real subspace. To approximate a saturated vector with $M(F)=K$, choose a normalized $g\in C_c^\infty((\pi,\pi K^{1/6}))$ in the same field, orthogonal to $F$ in BOTH pairings
$\langle F,g\rangle_H$ and $\int(x/\pi)^6\overline Fg\,dx$.
Such a nonzero $g$ exists: three linearly independent smooth functions in this interval satisfy two homogeneous linear constraints. Its support gives $M(g)<K$. Thus
$$
F_t=\frac{F+tg}{\sqrt{1+t^2}},\qquad
\|F_t\|_2=1,\qquad
M(F_t)=\frac{K+t^2M(g)}{1+t^2}<K\quad(t\ne0),
\qquad F_t\to F\text{ in }\mathcal V.
\tag{W327}
$$
If $M(F)<K$, no perturbation is needed. Apply W326 only after fixing this strict slack, then normalize $G$ in $H$. Both the normalized moment and complete energy converge, so the actual sources eventually obey the ORIGINAL bound $M\le K$, not merely $K+\varepsilon$. The same construction works separately in the real and complex fields; it does not convexify one field into the other.

### Identify the completed minimum with the actual cofinal optimum

Let $n(A)$ be any positive integer schedule with $n(A)e^{-2A}\to\infty$. Define $m_{A,w,n(A)}^{\mathbb F}(K)$ as the infimum of $A Q_{\mathcal K_A^g}(\sigma)$ over ORIGINAL finite Gaussian sources of field $\mathbb F$ with support in $[A,A+w)$, at most $n(A)$ active sites, $Q_H=1$ and $Q_{6,A}\le K$. For EVERY $K>1$,
$$
\lim_{A\to\infty}\ \sup_{w>0}
\left|4\pi^3m_{A,w,n(A)}^{\mathbb F}(K)-e_K^{\mathbb F}\right|=0.
\tag{W328}
$$
The source classes are nonempty for all sufficiently large $A$, uniformly over $w>0$. For the lower bound use each source's ACTUAL normalized feature and W257: $M(\psi)=Q_{6,A}/Q_H$ and $4\pi^3 A Q_{\mathcal K_A^g}=\mathfrak E(\psi)\ge e_K^{\mathbb F}$. For the upper bound choose a completed minimizer, use W327 if its budget is saturated, and apply W326 at a fixed sufficiently small tolerance. Normalize the resulting original source by W257. For every large enough $A$, its count is at most $Ce^{2A}\le n(A)$, for EVERY $w>0$, its original moment is at most $K$, and its complete normalized energy is at most $e_K^{\mathbb F}+\eta$. The start and $C$ depend on $K$, the chosen accuracy and target, but not on $w$. Let the accuracy tend to zero. This proves the displayed uniform cofinal equality without interchanging independent extrema or claiming that any finite source attains the minimum. At $K=1$ the normalized feasible set is empty, as before.

The same core also realizes W322's confined lowest level. Let $\lambda_0^{\mathbb F}(\lambda)$ be the normalized minimum of $q_\lambda$ in the indicated field, and let $r_{A,w,n(A)}^{\mathbb F}(\lambda)$ be the original-source infimum of
$A Q_{\mathcal K_A^g}+\lambda Q_{6,A}/(4\pi^3)$ with $Q_H=1$ and the same support/count constraints, without a moment cap. Then for EACH fixed $\lambda>0$,
$$
\lim_{A\to\infty}\ \sup_{w>0}
\left|4\pi^3r_{A,w,n(A)}^{\mathbb F}(\lambda)
-\lambda_0^{\mathbb F}(\lambda)\right|=0.
\tag{W329}
$$
Use W326 on a confined lowest vector and the SAME exact W257 normalization; the lower bound holds for every source. The real minimum exists by restriction of the same real-coefficient closed form and compact embedding. For $\mathbb F=\mathbb C$ this is precisely W322's lowest level. There is no uniformity claim as $\lambda\downarrow0$. In particular, a negative completed confined level would give genuinely negative original finite sources in every sufficiently late narrow window; it cannot be dismissed solely as an added-completion direction. No such negative level is exhibited here.

W324--W329 close the source-realization gap for the specified completed forms and their EXACT moment-budget minima. The completed minimizer still need not itself be finite, and no sign for $e_K^{\mathbb F}$ or $\lambda_0^{\mathbb F}(\lambda)$ has been established. These source correspondences supply neither W258's vanishing negative allowance nor unrestricted complete positivity. Full RH and strict Robin for EVERY integer $n>5040$ remain unproved. Classical Möbius inversion, approximate identities, the published polynomial approximation and closed-form facts are reused; the additional content is their joint full-Gamma/moment transport back to the original sources, with exact budgets, fields and cofinal counts. This is paper mathematics without Lean/kernel certification, numerical experiments, exhaustive literature coverage or a priority claim.

## Quantitative recovery of an entire fixed-budget energy sublevel

W326 gives a start and count constant for each target separately. Here the complete-energy upper recovery can be made quantitative and uniform over the ENTIRE normalized fixed-budget bounded-energy class. This is one-sided energy recovery, not uniform approximation in the full Gamma graph norm. The quantitative ingredients are an actual half-line Möbius commutator and a slow logarithmic cutoff; the qualitative compactness, form core and polynomial approximation are reused.

Keep the SAME $\mathcal V_{\mathbb F}$, $\mathcal P$, complete $\mathfrak J$, $\mathfrak E=\mathcal P-\mathfrak J$ and original W257 normalization, separately for $\mathbb F=\mathbb R,\mathbb C$. Constants below are universal after fixing these owned norms and smooth scalar cutoffs. They are not numerical constants or an efficient certificate bound. For $K>1$, $B\in\mathbb R$ and $0<\eta\le1$ put
$$
L=2+K+B_++\eta^{-1}+(K-1)^{-1}.
$$
There is a universal $C>0$ such that EVERY $F\in\mathcal V_{\mathbb F}$ with $\|F\|_2=1$, $M(F)\le K$, $\mathfrak E(F)\le B$, EVERY $A\ge CL^{100}$ and EVERY $w>0$ admit an ORIGINAL finite Gaussian source $\sigma$ of the SAME field, whose actual normalized feature $\psi$ satisfies
$$
\begin{gathered}
\operatorname{supp}\sigma\subset[A,A+w),\qquad
\#\operatorname{supp}\sigma\le
\left\lceil e^{CL^{100}}e^{2A}\right\rceil,\\
Q_H(\sigma)=1,\qquad Q_{6,A}(\sigma)=M(\psi)\le K,\\
\mathcal N(\psi-F)\le\eta,\qquad
4\pi^3A Q_{\mathcal K_A^g}(\sigma)
=\mathfrak E(\psi)\le\mathfrak E(F)+\eta.
\end{gathered}
\tag{W330}
$$
Neither the common start nor the count bound depends on the vector or on $w$. Gaps and coefficients may depend on all these data and are uncontrolled. The exponent $100$ is a deliberately nonsharp universal choice. This does not establish any sign of the completed or original optimum.

### A Gamma-decreasing filter with a controlled moment cost

First work on $M(F)+\mathcal P(F)\le D$, $D\ge1$. Put $U=\mathscr TF$ and use W324's zero-extended profile $u(t)=(\pi e^t)^{9/4}U(\pi e^t)$. Let $\rho$ be real, nonnegative, smooth, supported in $[-1,1]$ and of integral one. For $0<h<e^{-2}$ set $r=\log(1/h)$ and
$$
u_h(t)=\int_{-1}^1\rho(s)u(t-2h-hs)\,ds.
$$
Let $U_h$ be its physical feature and $F_h=\mathscr SU_h$, using the ACTUAL inverse W324. With $b(\xi)=\int\rho(s)e^{i\xi s}ds$, the profile multiplier is $e^{2ih\xi}b(h\xi)$, whose modulus is at most one. Thus
$$
\begin{aligned}
\mathcal P(F_h)&\le\mathcal P(F),\\
\mathcal N(F_h-F)&\le C\sqrt D\,r^{-1/5},\\
\mathfrak E(F_h)&\le\mathfrak E(F)+CD r^{-1/5},\\
\sqrt{M(F_h)}&\le e^{Ch}\sqrt{M(F)}
   +C\sqrt D\,r^{-2/5}.
\end{aligned}
\tag{W331}
$$
In particular the filter pays the FULL Gamma form, with every debit still evaluated on the same reconstructed feature. It need not preserve the original high-frequency Gamma mass.

Here are the rate-producing estimates. A frequency split at $R=h^{-1/2}$, using $|e^{2ih\xi}b(h\xi)-1|\le Ch|\xi|$ at low frequency and $p(\xi)\ge c\log(2+|\xi|)$ at high frequency, gives
$\|U_h-U\|_W^2\le CD/r$. Both inputs are bounded in $H_6$. Define $\|G\|_{H_5}^2=\int_\pi^\infty(x/\pi)^5|G|^2dx$. Interpolating physical exponents $7/2$ and $6$ to $5$ gives
$\|U_h-U\|_{H_5}\le C\sqrt D\,r^{-1/5}$. A single term $n^4G(n^2x)$ has $H_5$ norm at most $n^{-2}\|G\|_{H_5}$, so $\mathscr S$ is bounded there by $\zeta(2)$. Also $\mathcal N(G)\le C\|G\|_{H_5}$. This proves the second line, without claiming a bounded inverse in $W$. W317's complete debit bound proves the third line from the first two.

For the last line set $v=e^{5t/4}u$, so $\|v\|_2=\pi^{7/4}\sqrt{M(U)}$. In these moment-normalized coordinates the inverse is
$S_6v(t)=\sum_{n\ge1}\mu(n)n^{-3}v(t+2\log n)$ on $t\ge0$. Let $R_a$ be right translation with zero extension. For $0<a<\log4$ the commutator $[S_6,R_a]v$ is supported on $[0,a)$; only $n\ge2$ occur. The full Gamma bound gives the uniform small-interval estimate
$$
\int_I|u(t)|^2dt\le
\frac{C\mathcal P(F)}{\log(1/a)}\quad (|I|=a,\ 0<a<e^{-1}).
$$
Indeed split at $a^{-1/2}$: the low-frequency contribution is at most $Ca^{1/2}\|u\|_2^2$, and the high-frequency contribution is at most $C\mathcal P(F)/\log(1/a)$. For $h\le a\le3h$ and $n\le N$, undoing the exponential weight in the boundary strip changes $n^{-3}$ to at most $Cn^{-1/2}$. Triangle inequality therefore bounds this partial commutator by $C\sqrt{DN/r}$. The remaining terms have norm at most $C\sqrt D N^{-2}$, by their $n^{-3}$ operator tail. Taking $N$ comparable to $r^{1/5}$ yields
$$
\|[S_6,R_a]v\|_2\le C\sqrt D\,r^{-2/5}
\quad(h\le a\le3h).
\tag{W332}
$$
The weighted filter is the average of $e^{5a/4}R_a$ over these $a$. Commuting $S_6$ through this average and using W332 proves W331's moment bound. For the fixed bounded initial range of $r$, enlarge $C$; the displayed small-interval argument is needed only for large $r$. A mere use of $\|\mathscr S\|\|\mathscr T\|$ would leave a fixed budget inflation and would not prove this bound.

### Cut off slowly in logarithmic position

Choose $0\le\chi\le1$ smooth, equal to one on $(-\infty,1]$ and zero on $[2,\infty)$; put $\chi_T(t)=\chi(t/T)$, $T\ge1$. Let $U_{h,T}$ have profile $\chi_Tu_h$ and put $F_{h,T}=\mathscr SU_{h,T}$. Then
$$
\begin{aligned}
\sqrt{M(F_{h,T})}&\le\sqrt{M(F_h)}+C\sqrt D/T,\\
\mathcal N(F_{h,T}-F_h)&\le C\sqrt D e^{-T/2},\\
\mathfrak E(F_{h,T})&\le\mathfrak E(F_h)
   +CDh^{-2}e^{-T/2}.
\end{aligned}
\tag{W333}
$$
For the moment, the Lipschitz cutoff gives
$\|[S_6,\chi_T]v_h\|_2\le CT^{-1}\sum_{n\ge1}|\mu(n)|n^{-3}\log n\,\|v_h\|_2\le C\sqrt D/T$.
The multiplier $\chi_T$ is a contraction; no uniform moment tail tightness is assumed. For the second line use the $H_5$ inverse and compare its exponential weight $e^{3t/2}$ with the moment weight $e^{5t/2}$ on $t\ge T$.

For the FULL Gamma estimate use the smoothing derivative bound
$\|e^{5t/4}u_h'\|_2\le Ch^{-1}\sqrt D$. With $d=(\chi_T-1)u_h$, its $H^1$ norm is at most $C\sqrt D h^{-1}e^{-5T/4}$, so $\mathcal P(d)\le CDh^{-2}e^{-5T/2}$, where $\mathcal P(d)$ denotes the same Fourier profile norm. Cauchy--Schwarz in that norm bounds its cross term against $u_h$ by $CDh^{-1}e^{-5T/4}$. W317 and the second line bound the COMPLETE debit change by $CD e^{-T/2}$. These three terms are bounded by the last line of W333. Thus the cutoff controls the whole energy; it does not localize only a favorable Gamma channel.

The compact theta image is smooth and supported between $\pi e^h$ and $R=\pi e^{2T}$. Its W324 inverse on $x\ge\pi$ is the finite sum over $n\le\lceil e^T\rceil$. Use that SAME finite sum on $x>0$ to obtain a compact smooth extension $f_{h,T}$. It vanishes below a positive multiple of $e^{-2T}$ and above $R$. Since $\|u_h^{(j)}\|_\infty\le C_j\sqrt D h^{-j-1/2}$, differentiation of the finite inverse gives
$$
\|f_{h,T}^{(k)}\|_\infty
\le C_k\sqrt D\,h^{-k-1/2}e^{(5+2k)T},\qquad
C_{f_{h,T}}\le C\sqrt D\,h^{-7/2}e^{33T}.
\tag{W334}
$$
The last constant is precisely the owned Poisson constant from W235, bounded through $(1+x)^{10}(xf''_{h,T})'$ on $x\le R$. It is not a new polynomial approximation claim.

### Create budget slack uniformly before filtering

For the normalized class in W330, W317 gives $\mathcal P(F)\le B_++CK$. Set
$D_0=1+K+B_++(K-1)^{-2}\le CL^2$.
Choose three fixed disjoint smooth bump shapes rescaled into an interval just above $\pi$ of length $c\min(1,K-1)$, with $c$ a sufficiently small universal constant. Every point in this interval satisfies $(x/\pi)^6\le(K+1)/2$. Normalize the shapes in $H$. In their three-dimensional span choose a unit $g_F$ orthogonal to $F$ in BOTH the $H$ and moment pairings, over the SAME field. Two homogeneous linear constraints leave a nonzero choice. The uniform derivative bounds of this span and W325 give
$M(g_F)\le(K+1)/2$ and $\mathcal P(g_F)\le C[1+(K-1)^{-2}]$.

For $t=c_1\eta/D_0$ with fixed sufficiently small $c_1>0$, put $F^\circ=(F+tg_F)/\sqrt{1+t^2}$. The same two orthogonalities used in W327 now give quantitative, uniform slack:
$$
\begin{gathered}
\|F^\circ\|_2=1,\qquad
M(F^\circ)\le K-s,\qquad
s\ge c\eta^2(K-1)/D_0^2\ge cL^{-7},\\
M(F^\circ)+\mathcal P(F^\circ)\le CD_0,\qquad
\mathcal N(F^\circ-F)\le\eta/10,\qquad
\mathfrak E(F^\circ)\le\mathfrak E(F)+\eta/10.
\end{gathered}
\tag{W335}
$$
The energy bound uses polarization: both the Gamma cross term and W317's full debit cross term are at most $CD_0$. This construction applies whether or not $M(F)=K$ and keeps real and complex constraints separate.

Apply W331--W334 to $F^\circ$, with $D=CD_0$, and choose
$r=C_1L^{100}$, $h=e^{-r}$, $T=8r+1$. The $\mathcal N$ filter error is at most $CL^{-19}$, its squared-moment increase at most $CL^{-38}$, and the cutoff moment increase at most $CL^{-98}$, after adjusting universal constants. Its energy increase is at most $CL^{-18}+Ce^{-r}$. In particular the physical feature $f=f_{h,T}$ has moment at most $K-3s/4$; its norm differs from one by at most $CL^{-19}$. These bounds, including the norm error multiplied by $K$, are smaller than the slack $s\ge cL^{-7}$ at a sufficiently large universal $C_1$. Also $|\mathfrak E(f)|\le CD_0$, so the energy change from final normalization is controlled.

Now consume W235--W236 and W325 without repeating their approximation proofs. At $P=e^{2A}$, W334 gives
$$
\|G-f\|_{\mathcal V}\le C\|G-f\|_X
\le e^{C_2L^{100}}e^{-2A},\qquad
\#\operatorname{supp}\sigma\le
\left\lceil e^{C_2L^{100}}e^{2A}\right\rceil.
\tag{W336}
$$
Here $G$ is an actual finite Gaussian physical feature: choose the deconflation gap small enough to make its additional $X$ error no larger than the Poisson bound and put every source in $[A,A+w)$. The support upper bound $R$ pays the degree, uniformly over $F$. For $A\ge C_3L^{100}$, with $C_3$ sufficiently large, the graph error in W336 and the preceding $\mathcal N$ error have total effect on the squared normalization norm less than $s/(4K)$; the additional squared-moment error is less than $s/4$. Consequently normalizing $G$ to $\psi=G/\|G\|_2$ leaves $M(\psi)\le K$. The complete-energy changes in W335--W336, including normalization, total at most $\eta$, and the $\mathcal N$ errors total at most $\eta$. W257's exact return proves W330. Only the one-sided inequality for energy was used; there is no asserted uniform graph-norm approximation to the original $F$.

### A quantitative comparison for the original optimum

This uniform recovery has a consumer in W328's ACTUAL constrained optimum. A unit smooth bump supported in the interval used above has $M<K$ and energy at most $B_*(K)=C_0[1+(K-1)^{-2}]$, for a fixed sufficiently large $C_0$. Hence the completed minimum $e_K^{\mathbb F}\le B_*(K)$. Set
$L_*=2+K+B_*(K)+\eta^{-1}+(K-1)^{-1}$.
For EVERY $0<\eta\le1$, $A\ge CL_*^{100}$, $w>0$ and integer site allowance $n\ge\lceil e^{CL_*^{100}}e^{2A}\rceil$, the original infimum defined in W328 obeys
$$
0\le4\pi^3m_{A,w,n}^{\mathbb F}(K)-e_K^{\mathbb F}\le\eta.
\tag{W337}
$$
The lower bound is the existing original-source normalization, and the upper bound applies W330 to a completed minimizer with $B=B_*(K)$. The additional content is the common quantitative start/count, not another existence or spectral criterion. More generally if a member of the ENTIRE class has $\mathfrak E(F)\le-\Delta$, taking $\eta\le\min(1,\Delta/2)$ gives an original source with $A Q_{\mathcal K_A^g}\le-\Delta/(8\pi^3)$ at these same uniform bounds. No negative member is exhibited.

The estimate does not show that $e_K^{\mathbb F}$ is nonnegative, identify the real and complex minima, or reduce the count constant to W228's positive fixed fraction of $e^{2A}$. It therefore does not prove W258, unrestricted complete positivity, full RH or strict Robin for EVERY integer $n>5040$. Classical smoothing and the already cited polynomial approximation are reused; the joint quantitative inverse-boundary/cutoff estimates and their exact-budget source transport are repository-derived, without a priority claim. Bounded bibliography retrieval is not exhaustive literature coverage. This is paper mathematics without Lean/kernel certification or scientific execution.

## Retain a Gamma fraction in the actual complete prime-power debit

The [existing higher-prime-power budget](broadbent2026mertens.md#retaining-a-gamma-fraction-by-the-classical-stechkin-comparison), equation (15), supplies the classical Stechkin comparison on arbitrary compact smooth tests. It is reused. Its application to W317 needs a further interface: the actual arithmetic test is an even extension of the half-line $B$ image, whereas the original positive Gamma form uses the zero-extended theta image WITHOUT $B$. A factor-two bound would spend the available reserve. The following comparison pays this interface with a support-independent bounded error and consumes it in a lower bound for the SAME complete physical form.

Keep W317's $\mathcal V$, $\mathcal P$ and complete $\mathfrak E$. For $F\in\mathcal V$ put $U=\mathscr TF$, retain its zero-extended profile $u=u_F$, and set
$$
S(F)=\|u\|_2^2=\|U\|_W^2,\qquad
b(t)=u(t)-\frac32\int_0^\infty e^{-5s/4}u(t+s)ds\quad(t\ge0),
\qquad g_F(r)=b(2|r|).
$$
Here $b(t)=(\pi e^t)^{9/4}BU(\pi e^t)$ is the ACTUAL $B$ image, not an independently chosen arithmetic profile. Write
$$
R_g(s)=\Re\int_{\mathbb R}g(r)\overline{g(r-s)}dr,\qquad
T_1(g)=2\sum_p\frac{\log p}{\sqrt p}R_g(\log p),
\qquad \alpha=\frac2{\sqrt\pi},\quad\kappa_S=\frac1{\sqrt5}.
$$
Let $T_{\ge2}(g)$ denote the corresponding sum over $p^j$, $j\ge2$, with coefficients $(\log p)p^{-j/2}$. Reuse the shifted energy $E_*(g)$ and the nonnegative $\mathcal D_{\rm odd}(g)$ and $\mathcal J(g)$ of equations (8), (15) in the cited application. Its bounded rational-frequency energy $\mathcal J$ is distinct from W317's complete debit $\mathfrak J$.

For a universal $C$, depending only on the fixed Gamma shift of W317, EVERY $F\in\mathcal V$ satisfies
$$
\|g_F\|_2^2\le S(F),\qquad
\left|E_*(g_F)-\frac{\mathcal P(F)}\alpha\right|\le CS(F).
\tag{W338}
$$
Its SAME complete physical energy has the lower bound
$$
\mathfrak E(F)\ge
\kappa_S\mathcal P(F)-\alpha T_1(g_F)
-\frac\alpha2\left|\int_{\mathbb R}g_F\right|^2-CS(F)
+\alpha\bigl[\mathcal D_{\rm odd}(g_F)+\mathcal J(g_F)\bigr].
\tag{W339}
$$
There is no support, sign, mean, coefficient, source-count or moment-budget-size restriction within $\mathcal V$. The primary-prime correlation and mean terms remain explicit and uncontrolled against the retained reserve. Thus W339 is an all-source estimate, not positivity of $\mathfrak E$, a positive source subclass or another RH criterion.

### Pair the actual Toeplitz and Hankel channels before applying the supplier

Initially take $F\in C_c^\infty((\pi,\infty))$. Its $u$ and $b$ are smooth on the closed half-line and compact there. The even $g_F$ belongs to $H^1$, though it need not be smooth at zero. Splitting its correlation integral at $0$ and $s$ gives, for $s\ge0$,
$$
2R_{g_F}(s)=
2\Re\int_0^\infty\overline{b(t)}b(t+2s)dt
+\int_0^{2s}\overline{b(t)}b(2s-t)dt.
$$
The second integral is real by reflection. W249/W284's ENTIRE prime Toeplitz-plus-Hankel pairing is consequently
$\langle b,(C+C^*+H)b\rangle=T_1(g_F)+T_{\ge2}(g_F)$. The actual energy therefore has the identity
$$
\mathfrak E(F)=\mathcal P(F)
-\alpha[T_1(g_F)+T_{\ge2}(g_F)]-\mathcal B_0(F),
\qquad |\mathcal B_0(F)|\le CS(F).
\tag{W340}
$$
The remainder $\mathcal B_0$ retains BOTH folded-model channels, W247's rank-two cutoff and the fixed Gamma shift. Their $W$ bounds are W232/W247 and the right Hardy interface used in W317. None is discarded or counted as a separately positive reserve. Every prime power, including the first prime $2$, has its original coefficient.

### Compare the full logarithmic forms with a bounded boundary cost

Put $k=5/4$, $c=3/2$, $r_0=1/4$. On the full line let
$$
(B_{\rm full}u)(t)=u(t)-c\int_0^\infty e^{-ks}u(t+s)ds.
$$
Its Fourier multiplier has squared modulus
$|h(\xi)|^2=(\xi^2+r_0^2)/(\xi^2+k^2)\le1$.
Let $v=\mathbf1_{t\ge0}b$ and $w=B_{\rm full}u-v$. Then
$$
w(t)=-cA_ue^{kt}\mathbf1_{t<0},\qquad
A_u=\int_0^\infty e^{-ks}u(s)ds,\qquad
|A_u|^2\le\frac{S(F)}{2k}.
$$
Thus $\|b\|_2\le\|u\|_2$; the scaling and even extension defining $g_F$ preserve this norm exactly.

Use the nonnegative digamma-difference form $\mathcal A$ with multiplier
$a(\xi)=\Re\operatorname{digamma}(k+i\xi)-\operatorname{digamma}(k)$.
The classical [digamma integral, DLMF 5.9.16](https://dlmf.nist.gov/5.9.E16), gives
$$
a(\xi)=\int_0^\infty K(s)(1-\cos(\xi s))ds,
\qquad K(s)=\frac{e^{-ks}}{1-e^{-s}}\le\frac1s.
$$
For profiles supported on opposite half-lines, the off-diagonal pairing of $\mathcal A$ is minus one half of the Hankel kernel $K(s+t)$. The classical Carleman inequality used in W176--W177 bounds its modulus by $\pi/2$ times the product of the $L^2$ norms. Also $\mathcal A(w)\le C|A_u|^2$: the Fourier density of $e^{kt}\mathbf1_{t<0}$ is a constant times $(k^2+\xi^2)^{-1}$, and $a(\xi)=O(\log(2+|\xi|))$. Polarization with the ACTUAL $w$ gives
$$
|\mathcal A(v)-\mathcal A(B_{\rm full}u)|\le CS(F).
$$
To pay even extension without a factor two, put $z=(v+v(-\cdot))/\sqrt2$. Reflection invariance and the SAME off-diagonal kernel give
$$
\mathcal A(z)=\mathcal A(v)-\frac12
\int_0^\infty\int_0^\infty K(s+t)\overline{b(s)}b(t)dsdt,
\qquad |\mathcal A(z)-\mathcal A(v)|\le CS(F).
$$
The unitary scaling $g_F(r)=\sqrt2z(2r)$ yields $E_*(g_F)=\mathcal A(z)$, with the supplier's exact multiplier
$\Re\operatorname{digamma}(5/4+i\tau/2)-\operatorname{digamma}(5/4)$.
Finally digamma recurrence gives
$$
\begin{aligned}
|h(\xi)|^2a(\xi)
={}&|h(\xi)|^2
 [\Re\operatorname{digamma}(1/4+i\xi)-\log\pi]\\
&+[\log\pi-\operatorname{digamma}(5/4)]|h(\xi)|^2
+\frac{1/4}{\xi^2+25/16}.
\end{aligned}
$$
The first term is W317's unshifted $m_\Gamma/\alpha$; the two remaining multipliers and W317's fixed Gamma shift are bounded. Hence
$|\mathcal A(B_{\rm full}u)-\mathcal P(F)/\alpha|\le CS(F)$.
This proves W338 with the entire logarithmic form intact. No Fourier truncation, derivative replacement for Gamma, independently optimized profiles or loss proportional to $\mathcal P$ is used.

### Consume the signed higher-power estimate on this exact test

Let $\kappa_0=-\gamma+C_{\rm odd}$ and $d_\xi$ have their existing supplier meanings, distinct from $\kappa_S$. Its equation (15) states
$$
\begin{aligned}
T_{\ge2}(g)\le{}&\frac12\left|\int g\right|^2
+(2\kappa_0+d_\xi+2)\|g\|_2^2
+(1-\kappa_S)E_*(g)\\
&-\mathcal D_{\rm odd}(g)-\mathcal J(g).
\end{aligned}
$$
On the compact core, smooth the even $H^1$ function $g_F$ in $H^1$ with a common bounded support. The finite prime correlations, mean, shifted energy and both bounded nonnegative energies converge. The compact-smooth supplier therefore applies to this actual $g_F$. Insert it into W340, use the UPPER side of W338 with its exact leading coefficient, and absorb only bounded multiples of $S(F)$. This proves W339. Both retained nonnegative energies belong to the SAME $g_F$ as the primary-prime and mean terms.

For general $F\in\mathcal V$, use W324's existing joint full-Gamma/moment core. The theta transform is bounded in $H_6$, since its $n$th dilation has norm $n^{-3}$ and $\sum n^{-3}<\infty$. Thus $u$ has an exponentially weighted $L^2$ bound from $M(F)$; $b$ and $g_F$ have finite $L^1$ norms, and their means pass under the same core approximation. W338 applied to differences gives convergence of $g_F$ in the shifted logarithmic form. W313--W314 apply also to the primary-prime and higher-power SUBSUMS, so each arithmetic pairing passes continuously in $\mathcal N$. The two retained nonnegative energies are $L^2$-bounded. W340's bounded remainder and W317's full form pass under the same graph approximation. This proves W338--W340 on the entire specified $\mathcal V$.

For an original finite Gaussian source normalized by $Q_H(\sigma)=1$, use W257 once: with $\psi=F/\|F\|_H$, the right side of W339 evaluated at $\psi$, divided by $4\pi^3$, bounds its original $A Q_{\mathcal K_A^g}$ from below. EVERY fixed $K>1$ and every such source with $Q_{6,A}\le K$ are included at W257's admitted start; no condition on the remaining primary-prime/mean term is added.

The Gamma fraction is the existing Stechkin supplier's fraction. The additional content is the actual half-line $B$/even-extension comparison with a bounded error independent of support, and its complete-source consumer W339. W317's complete-debit bound remains independently available. The primary-prime and mean terms have not been controlled against the retained reserve, and neither constrained optimum is shown nonnegative. Full RH and strict Robin for EVERY integer $n>5040$ remain unproved. This is paper mathematics without numerical/scientific execution, Lean/kernel certification, exhaustive bibliography or a worldwide-priority claim.

## An arbitrarily large Gamma reserve after centering higher prime powers

The fixed Stechkin reserve in W339 can be strengthened by reusing an existing unconditional one-line estimate. [Hiary--Leong--Yang, *Explicit bounds for the Riemann zeta-function on the 1-line*, arXiv:2306.13289v3, Theorem 2](https://arxiv.org/html/2306.13289v3#Thmtheorem2), at $\sigma=1$, gives
$$
\left|\frac{\zeta'}{\zeta}(1+it)\right|
\le154.5\,\frac{\log t}{\log\log t}\qquad(t\ge500).
$$
Only its consequence $\zeta'/\zeta(1+it)=o(\log|t|)$ is used; negative heights follow by conjugation. This classical supplier is cited rather than reproved. [Leong, arXiv:2405.04869v5, introduction and the paragraph before Lemma 3](https://arxiv.org/html/2405.04869v5), identifies two gaps in older Trudgian estimates: a factor $1/c$ and an equal-log-exponent restriction. In the selected supplier, the local proof locators are §6, Lemma 4, footnote 7, which explicitly uses equal logarithmic exponents, and §6.1, the displayed choices of $A_2$ and $\lambda_2$, which retain the full $1/d$ term. No older erroneous constant is imported here. The published theorem is an external input; its complete proof and numerical constants are not independently certified.

Keep the angular Fourier convention and every definition of the [existing higher-power account](broadbent2026mertens.md#the-actual-even-power-boundary-pairing). To avoid confusing its regular zeta function with a physical feature, denote it here by
$$
F_{\rm reg}(s)=-\frac{\zeta'}{\zeta}(s)-\frac1{s-1},\qquad
F_{\rm reg}(1)=-\gamma.
$$
In particular the pole has already contributed the separate rank-one term $\tfrac12|\int g|^2$ in that account; it is not part of the multiplier below. For $g\in C_c^\infty(\mathbb R;\mathbb C)$ put
$$
\epsilon(g)=T_{\ge2}(g)-\frac12\left|\int g\right|^2
-2\kappa_0\|g\|_2^2,\qquad \kappa_0=-\gamma+C_{\rm odd}.
$$
For EVERY $0<\delta<1$ there is a finite $C_\delta$, independent of $g$, its support, mean and coefficients, such that
$$
\begin{aligned}
|\epsilon(g)|&\le\delta E_*(g)+C_\delta\|g\|_2^2,\\
\mathcal Z(g)&\ge(1-\delta)E_*(g)-C_\delta\|g\|_2^2.
\end{aligned}
\tag{W341}
$$
Here $\mathcal Z$, $\mathcal D_{\rm odd}$ and $\mathcal J$ are the SAME nonnegative forms as equation (8) of the cited account, and $\mathcal J$ is still distinct from the complete debit $\mathfrak J$.

Indeed its exact multiplier formula (7) is
$$
m_\epsilon(\tau)=2\Re F_{\rm reg}(1+2i\tau)
+2\Re O(\tau)-2\kappa_0.
$$
For $\tau\ne0$, $1/(2i\tau)$ has zero real part. The supplier therefore gives $\Re F_{\rm reg}(1+2i\tau)=o(\log|\tau|)$ at infinity. The function $F_{\rm reg}$ is continuous at one and on the zero-free line, so this real multiplier is bounded on every compact frequency interval. The absolutely convergent odd-power series $O$ is bounded. By the already used digamma asymptotic,
$$
a_*(\tau)=\Re\operatorname{digamma}(5/4+i\tau/2)
-\operatorname{digamma}(5/4)\sim\log|\tau|.
$$
Thus for each fixed $\delta$ a single compact-frequency split gives
$|m_\epsilon(\tau)|\le\delta a_*(\tau)+C_\delta$ at EVERY real frequency. Pair it with $|\widehat g|^2d\tau/(2\pi)$ to obtain the first line of W341. Equation (8), namely
$\mathcal Z=E_*-\epsilon+d_\xi\|g\|_2^2-\mathcal D_{\rm odd}-\mathcal J$, gives its second line because both subtracted energies are bounded by $C\|g\|_2^2$. Using that second line back in the SAME exact identity preserves the useful upper estimate
$$
\epsilon(g)\le\delta E_*(g)+C_\delta\|g\|_2^2
-\mathcal D_{\rm odd}(g)-\mathcal J(g).
$$
These are applications of the existing scalar supplier and residual identity, not new zero-free-region or logarithmic-derivative results.

### Consume the small relative expense in the entire actual form

Use the actual $u_F$, $b=Bu_F$, $g_F(r)=b(2|r|)$, $S(F)$ and $\alpha=2/\sqrt\pi$ of W338--W340. Their bounded-error Gamma comparison is reused without modification. EVERY $F\in\mathcal V$ satisfies, for the SAME $g_F$ and each fixed $0<\delta<1$,
$$
\left|\mathfrak E(F)-\mathcal P(F)+\alpha T_1(g_F)
+\frac\alpha2\left|\int g_F\right|^2\right|
\le\delta\mathcal P(F)+C_\delta S(F).
\tag{W342}
$$
The complete lower estimate can retain both independently nonnegative energies:
$$
\begin{aligned}
\mathfrak E(F)\ge{}&(1-\delta)\mathcal P(F)-\alpha T_1(g_F)
-\frac\alpha2\left|\int g_F\right|^2-C_\delta S(F)\\
&+\alpha\bigl[\mathcal D_{\rm odd}(g_F)+\mathcal J(g_F)\bigr].
\end{aligned}
\tag{W343}
$$
The constants do not depend on support, coefficients, source count or moment-budget size. They may grow as $\delta\downarrow0$. No claim with $\delta=0$ or a uniform $C_\delta$ is made.

For the proof, W340 gives the exact centered difference in W342 as
$$
-\alpha\epsilon(g_F)-2\alpha\kappa_0\|g_F\|_2^2-\mathcal B_0(F).
$$
Apply W341 and the UPPER side of W338, with $\|g_F\|_2^2\le S(F)$ and $|\mathcal B_0(F)|\le CS(F)$. This proves W342. Use instead the refined upper estimate for $\epsilon$ to obtain W343. In particular BOTH folded-model channels, the rank-two cutoff and fixed Gamma shift remain paid in $\mathcal B_0$; none is dropped or counted as a positive reserve. The primary-prime and mean terms remain the original ones on the SAME actual test.

On the compact physical core the actual even test is in $H^1$ and compactly supported, so the same smoothing passage already used for W339 applies. For all of $\mathcal V$, reuse W324's joint full-Gamma/moment core and the continuity arguments after W340. W338 on differences gives shifted-energy convergence; the mean, both arithmetic subsums, the complete form and the two bounded nonnegative energies pass under that SAME approximation. This establishes W342--W343 on the entire domain without an extra sign, parity, frequency, support or budget restriction.

For an ORIGINAL finite Gaussian source normalized by $Q_H(\sigma)=1$, W257 again applies once: evaluate the right side of W343 at its actual $\psi=F/\|F\|_H$ and divide by $4\pi^3$ to bound $A Q_{\mathcal K_A^g}$ from below. This includes EVERY fixed $K>1$ and every original source with $Q_{6,A}\le K$ at its admitted start.

The additional application is the infinitesimal FULL-Gamma expense of the centered higher-power term and its two-sided, actual-source consumer W342, with W343 retaining any fixed fraction $1-\delta$. W338's half-line interface, the pole-continuum pairing, the classical scalar estimate and the existing core are reused. This is a repository synthesis without a priority claim. The low-frequency allowance $C_\delta S$ and the SAME-source primary-prime/mean terms still need joint signed control; W342 does not make either constrained minimum nonnegative. Full RH and strict Robin for EVERY integer $n>5040$ remain unproved. This is paper mathematics without numerical/scientific execution or Lean/kernel certification.

## Extract real sources without changing the original moment budget

The real and complex problems in W328--W329 and W337 have so far been kept separate. A classical rank-one decomposition identifies their values, even at each fixed original source count and window. It suffices to preserve the moment and improve the COMPLETE energy; there is no need to preserve each prime, Gamma or folded contribution separately.

The supplier is Sturm--Zhang, *On Cones of Nonnegative Quadratic Functions*, [Mathematics of Operations Research 28 (2003), 246--267, DOI 10.1287/moor.28.2.246.14485](https://doi.org/10.1287/moor.28.2.246.14485). The exact statement used here is Proposition 4, section 5.2, printed p.18 of the [author working paper, CentER Discussion Paper 2001-26](https://pure.uvt.nl/ws/portalfiles/portal/538603/26.pdf). It says that, for a real positive semidefinite matrix $X$ of rank $r$ and a real symmetric matrix $Q$, $Q\mathbin\bullet X=0$ is equivalent to a decomposition $X=\sum_{j=1}^r z_jz_j^T$ with $z_j^TQz_j=0$ for every $j$. Here $Q\mathbin\bullet X=\operatorname{tr}(QX)$. This result is reused, not reproved; the proposition number refers to the specified working-paper version.

### Balance the actual moment before choosing a real component

Fix ANY admitted $A$, $w>0$, and finite list of distinct physical sites in $[A,A+w)$. In their original coefficient coordinates write the three actual quadratic forms as
$$
Q_H(\sigma_c)=c^*\mathbf Hc,\qquad
Q_{6,A}(\sigma_c)=c^*\mathbf Mc,\qquad
A Q_{\mathcal K_A^g}(\sigma_c)=c^*\mathbf Lc.
$$
The matrices are real symmetric: the original Gaussian weights and kernels are real, as is the physical feature map in W257. The last matrix is the COMPLETE actual kernel, including both folded channels and their correction; it is not a selected prime or model form. Also $\mathbf H\succeq0$. If a real coefficient vector has zero $\mathbf H$ form, W257 makes its actual physical feature zero in $L^2(\pi,\infty)$, so its moment and complete energy are both zero. This handles any null directions without a strict-positive-definiteness assumption.

For EVERY complex source $\sigma_c$ on these sites with $Q_H(\sigma_c)=1$, there is a real source $\sigma_d$ using only the SAME sites such that
$$
\begin{aligned}
Q_H(\sigma_d)&=1,\\
Q_{6,A}(\sigma_d)&=Q_{6,A}(\sigma_c),\\
A Q_{\mathcal K_A^g}(\sigma_d)&\le A Q_{\mathcal K_A^g}(\sigma_c).
\end{aligned}
\tag{W344}
$$
Zero coefficients may be removed, so the active count cannot increase. Arbitrary positive and negative real coefficients remain allowed. Neither a coefficient bound nor a stable numerical extraction is asserted.

To apply the supplier, put $c=x+iy$, $X=xx^T+yy^T$, and $m=c^*\mathbf Mc$. Every real symmetric matrix $D$ satisfies $D\mathbin\bullet X=c^*Dc$. Hence
$$
\mathbf H\mathbin\bullet X=1,\qquad
(\mathbf M-m\mathbf H)\mathbin\bullet X=0.
$$
Apply the cited proposition with $Q=\mathbf M-m\mathbf H$. It gives at most two vectors $z_j$, since $\operatorname{rank}X\le2$. Set $t_j=z_j^T\mathbf Hz_j\ge0$, so $\sum_jt_j=1$. Terms with $t_j=0$ have zero moment and complete energy by the actual feature factorization just stated and can be discarded. For every remaining term let $d_j=z_j/\sqrt{t_j}$. Its original norm is one and its moment is EXACTLY $m$. Moreover
$$
c^*\mathbf Lc=\sum_{j:t_j>0}t_j\,d_j^T\mathbf Ld_j.
$$
Choose a term whose energy is no larger than this average. This proves W344 on the original sites, with no extra site, support enlargement, moment slack or approximation. Taking the real or imaginary part alone would not justify this step: its normalized moment need not satisfy the original cap. The balanced decomposition is the reused input that keeps that constraint.

### The same extraction applies to the completed physical vectors

All three forms $\|F\|_H^2$, $M(F)$ and $\mathfrak E(F)$ on W317's domain are invariant under complex conjugation. For the Gamma part this uses the EVEN real multiplier $p(\xi)$ and the real theta map. The moment and all complete debit kernels are real. Consequently $\mathcal V_{\mathbb C}$ is closed under taking real and imaginary parts, and these forms split as the sum of their values on those two parts.

For EVERY $F\in\mathcal V_{\mathbb C}$ with $\|F\|_H=1$, there is
$G\in\operatorname{span}_{\mathbb R}\{\Re F,\Im F\}\subset\mathcal V_{\mathbb R}$ such that
$$
\|G\|_H=1,\qquad M(G)=M(F),\qquad
\mathfrak E(G)\le\mathfrak E(F).
\tag{W345}
$$
Indeed choose a real $H$-orthonormal basis of that span, whose dimension is one or two. Restrict the moment and complete energy to it and apply the SAME cited finite-dimensional decomposition with $\mathbf H=I$ and $Q=\mathbf M-M(F)I$. All restricted entries are finite because the span lies in $\mathcal V$. The preceding weighted-average argument gives W345. No theorem for bounded operators on the whole Hilbert space, extra dimension, closure of a joint numerical range or interchange of extrema is required.

### Consume the extraction in every fixed source problem

Use $m_{A,w,N}^{\mathbb F}(K)$ from W328, allowing any positive integer count cap $N$, and $r_{A,w,N}^{\mathbb F}(\lambda)$ from W329 with that same cap. For EVERY admitted fixed $A,w,N$, EVERY $K>1$, and EVERY $\lambda>0$,
$$
\begin{aligned}
m_{A,w,N}^{\mathbb R}(K)&=m_{A,w,N}^{\mathbb C}(K),&
r_{A,w,N}^{\mathbb R}(\lambda)&=r_{A,w,N}^{\mathbb C}(\lambda),\\
e_K^{\mathbb R}&=e_K^{\mathbb C},&
\lambda_0^{\mathbb R}(\lambda)&=\lambda_0^{\mathbb C}(\lambda).
\end{aligned}
\tag{W346}
$$
The first line follows from W344: every feasible complex source has a real source on a subset of its original sites with the SAME moment and no larger complete energy. The penalized objective also cannot increase because its moment term is unchanged. Real sources are a subset of complex sources, proving the reverse infimum inequalities. Empty normalized feasible classes match, with infimum $+\infty$; no finite-source attainment is inferred. The second line follows identically from W345 and the already existing completed minima W321--W322. In particular a real completed minimizer can be chosen with the same moment as any given complex minimizer.

Thus W328, W329 and W337 compare one common real/complex value, rather than two unconnected values. The equality holds already at EACH finite source budget, before the cofinal limit. Any uniform complete-energy lower bound proved for all signed real sources at a fixed moment cap therefore holds for all complex sources at exactly that cap, with the same start, count schedule and allowance. A hypothetical complex negative original source similarly yields a real negative source without changing its moment or introducing sites. No separate estimate for each real and imaginary component is needed.

This application removes the scalar-field distinction from the actual constrained problem; it does not restrict the signed real sources to positive coefficients or force any term of W343 to have a favorable sign. The extracted source may change its individual Gamma, primary-prime, higher-power, mean and low-frequency contributions. Their joint COMPLETE sign, nonnegativity of the common $e_K$, W258's vanishing scaled negative allowance, full RH and strict Robin for EVERY integer $n>5040$ remain unproved. The rank-one decomposition is established literature; its same-sites/exact-moment application here is a repository synthesis without a priority claim. This is paper mathematics without scientific execution, a numerical algorithm or Lean/kernel certification.

## Remove the mean by an exact null direction of the actual source form

The rank-one mean in W343 need not be estimated separately. The original odd kernel supplies a fixed zero-energy direction whose ACTUAL arithmetic profile has nonzero mean. Subtracting that direction preserves the complete energy and removes the mean. The auxiliary feature has a controlled finite moment, and no normalization of it is required. The original source's norm, count, window and moment constraints remain the ones being tested.

The classical xi null-vector and mixed-nullity results are already recorded in the [Lagarias account](lagarias2004li.md#mixed-nullity-and-the-theta-weighted-even-weil-interface), together with its full derivative family. They are not new results here. The following uses W255's own physical source map and the oddness in W38 to identify the direction in the DIFFERENT actual form $\mathfrak E$; no identity between that form and the classical full Weil form is assumed. The theta formula and its Fourier normalization are the existing [Romik supplier](../Analytic/romik2021orthogonal.md), equations (1.6)--(1.11). Adding radical vectors to adjust a functional already has a classical precedent in Connes--Consani--Marcolli, [The Weil proof and the geometry of the adeles class space](https://arxiv.org/abs/math/0703392v1), Proposition 6.4 and Lemma 7.3 (pp. 29--30 and 33). Their trace-pairing radical adjusts the degree $\widehat f(1)$ on the space in equation (4.20); this is not an identification with the present physical form or its unweighted mean $\ell(F)$. That degree-adjustment idea is reused as precedent; the bounds below concern the actual physical source and its auxiliary moment.

### Identify the mixed null direction before subtracting it

Let $F_\circ(x)=e^{-x}$ on $x\ge\pi$, and let $\mathfrak E(F,G)$ denote the Hermitian polarization of W317's complete form. Then
$$
\begin{aligned}
F_\circ&\in\mathcal V,\qquad
\mathfrak E(F_\circ,F)=0\quad(F\in\mathcal V),\\
g_{F_\circ}(r)&=\frac{\pi^{1/4}}4\Phi(r),\qquad
m_\circ:=\int_{\mathbb R}g_{F_\circ}(r)dr
=\frac{\pi^{1/4}}4\xi(1/2)>0.
\end{aligned}
\tag{W347}
$$
This is mixed nullity, not an inference from a single zero quadratic value. In W255's map the physical source $\delta_0$ has feature $F_\circ$. Since $L_0$ is odd in either argument, $L_0(0,a)=0$ for every real $a$. Polarizing the exact W255 source identity therefore gives $\mathfrak E(F_\circ,F)=0$ for every finite Gaussian source feature. The finite-feature core W326 and continuity of the polarized complete form in $M+\mathcal P$ extend this to all $\mathcal V$. The fixed feature belongs to that domain: its theta image has exponential physical decay, and its logarithmic zero extension has at most one jump, hence Fourier decay $O((1+|\xi|)^{-1})$, integrable against the owned logarithmic multiplier. Equivalently it is the same finite-Gaussian membership argument used in W317.

For its actual profile, $I\mathscr TF_\circ(x)=\sum_{n\ge1}n^2e^{-n^2x}$. Insert this into $B\mathscr TF_\circ$ and set $x=\pi e^{2|r|}$. The original theta series gives exactly $g_{F_\circ}=\pi^{1/4}\Phi/4$, with no Fourier rescaling or missing factor. The existing all-complex transform of $\Phi$ at zero and its positivity give the value and strict sign of $m_\circ$. The point $a=0$ is an auxiliary physical source, not an admitted site added to the original late-window Gaussian source.

### A fixed continuous centering map on the entire original domain

Define the linear functional and map
$$
\ell(F)=\int_{\mathbb R}g_F(r)dr,
\qquad
RF=F-\frac{\ell(F)}{m_\circ}F_\circ.
$$
There is a fixed finite $C_R$, independent of $F$, source count, support and moment-budget size, such that
$$
\begin{gathered}
RF\in\mathcal V,\qquad \ell(RF)=0,\qquad R^2F=RF,\qquad
\mathfrak E(RF)=\mathfrak E(F),\\
M(RF)\le C_RM(F),\qquad
\mathcal P(RF)\le C_R[\mathcal P(F)+M(F)].
\end{gathered}
\tag{W348}
$$
Indeed the change of variable in the ACTUAL profile gives
$$
\ell(F)=\int_\pi^\infty x^{5/4}B\mathscr TF(x)dx,\qquad
|\ell(F)|\le\sqrt{\frac25}\,\pi^{-5/4}
\|x^3B\mathscr TF\|_2\le C\sqrt{M(F)}.
$$
The last step is W238's cubic $B$ bound and W324's $H_6$ theta bound; no new Hardy or theta theorem is needed. The fixed $M(F_\circ)$ and $\mathcal P(F_\circ)$ now give both bounds in W348 by the triangle inequality in their form norms. Linearity of the actual profile gives $\ell(RF)=0$ and idempotence. W347 eliminates both mixed terms and the diagonal null term in the complete energy. The map preserves real-valued features when $F$ is real; signed coefficients are not restricted.

Neither the $H$ norm nor the auxiliary moment is asserted unchanged. In particular $RF$ can be zero. The argument never divides by $\|RF\|_H$; renormalizing it could destroy uniform control of its moment. W348 is a bounded change of the feature used to evaluate the energy, not an exact-budget replacement of the original source such as W344.

### Consume centering in the full Gamma-relative estimate

For EVERY $F\in\mathcal V$ and each fixed $0<\delta<1$, the SAME complete energy satisfies
$$
\begin{aligned}
\left|\mathfrak E(F)-\mathcal P(RF)+\alpha T_1(g_{RF})\right|
&\le\delta\mathcal P(RF)+C_\delta S(RF),\\
\mathfrak E(F)\ge{}&(1-\delta)\mathcal P(RF)-\alpha T_1(g_{RF})
-C_\delta S(RF)\\
&+\alpha[\mathcal D_{\rm odd}(g_{RF})+\mathcal J(g_{RF})].
\end{aligned}
\tag{W349}
$$
Apply the ALREADY established W342--W343 to $RF$ and use W348. This is their actual-source consumer with the mean charge eliminated exactly; their estimates and external logarithmic-derivative supplier are not reproved. Every remaining term belongs to the ONE profile $g_{RF}$. Both folded channels, their full correction, the rank-two cutoff and fixed Gamma shift stay paid as in W340. Constants have the same support/count/budget independence as before and may diverge as $\delta\downarrow0$. The positive form and primary-prime terms now use $RF$, so W349 is not claimed to dominate W343 numerically at every feature or to be a strict numerical improvement.

For an ORIGINAL source with $Q_H=1$, let $\psi=F/\|F\|_H$ be its W257 feature. Evaluate the second line of W349 at $\psi$ and divide its right side by $4\pi^3$ to bound the ORIGINAL $A Q_{\mathcal K_A^g}$. This includes EVERY original source with $Q_{6,A}\le K$ for EVERY fixed $K>1$, at the existing admitted start, with its original count and window. Its auxiliary feature obeys $M(R\psi)\le C_RK$; it is not normalized or passed off as a new source in that window. The two-sided line applies with the same exact W257 factor. It also covers $R\psi=0$, when the complete energy is zero.

Thus the explicit mean term can be removed from the actual all-source lower estimate without a sign assumption or an unpaid energy change. The remaining primary-prime term and low-frequency allowance still require a joint signed bound; their values change under $R$, and neither has been shown favorable. No nonnegativity of the common constrained minima, W258, full RH or strict Robin for EVERY integer $n>5040$ follows. The published theta/null-vector facts and W342--W343 are reused; the additional application is their exact physical null-direction realization, domain-controlled centering and original-source consumer, without a priority claim. This is paper mathematics without scientific execution or Lean/kernel certification.

## One fixed sixth-moment cap controls the entire signed source class

The previous source budgets ranged over every $K>1$. The actual mixed null direction W347 and the already established equal-moment extraction W345 give a quantitative reduction to the ONE fixed cap $4$, without losing any negative direction. The reduction is consumed below by a complete-energy bound for every original budget and by W330's original-source recovery. It does not assume the sign still sought in W349.

The quadratic mixing is classical; the rank-one extraction is the Sturm--Zhang supplier already cited in W344--W346 and is not reproved. The radical-adjustment precedent and its distinct adelic functional are recorded before W347. The application here uses the actual $e^{-x}$ direction, its actual sixth moment, and the already paid return to original Gaussian sources. No generic mixing theorem, new null-vector theorem or literature-priority claim is made.

### The fixed actual null vector fits below cap four

Retain exactly $H$, $M$, $\mathcal V$ and the COMPLETE $\mathfrak E$ of W317. Normalize the known null direction by
$$
z_\circ=\frac{e^{-x}}{\|e^{-x}\|_H}.
$$
Its moment and one convenient positive lower allowance are
$$
\begin{gathered}
\kappa_\circ:=M(z_\circ)
=\sum_{j=0}^6\binom6j\frac{j!}{(2\pi)^j}
<\frac{1223}{324}<4,\qquad c_*:=\frac{73}{324}<4-\kappa_\circ,\\
e_4:=\min_{\substack{F\in\mathcal V,\ \|F\|_H=1\\M(F)\le4}}
\mathfrak E(F)\le0.
\end{gathered}
\tag{W350}
$$
For the moment formula, substitute $x=\pi+y$ in the normalized exponential integral and integrate its degree-six polynomial expansion. Using $\pi>3$ bounds their sum by
$1+1+5/6+5/9+5/18+5/54+5/324=1223/324$.
The minimum is finite and attained by W321, agrees in both fields by W346, and is nonpositive because $z_\circ$ is feasible and has complete energy zero by W347. No nonnegative lower bound for it has been established.

### Compress an arbitrary signed feature and quantify its full energy

Define, for $m>1$,
$$
\theta_4(m)=
\begin{cases}
1,&m\le4,\\
(4-\kappa_\circ)/(m-\kappa_\circ),&m>4.
\end{cases}
$$
For EVERY $F\in\mathcal V_{\mathbb C}$ with $\|F\|_H=1$, writing $m=M(F)$, there is a REAL $G\in\mathcal V$ such that
$$
\|G\|_H=1,\qquad M(G)=\min(m,4),\qquad
\mathfrak E(G)\le\theta_4(m)\mathfrak E(F).
\tag{W351}
$$
First apply W345 to obtain a real unit $v$ with moment $m$ and complete energy no larger than that of $F$. If $m\le4$, take $G=v$. Otherwise set
$$
t^2=\frac{m-4}{4-\kappa_\circ},\qquad
Y=\frac{v+it z_\circ}{\sqrt{1+t^2}}.
$$
Since $v$ and $z_\circ$ are real, their cross terms in both the $H$ norm and moment vanish in this complex combination. W347 gives
$$
\|Y\|_H=1,\qquad M(Y)=4,\qquad
\mathfrak E(Y)=\frac{\mathfrak E(v)}{1+t^2}
\le\theta_4(m)\mathfrak E(F).
$$
Reuse W345 on $Y$ to extract the required real $G$ with the SAME moment and no larger COMPLETE energy. Thus complex mixing creates no restriction to complex final sources. Individual Gamma, prime and folded contributions are not asserted unchanged.

In particular, if $\mathfrak E(F)\le-\Delta<0$, put $d=\theta_4(m)\Delta$. Then
$\mathfrak E(G)\le-d$ and $d\ge c_*\Delta/m>0$.
The retained margin depends on the original feature; no universal negative margin or efficient extraction algorithm is claimed.

### Consume the reduction in every original budget

For $K>1$ set
$$
D_4(K)=\max\left(1,\frac{K-\kappa_\circ}{4-\kappa_\circ}\right).
$$
The SAME existing completed minima satisfy
$$
\begin{gathered}
e_K\ge D_4(K)e_4\quad(K>1),\qquad
e_K\le e_4\quad(K\ge4),\\
\mathfrak E(F)\ge\frac{e_4}{c_*}M(F)\quad(F\in\mathcal V).
\end{gathered}
\tag{W352}
$$
Indeed W351 makes $G$ feasible for $e_4$, so
$\mathfrak E(F)\ge e_4/\theta_4(m)$ for every unit $F$. For $m\le K$, the reciprocal is at most $D_4(K)$; since $e_4\le0$, this gives the first lower bound. Set inclusion gives the upper bound for $K\ge4$. Also $1/\theta_4(m)\le m/c_*$ for every $m>1$. Homogeneity now gives the global moment bound, including the zero feature.

This has a SAME-original-source consumer through W257. For every admitted original normalized source with $Q_H=1$ and $Q_{6,A}\le K$,
$$
4\pi^3 A Q_{\mathcal K_A^g}\ge D_4(K)e_4.
$$
Without normalization, every admitted finite original source obeys
$$
A Q_{\mathcal K_A^g}\ge\frac{e_4}{4\pi^3c_*}Q_{6,A}.
$$
These include arbitrary real or complex coefficients, counts and widths, with the ENTIRE kernel retained. The new coefficient is an unevaluated actual minimum, not a certified favorable number or a numerical improvement over earlier constants. A finite-source trial value supplies an upper bound on $e_4$; it cannot be inserted as its lower certificate.

### Return every compressed negative direction to legal original sources

The auxiliary $z_\circ$ is not a new site inserted in the original late window. Apply the existing recovery W330 to W351's completed $G$, at the exact budget $K=4$ and $B=0$. With
$$
\eta=\min(1,d/2),\qquad L=19/3+\eta^{-1},
$$
there is the SAME universal recovery constant $C$ such that EVERY $A\ge CL^{100}$ and EVERY $w>0$ admit a real ORIGINAL source satisfying
$$
\begin{gathered}
\operatorname{supp}\sigma\subset[A,A+w),\qquad
\#\operatorname{supp}\sigma\le\left\lceil e^{CL^{100}}e^{2A}\right\rceil,\\
Q_H(\sigma)=1,\qquad Q_{6,A}(\sigma)\le4,\qquad
A Q_{\mathcal K_A^g}(\sigma)\le-\frac{d}{8\pi^3}<0.
\end{gathered}
\tag{W353}
$$
W330 pays its own strict-slack step even when $M(G)=4$, and gives $\mathfrak E(\psi)\le\mathfrak E(G)+\eta\le-d/2$ for the recovered normalized feature. W257 supplies the displayed original factor. No original count, sites, gap or coefficient bound is asserted preserved by this recovery.

Consequently the conditional negative witnesses of W254, if any exist, can ALL be chosen inside the fixed original cap $4$ rather than a seed-dependent moment cap. This captures every possible negative direction; it does not replace the original goal by a positive subclass. W328/W337 already identify and approximate precisely this $e_4$ by actual cap-four source extrema. A vanishing lower allowance at that single cap would therefore pay all the other budgets through W352; such an allowance remains unproved.

The current W349 estimate can likewise be tested only on the normalized cap-four class when trying to exclude arbitrary negative features: W351 would move any negative feature into that class. Its centered auxiliary test then has $M(RG)\le4C_R$ and the SAME energy, by W348, and is still never renormalized. Every Gamma, primary-prime, low-frequency and folded term must remain on that one centered profile. Their required joint sign, the sign $e_4=0$ versus $e_4<0$, full RH and strict Robin for EVERY integer $n>5040$ remain unresolved. This is a paper application of the existing null direction, classical rank-one extraction and owned source recovery, without scientific execution or Lean/kernel certification.

## Center both moments in the actual primary-prime discrepancy estimate

The mean-centering in W348 removes the higher-power mean charge. A second actual mixed-null direction removes the exponential pole moment at the same time. On the resulting ONE profile, the primary-prime term is the signed discrepancy of $\vartheta(x)$ from $x$, minus a nonnegative Green energy. Consuming this identity in W349 gives an all-source lower bound with that Green reserve retained. The discrepancy still needs a joint estimate against the full Gamma energy.

The classical xi derivative-null family is already recorded in the [Lagarias account](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate). The pole-continuum identity is already owned by [`pole_continuum_completion`](../../D5/S3/Weil/ZetaGamma/PoleContinuumCompletion.lean), with its Green multiplier and digamma recurrence. These facts are reused, not reproved as new theorems. The additional interface below is their realization in the ACTUAL physical form W317 and their bounded simultaneous centering on its entire domain. The radical degree-adjustment precedent remains the one cited before W347.

### Realize the second mixed-null direction in the actual physical domain

Put $c_\Phi=\pi^{1/4}/4$, retain $z_0(x)=e^{-x}$, and define
$$
z_2(x)=\left(4x^2-22x+\frac{81}{4}\right)e^{-x},\qquad
\ell_0(F)=\int_{\mathbb R}g_F(r)dr,\qquad
\ell_1(F)=\int_{\mathbb R}\cosh(r/2)g_F(r)dr.
$$
All profiles here are W338's ACTUAL $g_F(r)=b_F(2|r|)$, with $b_F$ formed from $B\mathscr TF$. Then
$$
\begin{gathered}
z_2\in\mathcal V,\qquad
\mathfrak E(z_2,F)=0\quad(F\in\mathcal V),\qquad
g_{z_2}=c_\Phi\Phi'',\\
\ell_0(z_0)=c_\Phi\xi(1/2)>0,\quad
\ell_1(z_0)=c_\Phi/2,\quad
\ell_0(z_2)=0,\quad \ell_1(z_2)=c_\Phi/8.
\end{gathered}
\tag{W354}
$$
To check the actual-form interface, use W255's physical feature
$f_a(x)=e^{9a/2}e^{-e^{2a}x}$. Its second parameter derivative at zero is precisely $z_2$. The map $a\mapsto f_a$ is twice differentiable in the owned $X$ norm on a neighborhood of zero: its derivatives are fixed-degree polynomials in $x$ times an exponential with a uniformly positive decay rate. W325 transfers that convergence to $\mathcal V$. Differentiate the actual mixed identity $\mathfrak E(f_a,f_b)=L_0(a,b)$ twice at $a=0$. Oddness of $L_0$ in its first argument makes the result zero. W326's existing finite-Gaussian core and continuity of the mixed form extend this to every $F\in\mathcal V$. Thus mixed nullity belongs to the actual form, without identifying it with the classical full Weil form.

The same theta-series calculation used in W347 gives $g_{f_a}(r)=c_\Phi\Phi(a+|r|)$. Taking its second derivative yields $g_{z_2}=c_\Phi\Phi''$, since $\Phi''$ is even. The already owned transform values are $\int\Phi=\xi(1/2)$ and $\int\cosh(r/2)\Phi=\xi(1)=1/2$. Twice integrating the second derivative against these two weights gives the last line of W354. The theta decay pays every endpoint. This uses the existing derivative-null mechanism and transform normalization, rather than a new assertion about a different xi convention.

Both functionals are continuous in the actual sixth-moment norm. In fact the existing $H_6$ bounds for $B$ and $\mathscr T$, with $x=\pi e^{2|r|}$, give
$$
\|e^{5|r|/2}g_F\|_2^2
=\pi^{-5/2}\int_\pi^\infty x^6|B\mathscr TF(x)|^2dx
\le C M(F).
$$
Cauchy--Schwarz now bounds $|\ell_0(F)|+|\ell_1(F)|$ by $C\sqrt{M(F)}$. This is a moment estimate on the same actual source, not a pointwise bound on its Fourier transform.

### Remove both moments without changing the complete energy

Use the existing $R$ of W348, so $RF=F-\ell_0(F)z_0/\ell_0(z_0)$, and put
$$
R_\diamond F=RF-\frac{8\ell_1(RF)}{c_\Phi}z_2.
$$
There is a fixed finite $C_\diamond$, independent of support, source count, scalar field and moment-budget size, such that for EVERY $F\in\mathcal V$,
$$
\begin{gathered}
G:=R_\diamond F\in\mathcal V,\qquad
\ell_0(G)=\ell_1(G)=0,\qquad R_\diamond^2F=R_\diamond F,\\
\mathfrak E(G)=\mathfrak E(F),\qquad
M(G)\le C_\diamond M(F),\qquad
\mathcal P(G)\le C_\diamond[\mathcal P(F)+M(F)].
\end{gathered}
\tag{W355}
$$
The functional values in W354 give the two cancellations and idempotence. W347 and W354 eliminate every mixed and diagonal null contribution to the COMPLETE energy. The continuous functional bounds and the fixed $M+\mathcal P$ norms of $z_0,z_2$ give the two form-norm estimates. The map preserves reality and commutes with complex conjugation. It can give $G=0$ and is never followed by division by $\|G\|_H$. Neither its auxiliary norm nor its moment is claimed equal to the original one.

### Reuse the pole-continuum identity on this exact profile

For an even actual profile $g$, retain its real autocorrelation $R_g$ and primary-prime term $T_1(g)$ from W338. Define
$$
\begin{aligned}
\vartheta(x)&=\sum_{p\le x}\log p,\\
\mathcal D_\vartheta(g)&=2\int_{[1,\infty)}x^{-1/2}R_g(\log x)\,d(\vartheta(x)-x),\\
\mathcal G(g)&=\int_{\mathbb R}\frac{|\widehat g(\tau)|^2}{\tau^2+1/4}\,d\tau\ge0,
\end{aligned}
$$
where the Fourier transform is unitary, as in W231. The existing pole-continuum identity gives exactly
$$
T_1(g)=\mathcal D_\vartheta(g)
+2\left|\int_{\mathbb R}\cosh(r/2)g(r)dr\right|^2-\mathcal G(g).
\tag{W356}
$$
In particular $T_1(g_G)=\mathcal D_\vartheta(g_G)-\mathcal G(g_G)$ for $G=R_\diamond F$.

Here is the domain check for this reuse. If $D=\|e^{5|r|/2}g\|_2^2<\infty$, Cauchy--Schwarz and $|r|+|r-s|\ge|s|$ give $|R_g(s)|\le D e^{-5|s|/2}$. The primary-prime sum and continuous integral in W356 consequently converge absolutely, bounded respectively by $2D\sum_p(\log p)p^{-3}$ and $2D\int_0^\infty e^{-2s}ds$. The Green form is bounded by $4\|g\|_2^2$. Even smooth compact approximations converge in this weighted $L^2$ norm; the same bounds applied to the mixed differences pass the already owned compact-test pole-continuum identity to $g$. Its pole term is $2|\ell_1|^2$, its growing integral is $2\int_0^\infty e^{s/2}R_g(s)ds$, and its decaying Green multiplier is $(\tau^2+1/4)^{-1}$. In particular the growing integral alone is not the pole square: their difference is the Green form, with the sign in W356. No prime distribution error estimate is assumed by defining the Stieltjes discrepancy.

### Consume both cancellations in the full all-source inequality

For EVERY $F\in\mathcal V$ and each fixed $0<\delta<1$, put $G=R_\diamond F$ and $g=g_G$. W349 applied to this same $G$, followed by W355--W356, gives
$$
\begin{aligned}
\left|\mathfrak E(F)-\mathcal P(G)
+\alpha[\mathcal D_\vartheta(g)-\mathcal G(g)]\right|
&\le\delta\mathcal P(G)+C_\delta S(G),\\
\mathfrak E(F)\ge{}&(1-\delta)\mathcal P(G)
-\alpha\mathcal D_\vartheta(g)-C_\delta S(G)\\
&+\alpha[\mathcal D_{\rm odd}(g)+\mathcal J(g)+\mathcal G(g)],
\qquad \alpha=2/\sqrt\pi.
\end{aligned}
\tag{W357}
$$
The Green reserve is distinct from the supplier's bounded rational-frequency energy $\mathcal J$. Every term belongs to ONE centered actual profile; all primary primes, higher powers, folded channels, cutoff and fixed Gamma shift remain accounted for as in W349. The whole logarithmic Gamma form is retained. No separately favorable signs of correlations or coefficients, support restriction or new test criterion is imposed.

For an ORIGINAL normalized source with $Q_H=1$ and $Q_{6,A}\le K$, take its W257 feature $\psi$ with $\|\psi\|_H=1$ and put $G=R_\diamond\psi$. The same source therefore obeys
$$
\begin{aligned}
4\pi^3 A Q_{\mathcal K_A^g}(\sigma)
\ge{}&(1-\delta)\mathcal P(G)-\alpha\mathcal D_\vartheta(g_G)
-C_\delta S(G)\\
&+\alpha[\mathcal D_{\rm odd}(g_G)+\mathcal J(g_G)+\mathcal G(g_G)],
\qquad M(G)\le C_\diamond K.
\end{aligned}
\tag{W358}
$$
This includes every admitted original source at every fixed budget $K>1$, with its original window and count constraints. The auxiliary null vectors are not inserted as original late-window sites. At W351's universal cap $4$, the same estimate uses only $M(G)\le4C_\diamond$ and still covers every possible negative direction. No auxiliary renormalization is used, including when $G=0$.

The new interface removes both explicit moments and retains a nonnegative primary-continuum reserve in the actual all-source estimate. It does not give a favorable bound for the signed discrepancy $\mathcal D_\vartheta$ and the low-frequency allowance jointly against the remaining Gamma and positive energies. The change of auxiliary profile also supplies no pointwise numerical dominance over W349. The sign of $e_4$, full RH and strict Robin for EVERY integer $n>5040$ remain unproved. This is an actual-source paper application of existing classical derivative/null and pole-completion results, without scientific execution, Lean/kernel certification or a literature-priority claim.

## Identify the actual complete energy and retain an exact signed arithmetic budget

The estimates W338--W358 compared the actual half-line Gamma form with an even classical test up to bounded terms. The actual form can instead be identified exactly on that test. This pays the folded and cutoff terms jointly and permits an exact signed budget with an explicit scalar allowance, rather than an unspecified $C_\delta S$ error. The signed primary-prime discrepancy remains uncontrolled.

Reuse the actual Fourier identity W39, the classical paired Hadamard product and zero counting already supplied in the [Lagarias and logarithmic-derivative account](broadbent2026mertens.md#an-upper-budget-in-the-actual-logarithmic-gamma-energy), and the classical Weil explicit formula. In the inspected [Suzuki v3 primary](https://arxiv.org/pdf/2606.09096v3), printed p.13, equation (3.1), the frequency zeros may be nonreal and carry their actual multiplicities; printed p.14, Lemma 3.1, also treats the compact $H^1_0$ domain. No RH premise or new Hadamard, explicit-formula or general de Branges criterion is used below. The application concerns the actual source map and its full-domain energy, without identifying Hilbert-space completions.

### Fix the classical normalization on the actual test

Retain $g_F$ from W338 and $c_\Phi=\pi^{1/4}/4$. For an even test $g$ in the displayed range, write $s(g)=\|g\|_2^2$ and use the unitary Fourier transform. Define its complete arithmetic Weil value by
$$
\begin{aligned}
\mathcal Q_W(g)={}&\int_{\mathbb R}
\left[\Re\operatorname{digamma}(1/4+i\tau/2)-\log\pi\right]
|\widehat g(\tau)|^2d\tau\\
&-T_1(g)-T_{\ge2}(g)
+2\left|\int_{\mathbb R}\cosh(r/2)g(r)dr\right|^2.
\end{aligned}
$$
The prime terms and pole moment are exactly those used in W338--W356, and retain every prime power. The signed Gamma integral is finite by W338 and the bounded rational digamma shift. The exponential weighted estimate before W355 makes both arithmetic sums and the pole moment finite. Thus this is the classical arithmetic form on the ACTUAL range, rather than a new completion chosen to enforce an identity.

For EVERY $F\in\mathcal V$, including signed real and complex features,
$$
\mathfrak E(F)=\alpha\mathcal Q_W(g_F),\qquad
\alpha=\frac2{\sqrt\pi}.
\tag{W359}
$$
Here $\mathfrak E$ is the ENTIRE actual form W317, including both folded channels, the rank-two cutoff and the fixed Gamma shift. They have not been independently dropped or assigned favorable signs.

### Verify the source-specific identity through the actual signed zero sum

Let $\mathcal F(z)=\int\Phi(t)e^{izt}dt$ be W7's actual entire function and write $\mathcal F(z)=\mathcal H(z^2)$ as in W39. Let $\Gamma$ be its complete zero set, with multiplicities $m_\gamma$. The actual xi normalization gives $|\Im\gamma|<1/2$, $0\notin\Gamma$, and invariance under sign and conjugation. No inclusion $\Gamma\subset\mathbb R$ is assumed.

For the physical Gaussian $f_a$ of W255 put
$$
g_a(t)=g_{f_a}(t)=c_\Phi\Phi(a+|t|),\qquad
v_a(z)=\int_{\mathbb R}g_a(t)e^{izt}dt.
$$
The transform in this definition is ordinary, without the unitary factor. At every $\gamma\in\Gamma$,
$$
v_{-a}(\gamma)=-v_a(\gamma),\qquad
\mathcal Q_W(g_a,g_b)
=\sum_{\gamma\in\Gamma}m_\gamma
 v_a(\gamma)\overline{v_b(\overline\gamma)}.
\tag{W360}
$$
The first equality follows from
$g_a(t)+g_{-a}(t)=c_\Phi[\Phi(t+a)+\Phi(t-a)]$ and $\mathcal F(\gamma)=0$. The second is the reused signed Weil explicit formula; conjugating the zero as displayed is essential.

The noncompact and summation interfaces in W360 can be paid explicitly. For $a\ge0$, twice integrating $2c_\Phi\int_0^\infty\Phi(a+t)\cos(\gamma t)dt$ gives
$|v_a(\gamma)|\le A(a)/(1+|\gamma|^2)$, where $A(a)$ is bounded by a fixed multiple of
$|\Phi'(a)|+\int_0^\infty(|\Phi|+|\Phi''|)(a+t)e^{t/2}dt$.
The existing full theta derivative bounds make $A(a)$ superexponentially decreasing at infinity. The first identity extends this bound to $A(|a|)$ for all real $a$. Zero counting gives $\sum_\gamma m_\gamma(1+|\gamma|^2)^{-2}<\infty$. Compact even cutoffs and smoothing of $g_a$ converge in weighted $H^1$; their second distributional derivatives have uniformly bounded weighted total variation, including the derivative jump at zero. They consequently retain a common $O((1+|\gamma|^2)^{-1})$ transform bound in the zero strip. Dominated convergence passes the classical compact explicit formula to W360. The prime correlations converge by the same exponential weighted bound used in W356, and the Gamma integral converges in its full logarithmic form norm.

For $\Im z,\Im w<-1/2$, absolute integration gives
$$
\int_{\mathbb R}v_a(\gamma)e^{iza}da
=-\frac{2ic_\Phi z\mathcal F(z)}{z^2-\gamma^2}.
$$
The zero sum and both source integrals may be interchanged by the preceding $A(|a|)A(|b|)$ majorant. Reuse the classical paired product for $\mathcal H$, with one root $\gamma^2$ per sign pair. Its logarithmic derivative gives
$$
\sum_{\gamma\in\Gamma}
\frac{m_\gamma}{(z^2-\gamma^2)(\overline w^2-\gamma^2)}
=\frac{2\mathcal D_{\mathcal H}(w^2,z^2)}
 {\mathcal F(z)\overline{\mathcal F(w)}}.
$$
The factor two counts the two frequency roots in each sign pair, with their multiplicities. Hence the double source Fourier transform of $\mathcal Q_W(g_a,g_b)$ is
$8c_\Phi^2z\overline w\mathcal D_{\mathcal H}(w^2,z^2)$.
The EXISTING W39 says that the transform of $L_0(a,b)$ is exactly
$z\overline w\mathcal D_{\mathcal H}(w^2,z^2)$. Weighted Fourier uniqueness and continuity therefore give
$$
\mathcal Q_W(g_a,g_b)=8c_\Phi^2L_0(a,b)
=\frac{\sqrt\pi}{2}L_0(a,b).
\tag{W361}
$$
There is no positive-zero-sum substitution in this argument: both nonreal conjugate zeros and the displayed signed pairing remain present.

Polarizing the existing W255 Gaussian identity proves W359 on every finite complex Gaussian feature. W326 is a core in the ACTUAL $M+\mathcal P$ norm. The classical arithmetic pairing above is continuous in that norm on its range: W338 controls its whole logarithmic Gamma pairing, the exponential weighted bound controls the complete prime and pole pairings, and the original actual form is continuous there by W317. Passage through that core proves W359 for all $F\in\mathcal V$. No global equality of operator domains or equality of unrelated completed norms is inferred.

### Consume the exact identification without an unspecified bounded remainder

Use precisely $\mathcal Z$, $\mathcal D_{\rm odd}$, $\mathcal J$, $\kappa$ and $d_\xi$ of equation (8) in the [owned higher-power account](broadbent2026mertens.md#an-upper-budget-in-the-actual-logarithmic-gamma-energy). With unitary Fourier normalization,
$$
\mathcal Z(g)=\int_{\mathbb R}
2\Re\frac{\xi'}{\xi}(1+2i\tau)|\widehat g(\tau)|^2d\tau\ge0,
\qquad
C_{\rm odd}=\sum_p\frac{\log p}{\sqrt p(p-1)},\qquad
c_{\rm a}=\log2+2C_{\rm odd}>0.
$$
The positivity is the existing unconditional right-boundary resolvent theorem, not a critical-line or RH assertion. All zeros in that supplier have their actual multiplicities; no zero-height truncation is made. The other two energies are nonnegative as before.

For EVERY $F\in\mathcal V$, with $g=g_F$, the complete form has the EXACT signed decomposition
$$
\frac{\mathfrak E(F)}\alpha
=\mathcal Z(g)+\mathcal D_{\rm odd}(g)+\mathcal J(g)
-\mathcal D_\vartheta(g)-c_{\rm a}s(g)
-\frac12|\ell_0(F)|^2.
\tag{W362}
$$
To consume the suppliers, first insert W356 in W359. Its two pole squares cancel exactly. The retained Green multiplier advances the quarter-Gamma argument to $5/4$ by the owned digamma recurrence. Thus
$\mathcal Q_W(g)=E_*(g)+[\operatorname{digamma}(5/4)-\log\pi]s(g)-\mathcal D_\vartheta(g)-T_{\ge2}(g)$.
The existing definitions give
$T_{\ge2}=|\int g|^2/2+2\kappa s+\epsilon$ and
$E_*-\epsilon+d_\xi s=\mathcal Z+\mathcal D_{\rm odd}+\mathcal J$.
Finally the classical quarter-value normalization yields
$$
\operatorname{digamma}(5/4)-\log\pi-2\kappa-d_\xi
=-\log2-2C_{\rm odd}.
$$
This fixes the scalar in W362; it is not absorbed into a newly chosen constant. The existing W342 logarithmic boundary estimate bounds the $\mathcal Z$ multiplier by $C(1+\log(2+|\tau|))$. Together with W338 it passes the exact supplier identity from the joint core to every actual profile, keeping its full frequency contribution. The odd and rational energies are bounded in $L^2$, and W356 pays the discrepancy and moments. Thus this consumption applies on the whole specified domain, without substituting a derivative norm for Gamma.

For an ORIGINAL source with $Q_H=1$, $Q_{6,A}\le K$, use its W257 unit feature $\psi$ and the EXISTING mean-centering $G=R\psi$ from W348. With $g=g_G$, the same original complete form satisfies
$$
4\pi^3 A Q_{\mathcal K_A^g}(\sigma)
=\alpha\left[
\mathcal Z(g)+\mathcal D_{\rm odd}(g)+\mathcal J(g)
-\mathcal D_\vartheta(g)-c_{\rm a}s(g)\right],
\qquad M(G)\le C_RK.
\tag{W363}
$$
The double-centering $R_\diamond$ may also be used, with its corresponding bound, but is not needed for cancellation of the explicit pole square in the exact identity. Neither auxiliary feature is renormalized. All original counts, windows, coefficients and prime powers remain in scope. W351 again permits the search for a negative direction to be restricted to the ONE full original cap $4$, with no positive-subclass replacement.

The already owned Stechkin comparison, equation (15) of the higher-power account, also gives a concrete LOWER estimate from this exact identity. With $\kappa_S=1/\sqrt5$, EVERY $F\in\mathcal V$ satisfies
$$
\frac{\mathfrak E(F)}\alpha\ge
\kappa_SE_*(g_F)-\mathcal D_\vartheta(g_F)
-(c_{\rm a}+2)s(g_F)-\frac12|\ell_0(F)|^2
+\mathcal D_{\rm odd}(g_F)+\mathcal J(g_F).
\tag{W364}
$$
Indeed insert that supplier's upper bound for $T_{\ge2}$ into the exact expression for $\mathcal Q_W$ above and use the displayed scalar identity. The full $E_*$ logarithmic Gamma energy is retained with its fixed fraction; the scalar debit is explicitly $2+\log2+2C_{\rm odd}$. No boundary-comparison constant is left unpaid. On the ORIGINAL source in W363, the same lower bound multiplied by $\alpha$ applies to $4\pi^3 A Q_{\mathcal K_A^g}$ with $g=g_{R\psi}$ and no mean-square term. It covers every original budget and coefficient with the already stated auxiliary moment control.

W362--W364 replace the previously unspecified low-frequency comparison loss by the explicit scalar $c_{\rm a}s(g)$ and preserve the entire nonnegative resolvent, odd and rational energies on the SAME actual profile. The remaining task is a signed bound for $\mathcal D_\vartheta(g)+c_{\rm a}s(g)$ against their joint sum, on the full allowed class. No favorable sign, numerical dominance over every earlier estimate, all-source positivity, sign of $e_4$, full RH or strict Robin for EVERY integer $n>5040$ follows yet. Classical Hadamard, Weil and higher-power results are reused; the actual exact interface and its all-source signed consumer are paper mathematics without scientific execution, Lean/kernel certification or a priority claim.

## A finite verified zero height controls the entire actual negative allowance

The exact interface W359 gives a quantitative use of finite zero verification on the ENTIRE actual source class. The allowance below is measured by the original sixth moment, without a fixed-support, finite-dictionary or theta-variance-norm restriction. It decreases with the verified height, but a fixed verified height does not remove it.

Reuse W317's complete-energy bound, W338's full logarithmic Gamma comparison, the exponential profile estimate before W355, W359's exact identification, and W257's original-source normalization. The analytic tools are classical Gaussian convolution, weighted interpolation, the signed Weil explicit formula and the already cited actual zero count; none is introduced as a new general theorem. The [existing whole-projector height supplier](fukushima2011dirichlet.md#verified-zero-height-and-a-whole-projector-strip-tail-budget) retains its different theta-variance domain and cutoff constants. Division by $\Phi$ is not assumed bounded on the present finite-moment domain. No literature-priority or Lean/kernel-certification claim is made.

### State the height premise and the full-source lower bound

For $T\ge3$, let $\mathsf{RH}(T)$ mean that every nontrivial zeta zero $\rho$ with $|\Im\rho|\le T$ has $\Re\rho=1/2$, including the height boundary. There is an absolute $C$, independent of $T$, the scalar field, source count, widths, support and coefficients, such that
$$
\mathsf{RH}(T)\quad\Longrightarrow\quad
\mathfrak E(F)\ge-\frac{C}{(\log T)^{1/3}}M(F)
\qquad(F\in\mathcal V).
\tag{W365}
$$
Here $\mathfrak E$ and $M$ are exactly W317's COMPLETE form and sixth moment. The constant is not numerically evaluated; no numerical improvement at a particular available height is asserted.

It suffices to consider $\mathfrak E(F)\le0$. The opposite sign already satisfies W365, and the zero source requires no division. Put $g=g_F$, $b=5/2$, and write
$$
\|v\|_a^2=\int_{\mathbb R}e^{2a|r|}|v(r)|^2dr,
\qquad
\mathcal L(v)=\int_{\mathbb R}\log(2+|\tau|)|\widehat v(\tau)|^2d\tau
$$
with unitary Fourier normalization. W317 gives
$\mathcal P(F)\le|\mathfrak J(F,F)|\le C\mathcal N(F)^2\le CM(F)$
on this nonpositive-energy class. W338, its shifted digamma multiplier and the exponential estimate then imply
$$
\|g\|_b^2+\mathcal L(g)\le CM(F).
\tag{W366}
$$
The moment by itself is not claimed to bound Gamma: the sign of the COMPLETE energy is used for precisely that step.

### Filter once and retain the signed Gamma comparison

For $0<\epsilon\le1$ use the normalized heat kernel
$$
K_\epsilon(r)=(4\pi\epsilon)^{-1/2}e^{-r^2/(4\epsilon)},
\qquad h_\epsilon=K_\epsilon*g,
\qquad \widehat h_\epsilon(\tau)=e^{-\epsilon\tau^2}\widehat g(\tau).
$$
The auxiliary $h_\epsilon$ remains even, also for complex $g$; no assertion that it is another actual profile is needed. The classical weighted convolution bound gives
$\|h_\epsilon\|_b\le2e^{b^2\epsilon}\|g\|_b$.
Split its unweighted Fourier error at $|\tau|=\epsilon^{-1/4}$. The low part is at most $\epsilon\|g\|_0^2$ and the rest is at most $\mathcal L(g)/\log(2+\epsilon^{-1/4})$. For $a=5/6$, weighted interpolation with $a/b=1/3$ therefore gives
$$
\begin{aligned}
\|g-h_\epsilon\|_0^2&\le\frac{CM(F)}{\log(2+\epsilon^{-1})},
&\|g-h_\epsilon\|_b^2&\le CM(F),\\
\|g-h_\epsilon\|_a^2
&\le\|g-h_\epsilon\|_0^{4/3}\|g-h_\epsilon\|_b^{2/3}
\le\frac{CM(F)}{[\log(2+\epsilon^{-1})]^{2/3}}.
\end{aligned}
\tag{W367}
$$

Let $q(\tau)=\Re\operatorname{digamma}(1/4+i\tau/2)-\log\pi$ and $q_0=q(0)$. The owned digamma integral gives $q\ge q_0$. The shifted nonnegative Gamma form with multiplier $q-q_0$ cannot increase under the filter. Thus the signed Gamma difference is bounded below by
$-|q_0|(\|g\|_0^2-\|h_\epsilon\|_0^2)$.
The nonnegative norm-square loss is at most $2\|g\|_0\|g-h_\epsilon\|_0$, so its cost is $CM(F)[\log(2+\epsilon^{-1})]^{-1/2}$. No absolute-value estimate spends the positive Gamma tail.

For weighted tests $v,w$, the same-source correlation estimate
$$
\left|\int v(r)\overline{w(r-s)}dr\right|
\le e^{-a|s|}\|v\|_a\|w\|_a
$$
bounds the complete prime-power pairing by
$2\sum_{n\ge2}\Lambda(n)n^{-a-1/2}\|v\|_a\|w\|_a$.
This series converges for the chosen $a>1/2$. Both exponential pole functionals are bounded in that SAME norm; on even tests they give W359's coefficient-$2$ cosh square. Polarization, W366 and W367 bound the change of the entire prime-and-pole part by
$C(\|g\|_a+\|h_\epsilon\|_a)\|g-h_\epsilon\|_a$.
Consequently
$$
\mathcal Q_W(g)\ge\mathcal Q_W(h_\epsilon)
-\frac{CM(F)}{[\log(2+\epsilon^{-1})]^{1/3}}.
\tag{W368}
$$
Every prime power and both pole contributions remain; no favorable correlation sign is assumed.

### Bound the entire unverified zero tail

Use ordinary transforms, without the unitary factor, in the zero formula:
$$
v(z)=\int g(r)e^{izr}dr,
\qquad v_\epsilon(z)=e^{-\epsilon z^2}v(z),
\qquad |v(z)|\le C\sqrt{M(F)}\quad(|\Im z|\le1/2).
$$
The last estimate follows from W366 by weighted Cauchy--Schwarz. For the complete frequency zero set $\Gamma$ and actual multiplicities $m_\gamma$ of W360, the classical signed formula is
$$
\mathcal Q_W(h_\epsilon)=
\sum_{\gamma\in\Gamma}m_\gamma
v_\epsilon(\gamma)\overline{v_\epsilon(\overline\gamma)}.
\tag{W369}
$$
For each fixed $\epsilon>0$, the filtered function and its first two derivatives have exponentially weighted $L^2$ and weighted $L^1$ bounds. Smooth compact even cutoffs give a common inverse-square transform majorant in the closed zero strip. Actual zero counting permits the signed sum to pass to the limit; the full Gamma norm, poles and absolutely convergent prime-power sums pass under the same approximation. Constants for this domain passage may depend on $\epsilon$ and are not used to estimate the tail.

Under $\mathsf{RH}(T)$, every term with $|\Re\gamma|\le T$ is a nonnegative square. On the remaining zeros, $|\Im\gamma|<1/2$ gives
$$
\left|v_\epsilon(\gamma)\overline{v_\epsilon(\overline\gamma)}\right|
\le CM(F)e^{\epsilon/2}e^{-2\epsilon(\Re\gamma)^2}.
$$
The owned count $N(u)\le C[1+u\log(2+u)]$, including both signs and all multiplicities, gives by summation by parts
$\sum_\gamma m_\gamma e^{-(\Re\gamma)^2/T}\le C\sqrt T\log(2+T)$.
Set $\epsilon=1/T$. For $|\Re\gamma|>T$,
$e^{-2(\Re\gamma)^2/T}\le e^{-T}e^{-(\Re\gamma)^2/T}$; therefore
$$
\mathcal Q_W(h_{1/T})
\ge-CM(F)\sqrt T\log(2+T)e^{-T}.
\tag{W370}
$$
Nonreal zeros retain their signed pairing throughout. W368, W370 and W359 prove W365, after increasing a single absolute constant. No numerical zero truncation or assumption about the unverified zeros has entered.

### Return the height allowance to every original source

The already defined completed minima and original sources now satisfy, under the SAME $\mathsf{RH}(T)$,
$$
\begin{gathered}
e_K\ge-\frac{CK}{(\log T)^{1/3}}\quad(K>1),
\qquad -\frac{4C}{(\log T)^{1/3}}\le e_4\le0,\\
4\pi^3 A Q_{\mathcal K_A^g}(\sigma)
\ge-\frac{C}{(\log T)^{1/3}}Q_{6,A}(\sigma).
\end{gathered}
\tag{W371}
$$
The last line is W257 and homogeneity on EVERY admitted finite original source, with arbitrary real or complex coefficients, counts and widths. No source class has been replaced by the filtered auxiliary test, and no auxiliary feature is normalized.

The existing published premise can be used at $T_0=3\cdot10^{12}$: [Platt--Trudgian, arXiv:2004.09765v1](https://arxiv.org/pdf/2004.09765v1), Theorem 1, printed p.2, verifies through $3000175332800$. Their computation is cited, not repeated or independently certified. W365--W371 supply a uniform height-dependent rate in the actual moment norm; they do not evaluate the constant or establish a numerical improvement at $T_0$. Letting the allowance vanish requires unbounded verified heights. A fixed $T_0$ proves neither $e_4=0$, the missing full signed dominance, RH nor strict Robin for EVERY integer $n>5040$. These are paper-level source applications without Lean/kernel certification or scientific execution.
