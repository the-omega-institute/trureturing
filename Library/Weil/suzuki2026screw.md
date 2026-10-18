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
