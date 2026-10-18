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
