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
