---
bibkey: escobar2025earlystateexclusion
authors: Mia Gabriella Escobar; Valentin Garcia; Anastasiia Minenkova
year: 2025
title: "Early State Exclusion in 7-Qubit Spin Chains"
doi: 10.48550/arXiv.2507.18767
url: https://arxiv.org/abs/2507.18767v1
claim: "Section 4 conjectures that a 7 x 7 Jacobi matrix with symmetric spectrum realizing perfect state transfer does not have early state exclusion if and only if its positive eigenvalues are integer multiples of the smallest positive eigenvalue; Theorems 3.2 and 3.4 prove the spectra {0, +-1, +-2m, +-(2m+1)} (no early state exclusion) and {0, +-(2m+1), +-(2m+2), +-(2m+3)} (early state exclusion exactly 2m times)."
strata_touched:
  - D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros
license: citation-only
triage: anchor
---

# Early state exclusion in 7-qubit spin chains

M. G. Escobar, V. Garcia and A. Minenkova, *Early State Exclusion in 7-Qubit
Spin Chains*, arXiv:2507.18767v1 (24 July 2025). The arXiv record lists these
three authors; the title page of the source names M. G. Escobar and V. Garcia
as authors and A. Minenkova as project advisor. The quotations are taken from
the arXiv v1 source `Finaldraft7x7.tex`.

## Jacobi matrices, perfect state transfer and early state exclusion

The introduction fixes the Hamiltonian of a chain of $N + 1$ qubits as the
Jacobi matrix of Eq. (1.1), with diagonal entries $a_1, \dots, a_{N+1}$ and
off-diagonal entries $b_1, \dots, b_N$,

> for $a_i \in \R$ and $b_i > 0$.

Perfect state transfer is defined by:

> A Jacobi matrix $J$ realizes \textbf{perfect state transfer} (PST) between the end-vertices of the weighted path in Figure \ref{fig:nearestneighbor} at time $T > 0$ if
> \begin{equation}
> e^{-iJT}\e_0 = e^{i\phi}\e_N
> \end{equation}
> for some phase $\phi \in \R$.

The source recalls Kay's criterion (persymmetry together with
$\mu_{k + 1} - \mu_k = \frac{(2n_k + 1)\pi}{T}$ for the ordered eigenvalues) and
restricts to symmetric spectra:

> We consider a special case where $J$ has symmetric spectrum in section 3, meaning that for $\{\lambda_k\}_{k = 0}^N$, $\lambda_j = -\lambda_{N - j}$ for all $1 \leq j \leq N - 1$. If we assume that the positive eigenvalues of $J$ are coprime, then \eqref{1.3} implies that $J$ first realizes PST at time $T = \pi$.

Early state exclusion is defined by:

> Let $J$ be a Jacobi matrix realizing PST at earliest time $T > 0$. If there exists some $\tau \in (0, T)$ such that
> \begin{equation}
>     \langle e^{-iJ\tau}\e_0, \e_0 \rangle = 0,
> \end{equation}
> then we say that $J$ exhibits \textbf{early state exclusion} (ESE) at time $\tau$.

## The first-site amplitude of a 7-site chain

For the symmetric spectrum $\{0, \pm x, \pm y, \pm z\}$, $0 < x < y < z$, the
source gives the persymmetric Jacobi matrix (zero diagonal,
$b_1 = xz/\sqrt{x^2-y^2+z^2}$,
$b_2 = \sqrt{(y^2-x^2)(z^2-y^2)/(x^2-y^2+z^2)}$,
$b_3 = \sqrt{(x^2-y^2+z^2)/2}$) and the amplitude, Eq. (2.1):

> \begin{align}
>     \langle e^{-iJt}\e_0, \e_0 \rangle &= \frac{1}{2y^2(z^2 - x^2)(x^2-y^2+z^2)}\Big((y^2 - x^2)(z^2 - x^2)(z^2 - y^2)\\
>         &\quad + y^2z^2(z^2 - y^2)\cos{xt} + x^2z^2(z^2 - x^2)\cos{yt} + x^2y^2(y^2 - x^2)\cos {zt}\Big).
> \end{align}

## The proved families and the conjecture

Theorem 3.2:

> Suppose that $J$ is a Jacobi matrix of order $7$ realizing PST with symmetric spectrum
> \[
> \{0, \pm 1, \pm 2m, \pm (2m + 1)\}
> \]
> for some integer $m \geq 1$. Then $J$ \textbf{does not} have ESE.

Theorem 3.4:

> Let $m \geq 1$ be an integer. Then the Jacobi matrix $J$ realizing PST with symmetric spectrum
> $
> \{0, \pm (2m + 1), \pm (2m + 2), \pm (2m + 3)\}$
> has ESE $2m$ times.

Section 4, "Observations and Future Work", states:

> \begin{conjecture}
> Let $J$ be a $7 \times 7$ Jacobi matrix with symmetric spectrum realizing PST. Then $J$ does not have ESE if and only if its positive eigenvalues are integer multiples of the smallest positive eigenvalue.
> \end{conjecture}
> We believe that the techniques used to prove Theorems \ref{Theorem 3.2} and \ref{Theorem 3.4} cannot be replicated here.

The module `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros` takes the
bracket of Eq. (2.1) at natural frequencies $(x, y, z) = (a, b, c)$ as its
definition `amplitudeNumerator` and proves, for odd $a$ < even $b$ < odd $c$
with $\gcd(a, b, c) = 1$, that this cosine sum has a zero in $(0, \pi)$ if and
only if $a \neq 1$. The triples $(1, 2m, 2m + 1)$ of Theorem 3.2 and
$(2m + 1, 2m + 2, 2m + 3)$ of Theorem 3.4 are special cases; the count of
exactly $2m$ zeros in Theorem 3.4 is not treated in that module.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2507.18767 (the arXiv-issued DOI; the
  arXiv API record of 2507.18767 carries no journal reference and no
  publisher DOI, read 2026-10-08).
- arXiv: https://arxiv.org/abs/2507.18767v1 (source file `Finaldraft7x7.tex`):
  Eq. (1.1), the definition of perfect state transfer, Eq. (1.3) and the
  definition of early state exclusion in Section 1; Eq. (2.1) in the
  subsection "$7 \times 7$ Persymmetric Jacobi Matrices with Symmetric
  Spectrum"; Theorems 3.2 and 3.4 in Section 3; the conjecture in Section 4.
