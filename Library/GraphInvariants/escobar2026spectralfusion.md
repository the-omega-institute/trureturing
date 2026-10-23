---
bibkey: escobar2026spectralfusion
authors: Mia Escobar; Valentin Garcia; Anastasiia Minenkova
year: 2026
title: "Spectral Fusion for Identifying Early State Exclusion in Symmetric Quantum Spin Chains"
doi: 10.48550/arXiv.2606.04353
url: https://arxiv.org/abs/2606.04353v1
claim: "For a persymmetric Jacobi matrix with symmetric spectrum of any order the first-site amplitude is a cosine sum with Hochstadt weights (Proposition, Amplitude Formulas); a reduced symmetric spectrum of odd order consists of integers of alternating parity with gcd 1 and first transfer time pi; the divisibility criterion for the absence of early state exclusion, known for order 5 and conjectured for order 7, is not true in general for larger chains."
strata_touched:
  - D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude
  - D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion
license: citation-only
triage: anchor
---

# Spectral fusion and early state exclusion in symmetric spin chains

M. Escobar, V. Garcia and A. Minenkova, *Spectral Fusion for Identifying Early
State Exclusion in Symmetric Quantum Spin Chains*, arXiv:2606.04353v1
(3 June 2026). The quotations are taken from the arXiv v1 source
`sn-article.tex`, without its TeX comments.

## Relation to the five- and seven-site criteria

The introduction describes the earlier work and the aim:

> In related works~\cite{EM25,EscobarGarcia2025}, the authors constructed Hamiltonians for chains of five and seven qubits with symmetric spectra and investigated the conditions under which ESE  occurs. They constructed examples when the smallest positive eigenvalue divides all other eigenvalues, in which case ESE does not occur, and examples when ESE appears and this divisibility condition fails. In the case of 5 qubit chains, this divisibility condition was a criterion for the Hamiltonian to exhibit no ESE. Based on these examples, it was conjectured that this spectral property characterizes the presence or absence of ESE in systems with symmetric spectra. In this work, we demonstrate that this is not the case in general for larger chains. In particular, we provide explicit counterexamples showing that the divisibility of eigenvalues by the smallest positive eigenvalue is not sufficient for the ``no ESE'' Hamiltonian. This indicates that ESE is governed by more subtle spectral and structural features of the Hamiltonian than previously suggested.

Later the paper states:

> It is known that a Jacobi matrix with a reduced symmetric spectrum $\{0, \pm \lambda_1, \pm \lambda_2\}$ has ESE if and only if $\lambda_1 \neq 1$~\cite{EM25}. This is not true in the general case (see Figures~\ref{fig: not true}-\ref{fig:1 14-17}).

The figures referred to carry the captions

> \caption{Example of $J$ with reduced spectrum $\{ 0,\pm1,\pm14,\pm15,\pm16\}$.}

> \caption{Example of no ESE occurrences for $J$ with the reduced spectrum $\{0,\pm1,\pm14,\pm15,\pm16,\pm19\}$.}

> \caption{Example of the ESE occurrences for $J$ with the reduced spectrum $\{0,\pm1,\pm14,\pm15,\pm16,\pm17\}$.}

## Symmetric spectra and the amplitude

> Let $J$ be a persymmetric Jacobi matrix of order $N + 1$ with spectrum $\sigma(J)$. We say that $\sigma(J)$ is \emph{symmetric } if $-\lambda \in \sigma(J)$ whenever $\lambda  \in \sigma(J)$.

> \begin{lemma}
> \label{Lemma b's}
> Let $J$ be a persymmetric Jacobi matrix of order $N + 1$ with a symmetric spectrum.
> Then
> \[
> \frac{1}{b_0 \cdots b_{N - 1}}
> =
> \begin{cases}
>     \displaystyle \sum_{j = 0}^{n} \prod_{\substack{i = 0 \\ i \neq j}}^n \frac{1}{|\lambda_j^2 - \lambda_i^2|} &\text{if $N + 1 = 2n + 1$ is odd} \\
>     \displaystyle \sum_{j = 1}^{n} \frac{1}{\lambda_j} \prod_{\substack{i = 1 \\ i \neq j}}^n \frac{1}{|\lambda_j^2 - \lambda_i^2|} &\text{if $N + 1 = 2n$ is even,}
> \end{cases}
> \]
> where each $b_k$ is given as in \eqref{eq:J}.
> \end{lemma}

> \begin{proposition}[Amplitude Formulas]
> \label{Prop: amplitudes}
> Suppose that $J$ is a persymmetric Jacobi matrix of order $N + 1$ with a symmetric spectrum.
> Then
> \begin{equation*}
> \label{eq:Amplitude Formulas}
> \langle e^{-iJt} \e_0, \e_0 \rangle_{\mathbb{C}^{N+1}} =
> \begin{cases}
>     \displaystyle
>     \sum_{k = 0}^{n} c_k\cos{\lambda_k t} &\text{if $N + 1 = 2n + 1$ is odd} \\
>     \displaystyle
>     \sum_{k = 1}^{n} \widetilde{c}_k\cos{\lambda_k t} &\text{if $N + 1 = 2n$ is even,}
> \end{cases}
> \end{equation*}
> where
> \begin{equation}
> \label{eq:c_k}
> c_k = \prod_{\substack{i = 0 \\ i \neq k}}^n \frac{1}{|\lambda_k^2 - \lambda_i^2|} \Bigg/\sum_{j = 0}^{n} \prod_{\substack{i = 0 \\ i \neq j}}^n \frac{1}{|\lambda_j^2 - \lambda_i^2|} \quad \text{for every $0 \leq k \leq n$}
> \end{equation}
> and
> \begin{equation}
> \label{eq:widetilde{c}_k}
> \widetilde{c}_k = \frac{1}{\lambda_k} \prod_{\substack{i = 1 \\ i \neq k}}^n \frac{1}{|\lambda_k^2 - \lambda_i^2|} \Bigg/\sum_{j = 1}^{n} \frac{1}{\lambda_j} \prod_{\substack{i = 1 \\ i \neq j}}^n \frac{1}{|\lambda_j^2 - \lambda_i^2|} \quad \text{for every $1 \leq k \leq n$.}
> \end{equation}
> \end{proposition}
>

After the proof the paper restricts to reduced spectra:

> $. As a further simplification, we will assume from here on that a symmetric $\sigma(J)$ is \emph{reduced}. That is, its ordered positive eigenvalues $0 < \lambda_1 < \cdots < \lambda_n$ of $J$ satisfy the following conditions:
> \begin{itemize}
>     \item The eigenvalues are integers that alternate in parity, with $\lambda_1$ being odd and $\gcd(\lambda_1, \dots, \lambda_n) = 1$ whenever $N + 1 = 2n + 1$.
>     \item The eigenvalues are odd half-integers with $\gcd(2\lambda_1, \dots, 2\lambda_n) = 1$, and each consecutive difference $\lambda_{k + 1} - \lambda_k$ is odd whenever $N + 1 = 2n$.
> \end{itemize}
> Indeed, if the positive eigenvalues have a common factor, the only change compared to the reduced spectrum is time scaling (see Figures~\ref{fig:123} and~\ref{fig:369}). Evidently, the first instance of PST in a reduced symmetric spectrum is at $T_0 = \pi$ in either case (see~\cite{Kay10}).

For odd order it derives a bound on the number of early exclusion times:

> A Jacobi matrix of order $2n + 1$ realizing PST with a reduced symmetric spectrum exhibits ESE an even number of times, up to a maximum of $\lambda_n - n$ instances.

The module `D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude` formalises,
for seven sites, the amplitude formula of the Proposition and the reduction to
integers of alternating parity with transfer at $T/g$ for a common divisor
$g$, starting from perfect state transfer at a time $T$ and the symmetry of the
spectrum. The paper contains no proof or refutation of the seven-site
conjecture of arXiv:2507.18767, which
`D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion` proves.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2606.04353 (the arXiv-issued DOI; the
  arXiv API record of 2606.04353 carries no journal reference and no
  publisher DOI, read 2026-10-08).
- arXiv: https://arxiv.org/abs/2606.04353v1 (source file `sn-article.tex`):
  the introduction; Lemma `Lemma b's` and Proposition `Prop: amplitudes` in the
  section "Jacobi Matrices and the Amplitudes", followed by the definition of
  reduced spectra and Corollary `cor:odd case number of zeros`; the statement
  on the five-site criterion and the figures `fig: not true`,
  `fig:1 14-16 19`, `fig:1 14-17` in the subsection "Main Result".
