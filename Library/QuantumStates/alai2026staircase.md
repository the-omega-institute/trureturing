---
bibkey: alai2026staircase
authors: Aaron Alai
year: 2026
title: "Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations"
doi: 10.48550/arXiv.2608.00124
url: https://arxiv.org/abs/2608.00124v1
claim: "Conjecture 1 (Staircase), Section IX, PDF page 4: the faithful GHZ–Mermin minimum is R/(2(R+1)) for every n ≥ 3."
strata_touched:
  - D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2608.00124

Source: https://arxiv.org/abs/2608.00124v1

# Exact faithful GHZ–Mermin measurement dependence

Section IX, Conjecture 1 (Staircase), PDF page 4, literal source TeX:

```tex
With $R(n) := 2^{\lfloor (n-1)/2 \rfloor}$ the Mermin violation ratio and $s(n) := (R+1)/(2R)$ the classical satisfiability,
\begin{equation}
F_{\min}(n) \;=\; \frac{R}{2(R+1)} \;=\; \frac{1}{4\,s(n)}, \qquad F_{\min}\cdot s = \frac{1}{4}.
\end{equation}
```

Section II, PDF page 1, literal source TeX:

```tex
For $n \ge 3$ parties sharing the $n$-partite GHZ state $(|0\rangle^{\otimes n} + |1\rangle^{\otimes n})/\sqrt{2}$, each party measures Pauli $X$ or $Y$. The Mermin settings are strings $s \in \{X,Y\}^n$ with an even number of $Y$'s; there are $2^{n-1}$ of them. Quantum mechanics predicts with certainty
\begin{equation}
E(s) = \begin{cases} +1, & \#Y(s) \equiv 0 \pmod 4,\\ -1, & \#Y(s) \equiv 2 \pmod 4,\end{cases}
\label{eq:targets}
\end{equation}
with every proper-subset correlator vanishing.

A local deterministic model assigns each hidden state $\lambda$ pre-set answers $(a_i, b_i) \in \{\pm 1\}^2$ per party---$4^n$ deterministic strategies---and, for each settings string $s$, a probability density $\rho_s(\lambda)$. Following Hall \cite{Hall2010}, the degree of measurement dependence is
\begin{equation}
M := \max_{s,s'} \sum_\lambda \left| \rho_s(\lambda) - \rho_{s'}(\lambda) \right|,
\end{equation}
and the fraction of measurement independence surrendered is $F := M/2 \in [0,1]$. (Ref.~\cite{Hall2011} uses the symbol $F$ for the retained fraction $1 - M/2$; throughout this paper $F$ denotes the surrendered fraction.) A model is \emph{faithful} if it reproduces every full correlator $E(s)$ and every vanishing proper-subset correlator. The floors reported below are minima of $F$ over all faithful models for the stated finite setting sets; richer scenarios containing them can only raise the values.
```

False means X and true means Y; Boolean output bits encode +1 and −1. A deterministic table has type Fin n → Bool × Bool, with its first answer used at X and its second at Y. Hamming distance from the all-false string counts the Y settings. Nonnegative real densities are normalized separately at each setting. Every nonempty proper party subset, including mixed X/Y subsets, has correlator zero. A finite supremum represents the maximum defining M, and the infimum over attainable F values represents F_min; attainment and a universal lower bound establish that this infimum is a minimum.

Section VIII, Theorem 5 (general lower bound), PDF page 4, bounds the minimum using the maximum number of constraints satisfied by a deterministic table on a chosen setting subset. Appendix A, PDF pages 5–6, lifts class densities through uniform parity fibers, preserving full correlators and erasing proper-subset correlators.

DOI: https://doi.org/10.48550/arXiv.2608.00124

Source: https://arxiv.org/abs/2608.00124v1
