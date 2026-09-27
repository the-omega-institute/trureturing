---
bibkey: garciafernandez2026openqc
authors: Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore
year: 2026
title: "Open-boundary integrable quantum circuits with different geometries"
doi: 10.48550/arXiv.2607.02093
url: https://arxiv.org/abs/2607.02093v1
claim: "The paper builds open-boundary Yang-Baxter integrable quantum circuits for every configuration of -kappa inhomogeneities (Theorems 1 and 2) and conjectures that the minimum circuit depth with kappa_- such sites is (N + 3)/2 - kappa_- for odd N (Conjecture 1) and (N + 4)/2 - kappa_- for even N (Conjecture 2)."
strata_touched:
  - D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation
  - D5/S3/Quantum/Dynamics/OpenIntegrableCircuitMinDepth
license: citation-only
triage: anchor
---

# Open-boundary integrable quantum circuits with different geometries

The paper constructs Floquet circuits from the double-row transfer matrix of
an open integrable spin chain with inhomogeneities `±κ`. For a configuration

> $\vec{n}=(n_{\kappa_-},\cdots, n_2, n_1)$, with $1\le n_1 < n_2 < \cdots < n_{\kappa_-}\le N$

of the sites carrying `-κ`, Theorem 1 (`n_{κ₋} < N`) gives the circuit

> $\left(\overleftarrow{\prod}_{1 \le r \le \kappa_-}U_{n_{r},n_{r}+1}\right)K_1^R(\kappa)\left(\overrightarrow{\prod}_{1 \le j \le N-1,\ j \neq n_1,\ldots, n_{\kappa_-}}U_{j,j+1}\right)\tilde{K}^L_N(\kappa)$

up to a scalar, and Theorem 2 (`n_{κ₋} = N`) the circuit

> $\tilde{K}^L_N(\kappa)\left(\overleftarrow{\prod}_{1 \le r \le \kappa_- -1}U_{n_{r},n_{r}+1}\right)K_1^R(\kappa)\left(\overrightarrow{\prod}_{j \neq n_1,\ldots, n_{\kappa_-}}U_{j,j+1}\right)$.

Circuits with the same `κ₋` form one equivalence class; the depth is "the
numbers of sequential gate layers required to implement the circuit", and the
paper states:

> **Conjecture 1** For odd $N$ and $0<\kappa_-\le \frac{N-1}{2}$, the minimum
> depth is given by $d=\frac{1}{2}(N+3)-\kappa_-.$
>
> **Conjecture 2** For even $N$ and $0<\kappa_-\le \frac{N}{2}$, the minimum
> depth is given by $d=\frac{1}{2}(N+4)-\kappa_-.$

## Verified locator

- DOI: 10.48550/arXiv.2607.02093 (resolves through doi.org to https://arxiv.org/abs/2607.02093, checked 2026-09-27).
- URL: https://arxiv.org/abs/2607.02093v1 (the only version listed by the arXiv
  API on 2026-09-27); source file `OpenQC.tex`, section "Circuits with minimum
  depth $d$ and independent geometries", `\paragraph{Conjecture 1}` and
  `\paragraph{Conjecture 2}`; Theorems 1 and 2 in the section "General
  construction".
