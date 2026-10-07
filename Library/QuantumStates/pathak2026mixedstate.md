---
bibkey: pathak2026mixedstate
authors: T. Pathak
year: 2026
title: Mixed-State Entanglement in a Minimal Model of Quantum Chaos
doi: 10.48550/arXiv.2603.14292
url: https://arxiv.org/abs/2603.14292v1
claim: '2𝓔(t) = I_{A:B}^{(α)}(t), hold for generic states at all times t.'
strata_touched:
  - D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2603.14292

Source: https://arxiv.org/abs/2603.14292v1

PDF: https://arxiv.org/pdf/2603.14292v1

# Mixed-state entanglement in the kicked Ising chain

Page numbers refer to the arXiv v1 PDF.

Conjecture 1, p. 3, states:

> 2𝓔(t) = I_{A:B}^{(α)}(t), hold for generic states at all times t.

Its displayed equation in the source TeX is
`2\mathcal{E}(t)  = I_{A:B}^{(\alpha)}(t),` followed by the sentence
`hold for generic states at all times $t$.`

The model, equations (1)–(2), p. 1, is

$$H_I=J\sum_{i=1}^L\sigma_i^z\sigma_{i+1}^z+\sum_{i=1}^L h_i\sigma_i^z,
\qquad H_K=\sum_{i=1}^L b\sigma_i^x,
\qquad U=U_K U_I,$$

with periodic boundary conditions and $U_I=e^{-iH_I}$, $U_K=e^{-iH_K}$.

> We specifically consider J = π/4, b = −π/4 for our analysis.

The initial product state, equation (3), pp. 1–2, is

$$|\psi_{\theta,\phi}\rangle=\bigotimes_{k=1}^L
\left(\cos(\theta_k/2)|\uparrow\rangle+
 e^{i\phi_k}\sin(\theta_k/2)|\downarrow\rangle\right).$$

Equation (4), p. 2, defines the transverse class by $\theta_k=\pi/2$ at
all sites, and the longitudinal class by $\theta_k\in\{0,\pi\}$ at all sites.

> States which do not belong to these class will henceforth be called generic.

The measures, equations (5) and (9), p. 2, are

$$\mathcal E(t)=\ln\operatorname{tr}\sqrt{
 (\rho_{AB}^{T_B}(t))^\dagger\rho_{AB}^{T_B}(t)},$$

$$I_{A:B}^{(\alpha)}(t)=S_A^{(\alpha)}(t)+S_B^{(\alpha)}(t)-S_{AB}^{(\alpha)}(t),
\qquad S_A^{(\alpha)}=\frac{1}{1-\alpha}\log\operatorname{tr}(\rho_A^\alpha).$$

The Lean claim specializes to $\alpha=1/2$ and quantifies over the periodic
chain length, fields, angles, contiguous nonempty tripartition and integer time.
The square root is real continuous functional calculus on the density matrix.
The partial trace and trace norm reuse existing matrix definitions.

At $L=4$, $A=\{0\}$, $B=\{1\}$, $C=\{2,3\}$ and $t=1$, choose all fields
one and all phases zero, with initial state $|+\rangle|+\rangle|r\rangle|r\rangle$,
where $|r\rangle=(2|0\rangle+|1\rangle)/\sqrt5$.
The two retained qubits have, up to local unitaries, spectrum
$\{16/25,4/25,4/25,1/25\}$, and their partial transpose has spectrum
$\{23/50,17/50,17/50,-7/50\}$.
Consequently $2\mathcal E(1)=\log(1024/625)$ while
$I_{A:B}^{(1/2)}(1)=\log(100/81)$.
This refutes the all-times finite-chain equality. It does not settle the
thermodynamic-limit early-time question or negate the source's results under
its solvable-class and early-time assumptions.
