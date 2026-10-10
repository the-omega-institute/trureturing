---
bibkey: wei2024magicnoise
authors: Fuchuan Wei and Zi-Wen Liu
year: 2024
title: Noise robustness and threshold of many-body quantum magic
doi: null
url: https://arxiv.org/abs/2410.21215v1
claim: The local-depolarizing CCZ magic-capacity threshold is conjectured to be 1/3; stabilizer normal forms and robustness faithfulness specify its meaning.
strata_touched:
  - D5/S3/Quantum/Information/CCZMagicCapacityThreshold
license: citation-only
triage: anchor
---

# Noise robustness and the CCZ capacity conjecture

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2410.21215v1

The Crossref title query for “Noise robustness and threshold of many-body quantum magic” returns no exact title match. The locator is the arXiv v1 manuscript.

## Definitions and source statements

On printed page 2:

> Let $\mathrm C^{n-1}Z=\operatorname{diag}(1,\cdots,1,-1)$ denote the multi-controlled-Z gate on $n$-qubits, with $\mathrm C^0Z=Z$.

> Let $\mathrm{STAB}_n$ denote the set of all $n$-qubit stabilizer states, namely the convex hull of all pure stabilizer states.

> For a $n$-qubit state $\rho$, its robustness of magic (RoM), denoted by $\mathcal R(\rho)$, is defined as
> $\mathcal R(\rho)=\min_{\sigma,\tau\in\mathrm{STAB}_n}\{2a+1\mid\rho=(a+1)\sigma-a\tau,a\geq0\}$.

The source's property i) on page 2 states that “$\mathcal R(\cdot)$ is faithful, i.e., $\mathcal R(\sigma)=1$ iff $\sigma\in\mathrm{STAB}$”. Faithfulness makes capacity one equivalent to every permitted stabilizer input having stabilizer-mixture output. The Lean claim uses that membership formulation; it does not define or optimize RoM.

On printed page 2:

> As a standard noise model, we primarily consider the independent depolarizing noise $\mathcal E_\lambda^{\otimes n}$ acting on the $n$-body quantum system, which leaves the qubits it acts on unchanged with probability $1-\lambda$, and replaces them with $\mathbb I_2/2$ with probability $\lambda$.

The source writes $\mathcal G(\sigma)=\operatorname{Tr}(\sigma)\mathbb I_2/2$ and $\mathcal E_\lambda=(1-\lambda)\mathcal I+\lambda\mathcal G$. Thus `depol` acts on arbitrary single-qubit matrices, and `depolA` applies it to coordinates 0, 1 and 2 of the six-qubit space.

On printed page 3, following Seddon–Campbell [31]:

> Define the magic capacity [31] of the $\mathrm C^{n-1}Z$ gate as $\mathcal C(\mathrm C^{n-1}Z)=\max_{\ket s}\mathcal R(\mathrm C^{n-1}Z\otimes\mathbb I_{2^n}\ket s)$, where the maximum is taken over all $2n$-qubit pure stabilizer states $\ket s$.

On printed page 11, Appendix D, Eq. (D2):

> Any pure $n$-qubit stabilizer state has the form
> $\ket{\mathcal K,q,\mathbf b}:=\frac1{\sqrt{|\mathcal K|}}\sum_{x\in\mathcal K}i^{\mathbf b\cdot x}(-1)^{q(x)}\ket x$,
> where $\mathcal K\subset\mathbb F_2^n$ is an affine subspace, $\mathbf b\in\mathbb F_2^n$, $q$ is a quadratic form, and $i=\sqrt{-1}$.

The coefficient encoding uses `Fin n → Bool` for computational labels and `Fin n → ZMod 2` for the affine support. The binary dot product in the exponent of $i$ uses integer lifts before summation. Quadratic polynomials use upper-triangular binary coefficients, including diagonal terms. Nonempty support is required. These conventions are fixed in [the source-to-Lean statement](https://github.com/the-omega-institute/trureturing/issues/15085).

On printed page 6, Section VII:

> We conjecture that the magic capacity threshold for $\mathrm{CC}Z$ under local depolarizing noise is $1/3$.

The conjecture concerns a gate with a reference system. The paper's proved $1/3$ threshold for the three-qubit state $\mathrm{CC}Z\ket{+++}$ is a different statement.

## Use and boundary

The settling module refutes the membership claim at $\lambda=1/2$ with the six-qubit stabilizer input $\Omega=8^{-1/2}\sum_x\ket{x,x}$. A separating matrix has nonnegative trace pairing with every element of `STAB 6` and trace pairing $-7/1024$ with this noisy output. The diagonal restriction of the stabilizer normal form uses the quadratic carry term $\sum_i b_A(i)b_B(i)x_i^2$ together with the binary phase vector $b_A+b_B$.

The exact capacity threshold, the general reference advantage for $\mathrm C^{n-1}Z$, and the source's numerically reported dephasing threshold near $0.645$ remain open. The source's state-threshold theorem and its noiseless diagonal-gate capacity bound are not refuted by this example.
