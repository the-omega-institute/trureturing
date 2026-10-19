---
bibkey: rudzinski2024extremequantumness
authors: Marcin Rudziński; Adam Burchardt; Karol Życzkowski
year: 2024
title: "Orthonormal bases of extreme quantumness"
doi: 10.22331/q-2024-01-25-1234
url: https://arxiv.org/abs/2306.00532v3
claim: "For a spin-j state psi identified with a symmetric state F(psi) of 2j qubits by |j,m> -> |D_{2j,j-m}> (Eq. (8)), the t-anticoherence is A_t(psi) = ((t+1)/t)[1 - tr(rho_t(F(psi))^2)] with rho_t the t-qubit reduced state (Eqs. (12)-(14)), and the quantumness of an orthonormal basis given by the columns of a unitary U is B_t(U) = (1/N) sum_i A_t(psi_i) (Eq. (15)). The paper conjectures (Conjecture 1) that for N = 4 (j = 3/2) the matrix U_4^c of Eq. (21), with B_1 = 1/9, gives the most spin-coherent (classical) basis."
strata_touched:
  - D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis
license: citation-only
triage: anchor
---

# Orthonormal bases of extreme quantumness

Marcin Rudziński, Adam Burchardt, Karol Życzkowski, Quantum 8, 1234 (2024),
arXiv:2306.00532v3 (quant-ph). The arXiv v1 title was "Orthonormal bases of
extreme spin coherence". Quotations are from the arXiv v3 TeX source, with
equation numbers as in the arXiv v3 HTML.

The identification of spin j with the symmetric subspace of 2j qubits (Eq. (8)):

> By identifying the eigenstates of the $J_z$ operator with Dicke states $F\;:\; \ket{j,m} \;\mapsto \; \ket{D_{2j, j-m}},$ one can relate a $\mathcal{H}_{2j+1}$ state space with symmetric subspace of $ \mathcal{H}_{2}^{\otimes 2j} $

The Dicke states are described as "a uniform superposition of states with a
given number of $k$ excitations" (Eq. (6)).

The reduced state, its purity and the anticoherence (Eqs. (12)–(14)):

> For a pure symmetric quantum state of $2j$ subsystems $\ket{\psi}\in \mathcal{H}_{2}^{\otimes 2j}$, we consider a t-partite reduced density operator, $\rho_t (\psi ):= \text{tr}_{1,\ldots , 2j-t} \,  \ket{\psi} \bra{\psi},$ and analyze its purity, $R_t(\ket{\psi}) := \text{tr}\, \big(\rho_t (\psi )^2 \big).$

> $\mathcal{A}_t(\ket{\psi})=\frac{t+1}{t}[1-R_t(F(\ket{\psi}))].$

The basis measure (Eq. (15)):

> we propose the quantumness measure $\mathcal{B}_t$ for an orthonormal basis using the arithmetic mean of $t$-anticoherence measure of constituting states $\mathcal{B}_t(U)=\sum_{i=1}^{N} \frac{\mathcal{A}_t(\ket{\psi_i})}{N}.$

with the convention "$U=(U_{ki})$, where $U_{ki}=\braket{j,m|\psi_i}$, with $m=j+1-k$".

The conjectured minimizer for $N = 4$ (Eq. (21)):

> $U_4^{c}\text{=}\frac{1}{\sqrt{18(3\text{-}2\sqrt{2})}}\left(\begin{matrix} 1&1&1&\tau\sqrt{3}\\\nu&\nu \omega_3&\nu \omega^{2}_3&0\\\nu&\nu \omega^{2}_3&\nu \omega_3&0\\\tau&\tau&\tau&\text{-}\sqrt{3}\end{matrix}\right),$ where $\nu=\sqrt{3}(2-\sqrt{2})$, $\tau=3-2\sqrt{2}$ and $\omega_3=e^{i2\pi/3}$.

Conjecture 1:

> The matrix $U_4^{c}$ given in \cref{U-4-max}, for which  $\mathcal{B}_1=\frac{1}{9}$, leads to the most spin-coherent (classical) basis in $\mathcal{H}_4$.

Here `\cref{U-4-max}` is Eq. (21). The source obtains $U_4^c$ "by an
observation of specific symmetries of purely numerical expression and then
using them as constraints to reduce the problem to finding an extremum of a
one parameter function".

## Verified locator

- DOI: https://doi.org/10.22331/q-2024-01-25-1234 (Quantum, open access).
- URL: https://arxiv.org/abs/2306.00532v3 (v3, 2024-01-17, the latest
  version; source `quantum-template.tex`, md5
  `6a4822dead50e25f467b95f9a2426d90`): the Dicke states and the
  identification (l. 198–214), the reduced state, purity, anticoherence and
  basis measure (l. 242–270), the matrix convention (l. 279), Eq. (21)
  (l. 387–395) and Conjecture 1 (l. 420–422).
