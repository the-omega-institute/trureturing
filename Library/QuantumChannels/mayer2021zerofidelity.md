---
bibkey: mayer2021zerofidelity
authors: K. Mayer
year: 2021
title: "A short note on the 0-fidelity"
doi: 10.48550/arXiv.2109.09629
url: https://arxiv.org/abs/2109.09629v1
claim: "For every n-qubit process, the process fidelity and the 0-fidelity defined by product single-qubit SIC states satisfy 1 − (3/2)(1 − F_0) ≤ F ≤ F_0; an SDP for n ≤ 4 suggests that the lower bound is tight for all n, which is conjectured, and a description of the worst-case process is stated as an open problem."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness
license: citation-only
triage: anchor
---

# Mayer, a short note on the 0-fidelity

K. Mayer, *A short note on the 0-fidelity*, arXiv:2109.09629v1 (20 September 2021; quant-ph; the
only version).

## Verified locator

DOI: 10.48550/arXiv.2109.09629.
Primary version: https://arxiv.org/abs/2109.09629v1.
The TeX source `main.tex` of v1 supplies §I (Definitions 1 and 2), §II (Theorem 1 and its proof
through the operator $\Gamma$), §III (the semidefinite programs and the conjecture) and §IV (the
open problem).

## Source statements

0-fidelity (Definition 1): "$F_0(\cE)=\frac{1}{d^2}\sum_{k=1}^{d^2}\bra{\psi_k}\cE\big(\ket{\psi_k}\bra{\psi_k}\big)\ket{\psi_k}$,
for states $\ket{\psi_k}=\ket{\psi_{k_i}}\otimes\cdots\otimes\ket{\psi_{k_n}}$ such that for all $i$,
$\{\ket{\psi_{k_i}}\}_{k_i=1}^4$ is a single-qubit SIC-POVM", where a single-qubit SIC-POVM satisfies
"$|\braket{\psi_i}{\psi_j}|^2=\frac{1}{3}\quad i\ne j$" and $d=2^n$.

Process fidelity (Definition 2): "$F(\cE) = \bra{\phi}(\cI\otimes\cE)\big(\ket{\phi}\bra{\phi}\big)\ket{\phi}$".
The maximally entangled state is displayed in §II as "$\ket{\phi} = \frac{1}{\sqrt{d}}\sum_{x=1}^{d^2}\ket{x}\otimes\ket{x}$"
for an orthonormal basis $\{\ket{x}\}_{x=1}^{d}$ of $\mathbb C^d$; the upper summation index $d^2$ is
inconsistent with that basis and with the normalization $1/\sqrt d$. The repository reads the sum over
the $d$ basis labels, which gives the normalized maximally entangled vector
(`D5/S3/QuantumBounds/PeritoTsirelson.maxEntangledVector`).

Theorem 1: "Let $\cE$ be an $n$-qubit process with $0$-fidelity $F_0$ and process fidelity $F$. Then
$1-\frac{3}{2}(1-F_0)\le F \le F_0.$"

Conjecture (§III): "we … find that the solution is $1-\frac{3}{2}(1-F_0)$, independent of $n$ for
$n\le4$. This leads us to conjecture that the lower bound in Th.~1 is tight for all $n$."

Open problem (§IV): "A description of the worst-case process is an open problem."

## Scope

The lower bound of Theorem 1 is proved in the note through the spectrum of the operator $\Gamma$; its
tightness for every $n$ and the worst-case processes are left open. For $n=1$ the product states form
a 2-design and the lower bound holds with equality for every process.
