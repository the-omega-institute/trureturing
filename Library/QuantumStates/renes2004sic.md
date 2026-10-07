---
bibkey: renes2004sic
authors: J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves
year: 2004
title: "Symmetric Informationally Complete Quantum Measurements"
doi: 10.1063/1.1737053
url: https://arxiv.org/abs/quant-ph/0310075v1
claim: "A set of n ≥ C(t+d−1, d−1) unit vectors in C^d is a spherical t-design iff its t-th frame potential Σ_{j,k}|⟨φ_j|φ_k⟩|^{2t} equals n² t!(d−1)!/(t+d−1)!; consequently every SIC-POVM is a 2-design, and every 2-design with d² elements is a SIC-POVM."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness
license: citation-only
triage: anchor
---

# Renes, Blume-Kohout, Scott and Caves, symmetric informationally complete measurements

J. M. Renes, R. Blume-Kohout, A. J. Scott and C. M. Caves, *Symmetric Informationally Complete
Quantum Measurements*, J. Math. Phys. 45, 2171 (2004); arXiv:quant-ph/0310075v1 (13 October 2003).

## Verified locator

DOI: 10.1063/1.1737053.
Preprint: https://arxiv.org/abs/quant-ph/0310075v1 (the only arXiv version).
The TeX source `sicpovmarchive.tex` supplies §2 (frames and spherical $t$-designs, Theorem 2 and
the SIC-POVM consequence).

## Source statements

Spherical design (§2): "A \emph{spherical $t$-design\/} is a set of $n$ normalized vectors
$\{\ket{\phi_k}\in\mathbb{S}^d\}$ such that the average value of any $t$-th order polynomial
$f_t(\psi)$ over the set $\{\ket{\phi_k}\}$ is equal to the average of $f_t(\psi)$ over \emph{all\/}
normalized vectors $\ket{\psi}$."

Theorem 2: "A set of normalized vectors $\{\ket{\phi_k}\in\mathbb{S}^d\}_{k=1}^n$ with
$n\ge{t+d-1 \choose d-1}$ forms a spherical $t$-design if and only if
${\rm Tr}[S_t^2]= \sum_{j,k}|\langle\phi_j|\phi_k\rangle|^{2t} =\frac{n^2 t!\,(d\!-\!1)!}{(t\!+\!d\!-\!1)!}$.
Furthermore, this value is the global minimum of ${\rm Tr}[S_t^2]$."

Consequence (§2): "Immediately we can infer that every SIC-POVM is a 2-design since
Tr$[S_2^2]=\sum_{j,k}|\bracket{\phi_j}{\phi_k}|^4=2d^3/(d+1)$, the required value for a 2-design."

## Scope

For $d=2$ and $n=4$ the 2-design property is the operator identity
$\sum_k(\psi_k\psi_k^\dagger)^{\otimes2}=\frac23(I+\mathrm{SWAP})$ on $\mathbb C^2\otimes\mathbb C^2$; the
repository uses it in this form.
