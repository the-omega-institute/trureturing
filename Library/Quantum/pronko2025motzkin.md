---
bibkey: pronko2025motzkin
authors: A. G. Pronko
year: 2025
title: "Periodic Motzkin chain: Ground states and symmetries"
doi: 10.48550/arXiv.2504.00835
url: https://arxiv.org/abs/2504.00835v3
claim: "The paper studies the periodic Motzkin spin-1 chain H^periodic = sum_{i=1}^{N-1} Pi_{i,i+1} + Pi_{N,1}, conjectures (Conjecture 1) that its ground states are the 2N+1 path sums v_{S^z}, and conjectures (Conjecture 2) that the operators Sigma^{+-}, sums of products s_1^{r_1} ... s_N^{r_N} over r_i in {-2,...,2} with r_1 + ... + r_N = +-1, commute with the Hamiltonian and send v_{S^z} to nonzero multiples of v_{S^z+-1}, and v_{+-N} to 0."
strata_touched:
  - D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering
license: citation-only
triage: anchor
---

# Periodic Motzkin chain: Ground states and symmetries

Pronko represents the steps of Motzkin paths by the basis vectors
$\ket{\mathrm u}, \ket{\mathrm f}, \ket{\mathrm d}$ of $\mathbb C^3$ and uses
the spin-1 matrices (eq. `spin1rep`)

> $s^{+}=\begin{pmatrix}0&1&0\\0&0&1\\0&0&0\end{pmatrix}$,
> $s^{-}=\begin{pmatrix}0&0&0\\1&0&0\\0&1&0\end{pmatrix}$,

with $s_j^{\pm}$ acting on the $j$-th factor of $(\mathbb C^3)^{\otimes N}$.
The local projector is $\Pi = \mathrm U + \mathrm D + \mathrm F$ with
(eq. `UDF`) $\mathrm U=\frac12(\ket{\mathrm{uf}}-\ket{\mathrm{fu}})(\bra{\mathrm{uf}}-\bra{\mathrm{fu}})$,
$\mathrm D=\frac12(\ket{\mathrm{df}}-\ket{\mathrm{fd}})(\bra{\mathrm{df}}-\bra{\mathrm{fd}})$,
$\mathrm F=\frac12(\ket{\mathrm{ud}}-\ket{\mathrm{ff}})(\bra{\mathrm{ud}}-\bra{\mathrm{ff}})$,
and the periodic Hamiltonian is (eq. `Hpbc`)
$\mathrm H^{\text{Periodic}}=\sum_{i=1}^{N-1}\Pi_{i,i+1}+\Pi_{N,1}$.

Conjecture 1 describes the ground states $\ket{v_{S^z}}$ as "sums of paths
connecting points $(x,y)=(0,0)$ and $(x,y)=(N,S^z)$, having at each step
$\Delta x=1$ and $\Delta y\in \{-1,0,1\}$". The raising and lowering operators
should satisfy (eqs. `Sigmavec`, `SpmH`)

> $\Sigma^\pm\ket{v_{S^z}} = c_\pm(S^z)\ket{v_{S^z\pm1}}$ for $S^z\ne \pm N$,
> $0$ for $S^z=\pm N$, where $c_\pm(S^z)\ne 0$ are some constants;
> $[\Sigma^\pm,\mathrm{H}^\text{periodic}]=0$,

and Conjecture 2 reads

> There exist raising and lowering operators satisfying \eqref{Sigmavec} and
> \eqref{SpmH}, and they are given by
> $\Sigma^\pm=\sum_{r_1,\dots,r_N\in\{-2,-1,0,1,2\},\ r_1+\dots+r_N=\pm 1} s_1^{r_1}\cdots s_N^{r_N}$
> with the following notation: $s_i^{0}\equiv I$, $s_i^{\pm 1}\equiv s_i^{\pm}$,
> $s_i^{\pm 2}\equiv (s_i^{\pm})^2$.

The paper reports symbolic verification up to $N = 6$.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2504.00835
- URL: https://arxiv.org/abs/2504.00835v3
- Journal: Nuclear Physics B 1017 (2025) 116963,
  https://doi.org/10.1016/j.nuclphysb.2025.116963 (Crossref record retrieved
  2026-09-27).
- Version and location: arXiv:2504.00835v3, source file `sympmot_3a.tex`:
  eq. `spin1rep` (line 261), eq. `UDF` (line 367), eq. `Hpbc` (line 430),
  Conjecture 1 (lines 493–502), eqs. `Sigmavec` and `SpmH` (lines 553–568),
  Conjecture 2 (lines 570–593); retrieved 2026-09-27.
