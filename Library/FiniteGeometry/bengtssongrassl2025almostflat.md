---
bibkey: bengtssongrassl2025almostflat
authors: Ingemar Bengtsson; Markus Grassl
year: 2025
title: "A Conjecture on Almost Flat SIC-POVMs"
doi: null
url: https://arxiv.org/abs/2512.13201
claim: "Equation (8) is conjectured for every almost flat SIC fiducial vector in odd dimension."
strata_touched:
  - D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC
license: citation-only
triage: anchor
---

# Bengtsson and Grassl on almost flat SIC fiducials

I. Bengtsson and M. Grassl, *A Conjecture on Almost Flat SIC-POVMs*,
arXiv:2512.13201v1 [quant-ph], 15 Dec 2025.

## Locator

https://arxiv.org/abs/2512.13201

The source quotations below are supplied by the task brief associated with
issue #30316. No independent network retrieval is asserted.

## Source statements

Equation (1):

> Z|r⟩ = ω^r|r⟩ and X|r⟩ = |r + 1⟩, where ω = e^{2πi/d}.

Equation (3) characterizes a SIC orbit by nonidentity displacement overlaps
of modulus $1/\sqrt{d+1}$.

Equations (4)-(5):

> |Ψ⟩ = N|v⟩, |v⟩ = (√x₀, v₁, …, v_{d−1})^T, where x₀ = −2 − √(d+1),
> |v_j|² = 1, v_{−j} = −v_j^*, N² = 1/(d − 1 − x₀).

Here $\sqrt{x_0}=i\sqrt{\sqrt{d+1}+2}$ is purely imaginary.

Equation (8):

> ⟨v|X^{−2j}|v⟩ = (√(d+1) + 1) v_j² for j ≠ 0.

> The conjecture referred to in the title is that this equation holds for all
> almost flat SIC fiducial vectors in odd dimension.

## Mathematical use

The coordinate convention is exactly that of `WindowRegister.shiftMatrix`.
The SIC predicate is reused from `ErewGoldsteinSICStabilizerRefutation`.
Put $s=\sqrt{d+1}$, $C=s+1$ and $L=d+1+s=sC$. Finite character orthogonality
gives the diagonal quartic contraction. Conjugate reflection converts its sum
to a midpoint convolution. The distinguished zero term leaves
$\sum_{k\ne0}\overline{v_k}^{\,2}A_k=C(d-1)$, where
$A_k=\sum_r\overline{v_r}v_{r+2k}$. Oddness ensures $-2k\ne0$, so the SIC
equations give $|A_k|=C$. The sum of the nonnegative squared phase errors is zero.

## Search boundary

The repository and pinned Mathlib are searched locally. The brief supplies the
external statement and preregistration; no exhaustive literature search,
priority claim or independent verification of the external quotations is asserted.
