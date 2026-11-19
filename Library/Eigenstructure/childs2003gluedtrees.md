---
bibkey: childs2003gluedtrees
authors: Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman
year: 2003
title: "Exponential algorithmic speedup by a quantum walk"
doi: 10.48550/arXiv.quant-ph/0209131
url: https://arxiv.org/abs/quant-ph/0209131v2
claim: "Section III.D, Lemmas 1 and 2 give the finite-time averaged endpoint estimate and its inverse-cubic spectral separation."
strata_touched:
  - D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap
license: citation-only
triage: anchor
---

# Central defect spectral separation and endpoint averaging

## Locator

Childs et al., *Exponential algorithmic speedup by a quantum walk*,
[arXiv:quant-ph/0209131v2](https://arxiv.org/abs/quant-ph/0209131v2),
Section III.D, Lemma 1, equations (42)-(49), and Lemma 2, equations (50) and (64).
The Lemma 1 derivation is on PDF pages 13-14 of this version. The conference
publication is STOC 2003, DOI [10.1145/780542.780552](https://doi.org/10.1145/780542.780552).
DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131).

## Spectral scope

The receiving matrix is the real symmetric path on $2n$ vertices with zero
diagonal, unit nearest-neighbour entries except for the central edge of
weight $\sqrt 2$, and zero other entries. Its characteristic roots retain
all algebraic multiplicities. The receiving proof uses Robin endpoint
observability for every real energy, positive rank-one threshold counts
and exact reflection factorization. It does not use the source's stated
root count as a completeness certificate.

The uniform spectral estimate is one input to the paper's time-averaged
EXIT argument. It supplies no physical access implementation, EXIT
algorithm, classical oracle lower bound or entire quantum/classical
separation. This is literature-attested mathematics with a receiving
formal proof, without an external open-problem or originality claim.

## Finite-time endpoint scope

For every natural $n\ge1$ and the same actual matrix, write $\delta_n$ for the minimum separation
of the complete algebraic eigenvalue enumeration. Lemma 1 asserts, for
$\epsilon>0$ and $T\ge4n/(\epsilon\delta_n)$,

$$
\frac1T\int_0^T |[\exp(-itJ_n)]_{2n-1,0}|^2\,dt
>\frac{1-\epsilon}{2n}.
$$

The receiving argument retains the exact off-diagonal weight mass
$1-D$, where $D=\sum_i w_i^2$ and $\sum_i w_i=1$. The finite-window
lower bound is $D-2(1-D)/(T\delta_n)$. With $d=2n$, its difference
from $(1-\epsilon)/d$ is at least $\epsilon/d^2>0$, including equality
at the time threshold. Positivity of the actual minimum follows from
the spectral separation bound above; the explicit inverse-cubic estimate is not
substituted into the time hypothesis. Matrix reversal, its endpoint
weight relation, the negative imaginary phase and the real uniform
interval integral are retained. This finite matrix statement supplies
no graph-column realization or oracle implementation, physical access model,
complete EXIT algorithm or classical separation. Strictness holds for every
$\epsilon>0$, including $\epsilon\ge1$, and for $n=1$.

The complete application derivation and supplier correspondence are retained
in the existing [central-defect Blueprint](../../Blueprint/D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap.md).
The endpoint consequence is reuse-only application exposition of existing
frozen results and pinned upstream suppliers, with no separate frozen
endpoint declaration and no new mathematical-content claim.

Only citation and mathematical attribution are supplied; no third-party
program, proof code or paper text is transplanted.
