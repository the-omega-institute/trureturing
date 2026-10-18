---
bibkey: kopel2026sharpnorm
authors: E. Kopel
year: 2026
title: "A sharp norm inequality for entanglement-breaking channels"
doi: 10.48550/arXiv.2609.27906
url: https://arxiv.org/abs/2609.27906v1
claim: "Theorem 1: the Bloch data (A, c) of an entanglement-breaking channel on M_d satisfy ‖A‖_*² + (d(d−1)/2)|c|² ≤ (d−1)²; open question 3 asks whether the coefficient d(d−1)/2 is optimal."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient
  - D5/S3/QuadraticForms/WeightedGramContraction
  - D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity
  - D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity
license: citation-only
triage: anchor
---

# Kopel, A sharp norm inequality for entanglement-breaking channels

E. Kopel, *A sharp norm inequality for entanglement-breaking channels*, arXiv:2609.27906v1
(submitted 21 August 2026; quant-ph, cross-listed math-ph and math.OA).

## Verified locator

DOI: 10.48550/arXiv.2609.27906.
Primary version: https://arxiv.org/abs/2609.27906v1 (the only arXiv version).
The TeX source of v1 supplies the Holevo form (Eq. `eq:holevo`, Section 1), the Bloch
parameterisation (Section 2), Theorem 1 (`thm:main`, Section 3), the equality discussion
(Section 4) and the list of open questions (Section 8); the numbering is the printed one.

## Source statements

The source macros `\Tr`, `\I` and `\nuc{·}` are written out as $\mathrm{Tr}$, $I$ and $\|\cdot\|_*$.

Section 1: "A completely positive trace-preserving map $\Phi$ is \emph{entanglement breaking} (EB) if $(\mathrm{id}\otimes\Phi)(\rho)$ is separable for every input, equivalently if $\Phi$ admits a Holevo form $\Phi(\rho) = \sum_k \mathrm{Tr}[E_k\rho]\,\sigma_k$ with $\{E_k\}$ a POVM and $\sigma_k$ states".

Section 2: "Fix a Hermitian traceless basis $\{\lambda_i\}_{i=1}^{d^2-1}$ of $M_d$ normalised by $\mathrm{Tr}[\lambda_i\lambda_j]=2\delta_{ij}$. […] Every state is $\rho = \tfrac1d I + \tfrac12\,r\cdot\lambda$, $|r|^2 \le \tfrac{2(d-1)}{d}$, with equality precisely for pure states. A channel acts affinely on the Bloch vector, $r\mapsto Ar+c$."

Theorem 1: "Let $\Phi$ be an entanglement-breaking channel on $M_d$ with Bloch data $(A,c)$. Then $\|A\|_*^2 + \frac{d(d-1)}{2}\,|c|^2 \le (d-1)^2$."

Section 4: "Whether equality with $c\neq0$ is achievable for $d\ge3$ is not settled here; condition (ii) becomes restrictive as the number of rank-one terms grows."

Section 8, item 3: "Is the coefficient $d(d-1)/2$ optimal? It combines two separately sharp bounds which may not be simultaneously saturable with $c\neq0$ in higher dimension."

## Scope

In the basis $\{\lambda_i\}$ the Bloch data of a channel are $A_{ij}=\tfrac12\mathrm{Tr}[\lambda_i\Phi(\lambda_j)]$ and $c_i=\mathrm{Tr}[\lambda_i\Phi(I/d)]$, and $\|A\|_*$ is the nuclear (trace) norm. The paper proves Theorem 1 from the Holevo form, shows equality for the completely dephasing channel in every dimension and for a family with $c\neq0$ at $d=2$, and relates the inequality to the covariance-matrix separability criterion.

## Supplied v2 additions (17 October 2026 correspondence)

The author supplied `EB_note_v2_additions_external.pdf` in the correspondence on
17 October 2026. This is a separate source from the public v1 cited above.
Lemma 4 states that, for finite nonzero real vector families and strictly
positive weights, the nuclear norm of their weighted outer-product sum equals
the sum of the weighted products of their lengths exactly when the normalized
Gram matrices agree. Its proof passes through a common contraction attaining
each pairing, then constructs the converse contraction by extending the span
isometry by zero on the orthogonal complement.

The supplied PDF has SHA-256
`15c81e5f680bfd8a2822e6bae33eb2daade462ebdeffe7f57f2821e57f8fa1d1`.
Lemma 4 appears on page 2 and Theorem 5 on page 3.

`D5/S3/QuadraticForms/WeightedGramContraction` formalizes the geometric
common-contraction step. `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity`
proves real rectangular polar contraction and duality for the actual CFC trace
norm, and then the full Lemma 4 equivalence. These are formalizations of the
supplied result, with no claim of mathematical novelty.

`D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity` proves the
matrix-purity and centered-Gram portion of Theorem 5: for a fixed complete
rank-one POVM and pure outputs, the off-diagonal equation (7) forces
`rho = Phi(I/d)`, every output expectation to equal `P`, `Tr(rho²) = P`,
`1/d ≤ P < 1` for a nonconstant channel, and the centered Hilbert–Schmidt
pairing formula. The rank-one and pure-output assumptions are explicit here.
The full Theorem 5 remains unformalized: this result does not derive those
assumptions from saturation of Theorem 1, establish the saturation iff (7), or
identify the two Bloch norm values. Those require the general bound's equality
chain and the Bloch/Hilbert–Schmidt normalization bridges, beyond the existing
constant-channel coefficient proof.
