---
bibkey: "frenkel2023integral"
authors: "Péter E. Frenkel"
year: 2023
title: "Integral formula for quantum relative entropy implies data processing inequality"
doi: "10.22331/q-2023-09-07-1102"
url: "https://arxiv.org/abs/2208.12194"
claim: "Lemmas 4–5 establish the shift and its derivative and endpoint behavior. Theorem 6 expresses finite-matrix Umegaki relative entropy as a weighted negative-part trace integral of the affine pencil with an affine trace correction."
strata_touched:
  - D5/S3/Quantum/Divergence/HockeyStickPencilIntegral
  - D5/S3/Quantum/Divergence/UmegakiPencilIntegral
  - D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral
  - D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy
license: "citation-only"
triage: "anchor"
---

# Integral formula for quantum relative entropy implies data processing inequality

## Verified locator

[Journal record](https://doi.org/10.22331/q-2023-09-07-1102) · [arXiv record](https://arxiv.org/abs/2208.12194) · [Lemmas 4–5 and Theorem 6](https://arxiv.org/pdf/2208.12194)

## Formalization scope

Lemmas 4–5 establish the shift and its derivative and endpoint behavior. Theorem 6 expresses finite-matrix Umegaki relative entropy as a weighted negative-part trace integral of the affine pencil with an affine trace correction.

The proof uses the determinant zeros of the shifted pencil and complex residues. The fixed-shift integral uses the same shift and evaluates each strictly negative inertia contribution on its real half-line.

The finite PSD/PD case is also proved by a real scalar shift in the original
eigenbases, followed by the congruence and the integrated negative-inertia
identity. The trace correction is the limit of the shifted pairing at infinity.
At a zero eigenvalue the term \(a\log a\) has its continuous value zero.

The equal-trace shifted determinant formula in Fibonacci observation entropy,
`thermal-operation-width-renewal/fibonacci-observation-entropy/proof.txt` §18,
uses the same real scalar shift with the common reference \(b=1\). Equal
dimension and trace cancel its two correction sums, including for singular
positive semidefinite matrices. The resulting integral is the difference of
the two real trace-entropy pairings.

Related forms appear in Hirche and Tomamichel’s Corollary 2.3 and Eq. (2.22),
Jenčová’s Corollary 1, and Schmitt’s Corollary 4.2. Liu, Hirche and Cheng’s §4.1
gives an operator layer-cake proof. [Hirche and Tomamichel](https://arxiv.org/abs/2306.12343)
· [Jenčová](https://arxiv.org/abs/2303.11707) · [Schmitt](https://arxiv.org/abs/2609.12547)
· [Liu, Hirche and Cheng](https://arxiv.org/abs/2507.07065)

Both tails of Theorem 6 are transformed by the same involution \(s\mapsto s/(s-1)\) in the forward-profile identity. The integral on the central interval vanishes by positive semidefiniteness.
