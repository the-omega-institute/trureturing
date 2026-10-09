---
bibkey: johnston2026ldoi
authors: Nathaniel Johnston, Vincent Russo
year: 2026
title: "Distinguishability of locally diagonal orthogonally invariant quantum states"
doi: null
url: https://arxiv.org/abs/2604.12808v1
claim: "Example 17 asks whether opt_LOCC(E) = 1/2 − (n − 2)/(2n²) for the uniform Fourier LDOI ensemble with n ≥ 3; it proves opt_PPT(E) = opt_SEP(E) = 1/2."
strata_touched:
  - D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2604.12808v1

Crossref's bibliographic query for the exact title and both authors returns no
matching title among its eight results; no journal DOI is identified.

Section 1, p. 4, defines the optimization conventions:

> We use the notation optPPT(E) and optSEP(E) for the optimal success probabilities under PPT and separable measurements, and optLOCC(E) for the supremum over LOCC measurements (since LOCC is not topologically closed, the supremum may not be attained).

Definition 6, p. 9, Eq. (21), defines orthonormal LDOI bases by a unitary U and
coefficients A satisfying |aᵢⱼ|² + |aⱼᵢ|² = 1. The diagonal vectors are
Σₖ uᵢₖ|kk⟩; for i < j the two vectors are aᵢⱼ|ij⟩ + aⱼᵢ|ji⟩ and
conj(aⱼᵢ)|ij⟩ − conj(aᵢⱼ)|ji⟩. The coefficients in Example 17 are real and
all equal to 1/√2, so conjugation leaves them unchanged.

Theorem 10, pp. 11–13, gives the bounds for uniform ensembles. Its LOCC lower
bound uses a product measurement and its PPT upper bound admits parameters cᵢ.

Example 17, pp. 18–19, Eqs. (61)–(65), specializes to the Fourier unitary:

> Let n ≥ 3 and consider an orthonormal LDOI basis arising from Definition 6 with A = (1/√2)1ₙ (the all-ones matrix scaled by 1/√2) and U equal to the n-dimensional Fourier matrix. Define the uniform ensemble E = {(1/n², |ϕᵢⱼ⟩⟨ϕᵢⱼ|) : 1 ≤ i, j ≤ n}, where |ϕᵢⱼ⟩ are the basis vectors.

Equation (61) gives optLOCC(E) ≥ 1/2 − (n − 2)/(2n²) and optPPT(E) ≤ 1/2.
Equations (62)–(65) construct a PPT measurement attaining 1/2. Its effects are
also separable, yielding optSEP(E) = 1/2.

The explicit question on p. 19 is:

> Whether the lower bound in Equation (61) is tight—that is, whether opt_LOCC(E) = 1/2 − (n − 2)/(2n²)—remains an open question.

> Whether optLOCC(E) coincides with one of these bounds or takes an intermediate value remains unknown; resolving this would require new techniques for analyzing the full LOCC hierarchy beyond the product measurement strategy of Theorem 10.

The Conclusion, pp. 20–21, repeats the Fourier question and asks whether
optLOCC(E) = optPPT(E) holds for every uniform orthonormal LDOI ensemble.

## Formal scope

The Fourier LDOI refutation uses zero-based Fin n indices and the normalized
positive Fourier entries exp(2π I i k / n)/√n. A protocol is a finite tree of
complete square Kraus instruments on Alice or Bob, with a guessed label at
each leaf. The success probability is the uniform average of correct-leaf
squared norms. The public optLOCC is the supremum over finite-round LOCC trees
with dimension-preserving local Kraus instruments. Every finite-round LOCC
measurement has this form, since each Kraus operator's output space pulls
back by polar decomposition. This correspondence is an argument on paper.
The public claim is the literal equality optLOCC n = lower n for every n ≥ 3.
Local completeness and induction on the tree give success n T ≤ 1. The checked
counterexample has n = 3 and success 3 T = 1/2, so optLOCC 3 ≥ 1/2 > 4/9.
The PPT upper bound, the exact optimization value and an all-dimension
protocol family are not statements of the settling Lean module.
