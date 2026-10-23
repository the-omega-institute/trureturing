---
bibkey: girardplavalasikora2021jordan
authors: Mark Girard; Martin Plávala; Jamie Sikora
year: 2021
title: "Jordan products of quantum channels and their compatibility"
doi: 10.1038/s41467-021-22275-0
url: https://arxiv.org/abs/2009.03279v1
claim: "Two channels Φ_1, Φ_2 are Jordan compatible if some Hermitian A on X ⊗ X_1 ⊗ X_2 with Tr_{X_1}(A) = Tr_{X_2}(A) = J(1_{L(X)}) makes the generalized Jordan product Φ_1 ⊙_A Φ_2, whose Choi matrix is (1 ⊗ Φ_1 ⊗ Φ_2)(A), completely positive (Definitions 25 and 27). Jordan compatible channels are compatible (Proposition 26), and compatible invertible channels are Jordan compatible (Theorem 30). The authors conjecture that no pair of compatible channels fails to be Jordan compatible."
strata_touched:
  - D5/S3/QuantumChannels/JordanCompatibilityRefutation
license: citation-only
triage: anchor
---

# Girard–Plávala–Sikora, Jordan products of quantum channels and their compatibility

M. Girard, M. Plávala and J. Sikora, *Jordan products of quantum channels and their compatibility*, Nat. Commun. **12**, 2129 (2021), DOI 10.1038/s41467-021-22275-0; arXiv:2009.03279 [quant-ph] (v1, the only version).

## Verified locator

DOI: 10.1038/s41467-021-22275-0 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2009.03279v1.
Source: https://arxiv.org/pdf/2009.03279v1 (text read from the PDF):
- §5.3, Definition 25 with Eqs. (117)–(120), Proposition 26 and Definition 27;
- §5.4, Lemma 29, Theorem 30 and the conjecture after its proof.

## Source statements

Definition 25: "Let X = X_1 = X_2 be complex Euclidean spaces and let A ∈ Herm(X ⊗ X_1 ⊗ X_2) be an operator satisfying Tr_{X_1}(A) = Tr_{X_2}(A) = Σ_{i,j=1}^{dim(X)} E_{i,j} ⊗ E_{i,j}. (117) Let Φ_1 ∈ T(X, Y_1) and Φ_2 ∈ T(X, Y_2) be linear maps. The generalized Jordan product of the maps Φ_1 and Φ_2 with respect to the operator A is the linear map Φ_1 ⊙_A Φ_2 ∈ T(X, Y_1 ⊗ Y_2) whose Choi representation is the operator J(Φ_1 ⊙_A Φ_2) ∈ L(X ⊗ Y_1 ⊗ Y_2) given by J(Φ_1 ⊙_A Φ_2) = (1_{L(X)} ⊗ Φ_1 ⊗ Φ_2)(A). (119)"

Definition 27: "We say that Φ_1 ∈ C(X, Y_1) and Φ_2 ∈ C(X, Y_2) are Jordan compatible if there exists an operator A ∈ Herm(X ⊗ X_1 ⊗ X_2) satisfying (117) (where X = X_1 = X_2) such that Φ_1 ⊙_A Φ_2 is completely positive."

Theorem 30: "Let Φ_1 ∈ C(X, Y_1) and Φ_2 ∈ C(X, Y_2) be two quantum channels, such that they have inverse linear maps Φ_1^{−1} ∈ T(Y_1, X) and Φ_2^{−1} ∈ T(Y_2, X). The channels Φ_1 and Φ_2 are compatible if and only if they are Jordan compatible."

After its proof: "Almost all linear maps in T(X) are invertible. Hence naive numerical approaches cannot be used to search for a pair of channels Φ_1, Φ_2 ∈ C(X) that are compatible but not Jordan compatible (if such a pair exists), as this would involve randomly sampling from a set having zero measure. For this reason, the question of whether compatibility of channels is equivalent to Jordan compatibility remains open. We conjecture that such a pair of channels does not exists."

## Reading used by the repository

Channels are maps on d × d complex matrices of Kraus form R ↦ Σ_k K_k R K_k^† with Σ_k K_k^† K_k = 1, the finite-dimensional form of completely positive trace-preserving maps. Two channels are compatible if some channel into M_d ⊗ M_d has them as its two partial traces. The conjecture is read as: for every d, every compatible pair of channels on M_d is Jordan compatible. Complete positivity of Φ_1 ⊙_A Φ_2 is the positive semidefiniteness of its Choi matrix (1 ⊗ Φ_1 ⊗ Φ_2)(A), by Choi's theorem. A is only required to be Hermitian.
