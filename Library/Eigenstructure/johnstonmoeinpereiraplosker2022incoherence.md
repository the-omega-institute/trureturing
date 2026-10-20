---
bibkey: johnstonmoeinpereiraplosker2022incoherence
authors: Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker
year: 2022
title: Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix
doi: 10.1103/PhysRevA.106.052417
url: https://arxiv.org/abs/2205.05110v2
claim: "Section 5 asks whether the sufficient purity condition for absolute 2-incoherence is necessary in dimension four or higher."
strata_touched:
  - D5/S3/Quantum/Measurement/FactorWidthTwoCone
  - D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation
license: citation-only
triage: anchor
---

# Absolutely k-incoherent states and factor width

## Verified locator

DOI: 10.1103/PhysRevA.106.052417

Source: https://arxiv.org/abs/2205.05110v2

The quotations below refer to the printed pages of arXiv:2205.05110v2.

## Source statements

Section 2.1, page 3: “every mixed state ρ ∈ Mₙ⁺ can be written in the form
ρ = Σⱼ vⱼvⱼ* for some {vⱼ} ⊆ ℂⁿ. In the special case when each vⱼ can be
chosen to have at most k non-zero entries (where 1 ≤ k ≤ n), ρ is called
k-incoherent”. The vectors need not be normalized individually. A finite sum
of their outer products gives the factor-width cone; trace one gives the states.

Definition 1(b), page 4: “⟨v|X|v⟩ ≥ 0 for all |v⟩ ∈ ℂⁿ with at most k non-zero entries; or”.
For k = 2 the support can be parametrized by every coordinate subset of size
at most two and every vector that vanishes outside that subset.

Definition 3, page 10: “A mixed quantum state ρ ∈ Mₙ⁺ is absolutely k-incoherent
if UρU* ∈ I_{k,n} for all unitary matrices U ∈ Mₙ.”

Theorem 7, page 14: “Suppose ρ ∈ Mₙ⁺ is a quantum state with eigenvalues
λ₁, λ₂, …, λₙ. If Σⱼ λⱼ² ≤ 1/(n − 1) then ρ is absolutely 2-incoherent.
The converse holds if n ≤ 3.”

Section 5, page 17: “Theorem 7 gives a sufficient condition for absolute
2-incoherence that is also necessary in dimension n = 3. It is unclear whether
or not it is necessary in dimension n = 4 or higher.”

## Mathematical scope

The Lean statement asks for necessity simultaneously for every natural
dimension at least four. Its negation is established by a five-dimensional
density matrix. Purity is the real part of the trace of the square, equal to
the sum of squared eigenvalues for a Hermitian matrix. Dimension four and a
uniform family over all dimensions at least five are outside the formal result.

The theorem proving sufficiency and its low-dimensional converse retain their
stated scope. The completeness of the literature screen is ASSUMED-UNVERIFIED;
the question and source attribution do not assert priority over unpublished work.
