---
bibkey: krawec2015history
authors: W. O. Krawec
year: 2015
title: "History dependent quantum walk on the cycle with an unbalanced coin"
doi: 10.1016/j.physa.2015.02.061
url: https://arxiv.org/abs/1411.6298v1
claim: "The recycled-coin quantum walk on the d-cycle uses a memory parameter φ ∈ [0, 8). The paper conjectures that its time-averaged distribution is uniform for every non-integer φ: if 12 ∤ d, only φ = 0, 2, 4, 6 give a non-uniform distribution; if 12 ∣ d, only φ = 0, 1, 2, 4, 5, 6 do. It reports numerical verification for d ≤ 300 on the grid φ = m/10."
strata_touched:
  - D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity
license: citation-only
triage: anchor
---

# Krawec, history dependent quantum walk on the cycle with an unbalanced coin

W. O. Krawec, *History dependent quantum walk on the cycle with an unbalanced coin*, Physica A **428**
(2015) 319–331; arXiv:1411.6298v1 (23 November 2014; quant-ph).

## Verified locator

DOI: 10.1016/j.physa.2015.02.061.
Primary version read: https://arxiv.org/abs/1411.6298v1 (the only version).
Source: https://arxiv.org/pdf/1411.6298v1 (text read from the PDF):
- §II, Eqs. (3)–(8);
- §III.B, the uniformity observations;
- §IV, the conjecture.

## Source statements

Eq. (3): "C(θ) = ( cos θ sin θ ; sin θ − cos θ )".

Eq. (4): "Ĉ = |↓⟩₁⟨↓|₁ ⊗ C(π/4) + |↑⟩₁⟨↑|₁ ⊗ C(π/4 (1 + φ))".

Shift (§II): "This shift operator will map basis states |n, c₁, ↓⟩ to |n − 1, c₁, ↓⟩ and |n, c₁, ↑⟩ to |n + 1, c₁, ↑⟩ where all arithmetic is done modulo d".

Eq. (5): "M = |↓↓⟩⟨↓↓| + |↑↓⟩⟨↓↑| + |↓↑⟩⟨↑↓| + |↑↑⟩⟨↑↑|".

Eq. (6): "U = (I_P ⊗ M) · S · (I_P ⊗ Ĉ)".

Eqs. (7)–(8): "p(n, t, φ; ψ₀) = Σ_{c₁,c₂} |⟨n, c₁, c₂|Uᵗ|ψ₀⟩|²" and "p̄(n, φ; ψ₀) = lim_{T→∞} (1/T) Σ_{t=1}^{T} p(n, t, φ; ψ₀)".

§III.B: "for any memory parameter φ ≠ 0, 2, 4, or 6, and for any initial state ψ(0, 0), we observed that the time averaged distribution is uniform if the cycle size d is not divisible by 12. If the cycle size is divisible by 12, then all memory parameters φ ≠ 0, 1, 2, 4, 5, or 6 produced a uniform distribution … we did verify it for all cycle sizes d ≤ 300 … φ = m/10 for m ∈ {0, 1, ···, 79}."

§IV: "only integer values of φ seem to potentially produce non-uniform distributions (non-integer values of φ producing a uniform time averaged distribution). … If d is not divisible by 12 then only φ = 0, 2, 4, 6 produced a non-uniform distribution. This is a conjecture we verified for d ≤ 300 and we leave the proof as an open problem."
