---
bibkey: zhangxie2026bargmann
authors: Lin Zhang; Bing Xie
year: 2026
title: "A Survey of Bargmann Invariants: Geometric Foundations and Applications"
doi: 10.48550/arXiv.2601.01858
url: https://arxiv.org/abs/2601.01858v2
claim: The survey asks for the complete set of unit qubit tuples attaining the maximal imaginary Bargmann invariant tau_n for every n at least three.
strata_touched:
  - D5/S3/Quantum/Information/BargmannImaginaryMaximizers
license: citation-only
triage: anchor
---

# Zhang and Xie: imaginary Bargmann maximizers

## Verified locator

DOI: 10.48550/arXiv.2601.01858

Source: https://arxiv.org/abs/2601.01858v2

## Source statements

Section 2, p. 4: “Unit vector |ψ⟩ in ℂ^d will be called wave functions and its ranked-one projector ψ ≡ |ψ⟩⟨ψ| will be called pure state.”

Definition 3.1, p. 9: “The so-called nth-order Bargmann invariant for such n-tuple Ψ = (ρ₁, …, ρₙ) is defined as Δₙ(Ψ) := Tr(ρ₁ ⋯ ρₙ).”

Corollary 5.5, p. 25, Eq. (5.15): “τₙ := cosⁿ(π/n) secⁿ⁻¹(π/[2(n−1)]).”

Page 26: “The quantity τ_n predicts the upper bound for the imaginary part of any nth-order Bargmann invariant. This immediately raises the question: what is the complete set of n-tuples Ψ = (|ψ_1⟩, …, |ψ_n⟩) in ℂ² that achieve Im Tr(ψ_1 … ψ_n) = τ_n? We leave this characterization, along with the operational interpretation of the condition z ∈ 𝓑_{n+1} ∖ 𝓑_n, as interesting open problems for future work.”

## Encoding and scope

The vectors are functions `Fin 2 → ℂ`; the tuple indices are `Fin n`, starting at zero. The Bargmann invariant is the trace of the ordered product of `Matrix.vecMulVec (Ψ j) (star (Ψ j))`. A wave function satisfies `star (Ψ j) ⬝ᵥ Ψ j = 1`. The secant power is expressed as division by a cosine power. Natural subtraction is used in the exponent `n - 1`, and real subtraction is used in the denominator after coercing n.

The repository answer is one common unitary orbit, allowing a phase of norm one at each vertex, of `(√(1 − t_n), √t_n · exp(2πij/n))`, where `t_n = (1 − tan(π/[2(n−1)])/tan(π/n))/2`. The classification concerns every n ≥ 3. The operational interpretation of the difference between consecutive Bargmann sets and classification in dimensions at least three remain outside the statement.

The maximum and the source question are literature statements. The complete orbit equivalence is the repository's answer. Literature-search completeness is ASSUMED-UNVERIFIED.
