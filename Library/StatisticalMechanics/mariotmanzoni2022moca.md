---
bibkey: mariotmanzoni2022moca
authors: Luca Mariot and Luca Manzoni
year: 2022
title: Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata
doi: 10.48550/arXiv.2207.08280
url: https://arxiv.org/abs/2207.08280v1
claim: "Section 5 asks whether the binary orthogonal array obtained from every set of k-MOCA always has strength at least three."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2207.08280

Source: https://arxiv.org/abs/2207.08280v1

## Source statements

Definition 1, p. 6:

> Let n, d ∈ ℕ with d ≤ n, and let f : F₂ᵈ → F₂ be a d-variable Boolean function. A cellular automaton of length n, diameter d and local rule f is a mapping F : F₂ⁿ → F₂ⁿ⁻ᵈ⁺¹ defined for all x ∈ F₂ⁿ as: F(x₁, · · · , xₙ) = (f(x₁, · · · , x_d), f(x₂, · · · , x_{d+1}), · · · , f(x_{n−d+1}, · · · , xₙ)).

Page 7:

> Formally, a local rule f : F₂ᵈ → F₂ is called bipermutive if it is defined as f(x₁, · · · , x_d) = x₁ ⊕ ϕ(x₂, · · · , x_{d−1}) ⊕ x_d for all x ∈ F₂ᵈ, where ϕ : F₂ᵈ⁻² → F₂ is any function of the d−2 central variables.

> we define two bipermutive CA F₁, F₂ : F₂²⁽ᵈ⁻¹⁾ → F₂ᵈ⁻¹ to be orthogonal (or equivalently they are OCA) if the corresponding Latin squares are orthogonal.

> Accordingly, a family of k pairwise orthogonal bipermutive CA F₁, · · · , F_k will be called a set of k-MOCA (mutually orthogonal cellular automata).

Equation (7), p. 8:

> the row of A indexed by (x, y) is equal to: A(x, y) = (F₁(x, y), F₂(x, y), · · · , F_k(x, y)).

Orthogonal arrays, p. 6:

> is a N × n array with entries from a set S with s elements such that, for any N × t subarray, each t-uple of Sᵗ occurs exactly λ = N/sᵗ times

Section 5, p. 12:

> The most natural open question remains whether our Theorem 1 is really a tight lower bound on the correlation immunity of the Boolean functions constructed through k-MOCA. If further experiments show that the lowest correlation immunity order is always at least 3, then it would be interesting to try refining Lemma 3, and prove that the binary OA obtained from a set of k-MOCA has always at least strength 3.

## Encoding and scope

The cellular automaton uses length 2b, diameter b + 1 and zero-based Fin indices; bit addition is addition in ZMod 2. The left and right input halves are joined by Fin.append. The array retains every input as a row, and its columns are pairs consisting of a rule index and an output position. Strength t means equal pattern-fiber counts for every injective selection of t columns, with natural integer division by 2^t; if fewer columns exist the selection condition is vacuous.

The Lean theorem proves strength three. Its triple-XOR balance argument applies to arbitrary bipermutive families, whereas pair balance at a shared position uses orthogonality. Sharpness is not an additional Lean theorem.

The finite checker is in the-omega-institute/trureturing-experiments, commit dc61cd52, at docs/reports/mariot-manzoni-2022-moca-orthogonal-array-strength-three/check.py (sha256 741e7ffd7258cf0555ccb265ae097f501b3f09b793a9efb1117aa2133bf404eb; exit 0). Its output out.txt has sha256 f1d383b9bd35f5f90a8e00858aae82b7d14b578bdbbef00b8728802040413516.

## Literature boundary

The authors' survey arXiv:2503.10320v1, Section 5.3.2, records strength three as an experimental observation. The literature screen in issue #19624 and the probe found no published settlement in the inspected sources. Completeness is ASSUMED-UNVERIFIED: the full Springer chapter 10.1007/978-3-031-42250-8_11 and final journal survey 10.1016/j.dam.2025.10.014 were not read, and forward citations were not exhaustively checked.
