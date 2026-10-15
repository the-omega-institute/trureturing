---
bibkey: antipin2021genuinely
authors: K. V. Antipin
year: 2021
title: "Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states"
doi: 10.1088/1751-8121/ac37e5
url: https://arxiv.org/abs/2104.09664v1
claim: "§III.B.2 constructs a four-qubit subspace from the seven vectors (35a)–(35g), √λ_i|p_i⟩⊗|q_i⟩ + √(1 − λ_i)|p′_i⟩⊗|q′_i⟩ in ℂ⁴ ⊗ ℂ⁴ with 0 < λ_i < 1, by the substitutions (39) for the first and (40) for the second ququart into two qubits each; with every λ_i = 1/2 the span is stated to be a genuinely entangled subspace, and the paper conjectures that eqs. (35) together with eqs. (39) and (40) determine a GES for any set of values of λ_i."
strata_touched:
  - D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation
license: citation-only
triage: anchor
---

# Antipin, construction of genuinely multipartite entangled subspaces

K. V. Antipin, *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*, arXiv:2104.09664 [quant-ph] (v1, the only version); published as *Construction of genuinely entangled subspaces and the associated bounds on entanglement measures for mixed states*, J. Phys. A: Math. Theor. **54**, 505303 (2021), DOI 10.1088/1751-8121/ac37e5.

## Verified locator

DOI: 10.1088/1751-8121/ac37e5 (as listed in the arXiv metadata, with journal reference J. Phys. A: Math. Theor. 54 505303 (2021)).
Primary version read: https://arxiv.org/abs/2104.09664v1.
Source: https://arxiv.org/pdf/2104.09664v1 (text read from the PDF):
- §II.A, genuine multipartite entanglement: Eq. (2) and the definitions of biseparable and genuinely multipartite entangled pure states, completely entangled subspaces and GESs;
- §III.B, constructing GES of maximal dimension;
- §III.B.2, GES in four-qubit systems, page 8: the vectors (35a)–(35g), the unitaries (36)–(38), the substitutions (39)–(40) and the conjecture.

The journal version was not read.

## Source statements

§II.A: "A pure n-partite state |ψ⟩ is called biseparable if it can be written as a tensor product |ψ⟩ = |ψ⟩_A ⊗ |ψ⟩_Ā (2) with respect to some bipartition A|Ā where A denotes a particular subset of subsystems and Ā denotes its complement. A multipartite pure state is called genuinely multipartite entanged if it is not biseparable with respect to any bipartition." Further: "The natural generalization of this notion is genuinely multipartite entangled subspaces (GESs) – those composed entirely of genuinely entangled pure states."

Page 8: the 7-dimensional completely entangled subspace of the 4 ⊗ 4 Hilbert space "is spanned by the orthonormal system
√λ_1 |0⟩⊗|0⟩ + √(1 − λ_1) |2⟩⊗|1⟩, (35a)
√λ_2 |1⟩⊗|2⟩ + √(1 − λ_2) |3⟩⊗|3⟩, (35b)
√λ_3 |0⟩⊗|1⟩ + √(1 − λ_3) |3⟩⊗|2⟩, (35c)
√λ_4 |3⟩⊗|0⟩ + √(1 − λ_4) |2⟩⊗|2⟩, (35d)
√λ_5 |1⟩⊗|1⟩ + √(1 − λ_5) |0⟩⊗|3⟩, (35e)
√λ_6 |1⟩⊗|0⟩ + √(1 − λ_6) |2⟩⊗|3⟩, (35f)
√λ_7 |2⟩⊗|0⟩ + √(1 − λ_7) |3⟩⊗|1⟩, (35g)
where 0 < λ_i < 1, i = 1, …, 7."

Substitutions (39) for subsystem A:
- |0⟩ → (1/6)(5|00⟩ − |01⟩ + 3|10⟩ − |11⟩);
- |1⟩ → (1/6)(−|00⟩ + 5|01⟩ + 3|10⟩ − |11⟩);
- |2⟩ → (1/2)(|00⟩ + |01⟩ − |10⟩ + |11⟩);
- |3⟩ → (1/6)(−|00⟩ − |01⟩ + 3|10⟩ + 5|11⟩).

Substitutions (40) for subsystem B:
- |0⟩ → (1/3)(−|00⟩ + 2|01⟩ + 2|11⟩);
- |1⟩ → (1/3)(2|00⟩ − |01⟩ + 2|11⟩);
- |2⟩ → |10⟩;
- |3⟩ → (1/3)(2|00⟩ + 2|01⟩ − |11⟩).

"Now, to obtain a four-qubit GES, one should apply substitutions (39) and (40) in eqs. (35) for the basis states of the first and the second subsystems, respectively, and set all λ_i to 1/2. Actually, we've done calculations for several different sets of values of λ_i and each time obtained a GES. We can conjecture that eqs. (35) together with eqs. (39) and (40) determine a GES for any set of values of λ_i."

## Reading used by the repository

The four qubits are A_1, A_2 (from the first ququart) and B_1, B_2 (from the second). For λ ∈ (0, 1)⁷, S_λ is the complex span of the seven vectors (35) after the substitutions (39) for the first factor and (40) for the second.

A vector is product across a bipartition s | sᶜ of the four qubits when its coefficient function factors as a function of the coordinates in s times a function of the coordinates in sᶜ. S_λ is a GES when no nonzero vector of S_λ is product across any of the seven bipartitions. The conjecture is read as: S_λ is a GES for every λ ∈ (0, 1)⁷.
