---
slug: antipin-2021-four-qubit-genuinely-entangled-subspace-refutation
bibkey: antipin2021genuinely
doi: 10.1088/1751-8121/ac37e5
url: https://arxiv.org/abs/2104.09664v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.result
---

# Antipin's four-qubit subspaces are not genuinely entangled for every parameter

## Problem

K. V. Antipin, *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*, arXiv:2104.09664v1 (J. Phys. A: Math. Theor. 54, 505303 (2021)), constructs genuinely entangled subspaces (GESs): subspaces in which every nonzero vector is entangled across every bipartition of the parties.
- **The construction.** §III.B.2 starts from the seven orthonormal vectors (35a)–(35g) of ℂ⁴ ⊗ ℂ⁴, each of the form √λ_i |p_i⟩⊗|q_i⟩ + √(1 − λ_i) |p′_i⟩⊗|q′_i⟩ with 0 < λ_i < 1. It splits each ququart into two qubits by the substitutions (39) for the first factor and (40) for the second. This gives a seven-dimensional subspace S_λ of four qubits A₁A₂B₁B₂.
- **The conjecture.** With every λ_i = 1/2 the source obtains a GES. Then: "Actually, we've done calculations for several different sets of values of λ_i and each time obtained a GES. We can conjecture that eqs. (35) together with eqs. (39) and (40) determine a GES for any set of values of λ_i."

The verbatim statements are in [the literature note](../Library/QuantumChannels/antipin2021genuinely.md).

Issue [#17193](https://github.com/the-omega-institute/trureturing/issues/17193) fixes the reading: S_λ is a GES for every λ ∈ (0, 1)⁷. The conjecture is refuted.

## Motivation

§III.B.2 bounds the dimension of a four-qubit GES by seven, using the bipartitions with a single qubit on one side, and the construction is the source's example reaching that bound. §IV turns GESs into lower bounds on the concurrence and the convex-roof extended negativity of mixed states, so the conjecture would give a seven-parameter family of maximal GESs for these bounds.

## Gap

Issue #17193 records the literature check before any Lean:
- arXiv v1 is the only version and states the conjecture;
- three citing works were read in full and none treats the conjecture: Antipin, arXiv:2201.07918v2; Demianowicz, arXiv:2111.10193v4; and *Entangled Subspaces through Algebraic Geometry*, arXiv:2504.11525;
- a web search found no settlement;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Take λ = (1/2, 16/25, 1/2, 1/2, 1/17, 1/2, 1/2) and let v_1, …, v_7 be the vectors (35).
1. **Removing the square roots.** x = 3√2(v_1 + v_3 + v_4 + v_6 + v_7) + 5v_2 + 3√17 v_5 has the integer coefficient matrix M = [[3,3,0,12],[3,3,4,0],[3,3,3,3],[3,3,3,3]] in the basis |a⟩⊗|b⟩.
2. **The substitutions.** With U and T the coordinate matrices of (39) and (40), the coefficient matrix of the transformed vector y is UMTᵀ = (1/3)[[25,25,1,1],[1,1,13,13],[15,15,6,6],[7,7,10,10]].
3. **The product form.** The columns of UMTᵀ come in equal pairs, so y = (1/3)(25, 1, 1, 13, 15, 6, 7, 10)_{A₁A₂B₁} ⊗ (|0⟩ + |1⟩)_{B₂}.
4. **The contradiction.** y is a nonzero linear combination of the seven transformed vectors, so it lies in S_λ, and it is a product across A₁A₂B₁ | B₂. Hence S_λ is not a GES.

## Falsifier

The refutation would not hold if:
- the module's vectors or substitutions differed from (35), (39) or (40), or applied the substitutions to the wrong factors;
- its product predicate were weaker than the source's biseparability, so that a vector entangled across every bipartition could count as a product;
- its parameter domain were wider than 0 < λ_i < 1.

The module writes (35a)–(35g) with `Real.sqrt` of λ_i and 1 − λ_i. It writes (39) and (40) as linear maps into ℂ² ⊗ ℂ², applied to the first and the second ququart by `TensorProduct.map`. Its `IsProductAcross s z` says that the coefficients of z are a function of the coordinates in s times a function of the coordinates outside s, which is the tensor product |ψ⟩_A ⊗ |ψ⟩_Ā of the source's Eq. (2). `IsGES` forbids this for every nonzero vector and every nonempty proper set of parties, and `claim` quantifies over λ ∈ (0, 1)⁷.

## Evidence

The canonical source is `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.lean` (432 lines).
- It defines `Bit`, `Party`, `Qubit`, `Ququart`, `TwoQubit`, `Config`, `State`, `Original`, `coordinate`, `IsProductAcross`, `IsGES`, `ket44`, `ket22`, `v35`, `columns39`, `columns40`, `substitution39`, `substitution40`, `twoBasis`, `inputCoordinates`, `outputCoordinates`, `factorwise`, `transformed`, `S` and `claim`, and proves `result : ¬ claim`.
- It imports pinned Mathlib only.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.lean.json`, statement `sha256:f4cc36121619e3a48b552df559d8d57310a345e619e9f810fd9b287e0c379490`.

Declaration statements:
- `result`: `sha256:2cb571fbf4989b6f5e477f0321129a641927a61f14d00b8c6bca4479181f5f28`;
- `claim`: `sha256:9a06b5a747a797cbe7e367f8deabdb5736a0435bde231d658a4b0f26e1eb3212`.

## Triage

Tier 1 conjecture of a 2021 paper, preregistered in issue #17193 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the square-root identities, the coordinates of the tensor maps, the matrix product, span membership and the product factorization are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |

Every other public declaration is a definition used by a public statement. The module's 18 private theorems are bind-only helpers consumed on the proof path of `result`, and its 11 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** at λ = (1/2, 16/25, 1/2, 1/2, 1/17, 1/2, 1/2), S_λ contains a nonzero vector that is a product across A₁A₂B₁ | B₂, so the conjecture fails.

**Argued, not formalized.** Write r_i = √((1 − λ_i)/λ_i). A vector of S_λ of the form γ ⊗ (|0⟩ + |1⟩)_{B₂} corresponds to a solution of eight linear equations in the seven coefficients of the combination of the vectors (35): for each row (m_0, m_1, m_2, m_3) of the coefficient matrix, m_0 = m_1 and m_3 = 4m_0 − 3m_2. Eliminating the coefficients, a nonzero solution exists exactly when
- 4r_6/r_5 − 4r_1 + 3r_1r_4r_7 = 0, and
- (16/3)r_2/r_5 − 4r_1r_7 + 3r_3 = 0.

So these counterexamples form a five-parameter family. The witness has r = (1, 3/4, 1, 1, 4, 1, 1). The point λ_i = 1/2, where r_i = 1 for all i, is not in the family.

**Computed, not formalized** (orchestrator, NumPy, 15 October 2026):
- For 2,000 parameter points drawn uniformly from (0.01, 0.99)⁷, the linear system above has rank 7, so S_λ contains no vector of this form.
- For 2,000 points of the family, the system has rank 6, so S_λ contains such a vector.
- At λ_i = 1/2 the system has rank 7.

**Open.**
- The full set of λ ∈ (0, 1)⁷ for which S_λ is a GES. This settlement covers only product vectors with B₂-factor |0⟩ + |1⟩ across the cut A₁A₂B₁ | B₂; other cuts and other factors are not examined.

**Effect on the paper.** The construction (35), (39)–(40) does not give a GES for every λ. The GES at λ_i = 1/2 and the bound of seven on the dimension are not affected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal version was not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
