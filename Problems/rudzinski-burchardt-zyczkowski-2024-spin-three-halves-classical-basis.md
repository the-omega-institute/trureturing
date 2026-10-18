---
slug: rudzinski-burchardt-zyczkowski-2024-spin-three-halves-classical-basis
bibkey: rudzinski2024extremequantumness
doi: 10.22331/q-2024-01-25-1234
url: https://arxiv.org/abs/2306.00532v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.result
---

# The most classical orthonormal basis of spin 3/2

## Problem

M. Rudziński, A. Burchardt and K. Życzkowski, *Orthonormal bases of extreme quantumness*, Quantum 8, 1234 (2024), arXiv:2306.00532v3, Conjecture 1:

> The matrix $U_4^{c}$ given in (21), for which $\mathcal{B}_1=\frac{1}{9}$, leads to the most spin-coherent (classical) basis in $\mathcal{H}_4$.

Here $\mathcal{B}_1(U)$ is the mean, over the four basis vectors given by the columns of $U$, of the one-qubit anticoherence $\mathcal{A}_1(\psi) = 2[1 - \operatorname{tr}\rho_1(F\psi)^2]$, where $F$ sends a spin-3/2 state to the symmetric state of three qubits and $\rho_1$ is its one-qubit reduced state (Eqs. (8) and (12)–(15)). The verbatim statements are in [the literature note](../Library/QuantumChannels/rudzinski2024extremequantumness.md).

Issue [#18510](https://github.com/the-omega-institute/trureturing/issues/18510) fixes the reading: 1/9 ≤ ℬ₁(U) for every U ∈ U(4), and the printed $U_4^c$ is unitary with ℬ₁ = 1/9. This is proved.

## Motivation

A complete orthogonal measurement on a spin cannot consist of coherent states. ℬ₁ measures how far the best such measurement must stay from classical, and the source found its minimum for N = 4 only numerically, by imposing the symmetries of a random-walk optimum. The source settles N = 3 (Proposition 1) and the opposite extremum for N = 4 (Proposition 2).

## Gap

Issue #18510 records the literature check before any Lean:
- arXiv v3 is the latest version and keeps Conjecture 1;
- the seven arXiv citing works listed by Semantic Scholar cite the paper only for anticoherent states or bases, spin coherence or background, and none states or settles the minimum 1/9; the eighth listed citing work, a 2024 QISKit article, was not read;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Write J_x, J_y, J_z for the spin-3/2 matrices, p_i for the polarization of the column u_i of U and S(U) = Σ_i |p_i|².
1. **The Dicke bridge.** The one-qubit reduced state of Fψ has Bloch vector 2p/3, so 𝒜₁(ψ) = 1 − 4|p|²/9 and ℬ₁(U) = 1 − S(U)/9. The claim becomes S(U) ≤ 8.
2. **Determinant one.** Rescaling one column by a phase leaves every p_i unchanged, so U ∈ SU(4).
3. **A real six-frame.** For U ∈ SU(4) the matrix of 2 × 2 minors, in a basis of Λ²ℂ⁴ fixed by a Hodge-type real structure, is real orthogonal.
4. **The transport.** Since Σ_i p_i = 0, S = Σ_k |p₁ + p_{k+1}|². The one-body expansion of the lifted spin generators identifies each |p₁ + p_{k+1}|² with 2‖[X_k, Y_k]‖², where (s_k, X_k) and (t_k, Y_k) are frame vectors in ℝ ⊕ Sym₀(ℝ³).
5. **Böttcher–Wenzel.** ‖[X, Y]‖² ≤ 2(‖X‖²‖Y‖² − ⟨X, Y⟩²), together with the frame identities ‖X_k‖² = 1 − s_k², ‖Y_k‖² = 1 − t_k², ⟨X_k, Y_k⟩ = −s_k t_k and Σ_k (s_k² + t_k²) = 1, gives S ≤ 8.
6. **Attainment.** The polarizations of $U_4^c$ have squared length 2 and pairwise inner products −2/3, so S = 8.

## Falsifier

The theorem would not settle the question if the module's quantities differed from the source's. The module takes:
- the normalized Dicke embedding sending the k-th basis vector (m = 3/2 − k) to the uniform superposition of three-bit strings with k ones, as in Eq. (8);
- the trace over the first two qubits, as in Eq. (12), and 𝒜₁ = 2(1 − tr ρ₁²), as in Eq. (14) at t = 1;
- the columns of U as the basis vectors, as in the source's convention $U_{ki} = \langle j, j+1-k|\psi_i\rangle$;
- Eq. (21) entry by entry, with ω₃ = e^{2πi/3} written as (−1 + i√3)/2.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.lean` (743 lines).
- **Definitions.** It defines `dicke`, `reducedState`, `anticoherence`, `basisAnticoherence`, `classicalBasis` and `claim`, and proves `result : claim`.
- **Reuse.** It reuses:
  - the spin matrices `Jx`, `Jy`, `Jz` of `PrecessionSpinOneSeparableBound`;
  - the compound matrices of `Schatten/CompoundMatrices`;
  - the Frobenius norm and the Böttcher–Wenzel bound of `WeightedBotcherWenzel`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registration:** `Reg/D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.lean` (`result`, `declared_validated`).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.lean.json`, statement `sha256:cf869ff9b7dde4ab943b25cfccc33fe11e6fa481e51186bf799a42436b3bcccd`.

Declaration statements:
- `result`: `sha256:f11b356fe67549611957675ad7e5faf42a26535d34852c6dbbc2a32edd0895e2`;
- `claim`: `sha256:1ff4fd0bf3a7a7f743ca38a81ac9edaf23de69dfe7185bec75ffec7a20289f67`.

## Triage

Tier 1 conjecture of a 2023 paper (published 2024), preregistered in issue #18510 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the Dicke bridge, the compound-matrix frame, the transport and the Böttcher–Wenzel step are instantiations of existing lemmas and finite matrix identities | open-problem-resolution |
| `dicke`, `reducedState`, `anticoherence`, `basisAnticoherence`, `classicalBasis`, `claim` | bind-only | none | definitions used by `claim` |
| the polarization, frame, transport and attainment helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The module is a general theorem over all of U(4) with its attainment, so `utility` is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the minimum of ℬ₁ over all orthonormal bases of the spin-3/2 space is 1/9, attained by $U_4^c$.

**Computed, not formalized** (orchestrator, recorded in #18510):
- over 200 000 Haar-random unitaries S(U) ≤ 7.65, and 60 local ascents reach S = 8.000000000000;
- each step of the route holds numerically on 2000 random U ∈ SU(4).

**Argued, not formalized.**
- *Mechanism.* Λ²: SU(4) → SO(6) turns the four-vector problem into a six-frame of real symmetric 3 × 3 matrices, where the spin-2 part of Λ²(spin 3/2) is the traceless symmetric representation. Four coherent states would give S = 9. The orthogonality of the four vectors makes the transported vectors a real orthonormal six-frame: it gives the pairwise identities ‖X_k‖² = 1 − s_k², ‖Y_k‖² = 1 − t_k², ⟨X_k, Y_k⟩ = −s_k t_k and the completeness Σ_k (s_k² + t_k²) = 1, which together cost exactly one unit.
- *Equality.* Equality needs equality in Böttcher–Wenzel for each k, so the three commutators are extremal. This matches the regular tetrahedron of polarizations of $U_4^c$. Whether every minimizer is a rotation of $U_4^c$ up to phases and column order is not determined here.
- *Scope.* The argument uses SU(4) ≅ Spin(6) and does not extend directly to N ≥ 5; the source's numerical Conjectures 2 and 3 for N = 5, 6 are not addressed.

**Effect on the paper.** The numerically found basis $U_4^c$ is the global minimizer, so the most classical spin-3/2 measurement has mean anticoherence exactly 1/9, against the Haar mean 2/3 of the source's Eq. (31).

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
