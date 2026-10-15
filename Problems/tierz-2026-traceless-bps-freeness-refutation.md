---
slug: tierz-2026-traceless-bps-freeness-refutation
bibkey: tierz2026bpsoddp
doi: null
url: https://arxiv.org/abs/2604.27164v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.result
---

# The traceless BPS cohomology at (p, N) = (5, 4) is not free over the diagonal creators

## Problem

M. Tierz, *BPS spectra of Tr[Ψ^p] matrix models for odd p*, arXiv:2604.27164 (v1 April 2026, v2 August 2026), studies the cohomology of wedge multiplication by Q_p = Tr(Ψ^p) on the exterior algebra of the N² fermionic creators Ψ_ij.
- The trace fermion χ splits off (v2 Theorem 2), leaving the cohomology B•_0 of Q_p = Tr(A^p) on the traceless creators A = Ψ − (χ/√N)·1.
- The traceless diagonal creators anticommute with Q_p, so B•_0 is a graded module over their exterior algebra Λ•(C^{N−1}).

The source states freeness in two places, verbatim in [the literature note](../Library/HomologicalAlgebra/tierz2026bpsoddp.md):
- v1 §5 marks "(conjectural) H•_red is free over Λ•(C^{N−1})" as "the content of the open problem";
- v2 §6.3 calls an isomorphism of graded modules B•_0 ≅ Λ•(C^{N−1}) ⊗ M^{(p,N)} "a sufficient explanation for the remaining factors of 1+x" and says that "such freeness … is not proved here".

Issue [#16298](https://github.com/the-omega-institute/trureturing/issues/16298) fixes the reading: for odd p ≥ 5 with p ≤ 2N − 1, B•_0 is a free Λ•(C^{N−1})-module. The admissible case (p, N) = (5, 4) is refuted.

## Motivation

Freeness would explain the factors of 1 + x in the BPS generating functions beyond the structural ones (v2 Corollary 3) and would reduce the BPS spectrum to a primitive space M^{(p,N)} with Hilbert series p^{b_{p,N}} x^{q_min} T^{(p)}_N(x). Its failure means that the (1 + x)^N divisibility of v2 Conjecture 1, which the source observes at (5, 4), needs a different explanation there.

## Gap

Issue #16298 records the literature check before any Lean:
- arXiv v2 is the latest version and restates freeness as unproved;
- arXiv searches for the topic return only this paper, and the companion work "[36] M. Tierz, in preparation" of v1 was not found;
- Zenodo returns no related record;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Coordinates: the fifteen traceless creators u_ij = E_ij − δ_ij I/4 are ordered so that A = [[a,d,e,f],[g,b,h,i],[j,k,c,l],[m,n,o,−a−b−c]], and Q = Tr(A⁵) is computed from the matrix product. Let ℓ = a + b = u₀₀ + u₁₁ ∈ H and let y be the explicit sixteen-term cubic of the module.
1. **A class killed by ℓ.** z = ℓy satisfies Qz = 0 and ℓz = 0, and Q has degree 5, so no boundary has degree 4. Hence [z] is a degree-four class with ℓ[z] = 0.
2. **Freeness forces a lift.** Over a free Λ(H)-module the kernel of multiplication by a nonzero ℓ ∈ H equals its image. A free B₀ would therefore give a class [x] with ℓ[x] = [z]. Projecting onto degree three gives a cycle x ∈ E³ with Qx = 0 and ℓx = z. The module proves this for ungraded `Module.Free`; it does not assume a homogeneous basis.
3. **The obstruction.** Exactness of ℓ∧ on E gives x = y + ℓt. The algebra map π killing c, f, h, j, l, n, o has π(Qℓ) = 0 and π(Qy) = −20·abdegikm ≠ 0. So π(Qx) ≠ 0, contradicting Qx = 0.

The integer identities Qℓy = 0, π(Qℓ) = 0 and π(Qy) = −20·abdegikm are checked by `decide` on a sparse bit-mask evaluator. Its soundness is proved against Mathlib's exterior algebra basis.

## Falsifier

The refutation would fail if:
- the source's module were over a different algebra than the exterior algebra of the traceless diagonal creators acting by wedge multiplication;
- its Q_p differed from Tr(A^p) on the traceless creators;
- (5, 4) were outside the source's range. The source restricts to odd p ≥ 5 with p ≤ 2N − 1, which contains (5, 4), and computes this case in Eq. (45).

Graded freeness implies ungraded freeness, so the refutation of `Module.Free` covers the graded statement of v2.

## Evidence

The canonical source is `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.lean` (687 lines).
- Its carrier V is Mathlib's `LieAlgebra.SpecialLinear.sl (Fin 4) ℂ` of trace-zero matrices, and E is `ExteriorAlgebra ℂ V`. It defines `creatorVec`, `A`, `Q`, `H`, `R`, the action of `R` on `E` through `ExteriorAlgebra.map H.subtype`, `dR`, `Cycles`, `B0` and `claim`, and proves `result : ¬ claim`.
- It uses Mathlib's exterior algebra, its basis and contraction API, the grading `ExteriorAlgebra.gradedAlgebra` with `GradedAlgebra.proj`, and `Module.Free`; it has no frozen D5 dependency.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is a refutation result and is exempt from the §3.9 registration.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.lean.json`, statement `sha256:9f9acea7c409196e9aba3e6479dc115d3b6a193d639d1df0d113e044c869c280`.

Declaration statements:
- `result`: `sha256:ad204e89ae781984ee33e93d1a1155f4ad89d301fa7f98667a791719ad9e50d7`;
- `claim`: `sha256:a8c10d72998e8c9eb0bcc421d4529ffdd28c72bf3b784eb46f15079acd12e935`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #16298 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: the decisive steps are the three closed integer identities checked by `decide` and the specialization of pinned exterior-algebra, contraction and grading results | open-problem-resolution |
| the bit-mask evaluator and its soundness lemmas (`word_*`, `mono_*`, `eval_*`, `Q_eq_eval`), the odd-element helpers, `free_creator_exact`, `free_lift`, `projection_obstruction`, `degree_four_boundary`, `right_left`, `cycle_left`, `range_left` (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated equation, proof or instance projection on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` of `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** B•_0 at (p, N) = (5, 4) is not a free module over Λ(H), graded or ungraded. In particular there is no isomorphism of graded modules B•_0 ≅ Λ•(C³) ⊗ M^{(5,4)}.

**Established inside the proof.** The degree-four class [z] = [ℓy] is nonzero and killed by ℓ = u₀₀ + u₁₁, but it is not ℓ times a class.

**Computed, not formalized** (orchestrator, exact rank programs, 14 October 2026; the instrument reproduces the source's Eqs. (44) and (45) and gives zero ℓ-cohomology on a free control module):
- At (5, 4), over F_32003: dim B⁴_0 = 125, dim B⁵_0 = 1250 and B^R_0 = 0 for R ≤ 3. In degree four the ℓ-cohomology ker ℓ / ℓB³_0 has dimension 1 for ℓ = u₀₀ + u₁₁, and 0 for ℓ = u₀₀, u₀₀ − u₁₁, u₀₀ + u₁₁ + u₂₂ and a random ℓ. The obstruction sits on the special directions diag(1, 1, −1, −1), up to permutation, not on a generic one.
- At (5, 3), the smallest admissible case, exactly over ℚ: dim B^R_0 = 20, 55, 70, 55, 20 for R = 2, …, 6, which matches Eq. (44). For every tested ℓ (u₀₀, u₀₀ + u₁₁, u₀₀ − u₁₁, u₀₀ + 2u₁₁ and a random ℓ) the ℓ-cohomology is nonzero in degrees 2, 3, 5 and 6. Since degree two is the lowest, freeness would force ℓ to be injective there. So B•_0 is not free at (5, 3) either. There the factor (1 + x)³ is structural (v2 Corollary 3), and freeness is not needed to explain it.

**Argued, not formalized.** The obstruction is an exactness condition, which dimension counts do not see. Freeness requires every nonzero ℓ ∈ H to act exactly (kernel equal to image); this is the direction used in the proof. The Hilbert series records only the dimensions of the graded pieces, so divisibility by (1 + x)^{N−1} is compatible with a nonzero ℓ-cohomology. At (5, 3) and (5, 4) divisibility holds while freeness fails, which confirms the source's remark that freeness "is not implied by divisibility of the Hilbert series". Whether exactness for every ℓ is also sufficient for these modules is not used and not checked here.

**Open.**
- Freeness at (5, 5), (7, 4) and the further admissible cases, and whether it fails for every admissible (p, N).
- An explanation of the extra (1 + x) factor at (5, 4), and v2 Conjecture 1 itself, which this settlement does not address.

**Effect on the paper.** The second, conjectural layer of v1 §5 is false at (5, 4) and, by the exact computation above, at (5, 3). The sufficient explanation of v2 §6.3 is not available at (5, 4). The divisibility conjecture (v2 Conjecture 1) and the factorization pattern of Table 3 are not affected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized; the (5, 4) ℓ-cohomology values are computed modulo one prime.
