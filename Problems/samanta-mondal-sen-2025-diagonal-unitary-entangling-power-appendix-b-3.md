---
slug: samanta-mondal-sen-2025-diagonal-unitary-entangling-power-appendix-b-3
bibkey: samantamondalsen2025diagonalpowers
doi: 10.48550/arXiv.2505.18539
url: https://arxiv.org/abs/2505.18539v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.result
---

# Equal multipartite powers of diagonal phase gates

## Problem

M. Samanta, S. Mondal and A. Sen (De), *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*, arXiv:2505.18539v1, Appendix B.3, page 8, states:

> It also indicates that such an equivalence may hold for arbitrary diagonal unitary operators acted on arbitrary number of qubits.

The equivalence is $E_N(U)=D_N(U)$, where Eq. (1) maximizes the generalized geometric measure over fully separable inputs, Eq. (2) defines $D_N(U)=E_N(U^\dagger)$, and Appendix A.1 defines the generalized geometric measure by overlap with non-genuinely multipartite entangled pure states.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Any number of qubits | `claim` quantifies over every natural `N` | The physical multipartite interpretation concerns $N\ge2$; the same formal definitions include $N=0,1$. |
| Every diagonal unitary | Real phase function `θ` on `Fin N → Fin 2`, with diagonal entries $e^{i\theta_x}$ | Every computational-basis phase is independent. |
| Fully separable normalized inputs | `IsFullySeparable` | Squared-modulus sum one and a product of local amplitudes. |
| Non-genuinely multipartite entangled pure states | `IsBiseparable` | Normalization and factorization across a bipartition with both parts nonempty. |
| GGM | `G` | One minus the supremum of squared overlap over the biseparable subtype. |
| Entangling and disentangling powers | `E`, `D` | Suprema over fully separable inputs, with the adjoint in `D`. |
| Equality | `result : claim` | No additional hypotheses. |

The normalization expression is inlined; the overlap is Mathlib's `dotProduct` applied to the conjugated first argument. Maxima are represented by suprema. The argument identifies the entire value families, so it needs no attainment assertion or restriction on input local phases.

## Motivation

The settling declaration is `D5.S3.Quantum.Entanglement.DiagonalUnitary.SamantaMondalSenDiagonalPowers.result`, GID `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.result`. The admission basis is `open-problem-resolution (#19700; Proved)`, as preregistered in [#19700](https://github.com/the-omega-institute/trureturing/issues/19700). All six authored theorems are bind-only after expansion; the five private helpers have live consumers. There is no supporting module and no escape-witness admission claim.

## Gap

The equality is proved for every diagonal phase gate in the qubit amplitude model. It does not assert equality for non-diagonal unitary families, a restriction of optimizing local phases to zero, or a formula depending on only one diagonal phase.

The four-slot escape audit of the sole public theorem `result` is unfinished under [#19821](https://github.com/the-omega-institute/trureturing/issues/19821). The dependent phase telescope requires a faithful source-reconstruction bridge, source selection and actual observational-dependence evidence for the readouts. No Reg mirror or validated registration is delivered.

## Route

Let $C$ be coordinatewise complex conjugation. It preserves the squared-modulus sum and transforms every product factor into its conjugate. It therefore bijects both the fully separable input family and the biseparable overlap family. Conjugating both arguments of an overlap conjugates its value and leaves its squared modulus unchanged. Reindexing gives $G(C\psi)=G(\psi)$.

For diagonal $U$, $U^\dagger C p=C(Up)$. Thus $G(U^\dagger C p)=G(Up)$. Reindexing the fully separable inputs by the involution $C$ gives $E_N(U^\dagger)=E_N(U)$. The proof uses `Matrix.star_mulVec`, `Matrix.dotProduct_star`, `Complex.normSq_conj` and `Equiv.iSup_congr` from the pinned Mathlib import closure.

## Falsifier

A diagonal phase gate and a qubit count for which the two stated suprema differ would refute `claim`. A different entanglement measure, a non-diagonal gate or a maximum-attainment assertion is outside the settled statement.

## Evidence

The kernel-checked declaration is `D5.S3.Quantum.Entanglement.DiagonalUnitary.SamantaMondalSenDiagonalPowers.result`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. Its Scribe node displays the full quantified equality and carries one Proved `OpenProblemResolutionClaim`.

The source note is `Library/QuantumContext/samantamondalsen2025diagonalpowers.md`.

Experiment: [pinned numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/6f481a2b346d09e34b1bd716b01f282a22fd16cc/docs/reports/samanta-mondal-sen-2025-diagonal-unitary-entangling-disentangling). Command from the main repository root: `python3 ../trureturing-experiments/docs/reports/samanta-mondal-sen-2025-diagonal-unitary-entangling-disentangling/check.py`; exit 0. Script SHA-256: `cf7e9af37878da337f31cf078d59c4ffe1fb5e12578bf029cd941f971aae1b6f`. The seeded check evaluates 200 random diagonal gates and product inputs at each $N=3,4,5$, using the largest Schmidt coefficient across nontrivial bipartitions. It reports 600 cases and maximum absolute difference $0.0$ between $G(Up)$ and $G(U^\dagger Cp)$. It does not optimize either power or prove a uniform bound.

## Triage

| Item | Status and evidence |
| --- | --- |
| Appendix B.3 equality for arbitrary qubit count and diagonal phases | Proved in Lean: `SamantaMondalSenDiagonalPowers.result`. |
| Conjugation mechanism | Proved in Lean: private `isFullySeparable_star`, `isBiseparable_star`, `G_star`, `diagonal_intertwining`, and `E_diag_eq`, consumed by `result`. |
| Numerical pointwise check | Computed: the pinned experiment entry above, 600 samples at $N=3,4,5$, maximum difference $0.0$. |
| Arbitrary finite local dimensions | Open as a formal extension: the delivered statement uses qubits. |
| Input local phases and the source's other results | Open: setting optimizing local phases to zero and a one-phase-only formula are not consequences of the stated equality. Non-diagonal families are outside its scope. |
| Prior-art screen | Literature reading recorded in #19700: v1 states the expectation; the identified citing work arXiv:2604.26392v1 concerns imaginarity-generating power. No settlement was identified in that searched scope; completeness is ASSUMED-UNVERIFIED. |

### What the settlement shows

The decisive invariant is conjugation of the complete attainable-value families, rather than the value of an optimizer. The equality needs neither attainment nor elimination of local input phases. The intertwining identity is a diagonal-matrix identity; the separation-preserving conjugation and overlap identities account for the state constraints. The argument suggests the same equality for finite products of arbitrary local dimensions, but that extension has no delivered Lean declaration.

The source's special diagonal-family equalities are consistent with the universal equality. This settlement supplies that equality independently of a numerical restriction on local input phases. It establishes no replacement for the source's detailed optimizing-input or phase-dependence formulas, and makes no equality claim about its non-diagonal examples.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The preregistration records arXiv version and citing-work checks; rate limits restricted the citation census. No global novelty claim follows from a repository search. Source fidelity relies on the explicit amplitude, separability and supremum conventions above. The finite-dimensional extension and the source's additional optimization claims remain outside the kernel-checked settlement. The unfinished escape audit is disclosed in #19821.
