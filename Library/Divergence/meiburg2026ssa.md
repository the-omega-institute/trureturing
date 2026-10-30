---
bibkey: meiburg2026ssa
authors: Alex Meiburg; Leonardo A. Lessa; Rodolfo Soldati
year: 2026
title: Finite density states and strong subadditivity in Physlib
doi: null
url: https://github.com/leanprover-community/physlib/blob/2725b6f621901d4cd330869e9b77105045c1582e/QuantumInfo/Entropy/SSA.lean
claim: Attributed finite-dimensional strong subadditivity, including singular density states, supplies the actual-density bridge used by the repository's AD-classical conditional-copy Zhang-Yeung derivation.
strata_touched:
  - D5/S3/Quantum/Foundation/FiniteDensityPurification
  - D5/S3/Quantum/Information/StrongSubadditivity
  - D5/S3/Quantum/Information/ClassicalConditionalCopy
  - D5/S3/Quantum/Information/ClassicalADCopy
  - D5/S3/Quantum/Information/ClassicalADZhangYeung
license: Apache-2.0
triage: anchor
---

# Finite density strong subadditivity and its conditional-copy application

The consumed source is `leanprover-community/physlib` at immutable revision
`2725b6f621901d4cd330869e9b77105045c1582e`. The receiving pins are Lean
`v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
`QuantumInfo/Entropy/SSA.lean`, declaration `Sᵥₙ_strong_subadditivity`,
supplies strong subadditivity for finite `MState`, including singular states.
Its operator argument, positive-definite approximation, continuity and
purification dependencies are retained in the source closure below.
This is source reuse; no new SSA proof or direct Physlib package admission is claimed.

Original copyright and Apache-2.0 notices remain in each consumed Lean module.
The source authors are Alex Meiburg, with Leonardo A. Lessa on the projection
and mixed-state sources and Rodolfo Soldati on the pure-state source, as
identified by those headers. The full Apache-2.0 license text is retained in
`D5/S3/Quantum/Information/StrongSubadditivity/Physlib/ForMathlib/Misc.lean`.
The mathematical literature cited below is citation-only; its prose is not copied.

## Verified locator

- Immutable source URL: https://github.com/leanprover-community/physlib/blob/2725b6f621901d4cd330869e9b77105045c1582e/QuantumInfo/Entropy/SSA.lean
- Source repository and revision: `leanprover-community/physlib`, revision `2725b6f621901d4cd330869e9b77105045c1582e`; source file `QuantumInfo/Entropy/SSA.lean`.
- Cited declaration: `Sᵥₙ_strong_subadditivity`, whose statement applies to finite `MState (d₁ × d₂ × d₃)` and gives the strong-subadditivity inequality on its actual marginals.
- Preserved receiving source: `D5/S3/Quantum/Information/StrongSubadditivity/Physlib/Entropy/SSA.lean`, whose retained upstream header and declaration identify this exact source mapping. The locator covers the finite density-state supplier, including the singular-state scope recorded above; the receiving port and downstream AD-classical conditional-copy application remain repository content.

## Consumed source mapping

There are 32 local supplier modules. In this table local paths are relative to
`D5/S3/Quantum/Information/StrongSubadditivity/Physlib/`; upstream paths are
relative to the immutable revision above. Split local modules share one
upstream source. The table describes the consumed closure, not the complete
Physlib project.

| Local module | Upstream source |
| --- | --- |
| `ClassicalInfo/Distribution.lean` | `QuantumInfo/ClassicalInfo/Distribution.lean` |
| `ClassicalInfo/Entropy.lean` | `QuantumInfo/ClassicalInfo/Entropy.lean` |
| `ClassicalInfo/ForMathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` | `QuantumInfo/ClassicalInfo/ForMathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` |
| `ClassicalInfo/Prob.lean` | `QuantumInfo/ClassicalInfo/Prob.lean` |
| `Entropy/SSA/Operator.lean` | `QuantumInfo/Entropy/SSA.lean` |
| `Entropy/SSA.lean` | `QuantumInfo/Entropy/SSA.lean` |
| `Entropy/VonNeumann.lean` | `QuantumInfo/Entropy/VonNeumann.lean` |
| `ForMathlib/ContinuousLinearMap.lean` | `QuantumInfo/ForMathlib/ContinuousLinearMap.lean` |
| `ForMathlib/HermitianMat/Basic.lean` | `QuantumInfo/ForMathlib/HermitianMat/Basic.lean` |
| `ForMathlib/HermitianMat/CFC/Basic.lean` | `QuantumInfo/ForMathlib/HermitianMat/CFC.lean` |
| `ForMathlib/HermitianMat/CFC.lean` | `QuantumInfo/ForMathlib/HermitianMat/CFC.lean` |
| `ForMathlib/HermitianMat/Inner.lean` | `QuantumInfo/ForMathlib/HermitianMat/Inner.lean` |
| `ForMathlib/HermitianMat/LogExp.lean` | `QuantumInfo/ForMathlib/HermitianMat/LogExp.lean` |
| `ForMathlib/HermitianMat/NonSingular.lean` | `QuantumInfo/ForMathlib/HermitianMat/NonSingular.lean` |
| `ForMathlib/HermitianMat/Order.lean` | `QuantumInfo/ForMathlib/HermitianMat/Order.lean` |
| `ForMathlib/HermitianMat/Proj.lean` | `QuantumInfo/ForMathlib/HermitianMat/Proj.lean` |
| `ForMathlib/HermitianMat/Reindex.lean` | `QuantumInfo/ForMathlib/HermitianMat/Reindex.lean` |
| `ForMathlib/HermitianMat/Sqrt.lean` | `QuantumInfo/ForMathlib/HermitianMat/Sqrt.lean` |
| `ForMathlib/HermitianMat/Trace.lean` | `QuantumInfo/ForMathlib/HermitianMat/Trace.lean` |
| `ForMathlib/HermitianMat/Unitary.lean` | `QuantumInfo/ForMathlib/HermitianMat/Unitary.lean` |
| `ForMathlib/HermitianMat.lean` | `QuantumInfo/ForMathlib/HermitianMat.lean` |
| `ForMathlib/IsMaximalSelfAdjoint.lean` | `QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean` |
| `ForMathlib/Isometry.lean` | `QuantumInfo/ForMathlib/Isometry.lean` |
| `ForMathlib/LinearEquiv.lean` | `QuantumInfo/ForMathlib/LinearEquiv.lean` |
| `ForMathlib/Matrix/Positivity.lean` | `QuantumInfo/ForMathlib/Matrix.lean` |
| `ForMathlib/Matrix.lean` | `QuantumInfo/ForMathlib/Matrix.lean` |
| `ForMathlib/Misc.lean` | `QuantumInfo/ForMathlib/Misc.lean` |
| `ForMathlib/Tactic/Commutes/Attribute.lean` | `QuantumInfo/ForMathlib/Tactic/Commutes/Attribute.lean` |
| `ForMathlib/Tactic/Commutes.lean` | `QuantumInfo/ForMathlib/Tactic/Commutes.lean` |
| `States/Mixed/MState/Basic.lean` | `QuantumInfo/States/Mixed/MState.lean` |
| `States/Mixed/MState.lean` | `QuantumInfo/States/Mixed/MState.lean` |
| `States/Pure/Braket.lean` | `QuantumInfo/States/Pure/Braket.lean` |

Adaptations rewrite module imports into the content namespace and retain the
original attribution. Four supplier files are split into carrier/basic,
operator/entropy, or positivity/consumer pieces as shown in the table.
The Hermitian-matrix umbrella omits unconsumed `LiebConcavity`, `Peierls`,
`Rpow` and `Schatten` imports. The mixed-state port omits `traceNorm_eq_one`
and its trace-norm import, and unused `MState.ofClassical_pow` and `Rpow`.
The von Neumann entropy port omits `coherentInfo` and channel imports;
the SSA port stops after strong subadditivity. Local elaboration options and
project module headers are adapted. The existing `Schatten/MatrixSimilarity`
provides multiset permutation and unitary-similarity eigenvalue lemmas; their
duplicate supplier proofs and the unconsumed `HermitianMat.ker_sum` are omitted.
The supplier matrix diagonal-CFC lemma is named `Matrix.cfc_diagonal_real` to
avoid ambiguity with existing entropy-production lemmas.
The partial-trace scalar type is explicit. The isometry CFC proofs keep the
spectral unitary in `Matrix` and normalize matrix associativity explicitly;
rectangular products select the canonical `Matrix` multiplication instance
explicitly, and the
`Matrix`/`CStarMatrix` elaboration setting is confined to the isometry
conjugation lemma.
`FiniteDensityPurification` shares the
consumed carrier while retaining the project conversions and purification witness.
Replace each port by a direct import when equivalent declarations become
available in the repository's pinned Mathlib.

## Receiving mathematical interfaces

`FiniteDensityPurification.toMState` preserves the project's PSD trace-one
complex matrix. `StrongSubadditivity.toMState_marginalLeft` and
`toMState_marginalRight` identify the actual partial traces; explicit
relabeling handles the tensor associator. `entropy_toMState` identifies the
natural-logarithm entropies through continuous functional calculus, with
zero eigenvalues contributing zero. The receiving `strong_subadditivity`
therefore has actual marginal densities and no SSA, invertibility or
entropy-equality premise. These are receiving interfaces to the attributed
supplier, not an independent spectral or entropy foundation.

## AD-classical Zhang-Yeung scope and literature classification

Zhen Zhang and Raymond W. Yeung, *On characterization of entropy function via
information inequalities*, IEEE Transactions on Information Theory **44**(4),
1440–1452 (1998), DOI [10.1109/18.681320](https://doi.org/10.1109/18.681320),
is the classical non-Shannon inequality reference. That classical result is
not an attribution for arbitrary entangled conditional quantum blocks.

The repository's `ClassicalADZhangYeung.zhang_yeung_classical_ad` is a
repository-derived conditional-copy composition of the attributed SSA theorem
and the existing orthogonal-record and product-entropy results. For finite
nonempty A, B, C, D it treats exactly

$$
\rho_{ABCD}=\sum_{a,d}p_{ad}|a\rangle\langle a|_A
  \otimes\tau^{ad}_{BC}\otimes|d\rangle\langle d|_D,
\qquad p_{ad}\ge0,\quad\sum_{a,d}p_{ad}=1.
$$

Every conditional `tau_ad` is an arbitrary joint BC density state. Entangled
and singular blocks, noncommuting C marginals, and zero weights are included.
The constructed copy uses E with C's carrier and block
`tau_ad` tensor `Tr_B(tau_ad)`, reordered into ABCDE. Actual E-discard and
ADE/ACD relabel identities, CQ record entropy and product entropy establish
the copy entropy equalities and `I(E:BC|AD)=0`. Eleven SSA inequalities on
actual marginals of that same state imply

$$
I(A:B)+I(A:CD)+3I(C:D\mid A)+I(C:D\mid B)-2I(C:D)\ge0.
$$

This classification makes no novelty, uniqueness or priority claim. The
literature priority of this precise hybrid AD-classical/arbitrary-joint-BC
statement has not been established here. The proof does not establish the
nonorthogonal, merely separable, AB-classical or unrestricted quantum case.
No separate AC extension is claimed. The unrestricted quantum target
[issue #23764](https://github.com/the-omega-institute/trureturing/issues/23764)
remains open.
