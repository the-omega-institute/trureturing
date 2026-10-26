---
slug: rexiti-memarzadeh-mancini-2022-positive-kraus-side-entanglement
bibkey: rexiti2022dephasing
doi: 10.1088/1751-8121/ac6d2c
url: https://arxiv.org/abs/2201.00388v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.result
---

# Positive Kraus operators do not exclude a side-entanglement advantage

## Problem

M. Rexiti, L. Memarzadeh and S. Mancini, *Discrimination of dephasing channels*, J. Phys. A 55, 245301 (2022), arXiv:2201.00388v2, Section 7, conjecture:

> In contrast, if all Kraus operators have simply the identity as unitary part in the polar decomposition, there is no benefit from side entanglement.

The complete source passage is in the [Library note](../Library/QuantumChannels/rexiti2022dephasing.md). Issue [#16535](https://github.com/the-omega-institute/trureturing/issues/16535) preregisters the negative clause, its representation-dependent reading and the exact finite-dimensional conventions.

### Statement echo

| Source clause or convention | Lean counterpart and scope |
| --- | --- |
| Kraus operators have identity polar unitary | `claim` assumes every Kraus operator is strictly positive definite, which makes that unitary uniquely the identity; this stronger hypothesis suffices to refute the source statement. |
| Channels and side entanglement | Both channels act on complex qubit matrices; the ancilla is a qubit and the first tensor factor. These are instances of the source's unrestricted systems. |
| Trace-preserving Kraus representations | Both right Gram sums equal the identity, with the same finite number of operators. |
| No benefit | For every assisted density and binary effect, some unassisted density and binary effect achieve at least the same success probability, with equal priors (`successAs` and `successUn`). |
| Density and effect | Frozen `GHZMeasureBiseparableBound.IsDensity` is the positive-semidefinite, trace-one predicate. The preregistered effect condition and the two Kraus sums are inlined literally; proofs use the frozen Kraus and Bell owners. |
| Negative clause fails | `result : ¬ claim`, with four operators per channel. |

## Motivation

Polar factors describe a Kraus representation. The success probabilities depend on the channels represented. A positive-definite representation therefore needs a separate argument before it can rule out an entanglement advantage.

## Gap

The source's phase-damping theorem does not prove the general negative clause. The literature screen recorded by the orchestrator in #16535 covers the source v2 and all ten citing works returned by Semantic Scholar: 2607.03757, 2506.01851, 2411.11313, 2407.14935, 2402.18941, 2402.05793, 2401.15634, 2212.10139, 2211.15108 and 2205.05736. That screen reports no treatment of this polar-factor criterion. The two same-group follow-ups do not settle it. The positive-Kraus and assisted-discrimination ingredients are published separately; their combination refutes this particular clause. Literature status: `not-found-in-searched-scope`, with the scope and attribution above.

## Route

For the tetrahedron $T=\{(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)\}$ use

$$K_s(a)=\frac{aI+s_xX+s_yY+s_zZ}{2\sqrt{a^2+3}},\qquad a\in\{2,3\}.$$

The consumed private helpers prove positive definiteness, completeness, and

$$\Phi_a(A)=\lambda_a A+\frac{1-\lambda_a}{2}\operatorname{Tr}(A)I,\qquad \lambda_a=\frac{a^2-1}{a^2+3}.$$

Two nonnegative trace pairings bound every unassisted strategy by $47/84$. For the Bell density $P$, the assisted input and effect are both $P$, and the success probability is $33/56$. Since $33/56-47/84=5/168>0$, the asserted universal comparison fails.

## Falsifier

The refutation requires the literal right Gram normalization, positive definiteness of all eight operators, a valid Bell density and effect, the universal unassisted upper bound, and the assisted success equality. Changing the source interpretation to require positivity in every representation is a different conjecture. No such representation-invariant statement is settled here.

## Evidence

Canonical source: [PositiveKrausSideEntanglementRefutation.lean](../D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.lean), with public definitions `successUn`, `successAs`, `claim`, and the single public theorem `result`. The helpers below are private compiled declarations in that module. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The frozen Kraus owner `FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus` supplies the linear-map expression used in the proofs. Frozen `BroadcastingChannelExtremaRefutation.density_le_one` and `RHLinalg.trace_mul_nonneg_of_posSemidef` supply the density-complement and trace-pairing bounds. Frozen `BellPureStateMixedMarginal.bell_pure_state_has_maximally_mixed_marginal` supplies Bell idempotence, and `CHSHWitness.bell_density_is_state` supplies positivity and trace one. The density-complement bound is reused from its published owner.

Experiment: [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c47e28086bfa4a22b22ab8a47c30c58010ed188e/docs/reports/rexiti-memarzadeh-mancini-2022-positive-kraus-side-entanglement). Command: `python3 check.py` in that directory; exit 0, `ALL_OK`; script SHA-256 `d35ec2a9e0f1c617aa69b2a4808b61dfc108dccdc119ebe7967ef3d831cf2a60`. Tested scope: exactly $a=2,3$, with symbolic entries of a qubit matrix. It checks Hermiticity, positive eigenvalues, completeness, independence, the channel formula, $\lambda_2=3/7$, $\lambda_3=2/3$, $\delta=5/21$, the scalar unassisted value $47/84$, the Bell-output difference spectrum $\{5/28,-5/84,-5/84,-5/84\}$ and the Bell success $33/56$. The universal unassisted inequality is supplied by Lean, rather than by a finite sample of states.

## Triage

Tier 1 external named conjecture, resolution **Refuted**, preregistered in #16535. Module `admission_basis: open-problem-resolution (#16535; Refuted)`. Every theorem has `proof_shape: bind-only`; the private helpers have live consumers. No escape witness is claimed. The computational certificates have utility `kind=certified-instance; basis=refutes` the literal `claim`. Delivery form: deposit-uncovered, no atom and no cover.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Positive tetrahedral representations and side-entanglement advantage | **Kernel-checked:** `kraus_pos_def`, `kraus_complete`, `kraus_apply_formula`, `unassisted_bound`, `assisted_success`, and `result` prove the concrete representation and strict advantage for $a=2,3$. |
| Channel-pair versus representation mechanism; Pauli representation of the same channels | **Proved in prose:** the Pauli calculation below exhibits the same channel with nonidentity polar factors. It explains representation dependence; the Pauli comparison is not an additional Lean theorem. |
| Published ingredients | **Literature reading:** DeBrota–Stacey, arXiv:1907.10999, Proposition 1, treats positive Kraus representations of depolarizing channels; Sacchi, quant-ph/0505174 (also quant-ph/0506072), treats entanglement-assisted channel discrimination. These ingredients are prior art, not new standalone results. |
| Representation-invariant criterion | **Open:** neither the universal quantification over representations nor a general criterion from canonical Kraus operators is proved here. |
| Orthogonal/canonical reading for a fixed support decomposition | **Proved in prose:** the pinching argument below leaves no channel parameter to discriminate within that fixed decomposition. Comparisons between different decompositions are outside that argument. |
| Exact numerical check | **Computed:** the pinned experiment entry gives the command, exit, hash, exact values and tested scope; no extension to all $a>\sqrt3$ is attributed to the experiment. |
| Consequences for the source's other results | **Literature reading:** the source's proved phase-damping no-advantage result and its cited Pauli and amplitude-damping examples are unaffected. The failed negative clause supplies no general criterion for further channels. |

**Pauli representation (prose derivation).** For $\lambda=\lambda_a$, put $p_0=(1+3\lambda)/4=a^2/(a^2+3)$ and $p_x=p_y=p_z=(1-\lambda)/4=1/(a^2+3)$. The weighted Pauli Kraus operators $\sqrt{p_0}I,\sqrt{p_x}X,\sqrt{p_y}Y,\sqrt{p_z}Z$ have unitary polar factors $I,X,Y,Z$. For any qubit matrix, $XAX+YAY+ZAZ=2\operatorname{Tr}(A)I-A$, by its four entries. Substitution gives exactly the displayed $\Phi_a$. Thus changing these representations changes polar factors while preserving both channel maps and their discrimination probabilities, including the tensor extension.

**Unassisted sharpness (prose derivation).** Take the input and effect both equal to the projector onto the first computational basis vector. Then $\operatorname{Tr}(N\sigma)-\operatorname{Tr}(N)/2=1/2$. The expression in `success_un_formula` gives $47/84$. Lean proves the universal upper bound; this paragraph supplies attainability without claiming an additional compiled theorem.

**Orthogonal positive Kraus operators (prose derivation).** If positive semidefinite $K_i$ are Hilbert–Schmidt orthogonal, $\operatorname{Tr}(K_iK_j)=0$ for $i\ne j$. This trace is the squared Hilbert–Schmidt norm of $K_i^{1/2}K_j^{1/2}$, so their supports are orthogonal. On the support of $K_i$, the completeness equation $\sum_j K_j^2=I$ forces $K_i^2=I$; positivity makes $K_i$ the support projector. The channel is the pinching $A\mapsto\sum_i P_iAP_i$. Fixing those support projectors fixes the channel, so a pair with that same fixed decomposition is identical and has no discrimination advantage. Positivity in an arbitrary nonorthogonal representation does not impose this restriction, as the concrete refutation shows.

## ASSUMED-UNVERIFIED

Literature completeness outside the source and ten citing works recorded in #16535 is unverified. The general $a>\sqrt3$ family, a representation-invariant criterion, and comparison of arbitrary distinct canonical pinching decompositions are not settled by the delivered Lean theorem. The Pauli-representation and pinching arguments are prose mathematics, not additional kernel-checked claims.
