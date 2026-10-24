---
slug: fuchs-1996-thesis-logarithm-basis-question
bibkey: fuchs1996thesislogarithmbasis
doi: null
url: https://arxiv.org/abs/quant-ph/9601020v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.result
---

# Fuchs's physical-basis logarithm question

## Problem

C. A. Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1, §3.5.3, pp. 77–78, asks after equation (3.244):

> An interesting open question is whether there exists a basis in which to represent the operators ρ̂₀, ρ̂₁, etc., so that the matrix appearing in the logarithm above is diagonal. If so, this would greatly simply the computation of L(t).

The [source note](../Library/Entropy/fuchs1996thesislogarithmbasis.md) identifies the version and equations. [Preregistration #18588](https://github.com/the-omega-institute/trureturing/issues/18588) fixes the literal Lean conventions. The universal physical-basis assertion is **Refuted** by `D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Kronecker sum, equations (3.237), (3.242) | `ksum` | $I\otimes X+\overline X\otimes I$, with the preregistered column-vectorization order |
| Matrix inside the logarithm, equation (3.244) | `logArg` | $I+t\widetilde\rho_0^{-1/2}\widetilde\Delta\widetilde\rho_0^{-1/2}$; inverse of `CFC.sqrt` on both sides |
| Density operators | `d`, `rho0`, `rho1`, positive-definiteness and trace-one hypotheses in `claim` | Faithful finite-dimensional states; a counterexample here refutes a universal claim covering these states |
| Invertible difference in the source derivation | `(rho1-rho0).det ≠ 0` in `claim` | Preserved, with witness determinant $-1/4608$ |
| A basis in which to represent both operators | `U ∈ Matrix.unitaryGroup (Fin d) ℂ`, and both conjugations by $U^*\rho U$ | A physical basis induces $\overline U\otimes U$ on matrix space |
| Source's basis independent of $t$ | `∀ t, 0 < t → t ≤ 1 → ∃ U, …` | Permitting a separate basis at each $t$ weakens the positive assertion; its negation at $t=1$ also refutes a single basis for all $t$ |
| Diagonal logarithm argument | `Matrix.IsDiag` in `claim` | The entire matrix, in the induced basis |
| Negative answer | `result : ¬ claim` | Negation of the whole quantified assertion |

The explicit dimension, faithfulness, trace, determinant and interval binders are the preregistered finite density-state interpretation. The construction and every binder are retained literally. The proof uses the frozen `PathSpectralClassical.relativeCongruence` sandwich and `EntropyProductionCoherenceDeletionIdentity.cfc_diagonal` for square roots of diagonal matrices.

## Motivation

A physical change of basis acts on the original three-dimensional Hilbert space; its induced action on matrix space is constrained. The qutrit witness distinguishes that action from an unrestricted nine-dimensional unitary change of coordinates.

## Gap

The source is an explicitly published open question. Issue #18588 records the orchestrator's thesis reading and repository screen. Its literature screen reports no settlement in Fuchs–Caves (quant-ph/9604001), Jain–Nayak (quant-ph/0603278), or the surveyed later Fuchs papers; the reports concerning Petz–Sudár, Uhlmann and Bhatia–Rosenthal identify ingredients rather than this implication. Those literature reports are seat-reported. Search completeness is **ASSUMED-UNVERIFIED**.

## Route

Let

$$
R=\operatorname{diag}(1/2,1/3,1/6),\qquad
\rho_1=\frac1{16}\begin{pmatrix}7&-1&0\\-1&5&0\\0&0&4\end{pmatrix},\qquad D=\rho_1-R.
$$

The private `rho0_posDef`, `rho1_posDef`, `rho0_trace`, `rho1_trace` and `delta_det` verify the admissibility of this pair. Write $A=\operatorname{ksum}(R)$, $B=\operatorname{ksum}(D)$, $S=A^{1/2}$ and $K=S^{-1}BS^{-1}$. The private `K_conj` transports $K$ under a physical basis change.

Set $H=D+R/4$. The private `kernel_H` proves that $HX+XH=0$ forces $X$ to lie on the line through

$$
P=\begin{pmatrix}1&1&0\\1&1&0\\0&0&0\end{pmatrix}.
$$

The private `K_M` and `K_simple` identify the $-1/4$ eigenline of $K$ as the span of the vectorization of

$$
M=\begin{pmatrix}1&\sqrt{5/6}&0\\\sqrt{5/6}&\sqrt{2/3}&0\\0&0&0\end{pmatrix}.
$$

The private `M_minor` proves its upper-left minor is nonzero, since $\sqrt{2/3}\ne5/6$. In contrast, `product_column_minor` proves that every column of $\overline U\otimes U$ has zero such minor. The private `diagonal_has_eigen_column` supplies a column in the $-1/4$ eigenspace under a proposed diagonalization; `unitary_column_ne_zero` excludes a zero column. `physical_obstruction` combines these facts. The public `result` applies this obstruction at $d=3$, $t=1$.

### Declaration judgement

The public `result` has `proof_shape: bind-only`, `escape_witness: none`, and `admission_basis: open-problem-resolution (#18588; Refuted)`. The proof expands to existing matrix/CFC identities, finite entry calculations, algebraic normalization and their consumed logical consequences. Its private auxiliary theorems are consumed bind-only helpers. The helper-to-consumer relation and direct frozen declaration identities are generated from compiled proof terms in the PR judgement tables.

All short names below are in `D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation`; private declaration names have the compiler-generated `_private` prefix. Consumers are extracted from elaborated constants, including generated intermediate declarations.

| Declaration | `proof_shape` | `escape_witness` | Direct authored consumers |
| --- | --- | --- | --- |
| `conj_map_mul` | bind-only | none | `ksum_conj` |
| `liftU_unitary` | bind-only | none | `K_conj`, `physical_obstruction` |
| `ksum_conj` | bind-only | none | `K_conj` |
| `sqrt_conj` | bind-only | none | `K_conj` |
| `ksum_vec` | bind-only | none | `H_P_vec`, `K_simple` |
| `inv_conj` | bind-only | none | `K_conj` |
| `K_conj` | bind-only | none | `result` |
| `ksum_add` | bind-only | none | `ksum_shift_H` |
| `ksum_real_smul` | bind-only | none | `ksum_shift_H` |
| `rho0_posDef` | bind-only | none | `result` |
| `rho1_decomp` | bind-only | none | `rho1_posDef` |
| `rho1_posDef` | bind-only | none | `result` |
| `rho0_trace` | bind-only | none | `result` |
| `rho1_trace` | bind-only | none | `result` |
| `delta_det` | bind-only | none | `result` |
| `kernel_H` | bind-only | none | `K_simple` |
| `H_hermitian` | bind-only | none | `H_P_vec`, `K_simple` |
| `HP` | bind-only | none | `H_P_vec` |
| `sqrt_diag` | bind-only | none | `sqrt_rho0` |
| `sqrt_minor` | bind-only | none | `M_minor` |
| `M_minor` | bind-only | none | `physical_obstruction` |
| `diagonal_has_eigen_column` | bind-only | none | `physical_obstruction` |
| `unitary_column_ne_zero` | bind-only | none | `physical_obstruction` |
| `product_column_minor` | bind-only | none | `physical_obstruction` |
| `rates_pos` | bind-only | none | `S_posDef`, `S_sq`, `sqrt_rho0` |
| `ksum_rho0` | bind-only | none | `S_sq`, `sqrt_rho0` |
| `sqrt_rho0` | bind-only | none | `K_M`, `K_simple`, `S_sq` |
| `S_posDef` | bind-only | none | `S_inv_mul`, `S_mul_inv` |
| `S_mul_inv` | bind-only | none | `K_simple` |
| `S_inv_mul` | bind-only | none | `K_M`, `S_inv_M` |
| `S_sq` | bind-only | none | `K_M`, `K_simple` |
| `S_P` | bind-only | none | `K_M`, `K_simple`, `S_inv_M` |
| `M_ne_zero` | bind-only | none | `physical_obstruction` |
| `shift_H` | bind-only | none | `ksum_shift_H` |
| `ksum_shift_H` | bind-only | none | `B_P`, `K_simple` |
| `S_inv_M` | bind-only | none | `K_M` |
| `H_P_vec` | bind-only | none | `B_P` |
| `B_P` | bind-only | none | `K_M` |
| `K_M` | bind-only | none | `physical_obstruction` |
| `K_simple` | bind-only | none | `physical_obstruction` |
| `physical_obstruction` | bind-only | none | `result` |
| `result` | bind-only | none | settling conclusion |

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Falsifier

A physical unitary diagonalizing the stated logarithm argument for this pair at $t=1$, an incorrect source-to-operator correspondence, or an error in the eigenline/minor implication would defeat this refutation. Numerical optimization alone cannot establish the nonexistence of such a unitary; the Lean proof establishes it.

## Evidence

The canonical source is [FuchsLogarithmBasisRefutation.lean](../D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.lean); its [Blueprint](../Blueprint/D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.md) displays all public definitions and the entire negated claim. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

### Experiment

The [experiment directory at commit `a826c13d081fbfab273f201823dc367caa68749f`](https://github.com/the-omega-institute/trureturing-experiments/tree/a826c13d081fbfab273f201823dc367caa68749f/docs/reports/fuchs-1996-physical-basis-logarithm-diagonal) contains `check.py`, SHA-256 `96971449bd1f7f214a0d2c49c737c04c6eba2e05ca94070089ee51f84ec5148f`. Command: `/tmp/op-fuchs/probe/pyenv/bin/python /Users/auric/trureturing-experiments/docs/reports/fuchs-1996-physical-basis-logarithm-diagonal/check.py`; exit 0, `RESULT PASS`. The script bytes match the pinned commit.

For the fixed qutrit pair, at $t=0.25,0.5,1$, respectively, the computed minimum eigenvalues are $0.9375,0.8750,0.7500$, and the best off-diagonal squared Frobenius masses found over 40 optimization starts are $9.480\times10^{-5},3.792\times10^{-4},1.517\times10^{-3}$. These are optimization outputs, not certified global minima or analytic lower bounds. The computed commutator norm is $1.473\times10^{-2}$. A commuting control at $t=0.7$ yields mass $2.016\times10^{-16}$. Of 12 generated random qutrit candidates at $t=0.5$, 10 pass the positivity filter and are tested with 15 starts each; their printed commutator/mass pairs satisfy the script's thresholds. These finite computations prove no all-pair classification.

## Triage

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| FU_1: exact requested negative claim | **Proved, kernel-checked:** `result` | The preregistered universal positive assertion fails at the displayed faithful qutrit pair and $t=1$ |
| Mechanism | **Proved, kernel-checked:** private `kernel_H`, `K_M`, `K_simple`, `M_minor`, `product_column_minor`, `diagonal_has_eigen_column`, `physical_obstruction` | Every nonzero vector in the designated $-1/4$ eigenline has nonzero upper-left reshaped minor, whereas every induced physical column has zero minor |
| Whole parametric family | **Open:** not a completed Lean claim | The formula $\rho_1=(1-2\varepsilon)R+\varepsilon(I-P_v)$, where $P_v=vv^*$ and $v=(1,1,0)/\sqrt2$, for all $0<\varepsilon<1/2$ is outside this finite settlement |
| All-dimension iff-commute classification and converse | **Open:** no formal or prose proof of necessity is claimed here | Physical diagonalizability forcing commutation in arbitrary dimension is not needed for `result` |
| Commuting sufficient repair | **Proved in prose:** simultaneous diagonalization makes both Kronecker sums diagonal; the positive diagonal square root, its inverse, products and the identity remain diagonal | This sufficient condition excludes the exhibited pair; it is not a separate Lean theorem in this module |
| Non-physical bases | **Proved in prose, conditional on Hermiticity:** the finite-dimensional spectral theorem permits unrestricted unitary diagonalization of a Hermitian matrix | Such a unitary need not be induced by a physical basis; this module refutes the physical assertion only |
| Source consequence | **Proved by the refutation and scope of `claim`:** `result` | The universal basis step after (3.244) fails; equations (3.236)–(3.244) and unrestricted tensor-space diagonalization are not negated |
| Numerical evidence | **Computed:** the pinned experiment and exit-0 reading above | Only the fixed $t$ values, one commuting control, and 10 retained random qutrit samples |
| Literature and classification boundary | **Open:** completeness of the literature screen is **ASSUMED-UNVERIFIED** | Neither the all-dimension classification nor the family is included in the formal settlement |

For the displayed pair, the $(0,1)$ commutator entry is $(1/2-1/3)(-1/16)=-1/96\ne0$; this is an exact prose calculation, not an additional kernel-checked theorem. The surviving sufficient repair follows directly from the displayed diagonal operations. Neither it nor the numerical examples assert the general converse.

## ASSUMED-UNVERIFIED

Completeness of the prior-art screen and the seat-reported literature statements remain **ASSUMED-UNVERIFIED**. The all-dimension necessity theorem, the full parameter family and the integral/range route are outside the completed formal claim. Numerical search results are finite floating-point observations and do not certify nonexistence or a global minimum. The kernel-checked refutation is conditional on the explicit source interpretation recorded in the statement echo.
