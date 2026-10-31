---
slug: huang-kosugi-nishi-matsushita-2024-reflection-diagonal-cnot-lower-bound
bibkey: huangkosuginishimatsushita2024reflectiondiagonal
doi: 10.7566/JPSJ.93.054002
url: https://arxiv.org/abs/2310.06676v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.result
---

# Reflection-symmetric diagonal unitaries require the worst-case CNOT count

## Problem

X. Huang, T. Kosugi, H. Nishi and Y.-i. Matsushita, “Optimized synthesis of circuits for diagonal unitary matrices with reflection symmetry”, *J. Phys. Soc. Jpn.* 93, 054002 (2024), arXiv:2310.06676v2, study ancilla-free circuits over $\{\mathrm{CNOT},R_z\}$ for diagonal unitaries whose phases obey Eq. (1). Their $2^{2n}\times2^{2n}$ diagonal matrix has $\theta_{j,j'}=\theta_{2^n-1-j,2^n-1-j'}$ for the two $n$-qubit registers. In the source e-print `main_arXiv2.tex`, line 847, they write:

> “Although we conjecture that the number of entanglement gates is at best $2^{2n-1}+2n-2$ in the $\{\mathrm{CNOT}, R_z\}$-based circuit for the worst scenario of diagonal unitary matrices that satisfy Eq. \eqref{intro:eq-theta}, we find by numerical tests (with qiskit) that the circuit depth (based on the CNOT, $R_z$ implementation) can be further reduced by putting some CNOT gates with different control and target qubits together (see the numerical depth in the brackets in Table \ref{tab:6}).”

The formal model has $m$ wires with Boolean computational basis $\mathrm{Qubits}(m)=\mathrm{Fin}(m)\to\mathrm{Bool}$. A gate is either a subtype of an ordered pair of distinct wires (a CNOT target and control) or a pair consisting of a wire and a real rotation angle. Its matrix is the CNOT reindexing of the identity or the diagonal $R_z$ matrix with the two phases $\exp(\mp i\varphi/2)$. A circuit matrix is the right-fold product of these gate matrices, and `cnotCount` counts only the CNOT summands.

The settled proposition `claim` is: for every $n\in\mathbb N$ with $1\le n$, there exists $\theta:\mathrm{Qubits}(2n)\to\mathbb R$ invariant under bitwise complement, such that for every circuit over `gate (2 * n)` and every $c\in\mathbb C$, if its `circuitMatrix` equals $c$ times the diagonal matrix with entries $\exp(i\theta(x))$, then
$2^{2n-1}+2n-2\le\mathrm{cnotCount}(\mathrm{circuit})$.
This is a worst-case lower-bound existence statement; it does not quantify over every reflection-symmetric diagonal unitary.

## Motivation

The source’s Eq. (1) identifies the reflection symmetry with complementing all $2n$ bits, and its Algorithm 1 constructs every such diagonal unitary with $2^{2n-1}+2n-2$ CNOT gates (the construction is described at lines 229 and 314 of `main_arXiv2.tex`). A matching lower bound for one member of the class determines the worst-case CNOT count when combined with that construction. The formal result isolates the lower-bound half of this comparison.

## Gap

Issue [#24527](https://github.com/the-omega-institute/trureturing/issues/24527) records the bounded check made before formalization. The arXiv v2 source and the journal version retain the conjecture. The cited-work search reported there found no theorem settling this lower bound; the listed works on parity networks, diagonal-unitary synthesis, rotation-count bounds, and spin-boson mappings do not supply this statement. A later graph-parity result covers weight-two labels only and gives a weaker count for the present parameters. The repository had no prior problem, library, or D5 entry for this conjecture.

`not-found-in-searched-scope`.

## Route

1. The proof chooses the phase function `hardTheta`, which is $\pi/2$ on the all-false and all-true Boolean inputs and $0$ elsewhere. The private lemma `hardTheta_reflection` proves its invariance under complement for every $m$ and every input, with no additional positivity hypothesis.

2. For a circuit matrix equal to $c\,\mathrm{diag}(\exp(i\theta(x)))$, the private lemma `diagonal_forces_identity` applies to arbitrary $m$, circuit, $c$, and $\theta$ under exactly that matrix equality and proves that `wireLabels circuit` is the identity matrix. The normal-form lemma `matrix_normal` supplies the phase-and-permutation form used here, while `phase_ne_zero` supplies nonvanishing of every accumulated phase.

3. For a Boolean vector $v$ and a complex-valued function $f$, `character` multiplies the values of $f$ with exponent $-1$ or $1 according to the Boolean dot product. The private lemmas `character_mul`, `character_global`, and `character_factor` establish multiplicativity, cancellation of a nonzero constant when $v\ne0$ and the constant is nonzero, and cancellation of a nowhere-zero factor depending on a distinct nonzero label $w$ when $v\ne0$, $v\ne w$, $w\ne0$, and every value of the factor is nonzero. The private lemma `phase_character` uses these cancellations under a bijective current label map, $v\ne0$, and the hypothesis that $v$ is absent from the rotation-label set.

4. The private lemma `hard_character` applies when $0<m$ and `evenLabel v` holds: the two exceptional inputs contribute two imaginary units and all other inputs contribute one, so the character is $-1$. The private lemma `rotation_labels` then assumes the matrix equality, the identity final label matrix, a global-character hypothesis for every nonzero $v$ and nonzero scalar, and the corresponding $-1$ character hypothesis for every even nonzero $v$; it concludes that every such $v$ belongs to `rotationLabels circuit`.

5. The private lemmas `pairs_labels` and `pairs_count` remove rotations while preserving the CNOT label evolution and identify the remaining-list length with `cnotCount`. The private lemma `rotation_outputs` says that whenever $v$ is in `rotationLabelsAux gs ls`, either some current wire label equals $v$ or $v$ is an output of one of the retained CNOT pairs. The private lemma `initial_odd` proves that every identity row has Boolean parity `true`.

6. The imported theorem `ReflectionDiagonalParityCounting.count_bound` is applied with $0<m$, a CNOT-pair list `gs`, an initial label map `ls`, and three explicit hypotheses: every initial row has parity `true`; every final row in `labels gs ls` has parity `true`; and every nonzero even Boolean vector occurs in `outputs gs ls`. It concludes $2^{m-1}+m-2\le\mathrm{length}(gs)$. The private lemma `return_count` takes $0<m$, a circuit, the equality `hnf` that `wireLabels circuit` is the identity matrix, and the hypothesis $\forall v,\;\mathrm{evenLabel}(v)\to v\ne0\to v\in\mathrm{rotationLabels}(\mathrm{circuit})$; it concludes the same CNOT bound.

7. Finally, `claim_for_n` instantiates $m=2n$ for $1\le n$, so $0<m$ follows, takes `hardTheta` as the witness, invokes `diagonal_forces_identity`, `rotation_labels`, and `return_count`, and rewrites the count as $2^{2n-1}+2n-2$. The public theorem `result` proves `claim` by applying `claim_for_n` to each $n$.

## Falsifier

The dossier would not match the settled proposition if the circuit model allowed ancillary wires, gates beyond the disjoint-sum `gate` type, equal target and control indices, or a different $R_z$ convention. It would also be a mismatch if “reflection symmetry” were interpreted without the exact Boolean complement condition, if realization were required without an arbitrary complex global scalar, or if the quantity counted were circuit depth rather than the CNOT-only `cnotCount`. The proposition excludes $n=0$ and asserts existence of one hard phase function for each positive $n$; a claim about all symmetric matrices or about ancilla-assisted synthesis is outside its type.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.lean.json`.

Declaration statements:
- `result`: `sha256:17e1553601e2fce278fad196f73d99c272b4662eafb14a8e8a8063ed869f340b`;
- `claim`: `sha256:b13688383705a43d632753d6d0da0458a41680f589f51bd6525206146049fb29`.

Proof. It proves `result : claim`.

Axioms. `#print axioms` on `result` reports `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2023 preprint retained in the 2024 journal version, preregistered in issue #24527 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\in\mathbb N$ with $1\le n$, there exists a real phase function on $2n$ Boolean wires that is unchanged by complementing every bit, and every circuit over the declared `gate (2 * n)` type whose matrix is a complex scalar multiple of its diagonal exponential has CNOT count at least $2^{2n-1}+2n-2$.

**Computed, not formalized**. None.

**Argued, not formalized**

- **Mechanism.** The chosen phase is nontrivial only at the all-false and all-true inputs. For every nonzero even Boolean label, the character of that phase is $-1$, while a global scalar and any rotation factor with a distinct nonzero label cancel under the character. Therefore every nonzero even label must occur on a rotated wire; the parity-network count then charges one CNOT output for each required even label and at least $m-1$ compensating updates to return the final rows to odd parity. The private lemmas in the module formalize these steps, but this explanatory synthesis is not a separate public theorem.
- **Worst-case interpretation.** The source’s Algorithm 1 supplies an upper-bound construction with the same CNOT count for every reflection-symmetric diagonal unitary. Combining that source result with the proved lower-bound existence gives the exact worst-case CNOT count, but the upper-bound construction and this combined equality are not declarations of `result`.
- **Neighbouring questions.** The source’s circuit-depth bounds and its numerical depth reductions concern a different resource and are unaffected by this lower-bound result. Ancilla-assisted circuits, other gate sets, and which individual reflection-symmetric matrices require the full count remain outside the proposition.
- **Effect on dependent source statements.** The source’s claim that the Algorithm 1 CNOT count is optimal in the worst case is supported once its upper-bound construction is combined with this result; statements about depth, applications, and particular matrices do not follow from `result` alone.

## ASSUMED-UNVERIFIED

The literature search recorded in issue #24527 is bounded and does not establish exhaustive worldwide novelty or priority; the cited-paper readings reported there are not reproduced here. The source’s matching upper-bound construction is not formalized in this module, so the exact worst-case equality is a combined literature-and-Lean conclusion rather than the type of `result` alone. The explanatory mechanism, source applications, depth claims, ancilla-assisted variants, other gate sets, and any assertion about individual matrices beyond the existential witness remain outside the formal declaration.
