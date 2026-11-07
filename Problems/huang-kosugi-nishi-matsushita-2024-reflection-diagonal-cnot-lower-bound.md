---
slug: huang-kosugi-nishi-matsushita-2024-reflection-diagonal-cnot-lower-bound
bibkey: huangkosuginishimatsushita2024reflectiondiagonal
doi: 10.7566/JPSJ.93.054002
url: https://arxiv.org/abs/2310.06676v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.result
---

# The worst-case CNOT count for reflection-symmetric diagonal unitaries

## Problem

X. Huang, T. Kosugi, H. Nishi and Y.-i. Matsushita, *Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry*, J. Phys. Soc. Jpn. 93, 054002 (2024), arXiv:2310.06676v2, state in Sect. 6, Conclusion (`main_arXiv2.tex`, line 847):

> Although we conjecture that the number of entanglement gates is at best $2^{2n-1}+2n-2$ in the $\{\mathrm{CNOT}, R_z\}$-based circuit for the worst scenario of diagonal unitary matrices that satisfy Eq. \eqref{intro:eq-theta}, […]

The quoted TeX label denotes Eq. (1): for $n\ge1$, the real phases of a $2^{2n}\times2^{2n}$ diagonal unitary satisfy $\theta_{j,j'}=\theta_{2^n-1-j,\,2^n-1-j'}$ for every $0\le j,j'<2^n$ (`main_arXiv2.tex`, lines 207–227). Equivalently, writing $m=2n$ and $x\in\{0,1\}^m$, $\theta(\bar x)=\theta(x)$, where $\bar x$ complements every bit. The source specifies ancilla-free $\{\mathrm{CNOT},R_z\}$ circuits at lines 194 and 1225 and realization up to a global phase at lines 429–445.

Issue [#24527](https://github.com/the-omega-institute/trureturing/issues/24527) fixes the reading: for every $n\ge1$ there is such a phase function $\theta$ for which every finite circuit realizing $\operatorname{diag}(e^{\mathrm i\theta(x)})$ up to a global phase has at least $2^{2n-1}+2n-2$ CNOT gates. This lower-bound statement is proved. The source's matching upper bound from Algorithm 1 is separate from `claim`.

## Motivation

Huang, Kosugi, Nishi and Matsushita (2024, arXiv:2310.06676v2) use reflection symmetry to reduce circuit resources for diagonal unitaries occurring in first-quantized Hamiltonian simulation. Their Algorithm 1 supplies $2^{2n-1}-1$ blocks containing one rotation and one CNOT, together with $2n-1$ additional CNOT gates (Sect. 4, lines 314 and 434). A worst-case lower bound determines whether a smaller uniform CNOT budget can implement the whole reflection-symmetric class in the same gate and ancilla model.

The source definitions and locators are collected in [the literature note](../Library/Computability/huangkosuginishimatsushita2024reflectiondiagonal.md).

## Gap

The bounded literature check in #24527 reports:

- arXiv:2310.06676v2 retains the conjecture;
- no settlement in the six citing works listed by Semantic Scholar or the citing-work search through OpenAlex;
- no theorem directly supplying this count in the parity-network, diagonal-synthesis and graphic-parity-network literature examined there;
- no settlement in the recorded web, Zenodo, Crossref, formal-conjecture and repository searches.

`not-found-in-searched-scope`. These are the preregistration's reported search results; the source quotation is independently checked against the v2 TeX.

## Route

Put $m=2n$ with $n\ge1$. Vectors and dot products below are over $\mathbb F_2$; an even label $v$ has $\sum_i v_i=0$.

1. **A concrete hard phase.** `hardTheta` is $\pi/2$ at $0^m$ and $1^m$ and zero elsewhere, so its diagonal exponential $D_\ast$ is $\mathrm i$ at those two inputs and $1$ elsewhere. `hardTheta_reflection` gives complement invariance for every $m$ and every input. Here $m>0$ ensures that the two marked inputs are distinct.
2. **Circuit normal form and return.** Wire labels start at the identity rows, and a CNOT replaces its target label by target plus control. For every gate list, initial label matrix $L$, and inputs $x,y$, `matrix_normal` expresses the matrix entry from $Lx$ to $y$ as `phaseAux` times the indicator that the final label map sends $x$ to $y$; `phase_ne_zero` makes this phase nonzero for every list, $L$ and $x$. Under the equality $U=c\operatorname{diag}(e^{\mathrm i\theta(x)})$, with any $m$, real phase function $\theta$, circuit and complex scalar $c$, `diagonal_forces_identity` therefore gives final wire labels equal to the identity.
3. **Forcing all even parities.** Define $I_v(f)=\prod_x f(x)^{(-1)^{v\cdot x}}$, with the exponent $1$ when $v\cdot x=0$ and $-1$ otherwise. For $v\ne0$ and $c\ne0$, `character_global` gives $I_v(c)=1$. For distinct nonzero $v,w$ and a nowhere-zero function $f:\mathbb F_2\to\mathbb C$, `character_factor` gives $I_v(x\mapsto f(w\cdot x))=1$. Consequently, for a bijective initial label map, $v\ne0$ and $v$ absent from all rotation labels, `phase_character` gives $I_v(\mathrm{phaseAux})=1$. For $m>0$ and any even $v$, `hard_character` instead gives $I_v(D_\ast)=-1$. Under the diagonal matrix equality, final identity labels, cancellation of every nonzero constant at every nonzero $v$, and character value $-1$ at every nonzero even $v$, `rotation_labels` forces every nonzero even vector to occur on a rotated wire. Those are exactly its hypotheses; the matrix equality also supplies the nonzero scalar needed for cancellation.
4. **Counting outputs and restoration.** For any gate list and initial labels, whenever $v$ occurs on a rotated wire, `rotation_outputs` places it either among the initial labels or among the CNOT output labels. Identity rows are odd, so all required nonzero even vectors must be CNOT outputs. `ReflectionDiagonalParityCounting.count_bound` assumes $m>0$, every initial row odd, every final row odd, and every nonzero even vector present in the output list; it gives $2^{m-1}+m-2$ as a lower bound on the number of updates. In its proof, `even_output_count` needs $m>0$ and this output coverage and supplies at least $2^{m-1}-1$ even outputs. With $m>0$, odd initial rows and the same coverage, `birth_count` supplies at least $m-1$ odd-target, odd-control updates: their birth labels generate every even vector, while $b$ birth labels generate at most $2^b$ vectors. The identity `return_balance`, valid for every initial label matrix and update list, balances births against even-target, odd-control updates when both endpoint matrices have only odd rows. These restoring updates have odd outputs, so `disjoint_counts`, also valid for every initial matrix and list, counts them separately from the even outputs. `return_count` applies this bound when $m>0$, final labels are the identity and every nonzero even label occurs at a rotation; `pairs_count` identifies the extracted list length with `cnotCount`.

`claim_for_n` uses these lemmas for each $n\ge1$, and `result : claim` supplies the universal statement.

## Falsifier

A circuit-model mismatch would invalidate the interpretation. In the module, `Qubits m` is `Fin m → Bool`; `gate m` contains either distinct target and control wires or a wire and a real rotation angle. The gate matrices implement the target-bit exclusive-or and $R_z(\varphi)=\operatorname{diag}(e^{-\mathrm i\varphi/2},e^{\mathrm i\varphi/2})$. `circuitMatrix` is the right-folded product of these matrices, with the first list entry the leftmost factor, and `cnotCount` counts only CNOT entries. All wires belong to the same $m$-wire register.

`claim` quantifies over every complex scalar $c$ in the matrix equality, including every unit-modulus global phase. It requires exact matrix equality and exact real-phase reflection symmetry. It asserts an existential hard phase function for each $n\ge1$; it does not assert that every reflection-symmetric diagonal unitary requires the bound. Extra ancillas, approximate implementation, other gate sets and circuit depth are outside this statement.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.lean.json`.

Declaration statements:

- `result`: `sha256:17e1553601e2fce278fad196f73d99c272b4662eafb14a8e8a8063ed869f340b`;
- `claim`: `sha256:b13688383705a43d632753d6d0da0458a41680f589f51bd6525206146049fb29`.

## Triage

Tier 1 conjecture of a 2023 preprint retained in its 2024 journal version, preregistered in issue #24527 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge1$, there exists a real phase function $\theta$ on $2n$ Boolean wires with $\theta(\bar x)=\theta(x)$ for every $x$, such that every finite circuit of the module's CNOT and real $R_z$ gates, and every $c\in\mathbb C$, satisfying $\mathrm{circuitMatrix}=c\operatorname{diag}(e^{\mathrm i\theta(x)})$ has CNOT count at least $2^{2n-1}+2n-2$.

**Computed, not formalized**. None.

**Argued, not formalized.**

- *Sharpness and effect on the source.* Taking Huang, Kosugi, Nishi and Matsushita's Algorithm 1 and its correctness proof (2024, arXiv:2310.06676v2, Sect. 4 and Appendix C) as an external upper-bound premise, every allowed diagonal unitary has an implementation using at most $2^{2n-1}+2n-2$ CNOT gates. The existential lower bound therefore makes this budget exact in the worst case. The construction's resource guarantees and its Hamiltonian-simulation applications use this upper bound independently of the conjectured optimality; the settlement supplies the missing optimality conclusion. The upper bound is not a Lean conclusion of `result`.
- *Extension of the mechanism.* For any positive number $m$ of wires, mark any complementary pair $a,\bar a$ with a common real phase $\alpha$ satisfying $e^{2\mathrm i\alpha}\ne1$, and give all other inputs phase zero. For each nonzero even $v$, the two marked inputs have the same dot product with $v$, so their character product is $e^{2\mathrm i\alpha}$ or its inverse, hence is not $1$. A missing rotation label would give character $1$ by `phase_character`, applied from the bijective identity label map to this nonzero missing $v$. Under the circuit equality $U=c\operatorname{diag}(e^{\mathrm i\theta(x)})$ for this real phase function, `diagonal_forces_identity` returns the labels to the identity. The nonzero circuit phase equals $c$ times the nowhere-zero diagonal function, so $c\ne0$; `character_global` therefore removes this scalar at the nonzero $v$. Thus every nonzero even label is required. By `rotation_outputs`, each such rotation label is an initial row or a CNOT output; the initial identity rows are odd, so it must be an output. `ReflectionDiagonalParityCounting.count_bound` now applies because $m>0$, the initial and final rows are odd and all nonzero even labels occur as outputs. This gives the same lower-bound expression $2^{m-1}+m-2$ for this larger family, including odd $m$; this family statement is not formalized.
- *Neighbouring questions.* The optimal depth question in the source's Conclusion (lines 847–853) remains open here: a gate-count lower bound does not determine how many disjoint gates can run simultaneously. The source's ancillary comparator construction and its more structured interaction-potential families have additional resources or additional symmetry. This settlement gives no optimality statement for those restricted families or for ancilla-assisted implementations.

## ASSUMED-UNVERIFIED

The bounded literature check in #24527 does not establish exhaustive worldwide novelty or priority. The six citing-paper readings, the prior-literature comparisons and the index, web and repository search results reported there have not been independently reproduced for this dossier. The source's upper-bound construction has been read as a literature result, but is not independently implemented or Lean-verified here. The sharpness deduction using that external premise, the extended marked-pair family and the neighbouring-question analysis are not statements of `result`; the family extension is not formalized, and the depth and ancillary-model questions remain open here.
