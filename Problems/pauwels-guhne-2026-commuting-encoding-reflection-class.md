---
slug: pauwels-guhne-2026-commuting-encoding-reflection-class
bibkey: pauwelsguhne2026measurementbases
doi: 10.48550/arXiv.2608.21185
url: https://arxiv.org/abs/2608.21185v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CommutingEncodingReflectionClass.result
---

# Commuting product encoders define exactly the commuting-reflection qubit state class

## Problem

J. Pauwels and O. Gühne, *The Entanglement Content of Quantum Measurement Bases*, arXiv:2608.21185v1 (2026), Section VI, asks:

> Which other encoding classes define natural state classes, and what do these sets look like?

One of the proposed classes is:

> commuting families whose local factors are not Hermitian, the smallest step beyond our theorem

The paragraph states:

> For none of these is a characterization known, although $M_4$ now proves that the last class is strictly larger than commuting reflections.

These quotations are from the downloaded source `main.tex`, lines 1539–1547, md5 `217f1dae7e17966b2c9016fa75ef756b`. In the last quotation, “the last class” means tables of local Clifford unitaries. The source's local-encoding definition is at lines 328–340, and its encoder-structures definition is at lines 357–368; see also [the literature note](../Library/QuantumStates/pauwelsguhne2026measurementbases.md).

Issue [#20897](https://github.com/the-omega-institute/trureturing/issues/20897) fixes the following reading. For every $n\ge1$, put $N=2^n$ and let $\psi:\{0,1\}^n\to\mathbb C$ satisfy $\sum_x|\psi(x)|^2=1$. A commuting product encoding is a family of exactly $N$ operators $U_a=\bigotimes_{j=1}^n U_{a,j}$, with every $U_{a,j}$ a unitary $2\times2$ matrix, such that $U_aU_b=U_bU_a$ and $\langle U_a\psi,U_b\psi\rangle=\delta_{ab}$ for every pair of labels. A commuting-reflection encoding additionally requires $U_{a,j}^\dagger=U_{a,j}$ and $U_{a,j}^2=I$ for every label and site.

The claim is that $\psi$ admits a commuting product encoding if and only if it admits a commuting-reflection encoding. This equality of state classes is proved.

## Motivation

The paper organizes locally encoded measurement bases by the allowed encoder structure. Its characterization theorem (`main.tex`, lines 542–560) says that an $n$-qubit pure state admits a commuting-reflection encoding exactly when, up to a local unitary, it is a superposition with equal coefficient magnitudes in some graph-state basis. Determining whether arbitrary non-Hermitian local factors enlarge this state class answers one concrete branch of the Section VI question.

## Gap

The bounded literature check in #20897 records:

- arXiv listed only v1, and no existing repository issue matched this question;
- OpenAlex entry `W7204113169` reported zero citing works, the Google Scholar exact-title cluster showed no citations, and searches for commuting local encodings returned no classification;
- Kruszyńska–Kraus, arXiv:0808.3862, concerns commuting generalized stabilizers of LME states rather than this classification; no matching MathDB page was found.

The source and its single-version submission history were checked directly. The external citation and related-work readings above remain attributed to #20897. `not-found-in-searched-scope`.

## Route

1. **Local signs.** Commutation of the nonzero tensor products makes the corresponding local products proportional. The nonzero $2\times2$ determinants force each proportionality scalar to square to one. Thus two factors at the same site commute or anticommute.
2. **Local normal forms.** At each site, one local unitary makes all factors diagonal, or makes each factor a unit-modulus scalar times one of $I,X,Y,Z$. A nonscalar factor with nonzero trace forces the diagonal case; otherwise the nonscalar factors are traceless and reduce to reflection axes.
3. **A stabilizer frame.** Expand the transformed tensor operators in Pauli words. Their nonzero supports span an isotropic binary symplectic subspace: at diagonal sites only $I,Z$ occur, and at Pauli sites the supported letter is fixed by the factor. Global commutation makes the product of local signs one. Extend this subspace to a Lagrangian of dimension $n$ and construct a common orthonormal eigenbasis $\{f_x\}$, together with product reflections $H_a$ acting by $H_af_x=(-1)^{a\cdot x}f_x$.
4. **Flat coefficients.** Write the transformed state as $\sum_x c_xf_x$ and the original transformed encoders' eigenvalues as $\lambda_{a,x}$. The square orbit matrix $M_{x,a}=c_x\lambda_{a,x}$ has orthonormal columns. Hence its rows are orthonormal, and $|\lambda_{a,x}|=1$ gives $N|c_x|^2=1$ for every $x$.
5. **Replacement orbit.** Character orthogonality gives $\langle H_a\psi',H_b\psi'\rangle=N^{-1}\sum_x(-1)^{(a+b)\cdot x}=\delta_{ab}$ for the transformed state $\psi'$. The sign of a Hermitian phased Pauli word can be absorbed into one local factor since $n\ge1$. Conjugate the local reflection factors back to obtain an encoding of the original state. The converse retains a reflection encoding and discards its extra conditions.

## Falsifier

The settlement would miss the registered question if commutation were imposed on the individual local factors, if fewer than $2^n$ encoded vectors were used, or if a group law were assumed for the input encoders. The predicates impose none of these changes: there are exactly $2^n$ labels, commutation concerns the complete tensor operators, and the input is an arbitrary table of local unitaries satisfying the overlap equations. Local anticommutation is allowed.

The conclusion asserts existence of another encoding of the same state. It does not assert preservation of the given encoded basis, the original local spectra, or the original table of operators. The local dimension is exactly two.

## Evidence

The canonical source is `D5/S3/Quantum/Information/CommutingEncodingReflectionClass.lean` (804 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/CommutingEncodingReflectionClass.lean.json`, statement `sha256:64a070e09eb1ddfa9e05b01dd2d6184f524b636238ea9c749590134aef0fecb0`.

Declaration statements:

- `result`: `sha256:3e166dfc039a951011c3cfb028f170a56bf265dbc2186c83e2360a6e5e973e44`;
- `claim`: `sha256:ad0ae8af45937396ad79624fd4cc3320782801fb81c93aa99550180119767415`.

## Triage

Tier 1: an explicit open question of a 2026 paper, preregistered in issue #20897 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural number $n\ge1$ and every normalized $n$-qubit vector $\psi$, existence of a complete orthonormal orbit under pairwise commuting product unitaries is equivalent to existence of such an orbit with every local factor Hermitian and squaring to the identity.

**Argued, not formalized**

- *Decisive mechanism and completeness.* The qubit determinant constraint reduces local commutation phases to signs, allowing the encoders' Pauli supports to share a stabilizer frame. Completeness then forces flat weights through the square orbit matrix. With an incomplete orbit the matrix is rectangular and orthonormal columns do not imply orthonormal rows: the single encoder $I$ on $|0\rangle$ already has weights $(1,0)$ in the computational basis. This example limits the flatness argument; it does not refute an incomplete-orbit replacement statement.
- *Normalization.* An encoding already implies normalization: each orbit vector has norm one, and each tensor encoder is unitary, so its norm equals $\|\psi\|$. The separate normalization assumption can therefore be removed from an existential equivalence by splitting into the cases where an encoding exists or neither predicate is inhabited. This broader formulation is not the stated type of `result`.
- *Dimension boundary.* For one qutrit, let $\omega=e^{2\pi i/3}$, $\psi=(1,1,1)/\sqrt3$, and $D=\operatorname{diag}(1,\omega,\omega^2)$. The encoders $I,D,D^2$ commute and have overlaps $\frac13\sum_{x=0}^2\omega^{(b-a)x}=\delta_{ab}$. In contrast, three commuting Hermitian involutions admit a common eigenbasis with eigenvalues $\varepsilon_{a,x}\in\{\pm1\}$. If their orbit were orthonormal, its square matrix would have orthonormal rows, forcing every coefficient magnitude squared to be $1/3$. Distinct orbit columns would then have overlap $\frac13\sum_{x=0}^2\varepsilon_{a,x}\varepsilon_{b,x}$, which cannot vanish because it sums three signs. Thus the corresponding replacement statement in local dimension three is obstructed; this argument is outside the Lean module.
- *Effect on the source.* Combining `result` with Pauwels–Gühne's graph-basis characterization gives the same graph-basis description for states admitting arbitrary complete commuting product encodings. That composition with the source theorem is not formalized here. Its $M_4$ separation, $|M_4\rangle\in E_{\mathrm{gen}}^{(4)}\setminus E_{\mathrm{CR}}^{(4)}$ (`main.tex`, lines 905–909), consequently excludes every complete commuting product encoding of that state, conditional on the source's separation: any complete product encoding of it must contain a noncommuting pair. The settlement supplies a replacement basis and does not by itself extend the source's localization claims to a specified original basis.
- *Neighbouring questions.* The source also conjectures, “Every three-qubit pure state admits a commuting-reflection local encoding” (`main.tex`, lines 1592–1593). This remains open here; `result` only makes it equivalent to existence of a complete commuting product encoding for every three-qubit pure state. The classifications of noncommuting Pauli tables and local Clifford tables, and quantitative approximate or incomplete encoding problems, are not settled by this module.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The OpenAlex, Google Scholar, MathDB and Kruszyńska–Kraus readings reported in #20897 were not reproduced. The arXiv-issued DOI is displayed on the source's abstract page; no journal DOI is supplied there.

The arguments labelled above are not formalized. The graph-basis characterization and the $M_4$ separation were read in the source but their proofs were not independently verified here; consequences using them retain those premises. No assertion is made about preservation of a given encoded basis, an efficient construction or membership algorithm, approximate encodings, or incomplete encodings. No general classification is claimed for other local dimensions. The separate three-qubit universality conjecture remains open.
