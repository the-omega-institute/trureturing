---
slug: xie-younis-mei-eberly-2024-qudit-tetrahedron-genuine-refutation
bibkey: xieyounismeieberly2024journey
doi: 10.3390/e26030217
url: https://arxiv.org/abs/2304.03281v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.result
---

# The entropic tetrahedron is not a genuine four-qudit entanglement measure

## Problem

S. Xie, D. Younis, Y. Mei and J. H. Eberly, *Multipartite Entanglement: A Journey Through Geometry*, arXiv:2304.03281v2; Entropy 26(3), 217 (2024), define the genuine requirement in `tetrahedron.tex`, line 57:

> The ``genuine'' requirement requires that a GME measure should only, and always, vanish for biseparable states \cite{ma2011,xie2021}.

Their Scalability paragraph, line 220, states:

> Nonetheless, our tetrahedron measure presented in this work maintains its scalability. Specifically, we can consistently partition a large system into four groups and explore genuine quadripartite entanglement among these groups. Essentially, the tetrahedron measure is a genuine four-qudit entanglement measure, where each party possesses more than two dimensions. The extension of entropic fill to qudit systems has been made possible by a recent study \cite{yang2022}. Additionally, we have conducted numerical verifications, demonstrating the existence of unique nonnegative solutions for Eq.~\eqref{eqn1} and \eqref{eqn2} in qudit systems up to $d=50$. Consequently, we conjecture that our tetrahedron measure is also applicable to qudit systems.

These quotations were checked against the complete v2 TeX source, `tetrahedron.tex` (233 lines, md5 `da0b24bf21c330f90979f63e7679749c`), fetched from https://arxiv.org/src/2304.03281v2. The definitions and further quotations are collected in [the literature note](../Library/QuantumContext/xieyounismeieberly2024journey.md).

Issue [#20861](https://github.com/the-omega-institute/trureturing/issues/20861) fixes the following reading. Each of four parties has Hilbert space $\mathbb C^d$, with $d\ge2$, and $\psi$ is a coefficient function with $\sum_x\|\psi(x)\|^2=1$. Write $S_X$ for the base-two von Neumann entropy of its reduced density matrix on $X$. Biseparability means factorization across some nonempty proper subset of the four parties.

An admissible fill consists of six nonnegative real coordinates $\sigma=(\sigma_{AB},\sigma_{AC},\sigma_{AD},\sigma_{BC},\sigma_{BD},\sigma_{CD})$ and a real parameter $\lambda$. The face equations are $\sigma_{ij}+\sigma_{ik}+\sigma_{il}=S_i$ for each party $i$. Put $p=\sqrt{\sigma_{AB}\sigma_{CD}}$, $q=\sqrt{\sigma_{AC}\sigma_{BD}}$ and $r=\sqrt{\sigma_{AD}\sigma_{BC}}$. The radical equations are $-p+q+r=\lambda S_{AB}$, $p-q+r=\lambda S_{AC}$ and $p+q-r=\lambda S_{AD}$. These are the source equations labelled `eqn1` and `eqn2`, TeX lines 103–121.

The source volume, TeX lines 92–101, is $V=(\sqrt2/3)\sqrt{2\sum_{ij}\sigma_{ij}}\big((p+q+r)(-p+q+r)(p-q+r)(p+q-r)\big)^{1/4}$. The formal claim is: for every $d\ge2$ and every unit $\psi$, if an admissible fill exists and every admissible fill has $V=0$, then $\psi$ is biseparable. This implication is refuted.

## Motivation

The source proposes using four groups of a larger system as the four parties of an entropic tetrahedron. Its interpretation as a genuine entanglement measure requires zero volume to distinguish biseparable states from pure states entangled across every bipartition. Existence or uniqueness of the area coordinates alone cannot supply that distinction.

## Gap

The bounded literature check in #20861 records:

- the orchestrator's reading of the claim in Xie et al. (2024), arXiv:2304.03281v2, and a qudit-extension statement in R. Amelung and H. Sahlmann (2026), arXiv:2601.14964v2;
- the orchestrator's web searches combining entropic fill or entropic tetrahedron with qudit, genuine, counterexample, biseparable and star network states; the returned related concurrence-tetrahedron work concerns a different measure;
- the search contributor's screen of 16 OpenAlex citing titles and relevant passages in arXiv:2312.17496, 2408.14011, 2408.10272, 2412.07032, 2602.00617 and 2601.14964, with no settlement found; the reported thesis and database checks likewise yielded no settlement;
- the orchestrator's repository search with no existing entropic-fill settlement found.

`not-found-in-searched-scope`.

## Route

1. **The state.** At $d=8$, take $\psi_\star=8^{-1/2}\sum_{b,c,e\in\{0,1\}}|4b+2c+e\rangle_A|b\rangle_B|c\rangle_C|e\rangle_D$. There are eight supported labels with squared amplitude $1/8$, giving unit norm. The compiled private lemmas compute $\rho_A=I_8/8$ and $\rho_B=\rho_C=\rho_D=\operatorname{diag}(1/2,1/2,0,\ldots,0)$, hence $(S_A,S_B,S_C,S_D)=(3,1,1,1)$.
2. **Forced coordinates and actual existence.** Subtract the $A$ face equation from the sum of the other three: $2(\sigma_{BC}+\sigma_{BD}+\sigma_{CD})=S_B+S_C+S_D-S_A=0$. Nonnegativity forces these three coordinates to vanish, and the remaining equations force $\sigma_{AB}=\sigma_{AC}=\sigma_{AD}=1$. This vector with $\lambda=0$ satisfies all three radical equations. Thus an admissible fill exists, and every admissible fill has $p=q=r=0$ and $V=0$.
3. **No product cut.** Factorization across $X\mid X^c$ implies $\psi(x)\psi(y)=\psi(x_Xy_{X^c})\psi(y_Xx_{X^c})$ for every two basis labels. Every proper cut separates $A$ from some leaf. Pairing the zero label with $(4,1,0,0)$, $(2,0,1,0)$ or $(1,0,0,1)$ for that leaf gives left side $1/8$ and right side zero. The compiled proof checks all membership choices for the four parties and excludes every nontrivial cut.
4. **Contradiction.** Applying `claim` to this normalized state, its existing fill and its all-fills zero-volume property gives biseparability, contradicting the product-minor argument.

## Falsifier

The refutation would miss the source claim if its states, entropies, equations or zero-volume condition differed from the source's. The module uses:

- `rho1` and `rho2`, the finite sums for the one-party and two-party partial traces of the rank-one density matrix; every two-party use has distinct party indices;
- `entropy2`, the frozen spectral natural-log entropy divided by $\log 2$, matching the base-two convention of TeX lines 65 and 107;
- `Biseparable`, an actual coefficient factorization with each factor depending only on its side of a nonempty proper cut;
- `AdmissibleFill`, all four face equations and all three radical equations, with nonnegative areas and $\lambda\in\mathbb R$; in particular, it allows $\lambda=0$;
- `volume`, including the surface-area factor and all four radical factors of the source formula.

Existence of a fill is a separate premise, and vanishing is required of every admissible fill. There is no optimization or empty-set infimum in this reading. No uniqueness assumption is needed. The module does not define the source's $F_4$; the passage from zero volume to zero entropic fill is stated below as a nonformal consequence of its definition.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.lean` (273 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It reuses the spectral entropy and diagonal-entropy formula of `ChenKatoBrandaoCMIRefutation` and the real and complex normalization identities of `FourMUBBoundEntanglementRefutation`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.lean.json`, statement `sha256:47b0c8c12fe62f8ec3d6750299a0ef5853c15e4fa0166ba0c3588cb965b7fb18`.

Declaration statements:

- `result`: `sha256:1a81a9e073f080a454354774a31c19cb774e87851b87c4e306abe45e7b0b1ea5`;
- `claim`: `sha256:0f1e48679f32e240e1c5feb36744365cdbdc3b91f3f824ea8742fbc70af78153`.

## Triage

Tier 1: an explicit claim and conjecture of a 2024 paper, with a qudit-extension statement reported in a 2026 paper, preregistered in issue #20861 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal implication is false: it is not the case that, for every natural $d\ge2$ and every coefficient function $\psi$ with $\sum_x\|\psi(x)\|^2=1$, existence of an admissible fill and zero volume for every admissible fill imply `Biseparable ψ`.

**Computed by hand from the definitions, not formalized** (reduced density matrices of $\psi_\star$; the one-party values for $A$ and $B,C,D$ are those used in the proof of `result`):

| Reduced subsystem | Nonzero eigenvalues | Rank | Entropy in bits |
| --- | --- | --- | --- |
| $A$ | $1/8$, eight times | $8$ | $3$ |
| Each of $B,C,D$ | $1/2$, twice | $2$ | $1$ |
| Each of $AB,AC,AD$ | $1/4$, four times | $4$ | $2$ |

All remaining eigenvalues are zero. Each reduced matrix is a sum over the eight supported labels, each of weight $1/8$; under $\mathbb C^8_A\cong(\mathbb C^2)^{\otimes3}$ the two-party matrices $\rho_{AB},\rho_{AC},\rho_{AD}$ are a Bell projector tensored with the maximally mixed state on the two remaining qubit factors of $A$. At the forced area vector, the radical equations become $0=2\lambda$, so the full admissible tuple has $\lambda=0$. Parameter uniqueness is thus checked for this witness; it is not a conclusion stated by `result`.

**Argued, not formalized.**

- *Mechanism.* Under $\mathbb C^8_A\cong(\mathbb C^2)^{\otimes3}$, the state is a product of three Bell pairs, each linking one central qubit factor to a different leaf. Every party cut crosses at least one pair. The equality $S_A=S_B+S_C+S_D$ nevertheless forces the leaf-to-leaf area coordinates to zero and collapses the volume. This is exactly the configuration described by the source in scenario (c), TeX line 135, where its exclusion is explicitly restricted to four-qubit systems. Allowing a party large enough to purify three independent mixed leaves removes that obstruction.
- *Dimension boundary of this mechanism.* In scenario (c), all three leaf entropies are positive and $S_A=S_B+S_C+S_D$. For a pure state, $S_{BCD}=S_A$, so $D(\rho_{BCD}\Vert\rho_B\otimes\rho_C\otimes\rho_D)=S_B+S_C+S_D-S_{BCD}=0$. The standard finite-dimensional relative-entropy equality criterion gives $\rho_{BCD}=\rho_B\otimes\rho_C\otimes\rho_D$. Equality of the two Schmidt ranks then gives $\operatorname{rank}\rho_A=\operatorname{rank}\rho_B\operatorname{rank}\rho_C\operatorname{rank}\rho_D\ge8$. Thus this particular mechanism requires central dimension at least eight; it does not establish the genuine requirement for $3\le d\le7$. Conversely, zero-padding the witness into any $d\ge8$ preserves all nonzero reduced eigenvalues and the forced fill; a factorization of the padded state would restrict to a factorization of the original. This extends the counterexample in ordinary mathematics, beyond the compiled conclusion's explicit proof instance.
- *A surviving conditional implication.* If $\lambda>0$ and one of the three signed radical factors vanishes, its radical equation gives zero entropy on the corresponding two-party cut. A pure state's zero cut entropy means that its reduced density matrix has rank one, so its Schmidt decomposition has one term and it factors across that cut. This dimension-independent implication does not cover the $\lambda=0$ branch. Merely excluding the star configuration does not, by itself, supply a complete repaired theorem.
- *Effect on the source.* TeX line 128 defines $F_4=(3^{7/6}/2)V^{2/3}$, so the witness has $F_4=0$ although it is not biseparable. The universal four-qudit genuineness assertion and the interpretation of the proposed four-group scrambling applications in lines 220–224 as a faithful GME detector therefore fail. Unique nonnegative solvability cannot repair this defect: the area vector is already forced. The witness does not settle the source's four-qubit claims, additivity argument or numerical LOCC study. If the same pure-state prescription is extended to qudit mixed states by the convex roof of line 226, it retains this zero on the witness's rank-one density matrix, because every pure component of a rank-one density lies on the same ray; that extension cannot restore the genuine requirement.

## ASSUMED-UNVERIFIED

The bounded literature check in #20861 does not establish exhaustive worldwide novelty or priority. Its web, OpenAlex, citing-paper, thesis, MathDB, formal-conjectures and repository-absence checks were not independently repeated for this dossier. The Amelung–Sahlmann passage in arXiv:2601.14964v2 is reported by that issue and was not independently reread.

The two-party spectra, uniqueness of $\lambda$, Bell-pair interpretation, entropy-equality and rank argument, dimension extension, surviving conditional implication, consequences for $F_4$ and its convex roof, and application analysis above are not formalized by this module. The rank argument uses the standard relative-entropy equality criterion and pure-state Schmidt-spectrum identity, neither verified by a Lean declaration in this dossier. The general claim for $3\le d\le7$, a complete repaired qudit genuine criterion, and general existence or uniqueness of admissible fills remain unsettled here. The source's numerical investigations up to $d=50$ and its LOCC computations were not reproduced.
