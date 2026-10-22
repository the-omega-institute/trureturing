---
bibkey: garioncross2020cnotdihedral
authors: Shelly Garion; Andrew W. Cross
year: 2020
title: Synthesis of CNOT-Dihedral circuits with optimal number of two qubit gates
doi: 10.22331/q-2020-12-07-369
url: https://quantum-journal.org/papers/q-2020-12-07-369/
claim: Equation 12 relates conjugation of controlled-S by a local X to controlled-S inverse times a phase gate on the other qubit.
strata_touched: []
license: citation-only
triage: anchor
---

# Extracting a local phase from controlled-S

The [published open PDF](https://quantum-journal.org/papers/q-2020-12-07-369/pdf/), *Quantum* 4, 369, §2, p. 4, equation (12), gives identities for conjugating controlled-S by local $X$ gates. The exact equation and the source's gate definitions were inspected. Write $C=\operatorname{diag}(1,1,1,i)$ and $P=\operatorname{diag}(1,i)$ to distinguish its two-qubit $CS$ from its one-qubit $S$. The first two lines become

$$
(X\otimes I)C(X\otimes I)=C^\dagger(I\otimes P),\qquad
(I\otimes X)C(I\otimes X)=C^\dagger(P\otimes I).
$$

Right multiplication by $C$, using commutation of the diagonal factors, gives

$$
(X\otimes I)C(X\otimes I)C=I\otimes P,\qquad
(I\otimes X)C(I\otimes X)C=P\otimes I.
$$

Thus the local phase-extraction identity is an established relation. More generally, for $C_\vartheta|ab\rangle=e^{i\vartheta ab}|ab\rangle$ and $P_\vartheta=\operatorname{diag}(1,e^{i\vartheta})$, the same basis calculation follows from $ab+a(1-b)=a$. This elementary extension is not a novelty claim.

For a physical menu $R(t)=e^{-itX}$, the mutually inverse pulses $R(-\pi/2)=iX$ and $R(\pi/2)=-iX$ give the same conjugation with exact scalar cancellation. On a larger constrained space, one must still establish the pulse's restriction, subspace invariance and its action on any orthogonal sector. Those model-specific checks, and the count of forward fixed-phase calls, are supplied in [Static compatibility fibers §62](../../docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#62-五模式交互系数与保码端点控制). They are not supplied by the abstract two-qubit identity alone.

The article's optimality results concern its declared CNOT-dihedral generating set. They do not establish optimal pulse counts for the AURIC menu. This citation-only note reproduces no article text, figures or PDF.
