---
bibkey: wu2024distributedimaginarity
title: Resource theory of imaginarity in distributed scenarios
authors: Kang-Da Wu, Tulja Varun Kondra, Carlo Maria Scandolo, Swapan Rana, Guo-Yong Xiang, Chuan-Feng Li, Guang-Can Guo, Alexander Streltsov
year: 2024
url: https://arxiv.org/abs/2301.04782v1
doi: 10.1038/s42005-024-01649-y
claim: An explicitly real joint Kraus construction implements a given complex operation when supplied with a maximally imaginary qubit; the construction preserves that supplied qubit.
strata_touched: []
license: citation-only
triage: anchor
---

# Imbit-assisted real implementation

The journal locator is *Communications Physics* **7**, 171, Eq. (11),
the real Kraus construction immediately preceding it and the completeness
argument immediately following it. The corresponding arXiv locator is
arXiv:2301.04782v1, *Resource Theory of Imaginarity: New Distributed
Scenarios*, Appendix A, equations (22)–(23).

For complex Kraus matrices $K_j$, let
$|\widehat\pm\rangle=(|0\rangle\pm i|1\rangle)/\sqrt2$ and
$P_\pm=|\widehat\pm\rangle\langle\widehat\pm|$. The source constructs

$$
L_j=K_j\otimes P_+ +\overline{K_j}\otimes P_-.
$$

These matrices are real, because the two terms exchange under entrywise
conjugation. Their completeness operator is
$P\otimes P_++P^{\mathsf T}\otimes P_-$, where
$P=\sum_jK_j^\dagger K_j\le I$. With the supplied program $P_+$, the
joint operation produces $\sum_j K_j\rho K_j^\dagger\otimes P_+$.
This is a real operation on the joint complex algebra. It does not physically
conjugate an unknown input.

The use in the five-mode source problem is a restricted controlled real
rotation, together with a direct calculation for a mixed qubit extracted from
an actual source copy. A further source-specific circuit retains one
imaginary-sign qubit while measuring relative signs of the actual extracted
qubits using controlled real rotations and real Hadamards. Its mixed-source
orbit weights and conditional response budgets are proved in the owning
five-mode continuation, rather than supplied by this literature theorem.
The literature theorem does not provide that source,
select its unknown sign, distill a perfect imbit from its noisy states, or
establish a simultaneous unknown-label processor. Those are separate
source-specific obligations. Its exact finite real controls and joint
interaction remain declared services, rather than native operations supplied
by a classical description.

This note paraphrases the construction; no article text, figure or PDF is
redistributed.
