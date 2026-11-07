---
bibkey: peng2026shadowing
authors: Dekui Peng
year: 2026
title: 'Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits'
doi: null
url: https://arxiv.org/abs/2606.14435v3
claim: Question 5.1 asks whether every compact Hausdorff shadowing system is a factor of a compact zero-dimensional shadowing system.
strata_touched: []
license: citation-only
triage: anchor
---

# Compact Hausdorff shadowing and zero-dimensional extensions

The inspected edition is arXiv:2606.14435v3, revised 2 August 2026. Natural
time includes zero. Shadowing uses finite open covers: each error pair shares
one member of a control cover, and every pseudo-orbit is traced at every
time with respect to the prescribed output cover.

Question 5.1, PDF and printed p.21, reads:

> Let (X,f) be a compact Hausdorff dynamical system with shadowing. Does
> there exist a compact zero-dimensional dynamical system (Y,g) with
> shadowing and a factor map π:(Y,g)→(X,f)?

The factor map is continuous, onto, and satisfies πg=fπ. There is no
metrizability, countability, invertibility, or surjectivity assumption on f,
and no nonempty-space guard. For empty X, empty Y gives the vacuous case.
The unrestricted assertion is refuted by the kernel-checked result recorded
below.

## Repository formal status

`D5/S3/Topology/Shadowing/FreeFibreBoundary` defines the literal universal
claim as `claim` and proves `result : ¬ claim`. The witness is a compact
Hausdorff forward-shadowing source built from the supplied compact open map
with no zero-dimensional open resolution, a first-disagreement pullback, and
a binary full-shift core. The proof derives an open zero-dimensional
resolution from any hypothetical cover by finite initial graph languages and
the convergent Cantor section, contradicting that supplied static witness.
The formal result keeps arbitrary upstairs fibres and transients, continuous
onto semiconjugacy, and all natural times including zero. The generic
shift amplification is developed in the three modules listed below; the static compact
map and finite-observation suppliers are reused repository mathematics. This
records kernel status and attribution only; it makes no priority, uniqueness,
publication, or official-acceptance claim.

Definition 1.10, p.6, uses exactly the Mittag-Leffler condition

$$
\forall i\;\exists k\ge i\;\forall j\ge k,
\quad \varphi_i^j(X_j)=\varphi_i^k(X_k).
$$

Theorem 3.1 addresses compact metric systems by an inverse sequence of SFTs
with surjective bonds. Theorem 4.4 represents a compact shadowing system by
metrizable shadowing factors. Neither supplies the arbitrary compact
Hausdorff zero-dimensional extension of Question 5.1.

Section 5.1 indexes observations by finite subsets of an arbitrary
uniformity base. Question 5.2 asks for surjectivity of row-deletion maps in
the resulting symbolic arrays; coherent simultaneous-face lifts are the
obstacle. This is a sufficient construction route to Question 5.1, not a
separate solved problem.

The repository now formalizes one finite retained-cone step in
`D5/S1/Dynamics/Shadowing/BufferedConeExtension`. For a fixed finite old
graph and finite enlargement, its mixed-buffer graph uses explicit graph-of-
`f` edge witnesses, retains every complete old vertex path through time zero,
and gives one outer-buffer orbit tracer for each complete new path. This
finite result does not provide the global uniform follower bounds or settle
Question 5.1.

The four-slot Reg audit of
`D5.S1.Dynamics.Shadowing.buffered_whole_path_extension` remains unfinished:
the existing dependent-family owner recipe does not supply its typed exact
bridge, variation, sensitivity, observational dependence or source-selection
evidence. [Issue #25272](https://github.com/the-omega-institute/trureturing/issues/25272)
identifies the missing evidence. No validated registration is claimed.

The formal inverse-limit shadowing bridge is
`D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit`. It assumes a genuine
coherent ML diagram and therefore does not settle the construction question.

The generic binary graph coding, Baire decision, and first-disagreement
convergent section are in
`D5/S1/Dynamics/Shadowing/GenericBinarySection`. Open pullbacks, binary-shift
shadowing, and the finite-control one-step extension theorem are in
`D5/S1/Dynamics/Shadowing/OpenCoreShadowing`. Their declarations retain the
`D5.S1.Dynamics.Shadowing.FreeFibreBoundary` Lean namespace.
`D5/S3/Topology/Shadowing/FreeFibreBoundary` combines these with marked
complete graph languages to derive the open resolution contradiction;
its source-shadowing theorem, resolution-transfer theorem, literal `claim`,
and `result` remain in that endpoint module.

## Verified locator

Versioned primary source: https://arxiv.org/abs/2606.14435v3.
PDF: https://arxiv.org/pdf/2606.14435v3.

Question 5.1 is on printed/PDF p.21. Section 5.1 and Question 5.2 give
the simultaneous finite-face row-deletion construction on pp.21–22.
Definition 1.10 on p.6 supplies the Mittag-Leffler condition; Theorems
3.1 and 4.4 provide the metric-case and metrizable-factor results only.
