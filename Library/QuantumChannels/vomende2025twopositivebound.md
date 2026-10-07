---
bibkey: vomende2025twopositivebound
authors: F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi
year: 2025
title: "Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps"
doi: 10.1016/j.laa.2025.10.022
url: https://arxiv.org/abs/2506.02145v1
claim: "Theorem 1 proves the spectral trace bound for 2-positive trace-preserving maps; question (10) asks for the bound for arbitrary conditionally 2-positive maps."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace
  - D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound
  - D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization
  - D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound
license: citation-only
triage: anchor
---

# Universal bound for 2-positive maps

## Verified locator

DOI: 10.1016/j.laa.2025.10.022

Source: https://arxiv.org/abs/2506.02145v1

Theorem 1 and equation (3) appear on page 4 of arXiv v1. Question (10) and
conditional 2-positivity appear in §3, “Outlook”, on page 11. The journal
reference is *Linear Algebra and its Applications* 730 (2026), 262–275.
The journal text has not been verified; the quotations below are from arXiv v1.

## Source statements

Transition matrix, page 6:

> given Φ ∈ L(Cd×d) and any orthonormal basis G := {gj}dj=1 of Cd define TG(Φ) ∈ Cd×d (or TG, for short) via (TG)jk := ⟨gj|Φ(|gk⟩⟨gk|)|gj⟩.

Theorem 1, page 4:

> Let $\Phi\in\mathcal L(\mathbb C^{d\times d})$ be a 2-positive and trace-preserving linear map. Then

$$
{\rm tr}(\Phi)\leq d\min\Re(\sigma(\Phi))+(d^2-d).
$$

Question (10), page 11:

> Hence one may wonder whether all (generators of) completely positive maps, resp.~2-positive maps satisfy

$$
{\rm tr}(\Phi)\leq d\min\Re(\sigma(\Phi))+(d^2-d)\max\Re(\sigma(\Phi))\,?
$$

> A map $L$ is called *conditionally 2-positive* if $e^{tL}$ is 2-positive for all $t\geq 0$.

> In particular, every completely positive, every conditionally completely positive, and every 2-positive map is conditionally 2-positive.

> With this, (10) becomes really a conjecture about the spectrum of arbitrary conditionally 2-positive maps.

The trace is the trace of the linear endomorphism of the matrix algebra.
The spectrum is its characteristic-polynomial root multiset. Positivity of
$id_2\otimes\Phi$ is 2-positivity. No trace-preservation hypothesis occurs in
question (10).

## Sharpness and neighbouring questions

Remark 1(iii), equation (5), and Example 2 state that the coefficient `d`
in equation (3) cannot be increased, even for completely positive
trace-preserving maps. Those maps have maximal real eigenvalue 1, so the
same coefficient optimality holds in the larger class of equation (10).
This is a literature-based sharpness consequence; the Example 2 family is
not formalized in these modules. Attainment for conditionally 2-positive
maps beyond the source's classes is not addressed. The question of a positive
trace-preserving map violating equation (3) for $d\geq3$ remains open here.
