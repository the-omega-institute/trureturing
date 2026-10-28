---
bibkey: boixoknillsomma2009randomization
title: Quantum state preparation by phase randomization
authors: Sergio Boixo, Emanuel Knill, Rolando D. Somma
year: 2009
doi: null
url: https://arxiv.org/abs/0903.1652v2
claim: Random evolution times multiply spectral coherences by their characteristic function; independent sums multiply those functions, and fair two-point waits cancel specified known gaps exactly.
strata_touched: []
license: citation-only
triage: anchor
---

# Random evolution and known-gap cancellation

Boixo, Knill and Somma, arXiv:0903.1652v2, *Quantum Information and
Computation* **9**, 833–855, develop phase randomization. The primary
[HTML text](https://arxiv.org/html/0903.1652v2) carries the heading
*Eigenpath traversal by phase randomization*.

Section II.2, Theorem 1 and equation (4), express the action on a spectral
coherence with gap $\omega$ through the characteristic function
$\Phi(\omega)=\mathbb E(e^{i\omega T})$. Equation (6) multiplies the
characteristic functions for independent sums of evolution times.
Section II.3, Example 1 and equation (7), choose $T=0$ or
$T=\pi/\omega_1$, each with probability $1/2$, for a positive known gap
$\omega_1$. Its characteristic function vanishes at that gap. The same
example explicitly extends this construction by summing independent
two-point times over finitely many known gaps. All summands are
nonnegative. This finite construction is an established result.

The source's bounds for uniform suppression over an interval of unknown
gaps have different hypotheses from exact cancellation at finitely many
known gaps. A finite sum need not suppress other gaps; its value there
must be checked directly. Recording the selected evolution time also
retains conditional information that is absent from the averaged
channel. Neither averaging nor a coherence multiplier identifies the
instrument produced by a subsequent rank-one read.

The [AURIC reconstruction continuation, §§37–40](../../docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)
uses this machinery at the fixed five-mode frequencies $2a,2b,a+b$.
Its source-relative deductions retain $a-b$, obtain noncommuting polar
ray effects, and compute the distinct seed-resolved records and actual
post-read dark leakage. The cited paper is the supplier of the
random-time mechanism, not of those five-mode deductions. This note
contains bibliographic description and no reproduced source text.

The repository's existing first-read suppliers are in
[RankOneFeedbackProtocol](../../D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.lean):
the private `branch_is_lueders` and `suffix_law`, and public
`luders_law_eq` and `actual_protocol_effect_correspondence`.
[MeasurableRankOneControl](../../D5/S3/Quantum/Fibers/MeasurableRankOneControl.lean)
supplies `arbitrary_protocol_tv_supremum` for independent measurable
control. The continuation uses five original modes, wait $U(t)$, first
outcome $j$, independent eight-valued seed and immediate Stop.
[FiveModeRealResponse](../../D5/S3/Quantum/Fibers/FiveModeRealResponse.lean)
contains the private `first_effect_real`, `deterministic_response_fiber`
and `actual_effect_span_eq`, and public `five_mode_real_response_fiber`;
these concern the fixed real-frame response and do not by themselves
supply a positive randomized event. The explicit positive filter in the
continuation is additional to those response/span facts.
