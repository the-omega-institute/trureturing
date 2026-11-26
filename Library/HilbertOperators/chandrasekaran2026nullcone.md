---
bibkey: chandrasekaran2026nullcone
authors: Venkatesa Chandrasekaran
year: 2026
title: An algebraic quantization of gravity from the null cone
doi: null
url: https://arxiv.org/html/2611.34924v1
claim: Algebraic quantization of first-order four-dimensional vacuum gravity on intersecting null cones yields a gravitational clock that bounds corner area, a GNS Type I representation from a chosen pure state extension, a proposed finite-dimensional causal-diamond subspace and thermal trace bound, and a nonperturbative graviton pair sum finite at positive Newton constant.
strata_touched:
  - D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound
  - D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary
  - D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation
license: citation-only
triage: anchor
---

# Null-cone gravitational clock, closed-trace finiteness, and phase resummation boundaries

## Verified locator

Source: https://arxiv.org/html/2611.34924v1

Preprint arXiv:2611.34924v1. The primary HTML sections referenced here are:

- Sections 3.2, 4.3, and 5.1 (Eqs. 3.27–3.28, 4.25–4.27, 5.15–5.21): null-cone shear focusing, the angular-averaged gravitational clock operator, and the upper bound on corner area at bounded clock reading.
- Section 4.2 (Eqs. 4.16–4.17 and Footnote 20): pure-state extension of the fixed-area Gaussian state to the observable C-star algebra yielding an irreducible Type I GNS representation; unitary equivalence across extensions is deferred in Footnote 20.
- Section 4.4 (Eqs. 4.33–4.34): nonperturbative graviton pair sum proportional to the dilogarithm at finite coupling versus harmonic logarithmic divergence of its third derivative at zero coupling.
- Section 5.1 (Eq. 5.16 and Footnote 18): Wigner-function heuristic for noncommuting clock operators in the non-emptiness estimate of the bounded-clock subspace.
- Section 5.2 and Appendix D.2 (Eqs. 5.30–5.38, 5.44–5.46, D.23–D.25): cycle-rearranged partial traces, the proposed finite-dimensionality contradiction for the causal diamond, and the disjoint joint-cut argument for finiteness of the AdS thermal trace.
- Appendix E: five Lorentzian cobordism axioms and their equivalence to Euclidean axioms under finite-trace cylinder hypotheses.

## Use and boundary

The formal modules citing this note separate verified mathematical structures from unformalized continuum physics and isolate exact logical boundaries in the preprint:

1. `D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.lean` extends the scalar clock-area inequality (Eqs. 5.21a–d) to arbitrary noncommuting bounded self-adjoint density operators and arbitrary focusing operators $E_i \ge 1$ on any complex Hilbert space, proves the exact two-channel deficit decomposition (area inhomogeneity plus shear delay), and characterizes equality uniquely by zero shear and uniform corner density.
2. `D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.lean` proves: (a) the positive trace-class finite-dimensionality and sharp dimension bound $\dim H \le \operatorname{Tr}(W)/c$ for any positive trace-class $W \ge c\,\mathbf{1}$ (and its spectral-projection corollary corresponding to Eq. E.12); (b) the positive cycle-union area-variance bound (Eq. D.25); (c) an explicit counterexample on $\ell^2(\mathbb{N})$ with an exact order-$r$ cycle bijection showing that strong convergence $P_N \uparrow \mathbf{1}$ and $Z_{P_N^{\mathrm{cyc}}}[X] \le 0 < Z_{P_N^{\mathrm{sym}}}[X]$ do not by themselves contradict $\dim H = \infty$ without an independent closed-trace finiteness or rearrangement-invariance hypothesis; and (d) the exact equivalence showing that unordered finite-subset convergence of the disjoint joint cut in Eqs. 5.44–5.45 holds if and only if the thermal trace $\sum_i w_i$ is already summable.
3. `D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation.lean` proves absolute convergence and uniform $O(g^2)$ boundedness of the finite-coupling mode sum in Eq. 4.33 alongside the exact harmonic divergence of its third derivative at $g = 0$ in Eq. 4.34.

No continuum four-dimensional Plebański action, gravitational edge-mode phase space, Bekenstein–Hawking entropy, Ashoke Sen one-loop logarithmic correction, ER=EPR null-state equivalence, or semiclassical Einstein equation is formalized in these modules.
