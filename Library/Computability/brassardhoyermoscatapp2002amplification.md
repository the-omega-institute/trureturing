---
bibkey: brassardhoyermoscatapp2002amplification
authors: Gilles Brassard; Peter Høyer; Michele Mosca; Alain Tapp
year: 2002
title: Quantum Amplitude Amplification and Estimation
url: https://arxiv.org/abs/quant-ph/0005055
claim: Amplitude amplification rotates a coherently prepared state in its good and bad two-dimensional span, using the preparation, its inverse and a success phase oracle.
strata_touched: []
license: citation-only
triage: anchor
---

# Task focus is success amplitude, rather than state purity

The primary preprint is https://arxiv.org/pdf/quant-ph/0005055, with the
rotation identity in equation (8) and the complexity conclusions in
Theorems 2–3. The published chapter is in *Quantum Computation and
Information*, Contemporary Mathematics 305, 53–74.

Let a supplied unitary preparation satisfy

$$
A|0\rangle=\sin\theta\,|G\rangle+\cos\theta\,|B\rangle,
\qquad \alpha=\sin^2\theta,
$$

where $G$ and $B$ are the normalized good and bad components for a supplied
success projector $\Pi$. With the reflection convention

$$
Q=(2A|0\rangle\langle0|A^\dagger-I)(I-2\Pi),
$$

the exact iterate is

$$
Q^kA|0\rangle
=\sin((2k+1)\theta)|G\rangle
 +\cos((2k+1)\theta)|B\rangle.
$$

This follows by multiplying the two reflection matrices in the indicated
basis. The entire algorithm can stay pure and in this two-dimensional
invariant space while requiring order $\alpha^{-1/2}$ iterations to obtain
constant success for small $\alpha$. Continued rotation can also decrease
success. A two-dimensional description and perfect coherence therefore
do not supply a polynomial runtime in the input length.

Each iterate uses $A$, $A^\dagger$, and the success phase operation; their
construction and execution costs belong to the runtime. Knowing or
appropriately estimating $\alpha$ controls the iteration count. The
unknown-success search result does not supply a polynomial all-input
halting bound when the success probability can vanish. Neither a classical
proposal distribution nor a conditional successful state alone supplies
the required coherent preparation and inverse.

For a formula with $m$ variables and $M>0$ satisfying assignments, uniform
preparation has $\alpha=M/2^m$. A complete assignment can be checked and
phase marked efficiently from the explicit formula, but the single-solution
amplification count is still order $2^{m/2}$. Marking precisely those
prefixes having some valid extension asks the separate NP-complete
prefix-completion question; it is not ordinary assignment verification.

The associated optimality lower bound for unstructured oracle search is
Christof Zalka, *Grover's quantum searching algorithm is optimal*,
https://arxiv.org/abs/quant-ph/9711070. Its oracle scope does not establish
a lower bound for algorithms exploiting an explicit SAT formula.
