---
bibkey: lovas2016volume
authors: Attila Lovas, Attila Andai
year: 2016
title: Volume of the space of qubit channels and some new results about the distribution of the quantum Dobrushin coefficient
doi: 10.48550/arXiv.1607.01215
url: https://arxiv.org/abs/1607.01215
claim: The paper computes volumes of spaces of qubit channels, shows that the trace-distance contraction coefficient takes every value strictly between |a - f| and a stated upper value over the qubit channels above a fixed classical channel, and conjectures that its infimum there is |a - f|.
strata_touched:
  - D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum
license: citation-only
triage: anchor
---

# Volume of the space of qubit channels and the quantum Dobrushin coefficient

Lovas and Andai represent a qubit channel `Q : M_2 → M_2`, a completely
positive trace-preserving map, by its Choi block matrix: the action of `Q` is
`(a b; c d) ↦ a Q_11 + b Q_12 + c Q_21 + d Q_22`, and the underlying classical
channel is `P = (dg(Q_11); dg(Q_22))`. The general element is parametrized as

> Q = ((a, b, c, d), (b̄, 1−a, e, −c), (c̄, ē, f, g), (d̄, −c̄, ḡ, 1−f)),

with `a, f ∈ [0,1]` (eq:matQ). For a CPT map the trace-distance contraction
coefficient is

> η^Tr(Q) = sup { Tr|Q(ρ) − Q(σ)| / Tr|ρ − σ| : ρ, σ ∈ M_2 },

and the paper computes it as the largest singular value of the Bloch matrix
`T` (eq:matT), whose lower-right entry is `a − f`. The set of qubit channels
over the classical channel `((1−a, a), (1−f, f))` with respect to the
parametrization (eq:matQ) is denoted `Q_C(a,f)`. The theorem of the section on
the distribution of `η^Tr` over classical channels gives, for all
`x ∈ (|a−f|, √((1−a)f) + √(a(1−f)))`, a channel `Q ∈ Q_R(a,f) ⊂ Q_C(a,f)` with
`η^Tr(Q) = x`, and the section states

> We conjecture that inf{η(Q) : Q ∈ Q_C(a,f)} = |a−f| which is equal to the
> trace-distance contraction coefficient of the underlying classical channel.

The paper writes channel positivity as `Q > 0`; Choi's theorem characterizes
complete positivity by a positive semidefinite Choi matrix, and this reading
is used for `Q_C(a,f)`. By (eq:matT), the member of the theorem's family with
`d = e = 0`, whose Choi matrix is `diag(a, 1−a, f, 1−f)`, has `η^Tr = |a − f|`;
the theorem is stated for the open interval only.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1607.01215
- URL: https://arxiv.org/abs/1607.01215
- Version and location: arXiv:1607.01215 [math-ph, quant-ph] (2016-07-05), source file `volume04.tex`: the definition of `η^Tr` in the preliminaries, the parametrization (eq:matQ) and the Bloch matrix (eq:matT) in the section on the volume of qubit channels, and the theorem and conjecture (`\label{conj}`) of the subsection on the distribution of `η^Tr` over classical channels.
