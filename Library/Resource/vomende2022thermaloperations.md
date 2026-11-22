---
bibkey: vomende2022thermaloperations
authors: Frederik vom Ende
year: 2022
title: "Which bath Hamiltonians matter for thermal operations?"
doi: 10.1063/5.0117534
url: https://arxiv.org/abs/2207.11189v4
claim: "Proposition 4(iv) characterizes the closure of finite thermal operations using resonant bath spectra. Section V asks whether the thermal operation definition can restrict bath energy-level degeneracy to the dimension of the system."
strata_touched:
  - D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation
license: citation-only
triage: anchor
---

# Bath Hamiltonians and energy-level degeneracy in thermal operations

## Verified locator

Equation (1) in Section II defines finite-bath thermal operations. Proposition 4(iv) gives the reduction to resonant bath spectra for the closure. The second question in Section V, printed page 20 of arXiv v4, asks for a bound on the bath energy-level degeneracy and proposes the system dimension. [arXiv v4](https://arxiv.org/abs/2207.11189v4) · [J. Math. Phys. 63, 112202](https://doi.org/10.1063/5.0117534)

## Scope and derivation

Equation (1) defines the operation by adjoining a finite Gibbs bath, applying a unitary commuting with total energy, and tracing out the bath. In the bath eigenbasis, energy multiplicities are the dimensions of the eigenspaces. Conjugating the joint unitary by the corresponding bath basis change preserves commutation, the Gibbs preparation and the partial trace. Proposition 4(iv) establishes resonant spectra as sufficient to generate the closure. Corollaries 5 and 6 describe related reductions for commensurate system energies. These results allow the dimensions of the bath energy eigenspaces to vary.

The second open question in Section V reads “Can one specify an upper bound for how degenerate the energy levels of the bath need to be?” It then conjectures that “the definition of TO can be restricted to such (resonant) bath Hamiltonians which have degeneracy at most dimension of the system.” [Source, arXiv v4](https://arxiv.org/html/2207.11189v4#S5)

The qutrit with energies 0, 1 and 2 at inverse temperature log 2 gives a separation. A resonant bath with six levels and multiplicities (1, 1, 2, 3, 5, 8) admits an energy-conserving permutation for which the ground population on input (0, 2/3, 1/3) is 124/141. Any finite bath with energy-level degeneracy at most three and any exactly energy-conserving unitary give ground population at most 28/33 on that input. The upper bound includes arbitrary real bath spectra and arbitrary finite spectral width.

Ding, Ding and Hu give the decomposition by energy residues for equally spaced systems in Lemma 1 of their 2021 paper. Scharlau and Müller use finite energy ladders with energy-conserving permutations for qubits. The qutrit bound uses the two predecessor occupancies in each shell and a finite potential whose Gibbs-weighted sum cancels under an energy translation. [Ding–Ding–Hu](https://arxiv.org/html/2101.05690v2) · [Scharlau–Müller](https://doi.org/10.22331/q-2018-02-22-54)

Musat and Rørdam’s earlier quantitative factorization theorem also implies a higher-dimensional obstruction. For their size-11 Schur channel with parameter t = 31/65, Proposition 2.3 and Example 3.5 force five projections to sum to 31/13 times the identity in a factoring ancillary algebra with faithful trace. Taking the trace in a nonzero representation of finite dimension shows that its dimension is a multiple of 13. A faithful thermal implementation of that channel induces such a factorization over the bath eigenspaces because the channel fixes each system basis projection. The three-level result here separates population transfer on a single fixed diagonal input. [Musat–Rørdam](https://arxiv.org/html/1806.10242#S4)
