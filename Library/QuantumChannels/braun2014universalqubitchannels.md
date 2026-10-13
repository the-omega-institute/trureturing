---
bibkey: braun2014universalqubitchannels
authors: Daniel Braun, Olivier Giraud, Ion Nechita, Clément Pellegrini, Marko Žnidarič
year: 2014
title: A universal set of qubit quantum channels
doi: 10.1088/1751-8113/47/13/135302
url: https://arxiv.org/abs/1306.0495v2
claim: "Theorem IV.9 classifies pure output sets of qubit channels; three distinct pure outputs force unitary conjugation."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1088/1751-8113/47/13/135302

Source: https://arxiv.org/abs/1306.0495v2

Journal of Physics A: Mathematical and Theoretical **47**, 135302.
The arXiv DOI metadata and Crossref record agree on the DOI, title and authors.

## Pure-output rigidity

Theorem IV.9, arXiv v2 PDF pp. 21–22, states that the pure output set of a
qubit channel is empty, a singleton, a pair, or all pure qubit states. In the
last case the channel is unitary conjugation. Consequently three distinct
pure outputs force unitary conjugation, which sends every pure input to a
pure output.

## Covariant pure programs

Fixing a normalized basis input of a processor with a qubit program register
and qubit output gives a qubit channel from programs to outputs. The two basis
replacement targets and their equal-superposition target are three distinct
pure outputs. The classification forces unitary conjugation, so no pure
program can produce the fourth replacement target $\mathbb1/2$.
This is the literature ingredient applied to the GBW-5 pure-program question.
`PureProgramQubitObstruction.no_four_replacements` proves the selected-target
Gram-matrix obstruction even without program normalization. The classification
itself is cited literature; the delivered theorem does not formalize its full
classification statement.
