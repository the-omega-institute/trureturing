---
bibkey: nayaksen2007invertible
authors: Ashwin Nayak and Pranab Sen
year: 2007
title: Invertible Quantum Operations and Perfect Encryption of Quantum States
doi: 10.26421/QIC7.1-2-6
claim: A finite CPTP map with a CPTP left inverse has a unitary/isometric fixed-ancilla normal form.
strata_touched:
  - D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding
license: citation-only
triage: anchor
---

# Reversible finite quantum channels

Theorem 2.1 and its proof in arXiv:quant-ph/0605041 characterize a channel admitting a completely positive trace-preserving left inverse. The proof uses scalar Kraus products and diagonalizes their Gram matrix to produce orthogonal error copies and a fixed ancillary density state. This is prior literature for the recovery normal form used here. It does not state the parameter-bundle divisibility corollary or the explicit matrix-unit transport generator in the current manuscript.

Source: https://arxiv.org/abs/quant-ph/0605041
Publisher record: https://www.rintonpress.com/journals/doi/QIC7.1-2-6.html

The candidate Lean module proves a finite matrix decoding identity for supplied orthogonal copies; it does not formalize the entire channel classification theorem or its smooth global extension.
