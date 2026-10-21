---
bibkey: bittel2021training
authors: Lennart Bittel and Martin Kliesch
year: 2021
title: Training variational quantum algorithms is NP-hard
doi: 10.1103/PhysRevLett.127.120502
url: https://arxiv.org/abs/2101.07267
claim: Classical global optimization of specified variational quantum models is NP-hard, including restricted and efficiently classically simulable families; the result distinguishes evaluation from training.
strata_touched: []
license: citation-only
triage: anchor
---

# Training variational quantum algorithms is NP-hard

## Primary source and locators

Physical Review Letters 127, 120502 (2021); author preprint arXiv:2101.07267.
The preprint's Problem 2 and Lemma 1 give a continuous MaxCut optimization interface.
Problem 4 and Theorem 1 transfer hardness to VQA optimization; Theorem 2 gives a single-layer version.
The abstract also explicitly includes classically tractable systems of logarithmically many qubits or free fermions.
These results concern global optimization under the paper's encoded input and accuracy conventions.
They do not assert that every variational model, every individual instance or local state evaluation is hard.

## Native FIB application

[Native Capacity, Coherence and Growth §22](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md)
provides the specific correspondence for a zero-separated legal FIB code:
independently addressed odd-site pulses realize logical product states;
a succinct list of diagonal clause projectors gives expected violated-clause count.
The minimum is attained at a Boolean corner and equals the minimum number of violated clauses.
This is a standard diagonal-cost reduction specialized to the native menu, not a new general hardness theorem.

The unnormalized satisfiable/unsatisfiable gap is one. Dividing by the clause count $M$ divides the gap by $M$.
A value approximation with fixed guaranteed error below $1/2$ for the unnormalized objective would decide SAT;
this contract is distinct from a fixed error for an objective normalized to $[0,1]$.
The value, angle descriptions, precision and readout costs must use finite effective encodings.
The reduction neither proves $\mathrm P\ne\mathrm{NP}$ nor rules out efficient special task families.
