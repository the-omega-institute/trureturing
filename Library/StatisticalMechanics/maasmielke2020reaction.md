---
bibkey: maasmielke2020reaction
authors: Jan Maas and Alexander Mielke
year: 2020
title: Modeling of chemical reaction systems with detailed balance using gradient structures
doi: null
url: https://arxiv.org/pdf/2004.02831v1
claim: "A mass-action reaction-rate equation with positive detailed-balanced reference concentration has a relative-entropy gradient structure with logarithmic-mean mobility."
strata_touched: []
license: citation-only
triage: anchor
---

# Reaction entropy and the level of the state

The cited version is arXiv:2004.02831v1. Section 1 and Section 2.1
distinguish concentration-valued reaction-rate equations from the chemical
master equation on particle counts. Section 2.3, printed pp. 8–9,
equations (2.9)–(2.12) and Theorem 2.2, states the entropy gradient
structure under detailed balance at a positive reference concentration.
Its logarithmic mean is $(a-b)/(\log a-\log b)$, continued as $a$ at $a=b$.
The authors attribute antecedents of this gradient structure to Yong and
Mielke; no historical priority beyond the cited statement is asserted.

The consumer is [Static §23, Assumption 23.3 and Theorem 23.4](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md).
The reaction $1+3\rightleftarrows0+13$ supplies a particular normalized
vector field. The theorem separately constructs its law-dependent
single-state directed-cycle realization. Reaction detailed balance and
edge detailed balance of that realization have different conditions;
the reaction theorem does not assert the latter. The five-state embedding,
bounded polynomial rates and nonuniform Gibbs example are the consumer's
application, not statements quoted from this paper.
