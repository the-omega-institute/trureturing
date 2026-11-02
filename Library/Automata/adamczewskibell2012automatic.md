---
bibkey: adamczewskibell2012automatic
authors: Boris Adamczewski and Jason P. Bell
year: 2012
title: "On vanishing coefficients of algebraic power series over fields of positive characteristic"
doi: null
url: https://arxiv.org/abs/1205.4091v1
claim: "Section 5.1, Definition 5.1 and Theorem 5.1 record Eilenberg's characterization of automatic sequences by finite arithmetic kernels."
strata_touched:
  - D5/S0/Automata/FiniteKernelDFAO
license: "arXiv distribution; cited mathematical statements, no copied prose or figures"
triage: anchor
---

# Eilenberg's finite-kernel characterization

## Verified locator

https://arxiv.org/abs/1205.4091v1

The inspected v1 PDF, Section 5.1, Definition 5.1 defines the arithmetic
kernel by the subsequences with indices `k^e n+r`, where `e ≥ 0` and
`0 ≤ r < k^e`. Theorem 5.1 attributes the equivalence of automaticity and
finite kernel to Eilenberg. This is the mathematical attribution of
`FiniteKernelDFAO.isKAutomatic_iff_isKAutomaticSequence`; the Lean proof
is the original ATLAS construction documented in `atlas2026finitekernel`.

## Representation convention

The ATLAS predicate used by the integration fixes a finite output alphabet,
a positive finite state count, natural indices including zero, and correctness
on every least-significant-digit-first representation. Its
`CobhamUniformMorphism.lean` source cites Zoran Sunic, *Rational Tree Morphisms and Transducer
Integer Sequences: Definition and Examples*, JIS 10 (2007), Definition 3
and the LSDF/zero-padding convention in the author's `cubefree.tex`:
https://cs.uwaterloo.ca/journals/JIS/VOL10/Sunic/cubefree.tex.
The formal predicate itself specifies the precise representation scope;
the cited finite-kernel characterization supplies mathematical provenance,
not an additional claim about canonical-only words or a zero state loop.
This integration makes no mathematical novelty or new-proof claim.
