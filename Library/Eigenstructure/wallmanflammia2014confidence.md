---
bibkey: wallmanflammia2014confidence
authors: Joel J. Wallman; Steven T. Flammia
year: 2014
title: Randomized Benchmarking with Confidence
doi: 10.1088/1367-2630/16/10/103032
url: https://arxiv.org/abs/1404.6025v4
claim: "Section VII defines n-contractivity by the peripheral spectrum of a tensor-power channel twirl and conjectures unrestricted 2-contractivity for nonunitary channels."
strata_touched:
  - D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity
license: citation-only
triage: anchor
---

# Randomized Benchmarking with Confidence

## Verified locator

DOI: 10.1088/1367-2630/16/10/103032

Source: https://arxiv.org/abs/1404.6025v4

The source is arXiv version 4. The publisher text has not been compared with
this version.

## Statement

Definition 15, PDF page 23:

> A channel $\Lambda:\mathcal D_d \to \mathcal D_d$ is *$n$-contractive*
> with respect to a group $\mathcal G\subseteq \mathcal U(d)$ if
> $(\Lambda^{\otimes n})^{\mathcal G}$ has at most one eigenvalue of modulus 1.

The unnumbered conjecture before Proposition 16, PDF page 24:

> We conjecture that *all* nonunitary channels are in fact $2$-contractive
> with respect to any unitary 2-design.

The finite-group scope is fixed in Section II. The channel is completely
positive and trace preserving. Nonunitary means that it does not act by
conjugation with a unitary matrix on every input matrix. Characteristic-polynomial
roots retain algebraic multiplicity. The finite exact-design statement covers
every dimension at least two; it assumes no unitality or small-noise bound.

## Boundaries

Proposition 16 proves the unital case. The repository result addresses the
remaining nonunital case in the finite exact-design setting. Literature
completeness and agreement between the journal and arXiv wording are
ASSUMED-UNVERIFIED. Approximate designs, compact infinite designs,
gate-dependent noise and tensor powers at least three are outside the statement.
