---
bibkey: hervakari2023forced
authors: Pyry Herva, Jarkko Kari
year: 2023
title: On forced periodicity of perfect colorings
doi: null
url: https://arxiv.org/html/2301.05232v1
claim: "Section 3, Theorem 2: a finitary integral planar configuration with a complex Laurent periodizer is two-periodic if the periodizer has no line polynomial factors, and periodic in the common primitive direction if all its line factors have that direction."
strata_touched:
  - D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality
  - D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry
  - D5/S1/Dynamics/Symbolic/KhetanSixCellPeriodicity
license: citation-only
triage: anchor
---

# General integral periodizers with at most one line direction

## Verified locator

https://arxiv.org/html/2301.05232v1

Section 3, Theorem 2, and the definitions of configuration, periodizer and
line polynomial preceding it. The theorem is attributed there to reference
[18]: Jarkko Kari and Michal Szabados, *An algebraic geometric approach to
Nivat's conjecture*, Information and Computation **271**, 104481 (2020).
No DOI is asserted here.

## Reused mathematical statement

A configuration in this paper is finitary: its coefficients take finitely
many values. Theorem 2 applies to an integral configuration
$c\in\mathbb Z[[x^{\pm1},y^{\pm1}]]$ and a complex Laurent periodizer
$f$. A periodizer means that $fc$ is two-periodic, with two linearly
independent lattice periods. In the nontrivial applications $f\ne0$.

If $f$ has no line polynomial factors, $c$ itself is two-periodic. If all
line polynomial factors of $f$ have the same primitive direction, $c$
itself is periodic in that direction: some nonzero integer multiple of
that primitive vector is a period. The statement concerns the original
configuration, not just a replacement or a point in its orbit closure.
It imposes no low-complexity, perfect-coloring or small-alphabet-cardinality
hypothesis beyond finitariness and integrality. The restricted
low-complexity results elsewhere in the paper must not be substituted for
this theorem.

The first proof sketch uses the principal periodizer ideal and its product
of line polynomials in distinct directions; the second uses resultants.
The attribution to Kari–Szabados is part of the literature provenance,
not a claim that the general periodizer theorem originates in this project.

## Correspondence with the formal sources

The one-direction consumer is
`D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality.lean`, specifically
`integer_one_direction_periodizer_periodic`, with its matching Blueprint
Scribe. The exact-cover mask periodizes the given integral zero-one
indicator because its action is the constant one configuration.
The intended complete consumer is `KhetanSixCellPeriodicity.lean`.
These references identify the mathematical supplier and intended use;
they do not certify completion of the whole imported formal proof.

`Blueprint/D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry.scribe.cs`
identifies this as the other branch of the six-cell argument. The geometry's
two-direction theorem instead uses actual fiber cancellation and the
general incidence proof in `KhetanSectionCancellation.lean`. The software
attribution for the reused product-difference and finite-state suppliers
remains in [ho2026nivat.md](ho2026nivat.md).
