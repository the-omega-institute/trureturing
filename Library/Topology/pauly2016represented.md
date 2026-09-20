---
bibkey: pauly2016represented
authors: Arno Pauly
year: 2016
title: 'On the topological aspects of the theory of represented spaces'
doi: 10.3233/COM-150049
url: https://arxiv.org/abs/1204.3763
claim: Sierpinski-valued observations organize open sets and semidecidability in represented spaces; effective content requires a specified representation.
strata_touched:
  - D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel
license: citation-only
triage: anchor
---

# Open observations and represented spaces

Pauly, *Computability* 5(2), 159–180 (2016). The publisher lists online
publication in December 2015 and the journal issue in 2016. The canonical
bibliographic year used here is the journal issue year.

## Verified scope

The author manuscript arXiv:1204.3763v3, Section 4, identifies open sets through
continuous Sierpinski-valued maps. Proposition 5 gives the computability of
binary conjunction and disjunction and countable disjunction; its following
remark distinguishes negation and countable conjunction. The manuscript's
Section 3 also warns that continuity of represented-space realizers and plain
topological continuity must not be identified without the relevant conditions.

The Sierpinski convention in the cited Section 4 is positive evidence: top is
recognized by a nonzero entry in a name. No claim is made that every abstract
open subset is computable without an effective representation and index.

## Repository use and limits

The existing Lean theorem `partition_inseparable_iff_kernel` is about a readout
into a **discrete** codomain. Its proof and declaration are unchanged. The
existing Scribe document links this note as context and as a scope restriction,
not as a new Lean theorem or a new axiom.

The computational-behavior theory volume, Sections 51–55, distinguishes the
product observation topology on infinite bit sequences from the discrete
whole-sequence readout. Those spaces have the same pairwise inseparability
kernel but different open tests. Its later sensor construction and finite-noise
bounds are independently proved in the theory volume and are not attributed to
Pauly.

## Retrieval record

On 2026-09-20 the publisher bibliographic page and the author's Swansea record
were checked. The author PDF was read, and PDF page 5 (zero-based index 4),
containing Section 4 and Proposition 5, was inspected as an image. Repository
search for the DOI returned no pre-existing note. This is an original
citation-only summary; no publisher PDF or copyrighted article text is copied
into the repository.
