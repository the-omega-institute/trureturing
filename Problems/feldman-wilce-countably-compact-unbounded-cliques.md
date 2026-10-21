---
slug: feldman-wilce-countably-compact-unbounded-cliques
bibkey: feldmanwilce2026compactnesscliques
doi: 10.48550/arXiv.2608.13320
url: https://arxiv.org/abs/2608.13320v1
triage: theorem
motivation_gids:
  - D5/S3/Topology/StoneCech/SectionClosedGraph.exists_countablyCompact_closed_fibreGraph
---

# Feldman–Wilce Question 1: finite, unbounded cliques

## Problem

David V. Feldman and Alexander Wilce, *A Note on Compactness and Clique Size*,
arXiv:2608.13320v1, Question 1, printed page 5:

> Is there a countably compact T1 (or Hausdorff) space with a closed
> orthogonality relation having finite but unbounded cliques?

An orthogonality relation is symmetric, irreflexive and closed in the entire
product, including the diagonal. A clique is a subset with every distinct
pair related. The requested relation must have every clique finite and no
natural number bounding all clique sizes.

## Motivation

The paper proves that compact spaces have the bounded clique property and
that, for T1 spaces, countable compactness is equivalent to every closed
orthogonality relation having only finite cliques. Q1 asks whether countable
compactness can fail the bounded clique property. Section 4
proposes a finite-block Stone–Čech construction but assumes the missing
countably compact selector.

The repository's actual section-good supplier, section-dense selector and
closed fibre graph chain construct that selector for arbitrary maps on a
countable source. The finite-block application has source
`Sigma (fun n : Nat => Fin (n+1))` and map `Sigma.fst`.

## Gap

The existing generic theorem supplies the actual selector, space and graph.
Its finite-block parameter discharge, inherited T2/T1 instances and explicit
negation of a uniform finite bound passed a canonical targeted Lean build
and scoped statement/axiom report. The axiom closure contains only
`Classical.choice`, `Quot.sound` and `propext`. The existing generic module
completed canonical FirstFreeze. The application retains all clauses of the
original question and assumes no selector or extra countable compactness
supplier. The owning Scribe retains the complete parameter correspondence
and derivation.

## Route

Each fibre over `b` is the finite range of `Sigma.mk b`; injectivity gives
`n+1` points in the `n`-th fibre. The countable finite-block source therefore
satisfies the only premises of
`SectionClosedGraph.exists_countablyCompact_closed_fibreGraph`.
The output is the principal extension of the internally constructed selector,
with the induced topology from the ultrafilter space. Its graph is an actual
`SimpleGraph`; its relation is closed in the whole product. A clique of size
`bound+1` refutes any proposed uniform finite bound.

## Falsifier

A hidden selector-existence premise, an extra set-theoretic hypothesis,
closedness restricted away from the diagonal, loss of Hausdorffness, a weaker
sequential assertion replacing countable compactness, or a bound on only a
selected family of cliques would invalidate the claimed correspondence.

## Evidence

The current arXiv record lists only v1 and its abstract still identifies this
existence problem as the main open problem. The authors' formal repository
`DavidVFeldman/compactness-clique-size`, main commit
`1f4da701cfb6d7588a90f005fa83698e3a1b081b`, marks `MainQuestion` open in its
README. Its `Witness.lean` proves
`mainQuestion_of_exists_countablyCompact_dense_subset_goodSet`, conditional
on a supplied free, section-good, section-dense and countably compact Y.
Neither primary surface supplies Y. This is a bounded primary-source check,
not a claim that all subsequent or unindexed work has been excluded.

## Triage

Tier 1 external named Question 1. The parameter application is bind-only and
reuses the existing generic theorem. Its definitions, hypotheses, parameter
correspondence and complete derivation are retained in that theorem's owning
Scribe; the exact Lean application is transient evidence. There is no new
D5 theorem requiring the external-resolution exception or a new Reg wrapper.
The mathematical mechanism lies in the existing arbitrary-map fresh-cluster
and closing-off chain. No CH or MA premise is present in the supplier theorem
signatures: the ordinal construction uses
omega1 and `aleph_one_le_continuum`, and the abundance argument uses Cantor's
theorem and free ultrafilters.

The construction makes the first horn of the paper's dichotomy hold:
the bounded clique property differs from countable compactness for T1 spaces.
The paper's remaining chromatic Questions 2 and 3 remain outside this target.
The broader arbitrary-map graph endpoint is already in the repository; this
application does not reissue it as a new general theorem.

The reused generic module reports `utility: none`: its statements concern
arbitrary topological and fibre data. The finite-block parameter discharge
quantifies over every natural block index and performs no bounded search,
finite-input certification, checker implementation or numerical reduction.

## ASSUMED-UNVERIFIED

The bounded literature check establishes the status of the inspected primary
sources. Worldwide absence, publication priority and acceptance by the
original authors are unverified. Lean source fidelity has a separate
human/model review boundary;
the kernel can certify only the formal statement and proof.
The application exposition does not claim a new mathematical declaration or
retroactive preregistration. Formal source fidelity remains separate from
compiled theorem identity and the machine resolution marker.
