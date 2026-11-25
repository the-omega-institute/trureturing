---
slug: garber-et-al-2026-tamari-boolean-antichains
bibkey: garber2026booleanantichains
doi: 10.48550/arXiv.2608.27126
url: https://arxiv.org/html/2608.27126v2#S6.Thmtheorem2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.result
---

# The order of maximum Boolean antichains in the Tamari lattice

## Problem

Julien Garber, Lina S. Goltermann, Daniel Horiatakis, Dennis König and Tal
Gottesman, *Counting Boolean antichains* (2026), arXiv:2608.27126v2, §6,
Question 6.2, p. 22, first sentence.

> Is the order on Boolean antichains of maximal size in the Tamari lattice
> equivalent to the Tamari order, the order on non-crossing partitions, or
> the order on Dyck paths?

For each integer \(n\ge 1\), let \(T_m\) be the set of full binary
parenthesizations of \(m+1\) ordered letters, ordered by sequences of
contextual right rotations \(((XY)Z)\to (X(YZ))\). A Boolean antichain
\(C\subseteq T_{n+1}\) is pairwise incomparable, excludes top, and has
\((\bigwedge S)\vee(\bigwedge S')=\bigwedge(S\cap S')\) for every
\(S,S'\subseteq C\), with empty meet top. Order the families of maximum
cardinality by inclusion of their generated lower sets.
[Published question](https://arxiv.org/html/2608.27126v2#S6.Thmtheorem2).

## Motivation

The source identifies and counts valid maximum families. The order
identification connects their comparison by generated lower sets with the
rotations of smaller trees and distinguishes the alternate Catalan orders.

## Gap

The source enumeration leaves the induced order open. The bounded literature
screen in the prospective tier-1 preregistration reports no exact prior
settlement. [Issue #33263](https://github.com/the-omega-institute/trureturing/issues/33263).

## Route

A proper fixed coordinate bounds the number of Boolean rows and forces one
interval per right endpoint at equality. The Boolean law then characterizes
laminar intervals. Inclusion of the generated lower sets is exactly
pointwise order on the left endpoints. Reflection and tree mirroring both
reverse order, so their composition produces the rotation order on \(T_n\).
The comparison orders separate by atom counts for noncrossing refinement
and by coatoms for Dyck height dominance. The remaining ranks give a
singleton and a two-element chain.

## Falsifier

A failure of the Boolean-law characterization, either direction of the
contextual rotation bridge or either comparison boundary would defeat the
corresponding claim under the stated conventions.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.result`. It proves that
for every \(n\ge1\) the maximum cardinality is \(n\) and the maximum families
are order-isomorphic to \(T_n\). The noncrossing partitions of \([n]\) under
refinement and the Dyck paths of semilength \(n\) under pointwise prefix
height are each order-isomorphic to these families if and only if
\(n\le 2\). Dyck paths of semilength \(n\) with the transported Tamari order
are order-isomorphic for every \(n\ge 1\).

## Triage

The order comparisons and the maximum are proved for the registered Tamari
family. The two negative comparisons hold uniformly for every \(n\ge 3\).
The question's second sentence about arbitrary lattices remains open in
this dossier.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish global priority. MathDB
denied direct access, and some citing-paper search requests were rate-limited.
