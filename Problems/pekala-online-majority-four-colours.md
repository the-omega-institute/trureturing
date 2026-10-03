---
slug: pekala-online-majority-four-colours
bibkey: pekala2026onlinemajority
doi: null
url: https://arxiv.org/abs/2609.37973
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation
---

# Four colours in small online majority edge-colouring games

## Problem

Problem 11 of Pękała (2026) asks whether Algorithm can guarantee an online
majority edge-colouring with at most four colours for each of `n=5,6,7`
vertices when Presenter must finish with minimum degree **exactly** two.
Presenter chooses each next edge after seeing previous colours. Algorithm
must colour it immediately and cannot recolour old edges.

## Motivation

This is a named external finite-game question. Issue #11457 registered its
source, quantifiers and a bounded literature check before the proof probe.
The issue comment corrects an initial explanatory misreading of `delta=2`
as `delta>=2`. All subsequent calculations and the Lean terminal predicate
use equality.

## Gap

The source handles `n>=8` and observes that one particular greedy strategy
fails for `n=5`. Failure of that strategy does not show that every
four-colour Algorithm strategy fails. The bounded search described in the
preregistration found no earlier resolution of Problem 11; it is not a
global novelty claim.

## Route

The Presenter has a finite adaptive strategy on five vertices. A game state
records the colour of each of the ten possible edges, with zero meaning
unrevealed. At a Presenter node, every legal colour response leads to a
child node. Colour names are normalized by first appearance: the response
set consists of each previously used class and, if fewer than four classes
exist, one fresh class. Inductively maintain a bijection between used named
colours and classes `1,...,k`: a repeated named colour selects its old
class, while a previously unused named colour selects class `k+1` and
extends the bijection. Conversely each class choice has a representative
among the four named colours. Permuting colour names preserves all
frequencies, so this normalization loses no Algorithm response. The
certificate has 479 nodes and 352 distinct terminal
states. At every leaf the final simple graph has minimum degree exactly
two and some colour occupies more than half the incident edges at a vertex.

The same Presenter win extends to six and seven vertices. After a bad
five-vertex terminal state, choose a vertex `v` at which the majority
condition fails. There are at least two other old vertices `a,b`. For each
new vertex `x`, reveal the two edges `xa` and `xb`, and then stop. These
edges are distinct and avoid `v`, so its degree and offending colour
frequency are unchanged regardless of Algorithm's new colours. Every old
vertex still has degree at least two, and every new vertex has degree
exactly two. Thus the final graph again has minimum degree exactly two and
the colouring still violates majority. This adds two edges for `n=6` and
four for `n=7` after the adaptive five-vertex phase.

## Falsifier

A colour response missing from a strategy node, an illegal or repeated
presented edge, a leaf with minimum degree other than two, or a leaf
without a strict majority violation would invalidate the finite strategy.
The six- and seven-vertex extension would fail if an added edge met `v` or
if a new vertex did not end with degree two.

## Evidence

The Lean module defines the full finite games for `n=5,6,7` and refutes
their joint affirmative claim by a checked five-vertex strategy. Its
checker verifies every branch and terminal condition in the kernel. The
extension argument above establishes the stronger individual negative
answer for `n=6,7`; it is a separate combinatorial argument and is not
formalized in Lean. Source fidelity, repository admission, publication
and merge are separate gates until their receipts exist.

## Triage

`theorem`; resolution `refuted`; admission basis
`open-problem-resolution`; `proof_shape: content`, supplied by the adaptive
Presenter certificate. The source's joint positive question is false, and
the extension argument answers each listed order negatively.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish that no earlier solution
exists. The equivalence between named colours and normalized colour
classes, and the two-order extension, are explained above but do not have
standalone Lean bridge theorems.
