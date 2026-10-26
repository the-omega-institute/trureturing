---
slug: bhargava-2026-facemagic-module
bibkey: bhargava2026facemagic
doi: null
url: https://arxiv.org/html/2609.26762v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure
---

# All-ring coordinates for unrestricted face-magic hypercubes

## Problem

Manjul Bhargava's arXiv:2609.26762v1, [Section 6.2](https://arxiv.org/html/2609.26762v1#S6.SS2) asks: **What is the structure of the R-module U_n(R) of face magic hypercubes of dimension n over R when the characteristic is even and positive?** The source concerns unrestricted entries and one common sum on every two-coordinate face. The source question is recorded in [preregistration #19560](https://github.com/the-omega-institute/trureturing/issues/19560).

## Motivation

The theorem `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure` identifies the actual module over every unital ring, including noncommutative rings, zero divisors and the zero ring. It keeps the full cube, every dimension, and an existential common face constant in the carrier, rather than adjoining that constant as stored data.

## Gap

The source's Section 2 coordinates have determinant two, so that coordinate change does not identify the module when two is not invertible. The question asks for the unrestricted module itself in even positive characteristic. Integral coordinates remove that obstruction without imposing any characteristic or commutativity hypothesis.

## Route

For coordinates a, b_i and C, define the array on S by (-1)^k ((1-k)a − Σ_(i∈S)b_i + floor(k/2)C), where k = |S|, the floor is natural-number division, and the coefficients act additively as integers. A parity calculation proves that every face has sum C. Removing two elements and strong induction determine every array from the empty value, singleton values, and, for n ≥ 2, the fixed {0,1}-face. The evaluation and reconstruction maps are inverse R-linear maps. Dimensions zero and one have no two-coordinate faces and are handled separately. The face recurrence and induction method are inherited from Bhargava Section 2, equations (4), (8), (9) and Theorem 13; the integral coordinate choice avoids division by two.

## Falsifier

A counterexample would be a unital ring, dimension, or unrestricted face-magic array violating the displayed reconstruction or either inverse law. A source-reading falsifier would be that the cited question has a different quantifier scope or requires a prescribed set of entries.

## Evidence

**Proved:** `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure` gives R-linear equivalences U_0(R) ≃ R, U_1(R) ≃ R × R, and U_n(R) ≃ R × (Fin n → R) × R for every n ≥ 2 and every unital ring R. Its statement identity is `sha256:e3c0d656554e2493c82ce98f65769c20230de41e476f1d163d5a281e4692cafd`; the compiled module has only the standard axiom closure `propext`, `Classical.choice`, and `Quot.sound`. The reconstruction and uniqueness arguments are contained in its consumed helpers.

The mathematical formulas mirror this exact result and its actual array carrier. The four-slot Reg audit of the public settling theorem is **unfinished**, with its concrete missing evidence described in [audit issue #19602](https://github.com/the-omega-institute/trureturing/issues/19602). That audit issue is distinct from the source-question preregistration #19560 and does not assert completed registration.

## Triage

### What the settlement shows

**Proved** by `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure`: the unrestricted module question has the displayed all-ring answer. For n ≥ 2 the empty entry, all singleton entries and the common face sum are independent coordinates. The decisive mechanism is an integral reconstruction whose parity second difference supplies the face identity, together with cardinality induction for uniqueness. Central integer coefficients preserve linearity even over noncommutative rings, so the answer includes every characteristic and needs no inverse of two.

**Formula-supported explanation:** replacing determinant-two coordinates by these integral coordinates accounts for the absence of a characteristic obstruction in the unrestricted module. This classification does not alter the source's prescribed-entry hypotheses. Prescribed-entry existence, symmetry-orbit classification and collision or distinctness questions are **not addressed** by this theorem; no additional result or global openness claim about them is asserted.

## ASSUMED-UNVERIFIED

The source scope and method refer to arXiv:2609.26762v1. The supplied literature screen is bounded; exhaustive current literature coverage, global priority and independent publication are not established. The public theorem's four-slot Reg audit remains unfinished as specified in [#19602](https://github.com/the-omega-institute/trureturing/issues/19602).
