---
bibkey: browncameron2020imaginary
authors: J. I. Brown and Ben Cameron
year: 2020
title: A note on purely imaginary independence roots
doi: 10.1016/j.disc.2020.112113
url: https://arxiv.org/abs/2001.08881v2
claim: Question 2 on printed page 11 asks whether a graph has a purely imaginary independence root bi with irrational real b.
strata_touched:
  - D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot
license: citation-only
triage: anchor
---

# Purely imaginary independence roots

The source is arXiv:2001.08881v2, Question 2, printed page 11:

> Are there graphs with purely imaginary independence roots at bi where b is irrational?

The independence polynomial counts actual independent vertex subsets by cardinality,
including the empty subset. The question imposes no graph order, connectivity,
independence-number or modulus restriction. The separate discussion of square roots
of rationals greater than one does not add a hypothesis to Question 2.

The repository construction uses 128 vertices and b = 1/sqrt(2). Its native
independent-subset polynomial is (1+2X²)(1+128X+128X²), so evaluation at i*b
vanishes exactly. The construction and proof are repository work; the cited authors
pose the question. This note makes no minimum-order, priority or exhaustive
literature claim. Only the short question is quoted; no source implementation or
proof is copied.
