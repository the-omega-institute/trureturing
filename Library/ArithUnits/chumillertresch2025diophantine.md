---
bibkey: chumillertresch2025diophantine
authors: Hùng Việt Chu, Steven J. Miller, and Garrett Tresch
year: 2025
title: Problems Regarding a Pair of Diophantine Equations
doi: 10.48550/arXiv.2512.12681
url: https://arxiv.org/abs/2512.12681v1
claim: Section 3.4 asks whether every prescribed split of Gamma labels can be realized by a strictly increasing sequence with polynomial growth.
strata_touched:
  - D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth
license: citation-only
triage: anchor
---

# Gamma-label splits with slower growth

## Verified locator

DOI: 10.48550/arXiv.2512.12681

Source: https://arxiv.org/abs/2512.12681v1

## Source statements

Section 1, pp. 2–3: “Γ : ℕ² → {0, 1} … where Γ(a, b) = 0 if (a/gcd(a, b)) x + (b/gcd(a, b)) y = (a/gcd(a, b) − 1)(b/gcd(a, b) − 1)/2 has the nonnegative integral solution, and Γ(a, b) = 1 if 1 + (a/gcd(a, b)) x + (b/gcd(a, b)) y = (a/gcd(a, b) − 1)(b/gcd(a, b) − 1)/2 has the nonnegative integral solution.”

Corollary 2.6, p. 5, counts “#{n ≤ N : Γ(a_{n−1}, a_n) = 0}” for a sequence indexed from zero. The first counted edge has n = 1.

Section 3.4, p. 11: “As noted in Remark 2.7, the sequence grows exponentially fast (faster than the Fibonacci sequence). Is there a construction involving a strictly increasing sequence that grows slower than the Fibonacci sequence, or perhaps even like n^k for some k?”

## Mathematical scope

Gamma is encoded by the displayed gcd-reduced equation over natural numbers, returning 0 when it has a nonnegative integral solution and 1 otherwise. Natural division is integer division. Theorem 1.1 identifies the complementary branch with the second equation for positive inputs. The prefix count uses the inclusive interval from 1 to N, and the density ratio is real.

The repository's affirmative answer constructs two five-edge chains with opposite constant labels, period 40, and shared endpoints. Floor increments select the chains to realize every real p in [0,1]. The private estimates give 8n − 9 ≤ a_n ≤ 8n + 15 and counting discrepancy less than 5. The public claim states positivity, strict increase, a polynomial upper bound, and the prescribed limiting density; its proof chooses exponent 1 and coefficient 23. It does not state an optimal coefficient or settle the source's separate periodicity questions.

## Experiment and literature boundary

The experiment is in the-omega-institute/trureturing-experiments at commit 9d52d7d7ebb6eed0c13bf1b8bc7d1f641749fe8c, file docs/reports/chu-miller-tresch-2025-gamma-split-linear-growth/check.py, SHA-256 24b339e97002aa8c949f24d89790783e7064abf00c18d54925a1c6112b577ddd, recorded exit 0 in issue #20691. It checks the source examples, the ten polynomial certificates, and finite scheduled sequences; these computations are separate from the Lean proof.

The literature screen recorded at https://github.com/the-omega-institute/trureturing/issues/20691 includes arXiv:2309.04488v2, arXiv:2509.01781v2, and arXiv:2609.08728v1. Exhaustiveness is ASSUMED-UNVERIFIED; no global originality claim is made.
