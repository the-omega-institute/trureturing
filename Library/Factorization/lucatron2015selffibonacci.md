---
bibkey: lucatron2015selffibonacci
authors: "Florian Luca; Emanuele Tron"
year: 2015
title: "The Distribution of Self-Fibonacci Divisors"
doi: 10.1007/978-1-4939-3201-6_6
url: https://arxiv.org/abs/1410.2489v2
claim: "Theorem 2.2 uses strict descent of prime factors of Fibonacci entry points, and Section 4 explicitly describes Pratt-Fibonacci trees built from factors of z(p)."
strata_touched: []
license: citation-only
triage: anchor
---

# Fibonacci rank descent and Pratt-Fibonacci trees

The primary text is [arXiv:1410.2489v2](https://arxiv.org/pdf/1410.2489v2).
The published chapter is in *Advances in the Theory of Numbers*,
Fields Institute Communications 77, pages 149–158,
[DOI](https://doi.org/10.1007/978-1-4939-3201-6_6).
The locators below use the eight-page arXiv version.

For the standard Fibonacci sequence, write
\(z(n)=\min\{j\ge1:n\mid F_j\}\).
The proof of Theorem 2.2 on page 4 uses the fact that, for a prime
\(P\ge7\), every prime factor of \(z(P)\) is strictly smaller than \(P\).
It applies this descent, together with prime-power valuation information,
to iteration of \(z\) on integers.

Section 4, pages 7–8, explicitly calls the corresponding objects
“Pratt-Fibonacci trees”: the factors of \(z(p)\), with their exponents,
appear as children of a node \(p^\delta\).
Thus the prime-factor dependency construction and the descent mechanism
are literature-attested; renaming them does not give a new construction.

[Observer and Arithmetic Relations §24](../../docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#24-吸收秩父图的定量世代)
identifies nodes with the same prime value, absorbs \(2,3,5\), and bounds
the resulting directed-acyclic-graph height by \(\lfloor\log_2(p-1)\rfloor\).
Its height argument is supplied in that theory entry. The cited paper
is the source for the dependency relation and descent, not a citation for
that exact height statement or a Lean verification of the consumer.

Lemma 3.1 on page 6 quotes Gordon–Pomerance's uniform estimate for
integers with a prescribed rank. Its \(x^{1-o(1)}\) scale and its integer
counting domain do not supply the fixed-support prime count in §26 of
the observer volume.

## Verified locator

- DOI: https://doi.org/10.1007/978-1-4939-3201-6_6
- URL: https://arxiv.org/abs/1410.2489v2
- Version and location: arXiv:1410.2489v2, revised 20 February 2015; the arXiv record lists the
  DOI above as the related publication.
