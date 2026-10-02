---
bibkey: cohn1964squarefibonacci
authors: J. H. E. Cohn
year: 1964
title: "Square Fibonacci Numbers, Etc."
doi: null
url: https://www.fq.math.ca/Scanned/2-2/cohn2.pdf
claim: "Theorems 1 and 2 classify Lucas squares and twice squares at every natural index: the exceptional index sets are {1,3} and {0,6}."
strata_touched:
  - D5/S3/Arith/Primes/LucasSquareClassification
license: citation-only
triage: anchor
---

# Lucas square and twice-square classifications

J. H. E. Cohn, *Square Fibonacci Numbers, Etc.*, Fibonacci Quarterly
2(2) (1964), 109–113. The original primary paper gives the complete
Lucas square classification in Theorem 1 and the complete twice-square
classification in Theorem 2. The Lucas normalization is L_0 = 2,
L_1 = 1, L_(n+2) = L_(n+1) + L_n.

For every natural n, L_n is an integer square exactly for n = 1 or 3;
L_n equals twice an integer square exactly for n = 0 or 6. The four
exceptional values are 1, 4, 2 and 18, respectively.

The proof uses the signed Lucas trace identity, dyadic Lucas moduli
equal to three modulo four, and quadratic nonresidues detected by
Jacobi symbols. In the twice-square case, the modulus attached to
the residue minus thirty-six is coprime to three. The arithmetic
includes index zero explicitly.

The repository consumer is Theorem 52.1 of
`docs/develop/theory/GOLDEN_CUBIC_BLOCK_PRIME_PERIODS.md`; its formal
declaration is `lucas_square_classifications` in
`D5/S3/Arith/Primes/LucasSquareClassification.lean`. This is a
formalization of Cohn's classical result. The general Fibonacci and
Lucas square-class theorems additionally need product exclusions at
distinct indices, as proved in Ribenboim, *Square Classes of Fibonacci
and Lucas Numbers*, Portugaliae Mathematica 46 (1989), 159–175.

Only the bibliographic citation and a paraphrase of the mathematical
result are retained; the paper's PDF is an external source.
