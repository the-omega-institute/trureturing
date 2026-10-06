# Automatic Apwenian Sequences with One Odd Letter

## Abstract

Apwenian sequences, period doubling and uniform substitutions define the classification over finite alphabets with one odd letter.

**Definition 1.1 (The apwenian property).**

Lean statement: `D5/S3/Combinatorics/Apwenian/GuoHanDefs.IsApwenian`

*Formalization.* `D5/S3/Combinatorics/Apwenian/GuoHanDefs.IsApwenian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ying-Jun Guo, Guo-Niu Han (2025). *On a family of automatic apwenian sequences*. DOI: [10.1016/j.disc.2025.114399](https://doi.org/10.1016/j.disc.2025.114399). URL: <https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf>.

*Commentary.*

A sequence a of nonnegative integers is apwenian when a(0) = 1 and, for every nonnegative integer n, a(n) is congruent to a(2n + 1) + a(2n + 2) modulo two.

**Definition 1.2 (The period-doubling sequence).**

Lean statement: `D5/S3/Combinatorics/Apwenian/GuoHanDefs.periodDoubling`

*Formalization.* `D5/S3/Combinatorics/Apwenian/GuoHanDefs.periodDoubling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ying-Jun Guo, Guo-Niu Han (2025). *On a family of automatic apwenian sequences*. DOI: [10.1016/j.disc.2025.114399](https://doi.org/10.1016/j.disc.2025.114399). URL: <https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf>.

*Commentary.*

The sequence P of nonnegative integers is defined recursively by P(n) = 1 when n is even and P(n) = 1 - P(floor(n/2)) when n is odd. Thus P(0) = 1, P(2n) = 1 and P(2n + 1) = 1 - P(n). Its entries are zero or one, and it is the fixed point beginning with one of the substitution taking 1 to 10 and 0 to 11.

**Definition 1.3 (The classification statement).**

Lean statement: `D5/S3/Combinatorics/Apwenian/GuoHanDefs.claim`

*Formalization.* `D5/S3/Combinatorics/Apwenian/GuoHanDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ying-Jun Guo, Guo-Niu Han (2025). *On a family of automatic apwenian sequences*. DOI: [10.1016/j.disc.2025.114399](https://doi.org/10.1016/j.disc.2025.114399). URL: <https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf>.

*Commentary.*

For every finite alphabet Sigma of nonnegative integers containing one and having no other odd letter, every integer p at least two, every p-uniform substitution sigma mapping letters of Sigma to words over Sigma, and every sequence a over Sigma satisfying a(np + r) = sigma(a(n), r) for all nonnegative n and all r from zero through p minus one, a is apwenian if and only if a(n) modulo two equals P(n) for every nonnegative n. Here P is the period-doubling sequence. This is Conjecture 2 in Section 4 of Guo and Han's paper; the equivalence concerns parity and does not identify distinct even letters.

## References

- Truth anchor: `D5/S3/Combinatorics/Apwenian/GuoHanDefs.IsApwenian`
- Truth anchor: `D5/S3/Combinatorics/Apwenian/GuoHanDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/Apwenian/GuoHanDefs.periodDoubling`
