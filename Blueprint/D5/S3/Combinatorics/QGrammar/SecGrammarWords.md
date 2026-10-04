# Canonical Sec Grammar Words

## Abstract

Support words have two canonical blocks, and every such word is represented by one admissible tuple.

**Definition 1.1 (Canonical word encoding).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarWords.encode`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarWords.encode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

For a family tag, index j, and natural multiplicities a and b, encode forms a block of x at j plus one, x at j, and one y at j, or a block of x at j, one y at j, and x at j minus one.

**Theorem 1.2 (Unique word normal form).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarWords.normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QGrammar/SecGrammarWords.normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

A DIO-sorted word with one y at index j, width at most one, and the stated boundary condition has a unique family and pair of multiplicities whose encoding is that word.

**Theorem 1.3 (Support word invariants).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarWords.word_invariants`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QGrammar/SecGrammarWords.word_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

Every word in the support after n derivative steps is DIO-sorted, contains exactly one y, has index width at most one, and after a positive number of steps a y at index zero is accompanied by an x at index one.

## References

- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarWords.encode`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarWords.normal_form`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarWords.word_invariants`
- Dependency: [D5/S3/Combinatorics/QGrammar/SecGrammarSupport](SecGrammarSupport.md)
