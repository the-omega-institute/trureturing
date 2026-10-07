# Sec Grammar Definitions

## Abstract

The Sec grammar supplies ordered words, a q-derivative, and the conjectured support count.

**Definition 1.1 (Grammar variables).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.Var`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.Var` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

A grammar variable is a Boolean tag together with a natural index. The false tag denotes x at that index and the true tag denotes y.

**Definition 1.2 (DIO precedence).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.dioLe`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.dioLe` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

The DIO precedence places larger indices first and places x before y when the indices agree.

**Definition 1.3 (Decidable precedence).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.instDecidableRelVarDioLe`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.instDecidableRelVarDioLe` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

The DIO precedence has a decidable comparison for every pair of grammar variables.

**Definition 1.4 (DIO normalization).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.dio`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.dio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

DIO normalization sorts a finite word by the DIO precedence.

**Definition 1.5 (Index raising).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.up`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.up` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

The up operation raises every index in a word by one and preserves each variable tag.

**Definition 1.6 (The Sec replacement rule).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.rule`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.rule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

The replacement of y at index j is the single word y at j followed by x at j plus one, weighted by q to the j. The replacement of x at j is the sum of the empty word and that same two letter word, with the same weight.

**Definition 1.7 (Derivative of a word).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.derivWord`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.derivWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

The derivative of a word sums, over each position, the replacement at that position followed by the raised suffix, then normalizes the resulting word by DIO.

**Definition 1.8 (Linear q-derivative).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.deriv`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.deriv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

The q-derivative of a formal sum of words is the coefficient weighted sum of the derivatives of its words.

**Definition 1.9 (The conjectured support formula).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.omegaFormula`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.omegaFormula` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

The function omegaFormula gives one at step one, three at step two, the stated cubic expression at odd steps at least three, and the stated cubic expression at even steps at least four.

**Definition 1.10 (The support-count conjecture).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.claim`

*Formalization.* `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

For every positive natural step n, the support of the n-fold derivative of the single y at index zero has cardinality omegaFormula n.

## References

- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.Var`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.deriv`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.derivWord`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.dio`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.dioLe`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.instDecidableRelVarDioLe`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.omegaFormula`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.rule`
- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarDefs.up`
