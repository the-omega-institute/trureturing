# Generating functions of accepted suffixes

## Abstract

First-action decompositions determine accepted-word generating functions at all heights and both phases.

**Definition 1.1 (The finite action alphabet).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.instFintypeAction`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.instFintypeAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The action alphabet is enumerated by its three distinct letters: opening, oldest and second. Every action is exactly one of these letters.

**Definition 1.2 (The suffix generating function).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.wordSeries`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.wordSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For height h and phase f, W(h,f;x) is the formal power series whose coefficient of x^l counts action words of length l accepted from that state. Here x counts individual scan actions.

**Theorem 1.3 (Boundary and higher-height equations).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.word_series_recursion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.word_series_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Write N_h = W(h,false;x) and T_h = W(h,true;x). Then N_0 = 1+xN_1, N_1 = xN_2+xN_0, N_2 = xN_3+2xN_1 and T_2 = xT_3+xN_1. For every h at least three, N_h = xN_{h+1}+x(N_{h-1}+T_{h-1}) and T_h = xT_{h+1}+xN_{h-1}. Finally N_0 = A(x^2), so its odd coefficients vanish and its coefficient of x^{2n} counts the P1-avoiding perfect matchings on 2n vertices.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.instFintypeAction`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.wordSeries`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.word_series_recursion`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsCorrespondence](TripleAvoidingMatchingsCorrespondence.md)
