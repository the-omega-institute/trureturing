# Original guarded UNSAT and the ordered UNSAT-SAT pair

## Abstract

Conditional completeness of the exact original guarded languages.

**Theorem 1.1 (One original SAT premise).**

$$\operatorname{NPComplete}\left(S\right) \Rightarrow \left(\operatorname{CoNPComplete}\left(U\right) \land \operatorname{DPComplete}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/OriginalClauseClassification.lemma63` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

S is satisfiability on the original unrestricted formulaWord bytes, with canonical positive binary variable names and assignments on Appearing names. U contains only well-formed words outside S. Q encodes U first and S second by pairWords(u,v)=1^|u|0uv. Empty conjunctions, empty clauses, arbitrary finite clause and name widths, repetitions and tautologies retain these semantics. The sole hypothesis is NP-completeness of this exact S in the finite binary single-tape model. No other CNF language or machine certificate is a premise.

The finite lexical scanner is related to the exact original decoder. A false fallback repairs malformed outputs of SAT reductions while preserving SAT; a true fallback makes guarded UNSAT exactly complement SAT after repair. These directions differ because malformed words belong to complement SAT and belong to neither original guarded language. Each repair preserves valid input bytes and executes as a total polynomial transducer.

NP membership is transported by an executed preimage verifier that preserves both decisions and checks the target witness bound at the transformed instance length. Exact polynomial outer projections and the two repairs split Q into an NP factor and a coNP factor. DP means intersections of languages from those two classes.

For coNP hardness, a reduction of the complement source language to S is followed by false repair, so all outputs are well formed. For a DP source X intersect Y, reduce complement Y and X to S and false-repair both outputs. The common-input pairing transducer evaluates both maps on the same raw input and puts the complement-Y output first. Its ordered output belongs to Q exactly when the source input lies in X intersect Y. All maps are total on raw binary words and are measured by actual finite-machine instructions. The conditional theorem makes no assertion that the original NP-completeness hypothesis has itself been established here.

## References

- Truth anchor: `D5/S0/Computability/OriginalClauseClassification.lemma63`
- Dependency: [D5/S0/Computability/BinaryMachine/NPPreimage](BinaryMachine/NPPreimage.md)
- Dependency: [D5/S0/Computability/BinaryMachine/TransducerPair](BinaryMachine/TransducerPair.md)
- Dependency: [D5/S0/Computability/OriginalClauseGuard](OriginalClauseGuard.md)
- Dependency: [D5/S0/Computability/OriginalPairLanguages](OriginalPairLanguages.md)
