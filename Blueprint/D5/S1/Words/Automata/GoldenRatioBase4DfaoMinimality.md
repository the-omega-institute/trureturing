# Base-4 Golden-Ratio DFAO Minimality Refuted

## Abstract

The paper's fixed base-4 22-state minimality claim is false under its
admissible-input convention: a 21-live-state partial DFAO agrees with the
paper table on every valid Zeckendorf encoding and treats the dead state as
implicit.

**Theorem 1.1 (A 21-live-state counterexample).**

$$
\exists c : \operatorname{AdmissibleDFAO}(21),\quad
\operatorname{EquivalentOnAdmissibleEncodings}(c.\operatorname{machine},
\operatorname{paperBase4DFAO}).
$$

*Proof.* Machine-checked in Lean as
`D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.paper_base4_golden_ratio_dfao_is_not_minimal`
(`✓ std3`). ∎

*Refutes.* `Problems/golden-ratio-base4-dfao-minimality` by the theorem above.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"golden-ratio-base4-dfao-minimality","declaration_gid":"D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.paper_base4_golden_ratio_dfao_is_not_minimal","resolution_kind":"refuted"} -->

*Citation.* Aaron Barnoff, Curtis Bright, and Jeffrey Shallit (2024). *Using
finite automata to compute the base-b representation of the golden ratio and
other quadratic irrationals*. URL: <https://arxiv.org/abs/2405.02727>.

## Verification

The module records the literal 22-row table, the 21 live-state reduction, and
the state embedding. Finite certificates verify output and legal-transition
compatibility. Structural induction proves run compatibility for every valid
word, and a separate theorem proves leading-zero invariance and the implicit
dead-state convention. The witness is therefore stronger than a finite match
on the sparse inputs `4^i`.

## References

- Truth anchor: `D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.paper_base4_golden_ratio_dfao_is_not_minimal`
- Library anchor: `D5/L/Words/barnoffbrightshallit2024using`
