# Irrational Continued-Fraction Nontermination

## Abstract

An irrational real has a nonterminating continued-fraction computation.

**Theorem 1.1 (Irrational inputs do not terminate).**

$$\forall x\in \mathbb{R},\ \operatorname{Irrational}(x) \Rightarrow \neg\operatorname{Terminates}(\operatorname{continuedFraction}(x)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/IrrationalContinuedFractionNontermination.irrational_continued_fraction_nontermination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The declaration closes only the source clause that every irrational continued-fraction computation is infinite. It does not claim the separate error monotonicity, golden extremality, or comparison clauses.

Mathlib provides GenContFract.terminates_iff_rat, which identifies termination exactly with being a rational real. The proof applies that equivalence and contradicts Irrational directly, so no new continued-fraction machinery is introduced.

## References

- Truth anchor: `D5/S1/Depth/IrrationalContinuedFractionNontermination.irrational_continued_fraction_nontermination`
