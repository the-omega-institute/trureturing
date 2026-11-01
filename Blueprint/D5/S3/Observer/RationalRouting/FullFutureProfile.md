# Finite cells for complete future profiles

## Abstract

A bounded vector of instantaneous floors determines every finite future word and has an exact finite cell evaluator.

The carrier is every positive rational, with no denominator bound. False acts by L(x)=x/(1+x), true by R(x)=x+1, and the head of a word acts first. A reply at any positive integer scale m is the entire integer floor of m times the current value. SameInstant at B compares all scales 1 through B, including noncoprime scales; SameFuture quantifies over every finite chronological word, including the empty word. A predicted word is an index of a calculation, not an executed experiment.

**Theorem 1.1 (All future words from a finite vector).**

$$\forall B\in \mathbb {N},x,y\in \mathbb {Q},0<x\land 0<y\longrightarrow (\operatorname {SameInstant}(B,x,y)\iff \operatorname {SameFuture}(B,x,y))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/FullFutureProfile.instantaneous_iff_full_future` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a left action, a threshold j at scale m pulls back to the comparison with j/(m-j), whose positive denominator is at most m. Every such comparison is already determined by the original vector. A right action adds the integer m to its scale-m report. Induction through an arbitrary finite word therefore preserves the whole vector. The reverse implication uses the empty word.

**Theorem 1.2 (The exact containing cell).**

$$\forall B\in \mathbb {N},x,y\in \mathbb {Q},1\le B\land 0<y\longrightarrow (\operatorname {Contains}(\operatorname {containingCell}(B,y),x)\iff 0<x\land \operatorname {SameInstant}(B,x,y))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/FullFutureProfile.containing_cell_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a positive representative y, the lower endpoint is the maximum of zero and floor(sy)/s over original denominators 1 through B. The upper endpoint is the minimum of (floor(sy)+1)/s. The lower endpoint is included when positive; zero is excluded by positivity. The upper endpoint is always excluded. Thus membership is exactly equality of all instantaneous replies and, by the preceding theorem, equality of the complete future profile. The unreduced grids have the same positive cuts as the reduced fractions with denominator at most B. Integer cuts make every upper endpoint finite, including the first cell (0,1/B).

**Theorem 1.3 (Finite evaluation of every coordinate).**

$$\forall B\in \mathbb {N},y\in \mathbb {Q},1\le B\land 0<y\longrightarrow \operatorname {let} C: \operatorname {ProfileCell}()=\operatorname {containingCell}(B,y); (\operatorname {Contains}(C,\operatorname {representative}(C))\land (\forall x\in \mathbb {Q},\operatorname {Contains}(C,x)\longrightarrow \forall w\in \operatorname {List}(\operatorname {Bool}()),m\in \mathbb {N},1\le m\le B\longrightarrow \operatorname {evaluate}(C,w,m)=\operatorname {reply}(m,\operatorname {attain}(w,x))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/FullFutureProfile.containing_cell_evaluator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula C denotes containingCell(B,y). Choose the included lower endpoint if it is positive, or half the upper endpoint in the zero slice. This rational belongs to the cell. Exact arithmetic along any supplied finite word followed by one floor computes its coordinate for every possible original in the cell. The word length and requested scale are arbitrary finite inputs; an infinite tuple is never stored or emitted.

**Theorem 1.4 (Selecting endpoints without reductions in the scan).**

$$\forall B\in \mathbb {N},y\in \mathbb {Q},\operatorname {fastContainingCell}(B,y)=\operatorname {containingCell}(B,y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/FullFutureProfile.fast_containing_cell_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The executable endpoint scan uses integer quotients and cross-product comparisons. The executable pass is tail recursive; its state is the current denominator and the selected lower and upper numerator-denominator pairs. An exact refinement proof identifies its output with the recursive grid-intersection specification. Reduction takes place when those final two pairs become rational endpoints. Its projection agrees exactly with the mathematical cell intersection, so the moving-cut acquisition can use this representation without changing the output cell.

## References

- Truth anchor: `D5/S3/Observer/RationalRouting/FullFutureProfile.containing_cell_evaluator`
- Truth anchor: `D5/S3/Observer/RationalRouting/FullFutureProfile.containing_cell_exact`
- Truth anchor: `D5/S3/Observer/RationalRouting/FullFutureProfile.fast_containing_cell_eq`
- Truth anchor: `D5/S3/Observer/RationalRouting/FullFutureProfile.instantaneous_iff_full_future`
- Dependency: [D5/S3/Observer/RationalRouting/Source](Source.md)
