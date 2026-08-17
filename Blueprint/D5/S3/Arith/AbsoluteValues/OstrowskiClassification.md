# Ostrowski Classification over the Rationals

## Abstract

Every nontrivial real-valued absolute value on Q is real or uniquely p-adic.

**Theorem 1.1 (Every nontrivial absolute value on Q is real or uniquely p-adic).**

$$\forall f : AbsoluteValue(\mathbb{Q}, \mathbb{R}), IsNontrivial(f) \Rightarrow f \sim abs_{\infty} \lor \exists! p : Prime, f \sim abs_{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AbsoluteValues/OstrowskiClassification.rational_absolute_value_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nontrivial real-valued absolute value f on the rationals, either f is equivalent to the standard real absolute value, or there is a unique natural prime p for which f is equivalent to the p-adic absolute value. Equivalence is the standard equivalence relation on absolute values used by Mathlib.

The Lean theorem is a direct application of Mathlib's exact Ostrowski classification, Rat.AbsoluteValue.equiv_real_or_padic. The prime witness carries the Fact p.Prime instance required to construct the p-adic absolute value.

This closes only the Ostrowski-classification clause of residual atom pzg-residual-3af9cb02d8cf0390d9bb00bf5e9962ee013252a6491d3f74d5ff2a3f8dcfe4ee at remark/27.34. It does not claim the atom's separate rational product formula or adelic compactness assertions.

## References

- Truth anchor: `D5/S3/Arith/AbsoluteValues/OstrowskiClassification.rational_absolute_value_classification`
