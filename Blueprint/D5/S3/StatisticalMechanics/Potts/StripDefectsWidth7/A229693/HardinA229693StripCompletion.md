# Exact-cost row completions

## Abstract

Enumerate row completions that spend exactly a given budget.

**Definition 1.1 (Cost of a colour match).**

$$\mathit{matchCost}: (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to ((\operatorname{\mathit{Fin}}\left(3\right)) \to (\mathit{Nat}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.matchCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

An absent colour costs zero. A present colour costs one exactly when it agrees with the current colour.

**Definition 1.2 (Cost of a completion).**

$$\mathit{completionCost}: \forall k: \mathit{Nat}, (((\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right))) \to ((\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to (((\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))) \to (\mathit{Nat}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Sum the initial match, when a previous colour is supplied, the matches between neighbours, and the matches against the optional boundary colours.

**Definition 1.3 (Pruned completion list).**

$$\mathit{completionRows}: \forall k: \mathit{Nat}, (((\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right))) \to ((\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to ((\mathit{Nat}) \to (\operatorname{\mathit{List}}\left((\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Try the three available colours in order, keep each head whose cost fits the budget, and prepend it to the completions at the remaining budget. The last cell must spend the entire remaining budget.

**Theorem 1.4 (Multiplicity of qualifying rows).**

$$\forall k: \mathit{Nat}, (\forall p: (\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)), (\forall b: \operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall d: \mathit{Nat}, (\forall f: ((\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))) \to (\mathit{Bool}), (\operatorname{\mathit{List}}.\operatorname{\mathit{countP}}\left(f, \operatorname{\mathit{completionRows}}\left(p, b, d\right)\right) = \sum_{r: (\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (\mathit{if} (\operatorname{\mathit{completionCost}}\left(p, b, r\right) = d) \land (\operatorname{f}\left(r\right) = \mathit{true}) \mathit{then} 1 \mathit{else} 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionRows_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The sum counts each qualifying row once.

**Definition 1.5 (Pruned list in base three).**

$$\mathit{completionCodes}: (\operatorname{\mathit{List}}\left(\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)\right)) \to ((\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to ((\mathit{Nat}) \to (\operatorname{\mathit{List}}\left(\mathit{Nat}\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionCodes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Run the same recursion on a list of boundary colours. Prepending a colour x replaces the tail code c with x plus three times c.

**Theorem 1.6 (Code of a row with a new head).**

$$\forall k: \mathit{Nat}, (\forall x: \operatorname{\mathit{Fin}}\left(3\right), (\forall r: (\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{finFunctionFinEquiv}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(x, r\right)\right)\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(x\right) + 3 \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{finFunctionFinEquiv}}\left(r\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.rowCode_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The leading cell is the least significant digit of the code.

**Theorem 1.7 (Agreement of the two lists).**

$$\forall k: \mathit{Nat}, (\forall p: (\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)), (\forall b: \operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall d: \mathit{Nat}, (\operatorname{\mathit{completionCodes}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(p\right), b, d\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left(\lambda r \mapsto \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{finFunctionFinEquiv}}\left(r\right)\right), \operatorname{\mathit{completionRows}}\left(p, b, d\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionCodes_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The numeric enumerator returns the codes of the pruned completion list in the same order.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionCodes`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionCodes_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionCost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionRows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionRows_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.matchCost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.rowCode_cons`
