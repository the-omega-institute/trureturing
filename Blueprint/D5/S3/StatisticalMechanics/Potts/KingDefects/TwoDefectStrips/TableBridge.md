# Two-defect king transfers

## Abstract

The finite data support the literal fixed-width king-grid recurrence.

**Theorem 1.1 (A sorted successor list supplies all multiplicities).**

$$\forall (q: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (P: (\operatorname{DefectTransfer}.\operatorname{Row}\left(q, k\right)) \to (\operatorname{Prop})), ([\operatorname{DecidablePred}\left(P\right)], \forall (c: (\operatorname{DefectTransfer}.\operatorname{Row}\left(q, k\right)) \to (\operatorname{Fin}\left(M\right))), (\forall (s: \operatorname{Fin}\left(M\right)), (\operatorname{List}.\operatorname{count}\left(s, \operatorname{List}.\operatorname{insertionSort}\left(\lambda (a: \operatorname{Fin}\left(M\right)) \mapsto (\lambda (b: \operatorname{Fin}\left(M\right)) \mapsto (a \le b)), \operatorname{List}.\operatorname{filterMap}\left(\lambda (r: \operatorname{DefectTransfer}.\operatorname{Row}\left(q, k\right)) \mapsto ((\operatorname{if} \operatorname{P}\left(r\right) \operatorname{then} \operatorname{some}\left(\operatorname{c}\left(r\right)\right) \operatorname{else} \operatorname{none})), \operatorname{List}.\operatorname{ofFn}\left(\lambda (i: \operatorname{Fin}\left(q^{k}\right)) \mapsto (\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finFunctionFinEquiv}, i\right))\right)\right)\right)\right) = \sum_{(r: \operatorname{DefectTransfer}.\operatorname{Row}\left(q, k\right))} ((\operatorname{if} (\operatorname{P}\left(r\right)) \land (\operatorname{c}\left(r\right) = s) \operatorname{then} 1 \operatorname{else} 0))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge.count_successors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229753: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229753>.

*Commentary.*

For arbitrary palette q, width k, class size M, decidable admissibility P, classifier c and class s, the count of s in the sorted filtered enumeration equals the sum over rows of the indicator of P(r) and c(r)=s. The enumeration uses Mathlib finFunctionFinEquiv; insertion sorting preserves multiplicity.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge.count_successors`
