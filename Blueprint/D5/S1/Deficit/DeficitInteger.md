# The Normalized Beta Deficit Is an Integer Counting Bottom Carries

## Abstract

The normalized beta deficit of golden addition is an integer counting bottom carries.

**Theorem 1.1 (The normalized beta deficit is an integer counting bottom carries).**

$$c(v_1,v_2) := \beta(v_1) + \beta(v_2) - \beta(v_1+v_2) = \beta'(v_1) + \beta'(v_2) - \beta'(v_1+v_2), \quad c \in \mathbb{Z}, \quad c = \operatorname{lowCarries} - \operatorname{secondCarries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/DeficitInteger.deficit_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The model-set value of a natural number is obtained by evaluating its canonical Zeckendorf digits against golden-ratio powers, giving an element of the golden integers whose real image is the expansion face and whose Galois conjugate is the contraction face. The deficit of two operands is the failure of this value to be additive across their sum: the value of the first operand plus the value of the second minus the value of the sum. The theorem records three facts about this deficit at once. First, it is unchanged when read on the contraction face instead of the expansion face, because the two faces differ by a term proportional to the operand, and that proportional term cancels in the deficit exactly when the operands add. Second, the deficit is a rational integer rather than a general golden integer. Third, that integer is the signed count of the two bottom carry rules that fire while normalizing the concatenated digits, every internal carry contributing nothing.

The proof runs the normalization as a chain of local value-preserving carries and tracks how the golden-integer evaluation moves at each step. The golden coordinate of the evaluation is exactly the represented natural number, and normalization preserves that number, so the deficit has vanishing golden coordinate; this is at once the identity of the two faces and the integrality, since a golden integer with vanishing golden coordinate is a rational integer and is fixed by conjugation. The remaining rational coordinate is accumulated one carry at a time. The two adjacent and higher repeated carries are exactly value-neutral, each a direct consequence of the golden fixed-point relation, while the two lowest repeated carries each hide a single unit of opposite sign. Summing these contributions along the deterministic normalization path expresses the deficit as the signed count of bottom carries.

## References

- Truth anchor: `D5/S1/Deficit/DeficitInteger.deficit_integer`
- Dependency: [D5/S0/Carrier/Conj](../../S0/Carrier/Conj.md)
- Dependency: [D5/S1/Scale/Embedding](../Scale/Embedding.md)
