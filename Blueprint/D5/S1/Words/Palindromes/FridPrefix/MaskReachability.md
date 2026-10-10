# Bit masks retain actual nondeterministic paths

## Abstract

Bit masks retain actual nondeterministic paths

**Definition 1.1 (maskStep).**

$$\forall rows \in List\left(List\left(\mathbb{N}\right)\right),\; \forall mask \in \mathbb{N},\; \forall symbol \in \mathbb{N},\; maskStep\left(rows, mask, symbol\right) = foldl\left(\lambda (r:\mathbb{N}) \mapsto \lambda (q:\mathbb{N}) \mapsto if\left(testBit\left(mask, q\right), bitOr\left(r, getD\left(getElemBang\left(rows, q\right), symbol, 0\right)\right), r\right), 0, range\left(length\left(rows\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/MaskReachability.maskStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

bitOr is bitwise natural OR. The fold enumerates every row index, adds its transition mask exactly when that source-state bit is present, and uses zero for missing transition entries.

**Definition 1.2 (maskNFA).**

$$\forall rows \in List\left(List\left(\mathbb{N}\right)\right),\; \forall start \in \mathbb{N},\; maskNFA\left(rows, start\right) = nfa\left(setOf\left(\lambda (q:\mathbb{N}) \mapsto testBit\left(start, q\right) = true\right), univ, \lambda (q:\mathbb{N}) \mapsto \lambda (symbol:\mathbb{N}) \mapsto setOf\left(\lambda (s:\mathbb{N}) \mapsto q < length\left(rows\right) \land testBit\left(getD\left(getD\left(rows, q, nil\right), symbol, 0\right), s\right) = true\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/MaskReachability.maskNFA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All states accept in this auxiliary path automaton. An edge requires q<rows.length and the destination bit of rows[q][symbol] to be present.

**Theorem 1.3 (mask_path).**

$$\forall rows \in List\left(List\left(\mathbb{N}\right)\right),\; \forall w \in List\left(\mathbb{N}\right),\; \forall start \in \mathbb{N},\; \forall q \in \mathbb{N},\; testBit\left(foldl\left(maskStep\left(rows\right), start, w\right), q\right) = true \Rightarrow \left(\exists s \in \mathbb{N},\; testBit\left(start, s\right) = true \land Nonempty\left(Path\left(maskNFA\left(rows, start\right), s, q, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/MaskReachability.mask_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bit that survives a full word has an actual path from an initial bit. The proof reconstructs a predecessor through each bitwise-OR transition.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/MaskReachability.maskNFA`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/MaskReachability.maskStep`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/MaskReachability.mask_path`
