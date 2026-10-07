# A mismatch path constructs reflected unequal Fibonacci letters

## Abstract

A mismatch path constructs reflected unequal Fibonacci letters

**Definition 1.1 (badCoordinates).**

$$badCoordinates:Array\left(tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{Z}, \mathbb{Z}\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/MismatchWitness.badCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal 138 tuples contain previous-digit masks, comparison flags, and the two signed Fibonacci carry coordinates. The proof verifies every permitted transition against these coordinates.

**Theorem 1.2 (mismatch_witness).**

$$\forall symbols \in List\left(\mathbb{N}\right),\; \left(\left(\forall a \in \mathbb{N},\; mem\left(a, symbols\right) \Rightarrow a < 4\right) \land hasAccept\left(foldl\left(maskStep\left(badRows\right), badStart, symbols\right), badAccept\right) = true\right) \Rightarrow \left(\exists U \in List\left(Fin\left(2\right)\right),\; \exists V \in List\left(Fin\left(2\right)\right),\; length\left(U\right) = length\left(symbols\right) \land \left(length\left(V\right) = length\left(symbols\right) \land \left(NoAdjacentOnes\left(U\right) \land \left(NoAdjacentOnes\left(V\right) \land \left(NoAdjacentOnes\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, div\left(a, 2\right)\right), symbols\right)\right) \land \left(NoAdjacentOnes\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, a\right), symbols\right)\right) \land \left(fst\left(fibPair\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, div\left(a, 2\right)\right), symbols\right)\right)\right) \le fst\left(fibPair\left(U\right)\right) \land \left(fst\left(fibPair\left(U\right)\right) < fst\left(fibPair\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, a\right), symbols\right)\right)\right) \land \left(fst\left(fibPair\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, div\left(a, 2\right)\right), symbols\right)\right)\right) \le fst\left(fibPair\left(V\right)\right) \land \left(fst\left(fibPair\left(V\right)\right) < fst\left(fibPair\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, a\right), symbols\right)\right)\right) \land \left(fst\left(fibPair\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, div\left(a, 2\right)\right), symbols\right)\right)\right) + fst\left(fibPair\left(map\left(\lambda (a:\mathbb{N}) \mapsto ofNat\left(2, a\right), symbols\right)\right)\right) = fst\left(fibPair\left(U\right)\right) + fst\left(fibPair\left(V\right)\right) + 1 \land getLastD\left(U, 0\right) \neq getLastD\left(V, 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/MismatchWitness.mismatch_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X maps each paired symbol a to Fin.ofNat(2,a div 2), and Y maps it to Fin.ofNat(2,a). div is natural division. The two constructed canonical words U,V lie inside [value(X),value(Y)), their positions sum to value(X)+value(Y)-1, and their last digits differ. getLastD uses zero for an empty word.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/MismatchWitness.badCoordinates`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/MismatchWitness.mismatch_witness`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor](LanguageMonitor.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/NumeralSemantics](NumeralSemantics.md)
