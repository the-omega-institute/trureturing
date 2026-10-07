# The literal zero-digit rule for every Fibonacci palindrome

## Abstract

The literal zero-digit rule for every Fibonacci palindrome

**Theorem 1.1 (frid_canonical_necessity).**

$$\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \left(i < j \land Palindrome\left(goldenFactor\left(j - i, i\right)\right)\right) \Rightarrow \left(\exists m \in \mathbb{N},\; not\left(mem\left(m + 2, wdigits\left(i\right)\right)\right) \land int\left(j\right) = int\left(i\right) + int\left(wValue\left(m + 2\right)\right) - 2 - 2 \cdot int\left(sum\left(map\left(fib, filter\left(\lambda (r:\mathbb{N}) \mapsto r < m + 2, wdigits\left(i\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/CanonicalNecessity.frid_canonical_necessity` (`✓ std3`). ∎

*Citation.* Anna E. Frid (2018). *Representations of palindromes in the Fibonacci word*. URL: <https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf>.

*Commentary.*

Theorem 1, printed pages 10–11, begins: “Let w be a characteristic Sturmian word corresponding to the directive sequence (dₙ), and w(i..j] = w[i + 1] . . . w[j] be a palindrome. Denote the Ostrowski representation of i as i = xₙ ··· xₘ ··· x₀ [o]; note that it may start with several leading zeros. Then there exist a legal representation of j given by j = xₙ ··· xₘ₊₁ yₘ · (dₘ₋₁ − xₘ₋₁) ··· (d₀ − x₀), where 0 ≤ m ≤ n and xₘ < yₘ ≤ dₘ.” For the Fibonacci directive sequence all dₘ equal one: the selected canonical digit is zero, becomes one, and every lower digit is complemented. wdigits stores Fibonacci indices beginning at 2; the selected position m therefore has stored index m+2. wValue(m+2)=fib(m+4), and the filtered sum is the value of all canonical digits strictly below that index. The endpoint equation is an integer equation; the factor uses natural subtraction on the increasing interval. Zero residual carries identify the reconstructed legal numeral with j. No endpoint necessity is assumed.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/CanonicalNecessity.frid_canonical_necessity`
- Dependency: [D5/S1/Digit/GoldenBase4DenseInput](../../../Digit/GoldenBase4DenseInput.md)
- Dependency: [D5/S1/Digit/GoldenZeckendorfLanguage](../../../Digit/GoldenZeckendorfLanguage.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/CarryBounds](CarryBounds.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity](EndpointNecessity.md)
