# Minimum Parikh Cardinality and Sentinel Lengths

## Abstract

Minimum complete Parikh cardinality forces a sentinel-iterate length in the literal m-bonacci word.

Let m be a natural number with 2 at most m and 3 at most m. The alphabet is Fin m. The literal substitution sends each letter a below m minus one to the two letters zero and a plus one, and sends the terminal letter to zero. The word is the unbounded limit of the iterated images of zero. For a list s, T(s) is its substituted image followed by zero.

For a natural length n, parikhImage(m,n) is the range of the map sending every natural start q to the vector of letter counts of factor(word,q,n). Start zero is included. Each coordinate is at most n, so this complete image is finite even though the set of starts is infinite. Its cardinality is the abelian complexity of the actual word at length n.

**Theorem 1.1 (Minimum complexity determines a sentinel length).**

$$\forall m \in \mathbb{N},\; \left(2 \le m \land 3 \le m\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \left(1 \le n \land ncard\left(parikhImage\left(m, n\right)\right) = m\right) \Rightarrow \left(\exists k \in \mathbb{N},\; n = length\left(iterate\left(T\left(m\right), k, nil\left(\right)\right)\right) + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciMinimumParikhDescent.minimal_abelian_complexity_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the reverse r of the position-zero prefix of length n minus one. It is fully right-special: each list r followed by a letter has an actual occurrence. These m extensions give m distinct Parikh vectors, the central vector of r plus each unit vector. If the complete image has cardinality m, these vectors exhaust it.

A signed defect of r is an actual word v of length one more than r whose integer count difference is e(a) plus e(b) minus e(c), with a, b and c pairwise distinct. Its negative coordinate excludes it from the central vectors, so minimum cardinality rules it out.

For a nonempty fully right-special list starting with a nonzero letter a, choose another nonzero letter b distinct from a. An occurrence of r followed by b is followed by zero. Removing the first letter and retaining that zero produces a signed defect. Consequently every nonempty defect-free fully right-special list starts with zero and has a strictly shorter fully right-special preimage under T.

Signed defects lift under T. If the terminal coordinate difference is minus one, zero or one, use respectively the tail of the actual substituted occurrence, the whole occurrence or its sentinel extension. The start is respectively boundary(q) plus one or boundary(q). The new difference is the cyclic rotation of the old one. A defect-free image therefore has a defect-free preimage. Strong induction on length identifies r with an iterate of T starting at the empty list, yielding the stated equation.

The conclusion includes n equal to one, with k equal to zero. No balance, palindrome, finite occurrence window or numeration admissibility hypothesis is required.

## References

- Truth anchor: `D5/S1/Words/MBonacciMinimumParikhDescent.minimal_abelian_complexity_length`
- Dependency: [D5/S1/Words/MBonacciReversedPrefixFRS](MBonacciReversedPrefixFRS.md)
