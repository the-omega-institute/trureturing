# Actual extremal-word reconstruction

## Abstract

Reconstruct arbitrary actual extremal words as existing even or odd constructors.

**Theorem 1.1 (Literal reconstruction from the original word conditions).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction.extremal_word_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction.extremal_word_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

For every k at least two and every literal word w in actualWords(k), the hypothesis descents(w)=extremalValue(k) forces one of the stated reconstruction forms. The even case is exactly evenWord(t), with k=2t and t at least one. In the odd case k=2t+1, the word is exactly oddWord(t,i) for an index i in OddIndex(t). The theorem retains the original length, bounded alphabet, three equal letter counts, every lattice prefix inequality and full 321 subsequence avoidance through membership in actualWords. No candidate membership, ordered tiling or restricted cut is assumed. A proof-local recursion packs the actual adjacent descents into disjoint two-letter tiles. Saturation leaves zero or one interior singleton. Avoidance orders the actual tiles into 21,31,32 blocks, and letter counts fix their multiplicities. For singleton two, two lattice prefix inequalities and a crossing 321 triple force the cut j=t or j=2t. For singleton three, avoidance gives t+1<=j<=3t; reversing and complementing the literal base identifies the odd index with q=3t-j. This proves the inverse relation to the existing even and odd construction theorems. It does not establish a separately stated universal upper bound or top-fiber cardinality, coefficient log-concavity, unimodality or Conjecture 9.3. All auxiliary mathematical facts remain inside the live proof.

## References

- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction.extremal_word_reconstruction`
- Dependency: [D5/S3/Combinatorics/ShankarWords/OddWordConstruction](OddWordConstruction.md)
