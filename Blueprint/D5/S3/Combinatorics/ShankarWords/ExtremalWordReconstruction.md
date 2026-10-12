# Actual extremal-word cut reconstruction

## Abstract

Reconstruct arbitrary actual extremal words through their literal whole-pair cut.

**Theorem 1.1 (Literal reconstruction from the original word conditions).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction.extremal_word_cut_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction.extremal_word_cut_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

For every k at least two and every literal word w in actualWords(k), the hypothesis descents(w)=extremalValue(k) forces one of the stated reconstruction forms. The even case is exactly evenWord(t), with k=2t and t at least one. In the odd case k=2t+1, the singleton-one branch is exactly oddOneWord(t,q) for q in Fin(2t). The singleton-two and singleton-three branches recover the literal descending-pair base and an insertion at twice a whole-pair cut j with j at most 3t. The theorem retains the original length, bounded alphabet, three equal letter counts, every lattice prefix inequality and full 321 subsequence avoidance through membership in actualWords. No candidate membership, ordered tiling or restricted cut is assumed. A proof-local recursion packs the actual adjacent descents into disjoint two-letter tiles. Saturation leaves zero or one interior singleton. Avoidance forces the actual tile sequence into 21,31,32 blocks, and letter counts fix their multiplicities. This is a partial inverse relation. The singleton-two legal cuts j=t or j=2t and the singleton-three reverse-complement index identification remain unproved here. Consequently this theorem does not establish the exact oddWord classification, a universal upper-bound theorem, top-fiber cardinality, coefficient log-concavity, unimodality or Conjecture 9.3. All auxiliary mathematical facts remain inside the live proof.

## References

- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction.extremal_word_cut_reconstruction`
- Dependency: [D5/S3/Combinatorics/ShankarWords/OddWordConstruction](OddWordConstruction.md)
