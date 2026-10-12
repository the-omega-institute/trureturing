# Actual lattice-word extremal descent obligation

## Abstract

Define the original finite carrier for Shankar's 321-avoiding lattice words, its strict descent fiber, explicit candidate extremizers, and an all-parameter even construction. The all-k maximum and fiber-cardinality law remains unproved.

**Definition 1.1 (Prefix lattice inequalities).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.IsLattice`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.IsLattice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

A word is a list of natural numbers. For every prefix length from zero through the whole length, the number of ones is at least the number of twos, and the number of twos is at least the number of threes.

**Definition 1.2 (Subsequence avoidance).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.Avoids321`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.Avoids321` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

For all three strictly increasing positions, the letters cannot be 3, 2 and 1 in that order. This tests subsequences, not just adjacent triples.

**Definition 1.3 (The original word conditions).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.IsAdmissible`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.IsAdmissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

At parameter k, a word has length 3k, uses only the literal letters 1, 2 and 3, has exactly k copies of each, satisfies every prefix inequality, and avoids the subsequence 321. These are the original conditions from Shankar's sections 2.2 and 7. No refined counting identity is used as a predicate or premise.

**Definition 1.4 (Complete finite alphabet enumeration).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.rawWords`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.rawWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Enumerate every function from Fin(3k) to Fin(3), convert it to a list in index order, and add one to each letter value. Thus the encoding preserves order and uses 1, 2 and 3, with no quotient by word symmetries.

**Definition 1.5 (The actual finite carrier).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.actualWords`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.actualWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Filter rawWords by IsAdmissible. The scalar closedFormQ in the separate Stieltjes refutation is not used to define or count this carrier.

**Definition 1.6 (Strict adjacent descent count).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.descents`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.descents` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Zip a word with its tail and count pairs whose first letter is strictly greater than the second. Equal neighboring letters contribute zero. Inversions and major index are different statistics.

**Definition 1.7 (The proposed maximum).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.extremalValue`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.extremalValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The proposed value is the floor of 3k divided by two, minus one. Both division and subtraction are on natural numbers; the target law is restricted to k at least two.

**Definition 1.8 (The actual proposed extremal fiber).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.topFiber`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.topFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Filter actualWords(k) by equality of the strict descent count with extremalValue(k). Its size is not defined through the candidate family.

**Definition 1.9 (The exact open extremal obligation).**

$$\forall k\in \mathbb{N},2\leq k\Rightarrow (\forall w\in \operatorname{actualWords}\left(k\right),\operatorname{descents}\left(w\right)\leq \operatorname{extremalValue}\left(k\right))\land (\operatorname{card}\left(\operatorname{topFiber}\left(k\right)\right)=\operatorname{if}\left(\operatorname{mod}\left(k, 2\right)=0, 1, 2k\right))$$

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.extremalLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The conjunction asks that every actual word lie below the proposed maximum and that the actual fiber have cardinality one for even k and 2k for odd k. For k at least two, either required cardinality is positive, so this also requires attainment. This is an open proposition definition, not a theorem. Neither the universal bound nor the complete fiber classification is proved here. The full coefficient log-concavity and unimodality conjecture also remains open.

**Definition 1.10 (Repeated two-letter blocks).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.pairBlocks`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.pairBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Flatten n copies of the list [a,b]. Each block contributes both letters; there is no identification or duplication at a shared boundary.

**Definition 1.11 (Proposed even extremizer).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.evenWord`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.evenWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

For k=2t the candidate concatenates t copies of 12, t copies of 13, and t copies of 23. For t at least one, the construction theorem proves membership in the actual carrier and descent count 3t minus one. Global maximality and uniqueness remain open.

**Theorem 1.12 (Actual even words at the proposed descent level).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.even_word_construction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.even_word_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

For every natural t at least one, evenWord(t) belongs to actualWords(2t) and its strict adjacent descent count equals extremalValue(2t), namely 3t minus one. The proof verifies all prefix cuts, including cuts inside a two-letter block, the equal letter counts, and avoidance of the subsequence 321. It then encodes the word in the complete finite carrier and counts its descending block boundaries. All normalization and carrier lemmas are local to this one content theorem. This establishes attainment of the proposed level for even k; it does not establish a universal upper bound, uniqueness, the odd construction or injectivity, the complete fiber cardinality, or Conjecture 9.3.

**Definition 1.13 (Odd descending-pair base).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddOneBase`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddOneBase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Concatenate t copies of 21, t minus one copies of 31, and t plus one copies of 32. The classifier uses t at least one.

**Definition 1.14 (Extra-one odd candidates).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddOneWord`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddOneWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Place an initial 1 and a final 3 around oddOneBase. Insert one further 1 after q complete pairs, where q ranges from zero through 2t minus one. This is a proposed parametrization; no injectivity or exhaustiveness is assumed.

**Definition 1.15 (Reverse-complement operation).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.reverseComplement`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.reverseComplement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Reverse the list and replace each letter a by 4 minus a. On the intended alphabet this exchanges 1 with 3 and fixes 2. The function is defined on all natural-number lists; no general preservation theorem is asserted for that larger domain.

**Definition 1.16 (Two extra-two odd candidates).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddTwoWord`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddTwoWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Place an initial 1 and final 3 around t copies each of 21, 31 and 32. Insert a single 2 either before or after the block of 31 pairs.

**Definition 1.17 (The proposed odd parameter domain).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.OddIndex`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.OddIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The disjoint sum contains two copies of Fin(2t) and one Bool. The size of this parameter domain is not the cardinality of the actual maximizer fiber without the missing bijection.

**Definition 1.18 (Odd candidate encoding).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddWord`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The first Fin(2t) summand selects oddOneWord. The second selects its reverse complement. The Bool summand selects oddTwoWord. Required but unproved obligations are injectivity, actual extremal membership for every parameter, and coverage of every actual extremizer.

**Definition 1.19 (Separate candidate image).**

Lean statement: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddCandidates`

*Formalization.* `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddCandidates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

Take the finite image of oddWord. It remains separate from topFiber. The proposed descending-pair route must prove that every extremizer has one unpaired interior letter, that its descending pairs occur in the order 21 then 31 then 32, and that the prefix and avoidance conditions permit exactly these insertion positions. Those classification implications are unproved formal obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.Avoids321`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.IsAdmissible`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.IsLattice`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.OddIndex`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.actualWords`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.descents`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.evenWord`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.even_word_construction`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.extremalLaw`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.extremalValue`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddCandidates`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddOneBase`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddOneWord`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddTwoWord`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.oddWord`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.pairBlocks`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.rawWords`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.reverseComplement`
- Truth anchor: `D5/S3/Combinatorics/ShankarWords/ActualWordExtremal.topFiber`
