# The Conjectured Classification of Erdos-Deep Triples Is Incomplete

## Abstract

Three progressions in the integers modulo twenty-seven fall outside the conjectured list.

**Definition 1.1 (Distance in a cyclic group).**

$$\forall n \in \mathrm{Nat},\; \forall x \in \mathrm{Nat},\; \forall y \in \mathrm{Nat},\; \operatorname{cdist}\left(n, x, y\right) = \operatorname{min}\left(\operatorname{mod}\left(x + n - y, n\right), n - \operatorname{mod}\left(x + n - y, n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.cdist` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

Section 1 of the source measures distance in the integers modulo n by the smaller of the two arc lengths, writing the norm of x as the minimum of x and its negative, each reduced below n.

**Definition 1.2 (A modular arithmetic progression).**

$$\forall n \in \mathrm{Nat},\; \forall g \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{apList}\left(n, g, k\right) = \operatorname{map}\left(i \mapsto \operatorname{mod}\left(i \cdot g, n\right), \operatorname{range}\left(k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.apList` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

The source writes AP(n, g, k) for the progression with k terms, first term zero and common difference g, read inside the integers modulo n. The terms need not be distinct for every g and k; the statement below asks for distinctness separately.

**Definition 1.3 (Distances inside one progression).**

$$\forall n \in \mathrm{Nat},\; \forall x \in \mathrm{Nat},\; \forall l \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{pairDists}\left(n, []\right) = []   \operatorname{pairDists}\left(n, x :: l\right) = \operatorname{append}\left(\operatorname{map}\left(\operatorname{cdist}\left(n, x\right), l\right), \operatorname{pairDists}\left(n, l\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.pairDists` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

Every unordered pair of distinct points contributes one distance. A list of k points contributes k choose two of them.

**Definition 1.4 (Distances of a family of three).**

$$\operatorname{familyDists}\left(n, g1, g2, g3, k1, k2, k3\right) = \operatorname{append}\left(\operatorname{pairDists}\left(n, \operatorname{apList}\left(n, g1, k1\right)\right), \operatorname{append}\left(\operatorname{pairDists}\left(n, \operatorname{apList}\left(n, g2, k2\right)\right), \operatorname{pairDists}\left(n, \operatorname{apList}\left(n, g3, k3\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.familyDists` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

The source takes the multiset union over the members of the family; distances between points of different members are not counted.

**Definition 1.5 (The multiplicity of each distance that occurs).**

$$\forall ds \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{multiplicities}\left(ds\right) = \operatorname{map}\left(d \mapsto \operatorname{count}\left(ds, d\right), \operatorname{dedup}\left(ds\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.multiplicities` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

One entry for each distinct distance, giving how many pairs realise it.

**Definition 1.6 (Erdos-deep families).**

$$(\operatorname{IsErdosDeep}\left(n, g1, g2, g3, k1, k2, k3\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; (m = \operatorname{length}\left(\operatorname{multiplicities}\left(\operatorname{familyDists}\left(n, g1, g2, g3, k1, k2, k3\right)\right)\right)) \land (\forall i \in \mathrm{Nat},\; ((1 \le i) \land (i \le m)) \Rightarrow (\operatorname{count}\left(\operatorname{multiplicities}\left(\operatorname{familyDists}\left(n, g1, g2, g3, k1, k2, k3\right)\right), i\right) = 1)))$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.IsErdosDeep` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

Section 1 of the source reads: "we say that F is Erdos-deep if the multiplicities of distances that occur in the distance multiset are precisely one, two, up to k minus one for some integer k." Writing m for the number of distinct distances, that says each of one through m occurs exactly once among the multiplicities; the integer k is then m plus one, and it satisfies k times k minus one equals the sum over the members of the family of the length times the length minus one.

**Definition 1.7 (The conjectured list of length triples).**

$$\operatorname{allowed}\left(\right) = \{(4, 4, 3), (6, 3, 3), (6, 5, 3), (6, 6, 4), (6, 6, 6), (7, 7, 3), (9, 4, 3), (8, 7, 4), (8, 8, 5), (10, 6, 4), (12, 4, 4), (13, 5, 3), (13, 7, 4), (16, 5, 4), (21, 6, 4)\}$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.allowed` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

The two triples the source expects for infinitely many moduli, followed by the thirteen it expects for finitely many.

**Definition 1.8 (The conjectured classification).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall g1 \in \mathrm{Nat},\; \forall g2 \in \mathrm{Nat},\; \forall g3 \in \mathrm{Nat},\; \forall k1 \in \mathrm{Nat},\; \forall k2 \in \mathrm{Nat},\; \forall k3 \in \mathrm{Nat},\; (((3 \le k3) \land ((k3 \le k2) \land (k2 \le k1))) \land ((k1 \le \operatorname{div}\left(n, 2 \cdot \operatorname{gcd}\left(n, g1\right)\right) + 1) \land ((\operatorname{gcd}\left(n, g1, g2, g3\right) = 1) \land (((\operatorname{Nodup}\left(\operatorname{apList}\left(n, g1, k1\right)\right)) \land ((\operatorname{Nodup}\left(\operatorname{apList}\left(n, g2, k2\right)\right)) \land (\operatorname{Nodup}\left(\operatorname{apList}\left(n, g3, k3\right)\right)))) \land (\operatorname{IsErdosDeep}\left(n, g1, g2, g3, k1, k2, k3\right)))))) \Rightarrow ((k1, k2, k3) \in \operatorname{allowed}\left(\right)))$$

*Formalization.* `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.claim` (`✓ std3`).

*Citation.* Peter J. Dukes, Tao Gaede (2023). *Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities*. DOI: [10.48550/arXiv.2208.05527](https://doi.org/10.48550/arXiv.2208.05527). URL: <https://math.colgate.edu/~integers/x25/x25.pdf>.

*Commentary.*

Conjecture 1 of the source reads verbatim: "An Erdos-deep family of three APs of lengths k1 at least k2 at least k3 in Z n exists if and only if the triple lies in the first set, each for infinitely many n, or in the second set, each for a finite number of values of n." The statement displayed here is the forward half, the one the witness below contradicts. It carries the conventions the source fixes for families of progressions, lengths at least three and the generators together with the modulus having greatest common divisor one, and in addition the bound on the longest length that the accompanying thesis states in its own version of the conjecture. Carrying that bound makes the statement stronger, so refuting it refutes the published form as well.

**Theorem 1.9 (The conjectured list is incomplete).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/erdos-deep-triple-classification-refutation` (refuted) by `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"erdos-deep-triple-classification-refutation","declaration_gid":"D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

In the integers modulo twenty-seven take the progressions with twelve, six and five terms and common differences one, twelve and seven. The first is zero through eleven and gives each distance from one to eleven the multiplicity twelve minus it. The second is zero, twelve, twenty-four, nine, twenty-one, six and gives three four times, six three times, nine three times and twelve five times. The third is zero, seven, fourteen, twenty-one, one and gives one once, six twice, seven four times and thirteen three times. The union gives thirteen distinct distances whose multiplicities are twelve, ten, thirteen, eight, seven, eleven, nine, four, six, two, one, five and three, that is each of one through thirteen exactly once, so the family is Erdos-deep. The lengths are at least three and decreasing, the modulus and the three differences have greatest common divisor one, and twelve is at most fourteen, the bound the thesis imposes. The triple twelve, six, five is in neither part of the conjectured list.

## References

- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.IsErdosDeep`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.allowed`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.apList`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.cdist`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.familyDists`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.multiplicities`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.pairDists`
- Truth anchor: `D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.result`
