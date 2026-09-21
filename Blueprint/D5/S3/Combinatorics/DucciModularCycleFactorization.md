# Factoring the Cycles of the Modular Multiplicative Ducci Game

## Abstract

Every cycle of the modular multiplicative Ducci game factors through one constant and two generator cycles.

**Definition 1.1 (One move of the game).**

$$\forall u \in \mathrm{Position},\; \forall i \in \mathrm{Corner},\; \operatorname{entry}\left(\operatorname{step}\left(u\right), i\right) = \operatorname{entry}\left(u, i\right) \cdot \operatorname{entry}\left(u, i + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.step` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

The source replaces the difference map of the classical four-number game by a product map: every corner of the square is replaced by its product with the next corner. Corners are indexed by the residues modulo four, so that the next corner is addition of one.

**Definition 1.2 (Lying on a cycle).**

$$\forall u \in \mathrm{Position},\; (\operatorname{InCycle}\left(u\right)) \Leftrightarrow (\exists L \in \mathrm{Nat},\; (0 < L) \land (\operatorname{iterate}\left(L, u\right) = u))$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.InCycle` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

The source says a 4-tuple is in a cycle when iterating the game some positive number of times returns a 4-tuple equivalent to it under the symmetries of the square. That condition is the same as returning the 4-tuple itself. Rotations commute with the map, so a rotation after L moves gives the identity after four times L moves. For a reflection the map conjugates to the reflection shifted by one corner, so two rounds of L moves give a rotation and eight rounds give the identity. The displayed form is the one used below.

**Definition 1.3 (The 4-tuple with four equal entries).**

$$\forall a \in \mathrm{Zn},\; \forall i \in \mathrm{Corner},\; \operatorname{entry}\left(\operatorname{const}\left(a\right), i\right) = a$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.const` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

The 4-tuple carrying one value at all four corners.

**Definition 1.4 (Constant cycles).**

$$\forall u \in \mathrm{Position},\; (\operatorname{InConstantCycle}\left(u\right)) \Leftrightarrow ((\operatorname{InCycle}\left(u\right)) \land (\forall m \in \mathrm{Nat},\; \exists a \in \mathrm{Zn},\; \operatorname{iterate}\left(m, u\right) = \operatorname{const}\left(a\right)))$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.InConstantCycle` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

The source calls a cycle constant when all of its 4-tuples have equal entries, and its Lemma 3 shows that one such 4-tuple forces all of them.

**Definition 1.5 (Generator 4-tuples).**

$$\forall x \in \mathrm{ZnUnits},\; \operatorname{entry}\left(\operatorname{gen}\left(x\right), 0\right) = 1   \operatorname{entry}\left(\operatorname{gen}\left(x\right), 1\right) = x   \operatorname{entry}\left(\operatorname{gen}\left(x\right), 2\right) = 1   \operatorname{entry}\left(\operatorname{gen}\left(x\right), 3\right) = \operatorname{inverse}\left(x\right)$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.gen` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

The source calls a 4-tuple of this shape, with x invertible modulo n, a generator 4-tuple whenever it lies on a cycle.

**Definition 1.6 (Generator cycles).**

$$\forall u \in \mathrm{Position},\; (\operatorname{InGeneratorCycle}\left(u\right)) \Leftrightarrow ((\operatorname{InCycle}\left(u\right)) \land (\exists m \in \mathrm{Nat},\; \exists x \in \mathrm{ZnUnits},\; \operatorname{iterate}\left(m, u\right) = \operatorname{gen}\left(x\right)))$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.InGeneratorCycle` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

The source calls a cycle containing a generator 4-tuple a generator cycle, and notes that every second 4-tuple on such a cycle is again a generator 4-tuple.

**Definition 1.7 (Corner-by-corner product).**

$$\forall A \in \mathrm{Position},\; \forall B \in \mathrm{Position},\; \forall C \in \mathrm{Position},\; \forall i \in \mathrm{Corner},\; \operatorname{entry}\left(\operatorname{prod3}\left(A, B, C\right), i\right) = \operatorname{entry}\left(A, i\right) \cdot \operatorname{entry}\left(B, i\right) \cdot \operatorname{entry}\left(C, i\right)$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.prod3` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

The source multiplies 4-tuples entry by entry, and a product of cycles is the cycle carrying the products of their 4-tuples.

**Definition 1.8 (The factorization of cocomposite cycles).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (\forall u \in \mathrm{Position},\; (\operatorname{InCycle}\left(u\right)) \Rightarrow ((\forall i \in \mathrm{Corner},\; \neg \operatorname{IsUnit}\left(\operatorname{entry}\left(u, i\right)\right)) \Rightarrow (\exists A \in \mathrm{Position},\; \exists B \in \mathrm{Position},\; \exists C \in \mathrm{Position},\; ((\operatorname{InConstantCycle}\left(A\right)) \land ((\operatorname{InGeneratorCycle}\left(B\right)) \land (\operatorname{InGeneratorCycle}\left(C\right)))) \land (u = \operatorname{prod3}\left(A, B, C\right))))))$$

*Formalization.* `D5/S3/Combinatorics/DucciModularCycleFactorization.claim` (`✓ std3`).

*Citation.* Tasha Fellman, Dominic Klyve (2023). *Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication*. DOI: [10.5281/zenodo.10160456](https://doi.org/10.5281/zenodo.10160456). URL: <https://math.colgate.edu/~integers/x86/x86.pdf>.

*Commentary.*

Conjecture 1 of the source reads verbatim: "Every cocomposite cycle is a product of a constant cycle and two generating cycles." It is followed by: "This conjecture has been verified for all moduli up to 161. One possible direction of proving this conjecture is to show that all cocomposite cycles are a product of a cocomposite constant cycle and a coprime cycle, but we have been unsuccessful on this front." By Lemma 2 of the source a cycle has either all entries invertible or none, and the second case is the cocomposite one displayed here.

**Theorem 1.9 (The factorization holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DucciModularCycleFactorization.result` (`✓ std3`). ∎

*Resolves.* `Problems/ducci-modular-cycle-factorization` (proved) by `D5/S3/Combinatorics/DucciModularCycleFactorization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ducci-modular-cycle-factorization","declaration_gid":"D5/S3/Combinatorics/DucciModularCycleFactorization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The hypothesis that the entries are not invertible is never used, so the same construction covers coprime cycles and reproves Theorem 13 of the source, whose own argument inverts entries and therefore applies only to the coprime case. Write Q for the product of the four entries of a 4-tuple on a cycle of length L. The product of the four entries squares at every move, so Q is its own power with exponent two to the L. The second move carries opposite corners to Q, which gives both that the product of the entries at corners zero and two equals the product at corners one and three, and that this common value is Q raised to two to the L minus one. The third move has exponent vector one, three, three, one at every corner, so Q divides every entry. The fourth move has exponent vector two, four, six, four, so every entry after it is a square, and therefore every entry of the 4-tuple is a power with exponent two to the k for every k. Two of the iterated squaring maps of the finite ring of residues agree, and the gap t between them gives one exponent with the property that raising any such entry to the power two to the t returns it. Put D one less than two to the t, and let the idempotent be Q raised to D; it absorbs every positive power of Q and every entry. The constant factor is Q raised to two to the L minus two, whose square is the common product of opposite entries. Adding one minus the idempotent to a multiple of the inverse of that constant factor produces genuine units, because the cross terms vanish, and the two generator cycles are built from them. The constant factor returns after t moves; four moves send a generator 4-tuple to the generator 4-tuple of the inverse fourth power, so eight moves raise the unit to the sixteenth power and the generator cycle returns after eight t moves. The third factor is the second turned by one corner, the move commutes with that turn, and two moves place it on a generator 4-tuple. Neither a splitting of the ring into prime power parts nor any counting of multiplicative orders enters the argument.

## References

- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.InConstantCycle`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.InCycle`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.InGeneratorCycle`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.claim`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.const`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.gen`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.prod3`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.result`
- Truth anchor: `D5/S3/Combinatorics/DucciModularCycleFactorization.step`
