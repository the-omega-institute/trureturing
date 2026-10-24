# The right-special word of a rotor sequence

## Abstract

For every irrational slope greater than one, the unique right-special rotor factor of each positive length is the reversed prefix after the initial zero.

**Definition 1.1 (An arithmetic cutting sequence).**

$$\forall (\sigma: \mathbb{R}), (\forall (m: \mathbb{N}), (((\operatorname{cutting}\left(\sigma, m\right): \mathbb{N})) = (\operatorname{ite}\left((\exists (k: \mathbb{N}), (((1) \le (k)) \land ((m) = (((\operatorname{Nat.floor}\left(((\operatorname{Nat.cast}\left(k\right): \mathbb{R})) \cdot (\sigma)\right): \mathbb{N})) + (k))))), (3), (1)\right))))$$

*Formalization.* `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.cutting` (`✓ std3`).

*Citation.* Govind S. Krishnaswami; Anirudh Rameshan (2026). *Symbol sequences from three-rotor coincidences and their word-complexity*. DOI: [10.48550/arXiv.2606.25766](https://doi.org/10.48550/arXiv.2606.25766). URL: <https://arxiv.org/abs/2606.25766v1>.

*Commentary.*

The function cutting is defined for every real σ and natural m. It takes the value 3 exactly at indices of the form floor(kσ) + k with k a positive natural number, and takes the value 1 elsewhere. Here floor means the natural-valued floor, and k is first cast to a real number. In particular its value at m = 0 is 1. For irrational σ > 1, the positive indices describe the cutting sequence of y = σx starting at the origin, as in the v1 TeX, line 831. At the kth vertical crossing there have been floor(kσ) horizontal crossings and k vertical crossings; irrationality excludes simultaneous crossings. The index criterion therefore assigns 3 to vertical crossings and 1 to horizontal crossings.

**Definition 1.2 (The separator encoding).**

$$\forall (\sigma: \mathbb{R}), (\forall (m: \mathbb{N}), (((\operatorname{rotor}\left(\sigma, m\right): \mathbb{N})) = (\operatorname{ite}\left(((m) = (0)), (0), (\operatorname{ite}\left(((\operatorname{Nat.mod}\left(m, 2\right)) = (1)), (2), (\operatorname{cutting}\left(\sigma, \operatorname{Nat.div}\left(m, 2\right)\right))\right))\right))))$$

*Formalization.* `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.rotor` (`✓ std3`).

*Citation.* Govind S. Krishnaswami; Anirudh Rameshan (2026). *Symbol sequences from three-rotor coincidences and their word-complexity*. DOI: [10.48550/arXiv.2606.25766](https://doi.org/10.48550/arXiv.2606.25766). URL: <https://arxiv.org/abs/2606.25766v1>.

*Commentary.*

The rotor sequence starts with 0. Its odd positions contain the separator 2, and each positive even position m contains cutting(σ, m / 2), with natural division. Thus it reads 0, 2, s₁, 2, s₂, 2, s₃, and so on. This is the correspondence in the v1 TeX, line 835, for irrational σ > 1. The displayed definition also specifies a sequence for every other real σ.

**Definition 1.3 (Finite factors).**

$$\forall (R: \mathbb{N} \to \mathbb{N}), (\forall (w: \operatorname{List}\left(\mathbb{N}\right)), ((\operatorname{IsFactor}\left(R, w\right)) \Leftrightarrow (\exists (i: \mathbb{N}), (\forall (t: \mathbb{N}), (\forall (h: (t) < (\operatorname{List.length}\left(w\right))), ((R\left((i) + (t)\right)) = (\operatorname{GetElem.getElem}\left(w, t, h\right))))))))$$

*Formalization.* `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.IsFactor` (`✓ std3`).

*Citation.* Govind S. Krishnaswami; Anirudh Rameshan (2026). *Symbol sequences from three-rotor coincidences and their word-complexity*. DOI: [10.48550/arXiv.2606.25766](https://doi.org/10.48550/arXiv.2606.25766). URL: <https://arxiv.org/abs/2606.25766v1>.

*Commentary.*

A list w is a factor of a sequence R when it occurs at some natural starting position i: its tth entry equals R(i + t) for every t below its length. The variable h certifies that the list entry exists. This makes precise the subwords used in the v1 TeX, line 697. The definition allows an arbitrary natural-valued sequence and includes the empty list.

**Definition 1.4 (Two distinct right extensions).**

$$\forall (R: \mathbb{N} \to \mathbb{N}), (\forall (w: \operatorname{List}\left(\mathbb{N}\right)), ((\operatorname{IsRightSpecial}\left(R, w\right)) \Leftrightarrow (\exists (a: \mathbb{N}), (\exists (b: \mathbb{N}), ((a \ne b) \land ((\operatorname{IsFactor}\left(R, \operatorname{List.append}\left(w, [a]\right)\right)) \land (\operatorname{IsFactor}\left(R, \operatorname{List.append}\left(w, [b]\right)\right))))))))$$

*Formalization.* `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.IsRightSpecial` (`✓ std3`).

*Citation.* Govind S. Krishnaswami; Anirudh Rameshan (2026). *Symbol sequences from three-rotor coincidences and their word-complexity*. DOI: [10.48550/arXiv.2606.25766](https://doi.org/10.48550/arXiv.2606.25766). URL: <https://arxiv.org/abs/2606.25766v1>.

*Commentary.*

A list w is right-special when two distinct natural symbols a and b can each be appended to w to obtain a factor of R. The two extended words may occur at different positions. This is the right-special condition in the v1 TeX, line 697; no restriction to a fixed finite alphabet is imposed in the definition.

**Definition 1.5 (The reversed-prefix characterization).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (\sigma: \mathbb{R}), ((\operatorname{Irrational}\left(\sigma\right)) \Rightarrow ((((1: \mathbb{R})) < (\sigma)) \Rightarrow (\forall (n: \mathbb{N}), (((2) \le (n)) \Rightarrow (\forall (w: \operatorname{List}\left(\mathbb{N}\right)), (((\operatorname{List.length}\left(w\right)) = ((n) - (1))) \Rightarrow ((\operatorname{IsRightSpecial}\left(\operatorname{rotor}\left(\sigma\right), w\right)) \Leftrightarrow ((w) = (\operatorname{List.reverse}\left(\operatorname{List.ofFn}\left(\lambda (t: \operatorname{Fin}\left((n) - (1)\right)) \mapsto (\operatorname{rotor}\left(\sigma, ((\operatorname{Fin.val}\left(t\right): \mathbb{N})) + (1)\right))\right)\right)))))))))))$$

*Formalization.* `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.claim` (`✓ std3`).

*Citation.* Govind S. Krishnaswami; Anirudh Rameshan (2026). *Symbol sequences from three-rotor coincidences and their word-complexity*. DOI: [10.48550/arXiv.2606.25766](https://doi.org/10.48550/arXiv.2606.25766). URL: <https://arxiv.org/abs/2606.25766v1>.

*Commentary.*

For every irrational σ > 1 and natural n ≥ 2, a list w of length n − 1 is right-special precisely when it is the reversal of rotor(σ, 1), through rotor(σ, n − 1). This states the conjecture in the v1 TeX, line 701, with the right-special condition of line 697; the question is also listed in the Discussion, line 917. Since 0 occurs only at position zero, the unique factor of length n beginning with 0 is the initial prefix. Deleting its 0 and reversing gives exactly the list in the formula. The index t belongs to Fin(n − 1); Fin.val explicitly casts it to a natural number before adding one.

**Theorem 1.6 (Identification and uniqueness of the right-special factor).**

$$\forall (\sigma: \mathbb{R}), ((\operatorname{Irrational}\left(\sigma\right)) \Rightarrow ((((1: \mathbb{R})) < (\sigma)) \Rightarrow (\forall (n: \mathbb{N}), (((2) \le (n)) \Rightarrow (\forall (w: \operatorname{List}\left(\mathbb{N}\right)), (((\operatorname{List.length}\left(w\right)) = ((n) - (1))) \Rightarrow ((\operatorname{IsRightSpecial}\left(\operatorname{rotor}\left(\sigma\right), w\right)) \Leftrightarrow ((w) = (\operatorname{List.reverse}\left(\operatorname{List.ofFn}\left(\lambda (t: \operatorname{Fin}\left((n) - (1)\right)) \mapsto (\operatorname{rotor}\left(\sigma, ((\operatorname{Fin.val}\left(t\right): \mathbb{N})) + (1)\right))\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.result` (`✓ std3`). ∎

*Resolves.* `Problems/krishnaswami-rameshan-2026-rotor-right-special-word` (proved) by `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishnaswami-rameshan-2026-rotor-right-special-word","declaration_gid":"D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Govind S. Krishnaswami; Anirudh Rameshan (2026). *Symbol sequences from three-rotor coincidences and their word-complexity*. DOI: [10.48550/arXiv.2606.25766](https://doi.org/10.48550/arXiv.2606.25766). URL: <https://arxiv.org/abs/2606.25766v1>.

*Commentary.*

First relate a crossing index to a floor jump. For an irrational real d > 1 and natural m, the existence of a positive natural k with m = floor(kd) is equivalent to the integer-valued floor difference floor((m + 1) / d) − floor(m / d) being 1. In the forward direction, irrationality gives m < kd < m + 1. Since 1 / d < 1, the two floors are k − 1 and k. Conversely, let z = floor((m + 1) / d). A jump of one makes z positive. Taking k = z.toNat gives m < kd ≤ m + 1, and irrationality makes the upper inequality strict, so the natural floor of kd is m.

Set α = 1 / (σ + 1). Then 0 < α < 1 and α is irrational. Apply the floor-jump equivalence with d = σ + 1 and m = j + 1. The natural-floor identity floor(k(σ + 1)) = floor(kσ) + k identifies cutting(σ, j + 1) with 3 when lowerMechanicalWord(α, α, j) is true and with 1 when it is false. Indeed the corresponding mechanical letter is the integer-floor difference floor((j + 2)α) − floor((j + 1)α).

Next construct both right extensions of the reversed mechanical prefix. For any finite N, irrationality keeps −qα away from integers for 1 ≤ q ≤ N. Finite floor stability supplies ε > 0 such that subtracting any δ with 0 ≤ δ < ε leaves all these floors unchanged. One obtains this from stability at slope −α by perturbing the slope by −δ / q; because q ≥ 1, the perturbation has absolute value at most δ.

For a prefix of length m and a Boolean b, use N = m + 1 and take δ = 0 if b is true, and δ = min(ε, 1 − α) / 2 if b is false. In either case 0 ≤ δ < ε and δ < 1 − α. Consider the length m + 1 mechanical factor at position zero with intercept −(m + 1)α − δ. For its first m letters, the unchanged negative floors and the identity floor(−qα) = −floor(qα) − 1 show that its letters are the original prefix read backwards. Its last letter compares floor(−δ) with floor(−α − δ) = −1. For δ = 0 it is true, and for δ > 0 it is false. The factor language of an irrational lower mechanical word is independent of the intercept, by lowerMechanicalFactor_mem_factorSet. Hence both extensions occur also in the word with intercept α. Removing the final letter from an occurrence shows that the reversed prefix itself occurs, so it is right-special.

Now analyze the separator encoding. Cutting takes only the values 1 and 3. Thus rotor(σ, i) = 0 exactly when i = 0, and rotor(σ, i) = 2 exactly when i is odd. Every symbol other than 2 is followed by 2. If a nonempty rotor factor of length ℓ has two distinct continuations, neither occurrence can start at zero: equality of their first letters would force both starts to be zero and their continuations to agree. The factor must end in 2, since any other last letter forces the same next letter 2. For its positive occurrence starts i and j, both i + ℓ and j + ℓ are even.

For a positive start i with i + ℓ even, the letter at offset t is 2 when t + ℓ is odd. Otherwise it encodes the mechanical bit at index (i − 1) / 2 + t / 2. Reading the nonseparator offsets 2q + ℓ % 2 therefore projects the rotor factor to a mechanical factor of length ℓ / 2 starting at (i − 1) / 2. The two rotor occurrences give the same mechanical factor, since the encoding false ↦ 1, true ↦ 3 is injective. Their next mechanical bits are distinct, since their next rotor symbols are distinct. The projected factor is consequently right-special.

Apply exists_unique_lower_mechanical_right_special at slope and intercept α and length ℓ / 2. The projections of any two right-special rotor factors of length ℓ must coincide. The letter formula reconstructs the rotor factors from their common projection and the parity of t + ℓ, so the rotor factors coincide as well. This proves uniqueness.

To identify that factor, let m = ℓ / 2, let p be the reversed length m mechanical prefix, and let u be the reversal of the rotor letters at positions 1 through ℓ. For either Boolean b, choose an occurrence of p followed by b in the mechanical word, starting at k. Set i = 2k + 2 − ℓ % 2. Then i > 0, i + ℓ is even, and (i − 1) / 2 = k. The same letter formula shows that the rotor word starting at i is u followed by the encoding of b: separator positions agree by parity, and the remaining positions agree with the reversed mechanical prefix. Taking b false and true supplies the distinct continuations 1 and 3. Thus u is right-special, including the case m = 0.

Finally take ℓ = n − 1. The assumption n ≥ 2 gives ℓ > 0. The constructed word u has length ℓ and is right-special. Uniqueness forces every right-special w of that length to equal u; conversely, equality with u gives the right-special condition. These are the two directions of the claimed equivalence.

## References

- Truth anchor: `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.IsFactor`
- Truth anchor: `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.IsRightSpecial`
- Truth anchor: `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.claim`
- Truth anchor: `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.cutting`
- Truth anchor: `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.result`
- Truth anchor: `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.rotor`
- Dependency: [D5/S1/Words/Complexity/MechanicalSubshiftIntercept](../Complexity/MechanicalSubshiftIntercept.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalDyadicBoundary](MechanicalDyadicBoundary.md)
