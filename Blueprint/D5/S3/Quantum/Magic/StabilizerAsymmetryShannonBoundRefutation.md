# A counterexample to the Shannon branch-and-bound lower bound

## Abstract

A three-qubit state violates the proposed Shannon entropy lower bound for stabilizer bases.

**Definition 1.1 (The strictly upper-triangular part).**

$$\forall (n: \mathbb{N}), (\forall (q: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)), ((\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.IsStrictUpper}\left(q\right)) \Leftrightarrow (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((\neg (i < j)) \to (q\left(i, j\right) = (0: \operatorname{ZMod}\left(2\right))))))))$$

*Formalization.* `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.IsStrictUpper` (`✓ std3`).

*Citation.* Poetri Sonya Tarabunga; Martina Frau; Tobias Haug; Emanuele Tirrito; Lorenzo Piroli (2025). *A nonstabilizerness monotone from stabilizerness asymmetry*. DOI: [10.1088/2058-9565/adfd0d](https://doi.org/10.1088/2058-9565/adfd0d). URL: <https://arxiv.org/abs/2411.05766v1>.

*Commentary.*

A matrix is strictly upper triangular when every entry on or below its diagonal is zero. This is the condition on the off-diagonal part Q′ in the splitting Q = Qd + Q′ of draft.tex line 769.

**Definition 1.2 (Stabilizer amplitudes).**

$$\forall (n: \mathbb{N}), (\forall (q: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)), (\forall (c: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))), (\forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))), (\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.stabAmp}\left(q, c, x\right) = \operatorname{Inv.inv}\left((\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left((2: \mathbb{R})^{n}\right)\right): \mathbb{C})\right) \cdot (-(1: \mathbb{C}))^{\operatorname{ZMod.val}\left(\operatorname{Matrix.toQuadraticForm'}\left(q, x\right)\right)} \cdot \operatorname{Complex.I}^{\sum_{i: \operatorname{Fin}\left(n\right)} (\operatorname{ZMod.val}\left(c\left(i\right)\right) \cdot \operatorname{ZMod.val}\left(x\left(i\right)\right))}))))$$

*Formalization.* `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.stabAmp` (`✓ std3`).

*Citation.* Poetri Sonya Tarabunga; Martina Frau; Tobias Haug; Emanuele Tirrito; Lorenzo Piroli (2025). *A nonstabilizerness monotone from stabilizerness asymmetry*. DOI: [10.1088/2058-9565/adfd0d](https://doi.org/10.1088/2058-9565/adfd0d). URL: <https://arxiv.org/abs/2411.05766v1>.

*Commentary.*

The amplitude is the stabilizer standard form of draft.tex lines 757–764 with k = N and R equal to the identity, so the translation quotient has one element. Its magnitude factor is the inverse square root of two to the power n. Mathlib's Matrix.toQuadraticForm' computes the quadratic exponent xᵀqx in ZMod 2, which is then represented by its natural value zero or one. The exponent of Complex.I is instead the natural-number sum of the products of the natural representatives of c i and x i; this sum is not reduced modulo two. The definition allows arbitrary q; a stabilizer basis uses Matrix.diagonal d + q with q strictly upper triangular. Mathlib's Matrix.diagonal has entries d i on the diagonal and zero elsewhere.

**Definition 1.3 (Squared stabilizer overlaps).**

$$\forall (n: \mathbb{N}), (\forall (q: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)), (\forall (c: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))), (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))) \to (\mathbb{C})), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))), (\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.overlapProb}\left(q, c, \psi, d\right) = \operatorname{Complex.normSq}\left(\sum_{x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))} (\operatorname{Star.star}\left(\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.stabAmp}\left((\operatorname{Matrix.diagonal}\left(d\right) + q), c, x\right)\right) \cdot \psi\left(x\right))\right))))))$$

*Formalization.* `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.overlapProb` (`✓ std3`).

*Citation.* Poetri Sonya Tarabunga; Martina Frau; Tobias Haug; Emanuele Tirrito; Lorenzo Piroli (2025). *A nonstabilizerness monotone from stabilizerness asymmetry*. DOI: [10.1088/2058-9565/adfd0d](https://doi.org/10.1088/2058-9565/adfd0d). URL: <https://arxiv.org/abs/2411.05766v1>.

*Commentary.*

For a fixed q, c and state ψ, the value at d is the squared complex norm of the overlap with the stabilizer amplitude whose matrix is Matrix.diagonal d + q. Complex conjugation acts on the stabilizer amplitude. This specializes the distribution p of draft.tex line 769 to k = N and R equal to the identity. The function is defined for arbitrary ψ, q and c; the unit-vector and triangular conditions enter the conjecture.

**Definition 1.4 (Squared overlaps after taking absolute amplitudes).**

$$\forall (n: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))) \to (\mathbb{C})), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))), (\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.absProb}\left(\psi, d\right) = \operatorname{Complex.normSq}\left(\sum_{x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))} (\operatorname{Star.star}\left(\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.stabAmp}\left(\operatorname{Matrix.diagonal}\left(d\right), \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (0: \operatorname{ZMod}\left(2\right))\right), x\right)\right) \cdot \operatorname{Complex.ofReal}\left(\left\lVert \psi\left(x\right) \right\rVert\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.absProb` (`✓ std3`).

*Citation.* Poetri Sonya Tarabunga; Martina Frau; Tobias Haug; Emanuele Tirrito; Lorenzo Piroli (2025). *A nonstabilizerness monotone from stabilizerness asymmetry*. DOI: [10.1088/2058-9565/adfd0d](https://doi.org/10.1088/2058-9565/adfd0d). URL: <https://arxiv.org/abs/2411.05766v1>.

*Commentary.*

Replace each state amplitude by its nonnegative real norm, included in the complex scalars, and use Matrix.diagonal d with zero c. The resulting squared overlaps specialize the distribution qR of draft.tex line 776 to R equal to the identity. Function.const denotes the zero binary vector in the displayed formula.

**Lemma 1.5 (A sum over the eight binary words).**

$$\forall (A: \operatorname{Type}*), ([\operatorname{AddCommMonoid}\left(A\right)] \forall (f: ((\operatorname{Fin}\left(3\right)) \to (\operatorname{ZMod}\left(2\right))) \to (A)), (\sum_{x: (\operatorname{Fin}\left(3\right)) \to (\operatorname{ZMod}\left(2\right))} (f\left(x\right)) = f\left(![0, 0, 0]\right) + f\left(![0, 0, 1]\right) + f\left(![0, 1, 0]\right) + f\left(![0, 1, 1]\right) + f\left(![1, 0, 0]\right) + f\left(![1, 0, 1]\right) + f\left(![1, 1, 0]\right) + f\left(![1, 1, 1]\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.sum_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any type A in any universe with an additive commutative monoid structure, the sum of f over all functions Fin 3 to ZMod 2 is the displayed eight-term sum. The coordinates are ordered 0, 1, 2, with zero before one in each coordinate.

**Definition 1.6 (The Shannon lower-bound assertion).**

$$(\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((1 \le n) \to (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))) \to (\mathbb{C})), ((\sum_{x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))} (\operatorname{Complex.normSq}\left(\psi\left(x\right)\right)) = (1: \mathbb{R})) \to (\forall (q: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)), (\forall (c: (\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(2\right))), ((\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.IsStrictUpper}\left(q\right)) \to (\operatorname{D5.S3.Entropy.MaxEntropy.shannonEntropy}\left(\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.absProb}\left(\psi\right)\right) \le \operatorname{D5.S3.Entropy.MaxEntropy.shannonEntropy}\left(\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.overlapProb}\left(q, c, \psi\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Poetri Sonya Tarabunga; Martina Frau; Tobias Haug; Emanuele Tirrito; Lorenzo Piroli (2025). *A nonstabilizerness monotone from stabilizerness asymmetry*. DOI: [10.1088/2058-9565/adfd0d](https://doi.org/10.1088/2058-9565/adfd0d). URL: <https://arxiv.org/abs/2411.05766v1>.

*Commentary.*

For every positive number of qubits and every unit complex amplitude vector, the Shannon entropy of the absolute-amplitude law is asserted to be no greater than the entropy for each strictly upper-triangular q and each binary c. Shannon entropy is the finite sum of −r log r in nats, with the summand zero at r = 0. This is the k = N, R = I specialization of the conjectured Shannon extension of equation (69): draft.tex lines 776–779 give the bound for integer Rényi index greater than one, and line 782 conjectures it for index one. A lower bound on the minimum over q and c requires the same lower bound for every such pair.

**Theorem 1.7 (The three-qubit entropy reversal).**

$$\neg (\operatorname{D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/tarabunga-frau-haug-tirrito-piroli-2025-shannon-branch-bound` (refuted) by `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tarabunga-frau-haug-tirrito-piroli-2025-shannon-branch-bound","declaration_gid":"D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Poetri Sonya Tarabunga; Martina Frau; Tobias Haug; Emanuele Tirrito; Lorenzo Piroli (2025). *A nonstabilizerness monotone from stabilizerness asymmetry*. DOI: [10.1088/2058-9565/adfd0d](https://doi.org/10.1088/2058-9565/adfd0d). URL: <https://arxiv.org/abs/2411.05766v1>.

*Commentary.*

Take n = 3 and the real vector v = (1,0,2,−1,1,0,0,1), in binary order 000,001,010,011,100,101,110,111, with coordinate zero most significant. Include v in the complex scalars and put ψ = v/√8. Enumerating the eight binary strings gives the squared norm (1 + 0 + 4 + 1 + 1 + 0 + 0 + 1)/8 = 1.

FourMUBBoundEntanglementRefutation.scale_sq gives (√8)⁻² = 1/8. Consequently, for each pair d,x of three-bit strings, the overlap summand at q = 0 and c = 0 is (−1) to the natural representative of Matrix.toQuadraticForm' (Matrix.diagonal d) x, times v x divided by eight, all in the complex scalars. The corresponding absolute-amplitude summand has |v x| in place of v x. The quadratic exponent is computed in ZMod 2 before taking its natural representative.

Splitting each coordinate of d into its two possible values and summing over the eight x gives overlapProb 0 0 ψ = (1/4,1/4,0,0,0,1/4,0,1/4), whereas absProb ψ = (9/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16), in the same binary order.

Apply OrientationEntropyBalance.sum_entropy_formula first to four counts all equal to one with total four, and then to the eight counts (9,1,1,1,1,1,1,1) with total sixteen. Expanding Real.logb and clearing the positive factor log 2 converts the formula to natural logarithms. The power identities log 4 = 2 log 2, log 16 = 4 log 2 and log (9⁹) = 18 log 3, together with the displayed distributions and the zero Shannon summands, give respectively 2 log 2 and 4 log 2 − (9/8) log 3.

The upper bound in TwoDeletionRunEntropyBounds.logb_three_bounds is logb 2 3 < 5/3. Expand Real.logb and use log 2 > 0 to obtain 9 log 3 < 15 log 2 < 16 log 2. Now apply the asserted inequality to n = 3, the unit vector ψ and the zero q and c; the zero matrix is strictly upper triangular because every entry is zero. The two entropy values would give 4 log 2 − (9/8) log 3 ≤ 2 log 2, contradicting the strict logarithmic inequality. Thus the Shannon lower bound fails already for k = N = 3 and R = I.

## References

- Truth anchor: `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.IsStrictUpper`
- Truth anchor: `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.absProb`
- Truth anchor: `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.overlapProb`
- Truth anchor: `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.result`
- Truth anchor: `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.stabAmp`
- Truth anchor: `D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.sum_bits`
- Dependency: [D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance](../../../S0/Certificates/Hypergraphs/OrientationEntropyBalance.md)
- Dependency: [D5/S3/Entropy/TwoDeletionRunEntropyBounds](../../Entropy/TwoDeletionRunEntropyBounds.md)
- Dependency: [D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation](../Entanglement/FourMUBBoundEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold](../Measurement/BiasedTrineJointMeasurabilityThreshold.md)
