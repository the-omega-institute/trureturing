# Scalar extension and two binary bins

## Abstract

Binary bins over a characteristic-zero field carry the scalar-extended one-bin and two-bin sl₂ actions.

Let K be a field of characteristic zero. A bin of length m is indexed by the Boolean words Fin(m) → Bool. Its vector space consists of K-valued functions on these words. The function δ(w) is Pi.single(w,1), equal to one at w and zero elsewhere. Rational weights and operator coefficients are interpreted in K through the unique rational algebra map. Products of endomorphisms mean composition. Tensor products in the two-bin formulas are over K; the tensor product used for scalar extension is over the rationals.

**Definition 1.1 (Extension in delta coordinates).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall A \in \operatorname{End}\left(\mathbb{Q}, I \to \mathbb{Q}\right),\; \operatorname{extend}\left(K, A\right) = \operatorname{conjRingEquiv}\left(\operatorname{piScalarRight}\left(\mathbb{Q}, K, K, I\right)\right)\left(\operatorname{baseChangeHom}\left(\mathbb{Q}, K, I \to \mathbb{Q}\right)\left(A\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.extend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence piScalarRight sends z tensor φ to the function u ↦ φ(u)z. Conjugating baseChange by this equivalence gives an endomorphism in finite function coordinates. It sends each delta function to the rational image with every coefficient interpreted in K.

**Definition 1.2 (Extended weight multiplication).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall m \in \mathbb{N},\; \operatorname{binWeight}\left(K, m\right) = \operatorname{mulLeft}\left(K, ((w : \operatorname{Fin}\left(m\right) \to \operatorname{Bool}) \mapsto (\operatorname{weight}\left(w\right) : K))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.binWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational diagonal weight operator is extended to K. On a delta function at w it multiplies by the rational weight of w interpreted in K.

**Definition 1.3 (Extended raising).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall m \in \mathbb{N},\; \operatorname{binRaising}\left(K, m\right) = \operatorname{extend}\left(K, \operatorname{Rbin}\left(m\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.binRaising` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational raising operator has coefficient (p+1)(m−p−1) on each permitted adjacent swap. Scalar extension preserves these coefficients in K.

**Definition 1.4 (Extended lowering).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall m \in \mathbb{N},\; \operatorname{binLowering}\left(K, m\right) = \operatorname{extend}\left(K, \operatorname{Hbin}\left(m\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.binLowering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational lowering operator sums the permitted adjacent swaps with coefficient one. Its scalar extension has the same delta coefficients in K.

**Theorem 1.5 (One-bin relations and delta coefficients).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall m \in \mathbb{N},\; (\operatorname{Sl2Relations}\left(\operatorname{binWeight}\left(K, m\right), \operatorname{binRaising}\left(K, m\right), \operatorname{binLowering}\left(K, m\right)\right)) \land (\forall w \in \operatorname{Fin}\left(m\right) \to \operatorname{Bool},\; \forall u \in \operatorname{Fin}\left(m\right) \to \operatorname{Bool},\; (\operatorname{binWeight}\left(K, m\right)\left(\operatorname{PiSingle}\left(w, 1\right)\right)\left(u\right) = (\operatorname{weight}\left(u\right) : K) \cdot \operatorname{PiSingle}\left(w, 1\right)\left(u\right)) \land ((\operatorname{binRaising}\left(K, m\right)\left(\operatorname{PiSingle}\left(w, 1\right)\right)\left(u\right) = (\operatorname{Rbin}\left(m\right)\left(\operatorname{PiSingle}\left(w, 1\right)\right)\left(u\right) : K)) \land (\operatorname{binLowering}\left(K, m\right)\left(\operatorname{PiSingle}\left(w, 1\right)\right)\left(u\right) = (\operatorname{Hbin}\left(m\right)\left(\operatorname{PiSingle}\left(w, 1\right)\right)\left(u\right) : K))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.bin_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-bin triple supplies the relations for m at least two. At lengths zero and one there are no inner bonds and every weight is zero, so the action is zero. The delta identification applies to each of the three operators.

**Definition 1.6 (Two-bin weight).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{twoWeight}\left(K, m, n\right) = \operatorname{rTensor}\left(\operatorname{binWeight}\left(K, m\right), \left(\operatorname{Fin}\left(n\right) \to \operatorname{Bool}\right) \to K\right) + \operatorname{lTensor}\left(\operatorname{binWeight}\left(K, n\right), \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right) \to K\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight operator is the sum of the first-factor and second-factor weight operators.

**Definition 1.7 (Two-bin raising).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{twoRaising}\left(K, m, n\right) = \operatorname{rTensor}\left(\operatorname{binRaising}\left(K, m\right), \left(\operatorname{Fin}\left(n\right) \to \operatorname{Bool}\right) \to K\right) + \operatorname{lTensor}\left(\operatorname{binRaising}\left(K, n\right), \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right) \to K\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoRaising` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Raising acts in either bin, leaving the other factor fixed.

**Definition 1.8 (Two-bin lowering).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{twoLowering}\left(K, m, n\right) = \operatorname{rTensor}\left(\operatorname{binLowering}\left(K, m\right), \left(\operatorname{Fin}\left(n\right) \to \operatorname{Bool}\right) \to K\right) + \operatorname{lTensor}\left(\operatorname{binLowering}\left(K, n\right), \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right) \to K\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoLowering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lowering acts in either bin, leaving the other factor fixed.

**Theorem 1.9 (Two-bin relations and delta tensors).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{Sl2Relations}\left(\operatorname{twoWeight}\left(K, m, n\right), \operatorname{twoRaising}\left(K, m, n\right), \operatorname{twoLowering}\left(K, m, n\right)\right)) \land (\forall w \in \operatorname{Fin}\left(m\right) \to \operatorname{Bool},\; \forall v \in \operatorname{Fin}\left(n\right) \to \operatorname{Bool},\; (\operatorname{twoWeight}\left(K, m, n\right)\left(\operatorname{tensor}\left(\operatorname{PiSingle}\left(w, 1\right), \operatorname{PiSingle}\left(v, 1\right)\right)\right) = ((\operatorname{weight}\left(w\right) : K) + (\operatorname{weight}\left(v\right) : K)) \cdot \operatorname{tensor}\left(\operatorname{PiSingle}\left(w, 1\right), \operatorname{PiSingle}\left(v, 1\right)\right)) \land ((\operatorname{twoRaising}\left(K, m, n\right)\left(\operatorname{tensor}\left(\operatorname{PiSingle}\left(w, 1\right), \operatorname{PiSingle}\left(v, 1\right)\right)\right) = \operatorname{tensor}\left(((u : \operatorname{Fin}\left(m\right) \to \operatorname{Bool}) \mapsto (\operatorname{Rbin}\left(m\right)\left(\operatorname{PiSingle}\left(w, 1\right)\right)\left(u\right) : K)), \operatorname{PiSingle}\left(v, 1\right)\right) + \operatorname{tensor}\left(\operatorname{PiSingle}\left(w, 1\right), ((u : \operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \mapsto (\operatorname{Rbin}\left(n\right)\left(\operatorname{PiSingle}\left(v, 1\right)\right)\left(u\right) : K))\right)) \land (\operatorname{twoLowering}\left(K, m, n\right)\left(\operatorname{tensor}\left(\operatorname{PiSingle}\left(w, 1\right), \operatorname{PiSingle}\left(v, 1\right)\right)\right) = \operatorname{tensor}\left(((u : \operatorname{Fin}\left(m\right) \to \operatorname{Bool}) \mapsto (\operatorname{Hbin}\left(m\right)\left(\operatorname{PiSingle}\left(w, 1\right)\right)\left(u\right) : K)), \operatorname{PiSingle}\left(v, 1\right)\right) + \operatorname{tensor}\left(\operatorname{PiSingle}\left(w, 1\right), ((u : \operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \mapsto (\operatorname{Hbin}\left(n\right)\left(\operatorname{PiSingle}\left(v, 1\right)\right)\left(u\right) : K))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.two_bin_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Operators on different tensor factors commute. Expanding each commutator therefore leaves the sum of the two one-bin commutators. Delta tensors have total weight equal to the sum of the two bin weights; raising and lowering replace either delta factor by its coefficientwise extended image.

**Definition 1.10 (The certified concrete triple).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{twoBinRepresentation}\left(K, m, n\right) = \operatorname{SubtypeMk}\left((\operatorname{twoWeight}\left(K, m, n\right), \operatorname{twoRaising}\left(K, m, n\right), \operatorname{twoLowering}\left(K, m, n\right)), \operatorname{first}\left(\operatorname{twoBinAction}\left(K, m, n\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoBinRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SubtypeMk constructs the triple with its relation certificate. The certificate is the first projection of the theorem two_bin_action, denoted twoBinAction in this defining expression. The three data components are the concrete weight, raising and lowering operators.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.binLowering`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.binRaising`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.binWeight`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.bin_action`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.extend`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoBinRepresentation`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoLowering`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoRaising`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.twoWeight`
- Truth anchor: `D5/S3/Quantum/SpinChains/BinaryBinBaseChange.two_bin_action`
- Dependency: [D5/S3/Quantum/SpinChains/HypereclecticNonShortening](HypereclecticNonShortening.md)
