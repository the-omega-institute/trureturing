# BeamSplitter

## Abstract

The full bosonic attenuator and the coherent-state output-entropy question.

The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.

**Definition 1.1 (exponentialCoeff).**

$$\forall alpha : \mathbb{C}, (\forall n : \mathbb{N}, (\operatorname{exponentialCoeff}\left(alpha, n\right) = \frac{(alpha)^{n}}{\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(\operatorname{toReal}\left(\operatorname{factorial}\left(n\right)\right)\right)\right)}))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.2 (exponentialVector).**

$$\forall alpha : \mathbb{C}, (\operatorname{exponentialVector}\left(alpha\right) = \operatorname{lpmk}\left((n:\mathbb{N})\mapsto(\operatorname{exponentialCoeff}\left(alpha, n\right))\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

lp.mk forms the square-summable vector with the displayed coefficient function; its membership proof uses the complete exponential series. Proof fields are omitted in constructors.

**Definition 1.3 (weylVector).**

$$\forall alpha : \mathbb{C}, (\forall beta : \mathbb{C}, (\operatorname{weylVector}\left(alpha, beta\right) = \operatorname{smul}\left(\operatorname{Complexexp}\left(-(\operatorname{ComplexofReal}\left(\frac{(\left\lVert alpha \right\rVert)^{2}}{2}\right)) - (\operatorname{conj}\left(alpha\right)) \cdot (beta)\right), \operatorname{exponentialVector}\left(alpha + beta\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.weylVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The Weyl action on unnormalized exponential vectors includes its scalar phase and normalization factor.

**Definition 1.4 (displacement).**

$$\forall alpha : \mathbb{C}, (\operatorname{displacement}\left(alpha\right) = \operatorname{extendOfIsometry}\left(\operatorname{LinearEquivrefl}\left(\mathbb{C}, \operatorname{Finsupp}\left(\mathbb{C}, \mathbb{C}\right)\right), \operatorname{linearCombination}\left(\mathbb{C}, exponentialVector\right), \operatorname{linearCombination}\left(\mathbb{C}, (beta:\mathbb{C})\mapsto(\operatorname{weylVector}\left(alpha, beta\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.displacement` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

extendOfIsometry is Mathlib LinearEquiv.extendOfIsometry: the identity on finitely supported complex coefficient functions extends along the two displayed linearCombination maps. Density and equality of norms are proved in Lean; proof arguments are omitted. This specifies the global displacement on the Hilbert completion.

**Definition 1.5 (coherentCoeff).**

$$\forall alpha : \mathbb{C}, (\forall n : \mathbb{N}, (\operatorname{coherentCoeff}\left(alpha, n\right) = \frac{(\operatorname{ComplexofReal}\left(\operatorname{Realexp}\left(-(\frac{(\left\lVert alpha \right\rVert)^{2}}{2})\right)\right)) \cdot ((alpha)^{n})}{\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(\operatorname{toReal}\left(\operatorname{factorial}\left(n\right)\right)\right)\right)}))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.coherentCoeff` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.6 (coherent).**

$$\forall alpha : \mathbb{C}, (\operatorname{coherent}\left(alpha\right) = \operatorname{lpmk}\left((n:\mathbb{N})\mapsto(\operatorname{coherentCoeff}\left(alpha, n\right))\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.coherent` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

Every complex alpha gives the normalized coherent vector exp(-|alpha|^2/2) alpha^n/sqrt(n!). The infinite series proves square summability and norm one. The displayed flattened identifiers Realexp and Complexexp denote Mathlib Real.exp and Complex.exp; ComplexofReal denotes Complex.ofReal, Functionconst denotes Function.const, and lpmk denotes lp.mk. Namespace components are retained while punctuation is omitted.

**Definition 1.7 (tensor).**

$$\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\forall w : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\operatorname{tensor}\left(v, w\right) = \operatorname{lpmk}\left((n:\mathbb{N})\mapsto(\operatorname{smul}\left(w\left(n\right), v\right))\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.tensor` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The second-mode coordinate n is w(n) times the first-mode vector v. The norm and inner product are the Hilbert tensor-product ones.

**Definition 1.8 (exponentialPair).**

$$\forall z : \operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), (\operatorname{exponentialPair}\left(z\right) = \operatorname{tensor}\left(\operatorname{exponentialVector}\left(\operatorname{fst}\left(z\right)\right), \operatorname{exponentialVector}\left(\operatorname{snd}\left(z\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialPair` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.9 (rotate).**

$$\forall t : \mathbb{R}, (\forall r : \mathbb{R}, (\forall z : \operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), (\operatorname{rotate}\left(t, r, z\right) = \operatorname{pair}\left((\operatorname{ComplexofReal}\left(t\right)) \cdot (\operatorname{fst}\left(z\right)) - (\operatorname{ComplexofReal}\left(r\right)) \cdot (\operatorname{snd}\left(z\right)), (\operatorname{ComplexofReal}\left(r\right)) \cdot (\operatorname{fst}\left(z\right)) + (\operatorname{ComplexofReal}\left(t\right)) \cdot (\operatorname{snd}\left(z\right))\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.rotate` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

This real orthogonal rotation fixes the beam-splitter sign convention: creation operators give (t x+r y)^m(-r x+t y)^n.

**Definition 1.10 (beamUnitary).**

$$\forall t : \mathbb{R}, (\forall r : \mathbb{R}, (\forall h : (t)^{2} + (r)^{2} = 1, (\operatorname{beamUnitary}\left(t, r, h\right) = \operatorname{extendOfIsometry}\left(\operatorname{LinearEquivrefl}\left(\mathbb{C}, \operatorname{Finsupp}\left(\operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), \mathbb{C}\right)\right), \operatorname{linearCombination}\left(\mathbb{C}, exponentialPair\right), \operatorname{linearCombination}\left(\mathbb{C}, (z:\operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right))\mapsto(\operatorname{exponentialPair}\left(\operatorname{rotate}\left(t, r, z\right)\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamUnitary` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The global unitary is the dense isometric extension of the rotation on exponential vectors. extendOfIsometry has the same convention as in displacement; its density and norm-equality proof arguments are omitted.

**Definition 1.11 (beamSplitter).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\operatorname{beamSplitter}\left(eta, hEta\right) = \operatorname{beamUnitary}\left(\operatorname{sqrt}\left(eta\right), \operatorname{sqrt}\left(1 - eta\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamSplitter` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

Transmissivity lies in [0,1]. The coefficients are t=sqrt(eta), r=sqrt(1-eta); the unnamed proof argument of beamUnitary, derived from hEta, is omitted under the existing proof-argument convention.

**Definition 1.12 (fockPair).**

$$\forall m : \mathbb{N}, (\forall n : \mathbb{N}, (\operatorname{fockPair}\left(m, n\right) = \operatorname{tensor}\left(\operatorname{lpsingle}\left(2, m, \operatorname{ComplexofReal}\left(1\right)\right), \operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.fockPair` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.13 (fockExpansion).**

$$\forall t : \mathbb{R}, (\forall r : \mathbb{R}, (\forall m : \mathbb{N}, (\forall n : \mathbb{N}, (\operatorname{fockExpansion}\left(t, r, m, n\right) = \sum_{i:\operatorname{Fin}\left(m + 1\right)}(\sum_{j:\operatorname{Fin}\left(n + 1\right)}(\operatorname{smul}\left(\operatorname{ComplexofReal}\left(\frac{(((((((\operatorname{toReal}\left(\operatorname{choose}\left(m, \operatorname{val}\left(i\right)\right)\right)) \cdot (\operatorname{toReal}\left(\operatorname{choose}\left(n, \operatorname{val}\left(j\right)\right)\right))) \cdot ((t)^{\operatorname{val}\left(i\right)})) \cdot ((r)^{\operatorname{NatSub}\left(m, \operatorname{val}\left(i\right)\right)})) \cdot ((-(r))^{\operatorname{val}\left(j\right)})) \cdot ((t)^{\operatorname{NatSub}\left(n, \operatorname{val}\left(j\right)\right)})) \cdot (\operatorname{sqrt}\left(\operatorname{toReal}\left(\operatorname{factorial}\left(\operatorname{val}\left(i\right) + \operatorname{val}\left(j\right)\right)\right)\right))) \cdot (\operatorname{sqrt}\left(\operatorname{toReal}\left(\operatorname{factorial}\left(\operatorname{NatSub}\left(m, \operatorname{val}\left(i\right)\right) + \operatorname{NatSub}\left(n, \operatorname{val}\left(j\right)\right)\right)\right)\right))}{(\operatorname{sqrt}\left(\operatorname{toReal}\left(\operatorname{factorial}\left(m\right)\right)\right)) \cdot (\operatorname{sqrt}\left(\operatorname{toReal}\left(\operatorname{factorial}\left(n\right)\right)\right))}\right), \operatorname{fockPair}\left(\operatorname{val}\left(i\right) + \operatorname{val}\left(j\right), \operatorname{NatSub}\left(m, \operatorname{val}\left(i\right)\right) + \operatorname{NatSub}\left(n, \operatorname{val}\left(j\right)\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.fockExpansion` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The two finite sums are the binomial expansion with factorial normalization. val is the natural value of a Fin index; NatSub is truncated natural subtraction. Every term has total occupation m+n.

**Theorem 1.14 (beamUnitary_fock).**

$$\forall t : \mathbb{R}, (\forall r : \mathbb{R}, (\forall h : (t)^{2} + (r)^{2} = 1, (\forall m : \mathbb{N}, (\forall n : \mathbb{N}, (\operatorname{beamUnitary}\left(t, r, h, \operatorname{fockPair}\left(m, n\right)\right) = \operatorname{fockExpansion}\left(t, r, m, n\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamUnitary_fock` (`✓ std3`). ∎

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The global unitary has this Fock action for every pair of natural occupations. Comparing against the total exponential family identifies the finite binomial expansion.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamSplitter`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamUnitary`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.beamUnitary_fock`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.coherent`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.coherentCoeff`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.displacement`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialPair`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.fockExpansion`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.fockPair`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.rotate`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.tensor`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.weylVector`
