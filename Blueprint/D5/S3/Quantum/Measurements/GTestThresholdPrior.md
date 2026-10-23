# The threshold prior of the G-test

## Abstract

The G-test has larger Bayesian success probability than the always-unequal test exactly above the prior O/(M+O), where M counts words in a symmetric-group orbit and O counts its G-orbits.

**Definition 1.1 (Vectors indexed by words).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{TensorVec}\left(n, d\right) = (\operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right) \to \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.TensorVec` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The tensor coordinates in Section 4.1.1 are words of length n on the alphabet Fin d. A vector assigns a complex amplitude to each word.

**Definition 1.2 (Matrices indexed by words).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{TensorMat}\left(n, d\right) = \operatorname{Matrix}\left(\operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right), \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.TensorMat` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

Operators on the tensor coordinates have a row and a column for each word.

**Definition 1.3 (Words with the same multiplicities).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \operatorname{WordOrbit}\left(w\right) = \operatorname{Subtype}\left((\lambda (x : \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right)) \mapsto x \in \operatorname{MulAction.orbit}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right), w\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.WordOrbit` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The symmetric group permutes positions. Its orbit consists of the words with the same symbol multiplicities as w, corresponding to the multiplicity sector of Eqs. (11) and (12).

**Definition 1.4 (The map from permutations to words).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \forall pi \in \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{orbitMap}\left(w, pi\right) = \operatorname{Set.rangeFactorization}\left((\lambda (sigma : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{SMul.smul}\left(sigma, w\right)), pi\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.orbitMap` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

A permutation is sent to its action on w, regarded as an element of the orbit. The position action uses the inverse permutation on coordinates.

**Definition 1.5 (The number of words in the sector).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \operatorname{M}\left(w\right) = \operatorname{Fintype.card}\left(\operatorname{WordOrbit}\left(w\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.M` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

This finite cardinality is the multinomial coefficient of the multiplicities in w.

**Definition 1.6 (The number of subgroup orbits).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \operatorname{O}\left(G, w\right) = \operatorname{Fintype.card}\left(\operatorname{MulAction.orbitRel.Quotient}\left(G, \operatorname{WordOrbit}\left(w\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.O` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

Restricting the position action to G partitions the same word sector into G-orbits. The quotient counts those orbits.

**Definition 1.7 (The permutation representation).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (\operatorname{psi} : (\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right) \to^{*} \operatorname{TensorMat}\left(n, d\right))) = \operatorname{MonoidHom.comp}\left(\operatorname{Matrix.permMatrixHom}\left((n := \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right)), (R := \mathbb{C})\right), \operatorname{MulAction.toPermHom}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.psi` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The position action induces a permutation of the word basis. Matrix.permMatrixHom turns that permutation into its matrix, as in the representation used in Eqs. (12) and (62).

**Definition 1.8 (A word basis vector).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \operatorname{ket}\left(w\right) = \operatorname{Pi.single}\left(w, 1\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.ket` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The ket has amplitude one at w and zero at every other word, as for the basis vector in Eq. (11).

**Definition 1.9 (The common tensor power).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{tensorPower}\left(n, A\right) = \operatorname{ProductPrefixRigidity.productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(d\right)\right), \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), A\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.tensorPower` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The same local matrix acts at each of the n positions. This is the tensor power in Eqs. (11) and (13).

**Definition 1.10 (A repeated pure vector).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall phi \in (\operatorname{Fin}\left(d\right) \to \mathbb{C}),\; \operatorname{repeatKet}\left(n, phi\right) = (\lambda (x : \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right)) \mapsto \operatorname{ProductPrefixRigidity.productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Unit}\right), \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (\lambda (a : \operatorname{Fin}\left(d\right)) \mapsto \operatorname{Function.const}\left(\operatorname{Unit}, phi\left(a\right)\right))\right)\right)\left(x, \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Unit.unit}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.repeatKet` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The amplitude at a word is the product of its n single-particle amplitudes. Empty products have value one.

**Definition 1.11 (The equal-input pure state).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall phi \in (\operatorname{Fin}\left(d\right) \to \mathbb{C}),\; \operatorname{equalState}\left(n, phi\right) = \operatorname{PureStateHandshake.rankOneDensity}\left(\operatorname{repeatKet}\left(n, phi\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.equalState` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The rank-one matrix of the repeated vector is a pure equal-input state, before the Haar average in Eq. (13).

**Definition 1.12 (The subgroup average).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{PiG}\left(G\right) = \operatorname{Finset.expect}\left(\operatorname{Finset.univ}, (\lambda (g : G) \mapsto \operatorname{psi}\left((d := d), (g : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.PiG` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

Equations (61) and (62) use the average of the permutation matrices over G as the equal-outcome operator. Finset.expect is the finite average over the full subgroup.

**Definition 1.13 (The permuted unequal-input state).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \forall U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{rhoTilde}\left(w, U\right) = let T := \operatorname{tensorPower}\left(n, (U : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right); \operatorname{Finset.expect}\left(\operatorname{Finset.univ}, (\lambda (pi : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{psi}\left((d := d), pi\right) \cdot (T \cdot \operatorname{PureStateHandshake.rankOneDensity}\left(\operatorname{ket}\left(w\right)\right) \cdot \operatorname{Matrix.conjTranspose}\left(T\right)) \cdot \operatorname{psi}\left((d := d), pi^{-1}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.rhoTilde` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

For a fixed unitary U, Eq. (12) averages the conjugates of the word state after the common tensor unitary. The Haar average in Eq. (11) is taken only after these fixed-unitary states are formed.

**Definition 1.14 (Acceptance of equal inputs).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall phi \in (\operatorname{Fin}\left(d\right) \to \mathbb{C}),\; \operatorname{completeness}\left(G, phi\right) = \operatorname{RHLinalg.rtrace}\left(\operatorname{PiG}\left(G\right) \cdot \operatorname{equalState}\left(n, phi\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.completeness` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The real trace of the equal-outcome operator against the equal-input state is the completeness probability of Eq. (63), for a normalized vector.

**Definition 1.15 (Acceptance of unequal inputs).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \forall U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{soundnessError}\left(G, w, U\right) = \operatorname{RHLinalg.rtrace}\left(\operatorname{PiG}\left(G\right) \cdot \operatorname{rhoTilde}\left(w, U\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.soundnessError` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The real trace against the permuted unequal-input state is the soundness error appearing in Eqs. (64) and (65).

**Definition 1.16 (Rejection of unequal inputs).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \forall U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{soundness}\left(G, w, U\right) = \operatorname{UnifiedPinchingFee.doorGap}\left(\operatorname{soundnessError}\left(G, w, U\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.soundness` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

UnifiedPinchingFee.doorGap subtracts the soundness error from one, giving the soundness probability of Eq. (65).

**Definition 1.17 (Bayesian success of the G-test).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \forall U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall phi \in (\operatorname{Fin}\left(d\right) \to \mathbb{C}),\; \forall p \in \mathbb{R},\; \left(\operatorname{P}_{G}\right)\left(G, w, U, phi, p\right) = \operatorname{AffineMap.lineMap}\left(\operatorname{soundness}\left(G, w, U\right), \operatorname{completeness}\left(G, phi\right), p\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.P_G` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The prior p weights equal inputs. AffineMap.lineMap interpolates from soundness at p = 0 to completeness at p = 1, as in the Bayesian comparison of Section 4.1.

**Definition 1.18 (Bayesian success of the always-unequal test).**

$$\forall p \in \mathbb{R},\; \left(\operatorname{P}_{T}\right)\left(p\right) = \operatorname{UnifiedPinchingFee.doorGap}\left(p\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.P_T` (`✓ std3`).

*Citation.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

The test that always reports unequal succeeds with probability one minus the equal-input prior, as in Theorem 5.

**Definition 1.19 (The exact threshold and trace identity).**

$$(\operatorname{claim}) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall w \in \operatorname{OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(d\right), n\right),\; \forall U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall phi \in (\operatorname{Fin}\left(d\right) \to \mathbb{C}),\; \forall p \in \mathbb{R},\; (\exists i \in \operatorname{Fin}\left(n\right),\; \exists j \in \operatorname{Fin}\left(n\right),\; w\left(i\right) \ne w\left(j\right)) \Rightarrow ((\operatorname{dotProduct}\left(\operatorname{star}\left(phi\right), phi\right) = (1 : \mathbb{C})) \Rightarrow ((p \in \operatorname{Set.Icc}\left((0 : \mathbb{R}), 1\right)) \Rightarrow ((((\left(\operatorname{P}_{G}\right)\left(G, w, U, phi, p\right) > \left(\operatorname{P}_{T}\right)\left(p\right)) \Leftrightarrow (p > \frac{(\operatorname{O}\left(G, w\right) : \mathbb{R})}{(\operatorname{M}\left(w\right) : \mathbb{R}) + (\operatorname{O}\left(G, w\right) : \mathbb{R})})) \land ((\left(\operatorname{P}_{G}\right)\left(G, w, U, phi, p\right) = \left(\operatorname{P}_{T}\right)\left(p\right)) \Leftrightarrow (p = \frac{(\operatorname{O}\left(G, w\right) : \mathbb{R})}{(\operatorname{M}\left(w\right) : \mathbb{R}) + (\operatorname{O}\left(G, w\right) : \mathbb{R})}))) \land (\operatorname{Matrix.trace}\left(\operatorname{PiG}\left(G\right) \cdot \operatorname{rhoTilde}\left(w, U\right)\right) = \frac{(\operatorname{O}\left(G, w\right) : \mathbb{C})}{(\operatorname{M}\left(w\right) : \mathbb{C})})))))$$

*Formalization.* `D5/S3/Quantum/Measurements/GTestThresholdPrior.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

Section 6 asks for the prior below which the trivial test outperforms the G-test. For a nonconstant word, a normalized equal-input vector and p in Set.Icc 0 1, the threshold is O/(M+O), with equality exactly at that prior. The Haar integral of Eq. (11) is replaced by every fixed unitary because the traces tested do not depend on U. The comparison is between these two tests.

**Theorem 1.20 (The orbit ratio determines the threshold).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/GTestThresholdPrior.result` (`✓ std3`). ∎

*Resolves.* `Problems/buhrman-grinko-verduyn-lunel-weggemans-2026-g-test-threshold-prior` (proved) by `D5/S3/Quantum/Measurements/GTestThresholdPrior.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"buhrman-grinko-verduyn-lunel-weggemans-2026-g-test-threshold-prior","declaration_gid":"D5/S3/Quantum/Measurements/GTestThresholdPrior.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans (2026). *Permutation tests for quantum state identity*. URL: <https://arxiv.org/abs/2405.09626v2>.

*Commentary.*

On a word, the diagonal of PiG is the stabilizer cardinality divided by the subgroup cardinality. Commutation with the common tensor unitary removes U from the tested trace. The symmetric-group average is uniform on the word orbit; Burnside's lemma makes the sum of stabilizer cardinalities over the word orbit equal to O times the subgroup cardinality, giving trace O/M. A repeated normalized vector is fixed by every position permutation, so completeness is one. Substitution into the Bayesian success probability reduces the strict comparison and the equality comparison to linear inequalities and identities in p, with threshold O/(M+O).

## References

- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.M`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.O`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.P_G`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.P_T`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.PiG`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.TensorMat`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.TensorVec`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.WordOrbit`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.completeness`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.equalState`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.ket`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.orbitMap`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.psi`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.repeatKet`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.result`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.rhoTilde`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.soundness`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.soundnessError`
- Truth anchor: `D5/S3/Quantum/Measurements/GTestThresholdPrior.tensorPower`
- Dependency: [D5/S3/Quantum/Measurement/ExactConditionalPreparationCost](../Measurement/ExactConditionalPreparationCost.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](../QuantumChannels/TwoPositiveTransitionTrace.md)
- Dependency: [D5/S3/QuantumBounds/NonlocalityDepthQuantumBound](../../QuantumBounds/NonlocalityDepthQuantumBound.md)
- Dependency: [D5/S3/QuantumChannels/UnifiedPinchingFee](../../QuantumChannels/UnifiedPinchingFee.md)
