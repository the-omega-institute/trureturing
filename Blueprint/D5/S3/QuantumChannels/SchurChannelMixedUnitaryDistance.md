# Schur-channel mixed-unitary distance equality

## Abstract

For every Schur channel, the diamond distance to all mixed-unitary channels equals the distance to Schur mixed-unitary channels.

**Definition 1.1 (Reference amplification as a CPTP channel).**

Lean statement: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.referenceChannel`

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.referenceChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For independent finite reference, input and output types, referenceChannel lifts the canonical CPTP channel to the reference-first product system. Its linear action is referenceLinear; complete positivity follows by regrouping two finite reference factors, and trace preservation follows by summing the diagonal reference blocks.

**Theorem 1.2 (Trace contraction between different dimensions).**

Lean statement: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.trace_contract_rectangular`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.trace_contract_rectangular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any canonical CPTP channel between independent finite input and output types, the trace distance of the two output density states is at most the trace distance of the inputs. The positive and negative Jordan parts of the Hermitian input difference have preserved trace; their output trace norms are bounded by their total mass. Applied to referenceChannel, this bounds every amplified joint-state error.

**Theorem 1.3 (Bounded stabilized channel distance).**

Lean statement: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.diamond_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.diamond_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any pair of canonical channels with the same finite input and output types, the unhalved stabilized diamondDistance lies in [0,2]. Every joint output is a density state, whose unhalved trace-norm difference is at most two. The defining supremum contains zero, including when no input density state exists.

**Theorem 1.4 (Every reference-state error is bounded).**

Lean statement: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.reference_error_le_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.reference_error_le_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary independent finite reference, input and output types, referenceError is at most diamondDistance. Relabel the reference type by Fin of its cardinality; trace norm is invariant under this reindexing, and the error belongs to the bounded defining supremum set.

**Definition 1.5 (Finite convex mixtures of unitary channels).**

$$\forall (d: \mathbb{N}), \operatorname{MixedUnitary}\left(d\right) = \{Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right) \mid \exists (n: \mathbb{N}), \exists (p: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \exists (U: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (k: \operatorname{Fin}\left(n\right)), 0 \le p\left(k\right)) \land ((\sum_{k: \operatorname{Fin}\left(n\right)} p\left(k\right) = 1) \land (\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{act}\left(Psi, X\right) = \sum_{k: \operatorname{Fin}\left(n\right)} (p\left(k\right): \mathbb{C}) \cdot (\operatorname{val}\left(U\left(k\right)\right) \cdot X \cdot \operatorname{star}\left(\operatorname{val}\left(U\left(k\right)\right)\right))))\}$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.MixedUnitary` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Page 1: "So any Ψ ∈ Conv(U(H_d)) can be written as a mixture (convex combination) of unitary channels. (The number of unitary channels in the mixture can be made finite due to the Carathéodory’s theorem on convex hull)." The dimension d and mixture length n are natural numbers. The real weights p are nonnegative and sum to one. U is a family in Matrix.unitaryGroup; val exposes each matrix, star is its matrix adjoint, and act is the canonical channel action on every complex matrix X.

**Definition 1.6 (Entrywise channel action).**

$$\forall (d: \mathbb{N}), \forall (Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), \operatorname{IsSchurChannel}\left(Psi\right) \Leftrightarrow (\exists (C: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{act}\left(Psi, X\right) = \operatorname{Matrix}.\operatorname{hadamard}\left(C, X\right))$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.IsSchurChannel` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Section II, page 4: "For any S ∈ L(H_d), we can define a super-operator Φ_S via the following way:" followed by Φ_S(X) = S ◦ X, ∀X ∈ L(H_d), and "where S ◦ X = [s_kj x_kj] is the entry-wise product or Hadamard product." Here Psi already is a completely positive trace-preserving channel, and its action on every X is Matrix.hadamard C X. Complete positivity and trace preservation supply the source's matrix conditions.

**Definition 1.7 (Schur channels that are unitary mixtures).**

$$\forall (d: \mathbb{N}), \operatorname{SchurMixedUnitary}\left(d\right) = \{Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right) \mid (\operatorname{IsSchurChannel}\left(Psi\right)) \land (Psi \in \operatorname{MixedUnitary}\left(d\right))\}$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.SchurMixedUnitary` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Section V, page 8, defines Λ(H_d) = S(H_d) ∩ Conv(U(H_d)) and states: "Intuitively, Λ(H_d) (or simply Λ_d) is the set of Schur channels that are also mixtures of diagonal unitary channels. So any Ψ ∈ Λ_d can be written into the form Ψ = Σ_k p_k U_k · U_k†, where U_k are d × d diagonal unitary matrices." The displayed set requires both Schur action and membership in MixedUnitary d.

**Definition 1.8 (Diamond distance to a set of channels).**

$$\forall (d: \mathbb{N}), \forall (Phi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), \forall (S: \operatorname{Set}\left(\operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)\right)), \operatorname{distToSet}\left(Phi, S\right) = \operatorname{sInf}\left(\operatorname{Set}.\operatorname{image}\left((\operatorname{fun} (Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)) \mapsto \operatorname{FiniteDiamondDistance}.\operatorname{diamondDistance}\left(Phi, Psi\right)), S\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.distToSet` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Page 1 defines D(Phi, Conv(U(H))) as the infimum of D(Phi, Psi) over Psi in Conv(U(H)), and states: "where D(Φ, Ψ) will be given by the diamond norm of Φ − Ψ." Here S is any set of channels on Fin d. Set.image collects the unhalved FiniteDiamondDistance.diamondDistance values; sInf is the real infimum. The theorem uses nonempty sets whose values are bounded below.

**Definition 1.9 (The equality asked after Equation (8)).**

$$\operatorname{claim} \Leftrightarrow (\forall (d: \mathbb{N}), \forall (Phi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\operatorname{IsSchurChannel}\left(Phi\right)) \Rightarrow (\operatorname{distToSet}\left(Phi, \operatorname{MixedUnitary}\left(d\right)\right) = \operatorname{distToSet}\left(Phi, \operatorname{SchurMixedUnitary}\left(d\right)\right)))$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.claim` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Section V, page 9, after the proof of Theorem 3: "It seems quite likely that in Eq. (8) the first inequality should be strict and the second one should be an equality. However, this is still an unsettled issue." This proposition states the equality in the second inequality. d ranges over all natural dimensions, Phi over canonical channels on Fin d, and IsSchurChannel is the sole hypothesis. MixedUnitary represents Conv(U_d), and SchurMixedUnitary represents Λ_d. The empty dimension is included; both sets still contain the identity channel.

**Theorem 1.10 (The two diamond-distance infima are equal).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result` (`✓ std3`). ∎

*Resolves.* `Problems/yu-duan-xu-2017-schur-channel-diamond-equality` (proved) by `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yu-duan-xu-2017-schur-channel-diamond-equality","declaration_gid":"D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Copy a basis vector i to (i,i), apply the channel on the first factor while retaining the second, and recover coherently from the correlated subspace. On its complement, recovery maps (k,i) to i. These Kraus operators sum to a trace-preserving channel. The resulting superchannel fixes every Schur channel and contracts diamond distance. Each diagonal entry of a unitary is the midpoint of two unit complex phases; independent choices of those phases give a uniform family of 2^d diagonal unitaries. Thus every unitary mixture has a Schur unitary mixture at no greater distance from Phi. Set inclusion gives the opposite inequality. This proves equality of infima without requiring an attained minimum. Pointwise recovery errors need only satisfy the contraction inequality. The argument gives no closed form for the common distance. Relating positive distance to nonmembership requires compactness or closedness beyond the present theorem.

## References

- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.IsSchurChannel`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.MixedUnitary`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.SchurMixedUnitary`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.claim`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.diamond_bounds`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.distToSet`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.referenceChannel`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.reference_error_le_diamond`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.trace_contract_rectangular`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Quantum/Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Quantum/Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/CoherentCopyCorrelationTax](../Quantum/Information/CoherentCopyCorrelationTax.md)
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](../Quantum/Information/InputInformationBalance.md)
