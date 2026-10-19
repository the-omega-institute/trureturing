# Schur-channel mixed-unitary distance equality

## Abstract

For every Schur channel, the diamond distance to all mixed-unitary channels equals the distance to Schur mixed-unitary channels.

**Definition 1.1 (Finite convex mixtures of unitary channels).**

$$\forall (d: \mathbb{N}), \operatorname{MixedUnitary}\left(d\right) = \{Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right) \mid \exists (n: \mathbb{N}), \exists (p: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \exists (U: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (k: \operatorname{Fin}\left(n\right)), 0 \le p\left(k\right)) \land ((\sum_{k: \operatorname{Fin}\left(n\right)} p\left(k\right) = 1) \land (\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{act}\left(Psi, X\right) = \sum_{k: \operatorname{Fin}\left(n\right)} (p\left(k\right): \mathbb{C}) \cdot (\operatorname{val}\left(U\left(k\right)\right) \cdot X \cdot \operatorname{star}\left(\operatorname{val}\left(U\left(k\right)\right)\right))))\}$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.MixedUnitary` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Page 1: "So any Ψ ∈ Conv(U(H_d)) can be written as a mixture (convex combination) of unitary channels. (The number of unitary channels in the mixture can be made finite due to the Carathéodory’s theorem on convex hull)." The dimension d and mixture length n are natural numbers. The real weights p are nonnegative and sum to one. U is a family in Matrix.unitaryGroup; val exposes each matrix, star is its matrix adjoint, and act is the canonical channel action on every complex matrix X.

**Definition 1.2 (Entrywise channel action).**

$$\forall (d: \mathbb{N}), \forall (Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), \operatorname{IsSchurChannel}\left(Psi\right) \Leftrightarrow (\exists (C: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{act}\left(Psi, X\right) = \operatorname{Matrix}.\operatorname{hadamard}\left(C, X\right))$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.IsSchurChannel` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Section II, page 4: "For any S ∈ L(H_d), we can define a super-operator Φ_S via the following way:" followed by Φ_S(X) = S ◦ X, ∀X ∈ L(H_d), and "where S ◦ X = [s_kj x_kj] is the entry-wise product or Hadamard product." Here Psi already is a completely positive trace-preserving channel, and its action on every X is Matrix.hadamard C X. Complete positivity and trace preservation supply the source's matrix conditions.

**Definition 1.3 (Schur channels that are unitary mixtures).**

$$\forall (d: \mathbb{N}), \operatorname{SchurMixedUnitary}\left(d\right) = \{Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right) \mid (\operatorname{IsSchurChannel}\left(Psi\right)) \land (Psi \in \operatorname{MixedUnitary}\left(d\right))\}$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.SchurMixedUnitary` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Section V, page 8, defines Λ(H_d) = S(H_d) ∩ Conv(U(H_d)) and states: "Intuitively, Λ(H_d) (or simply Λ_d) is the set of Schur channels that are also mixtures of diagonal unitary channels. So any Ψ ∈ Λ_d can be written into the form Ψ = Σ_k p_k U_k · U_k†, where U_k are d × d diagonal unitary matrices." The displayed set requires both Schur action and membership in MixedUnitary d.

**Definition 1.4 (Diamond distance to a set of channels).**

$$\forall (d: \mathbb{N}), \forall (Phi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), \forall (S: \operatorname{Set}\left(\operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)\right)), \operatorname{distToSet}\left(Phi, S\right) = \operatorname{sInf}\left(\operatorname{Set}.\operatorname{image}\left((\operatorname{fun} (Psi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)) \mapsto \operatorname{FiniteDiamondDistance}.\operatorname{diamondDistance}\left(Phi, Psi\right)), S\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.distToSet` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Page 1 defines D(Phi, Conv(U(H))) as the infimum of D(Phi, Psi) over Psi in Conv(U(H)), and states: "where D(Φ, Ψ) will be given by the diamond norm of Φ − Ψ." Here S is any set of channels on Fin d. Set.image collects the unhalved FiniteDiamondDistance.diamondDistance values; sInf is the real infimum. The theorem uses nonempty sets whose values are bounded below.

**Definition 1.5 (The equality asked after Equation (8)).**

$$\operatorname{claim} \Leftrightarrow (\forall (d: \mathbb{N}), \forall (Phi: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\operatorname{IsSchurChannel}\left(Phi\right)) \Rightarrow (\operatorname{distToSet}\left(Phi, \operatorname{MixedUnitary}\left(d\right)\right) = \operatorname{distToSet}\left(Phi, \operatorname{SchurMixedUnitary}\left(d\right)\right)))$$

*Formalization.* `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.claim` (`✓ std3`).

*Citation.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Section V, page 9, after the proof of Theorem 3: "It seems quite likely that in Eq. (8) the first inequality should be strict and the second one should be an equality. However, this is still an unsettled issue." This proposition states the equality in the second inequality. d ranges over all natural dimensions, Phi over canonical channels on Fin d, and IsSchurChannel is the sole hypothesis. MixedUnitary represents Conv(U_d), and SchurMixedUnitary represents Λ_d. The empty dimension is included; both sets still contain the identity channel.

**Theorem 1.6 (Trace norm is invariant under finite reindexing).**

$$\forall (a: \operatorname{Type}), \forall (b: \operatorname{Type}), [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall (e: \operatorname{Equiv}\left(a, b\right)), \forall (X: \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), \operatorname{traceNorm}\left(\operatorname{Matrix}.\operatorname{reindexAlgEquiv}\left(\mathbb{C}, \mathbb{C}, e\right)\left(X\right)\right) = \operatorname{traceNorm}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.reindex_traceNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

For finite decidable index types a and b, an equivalence e preserves the trace norm under Matrix.reindexAlgEquiv. This identity also gives the submatrix form for the inverse equivalence, and it identifies ancillary coordinates in the capacity bounds.

**Theorem 1.7 (The two diamond-distance infima are equal).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result` (`✓ std3`). ∎

*Resolves.* `Problems/yu-duan-xu-2017-schur-channel-diamond-equality` (proved) by `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yu-duan-xu-2017-schur-channel-diamond-equality","declaration_gid":"D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nengkun Yu, Runyao Duan and Quanhua Xu (2017). *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*. DOI: [10.1109/TIT.2016.2641447](https://doi.org/10.1109/TIT.2016.2641447). URL: <https://arxiv.org/abs/1201.1172>.

*Commentary.*

Copy a basis vector i to (i,i), apply the channel on the first factor while retaining the second, and recover coherently from the correlated subspace. On its complement, recovery maps (k,i) to i. These Kraus operators sum to a trace-preserving channel. The resulting superchannel fixes every Schur channel and contracts diamond distance. Each diagonal entry of a unitary is the midpoint of two unit complex phases; independent choices of those phases give a uniform family of 2^d diagonal unitaries. Thus every unitary mixture has a Schur unitary mixture at no greater distance from Phi. Set inclusion gives the opposite inequality. This proves equality of infima without requiring an attained minimum. Pointwise recovery errors need only satisfy the contraction inequality. The argument gives no closed form for the common distance. Relating positive distance to nonmembership requires compactness or closedness beyond the present theorem. The amplified contraction estimates in this proof also have a finite-window channel application. Let A, B and C be independent finite decidable coordinate types, C1:A->B and C2:B->C canonical CPTP channels, and PA, PB and PC arbitrary specified real-time CPTP families. For a,b>0 and T>=0 define e_T(C1;a) as one half of the supremum, over 0<=t<=T, of the unhalved stabilized diamondDistance between C1 comp PA(t) and PB(a*t) comp C1; use the analogous definition for the other channels. The stabilization tests every finite reference dimension and every joint density input, including correlated inputs. The existing diamond_bounds bounds the distances by two; adjoining zero defines empty windows and does not change a nonnegative-horizon supremum, since t=0 belongs to the window. Thus 0<=e_T<=1. For a common joint input rho, insert the output of C2 comp PB(a*t) comp C1 between those of C2 comp C1 comp PA(t) and PC((a*b)*t) comp C2 comp C1. The existing traceDistance_triangle splits the error. Applying trace_contract_rectangular to referenceChannel C2 bounds the first term by the first channel error on rho. For the second term use the density state obtained from rho by referenceChannel C1; reference_error_le_diamond bounds it by the stabilized error of C2 at time a*t. The two bounded time suprema, 0<=a*t<=a*T and b*(a*t)=(a*b)*t yield e_T(C2 comp C1;a*b)<=e_T(C1;a)+e_(a*T)(C2;b), with the factor one half applied to the unhalved estimates. This includes T=0 and empty coordinate types through the zero convention; no identity at time zero, maximum attainment, semigroup, continuity, generator, recovery or locality is assumed. This application uses the existing estimates; the Schur-channel equality itself requires its stated Schur hypothesis. A complete application to actual rectangular stochastic channels and stochastic evolution requires their canonical CPTP realization and the corresponding diagonal relative-entropy identification. That realization is not established here. Channel composition alone supplies no RG universality or effective dynamics, and its residual estimate does not guarantee recovery of a specified state family.

## References

- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.IsSchurChannel`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.MixedUnitary`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.SchurMixedUnitary`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.claim`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.distToSet`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.reindex_traceNorm`
- Truth anchor: `D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.result`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Quantum/Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Quantum/Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/CoherentCopyCorrelationTax](../Quantum/Information/CoherentCopyCorrelationTax.md)
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](../Quantum/Information/InputInformationBalance.md)
