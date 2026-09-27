# Haar Measures of Converging Torus Subgroups

## Abstract

Normalized Haar probabilities on closed finite-torus subgroups vary weakly continuously with the Hausdorff distance.

**Definition 1.1 (The ambient Haar probability).**

$$\forall I \in \operatorname{FiniteTypes},\; \forall H \in \operatorname{ClosedSubgroups}\left(\operatorname{Circle}^{I}\right),\; \mu_{H} = (\iota_{H})_{*} m_{H} \land m_{H}(H) = 1$$

*Formalization.* `D5/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity.ambientHaar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let I be any finite index type and let T be the product of copies of the unit complex circle indexed by I. For each closed subgroup H of T, use the Borel sigma algebra on H and its Haar measure mH, normalized on the whole compact group H so that mH(H)=1. The inclusion iotaH from H into T is continuous. Its pushforward is the Borel probability muH on the same ambient torus T. Thus the normalization belongs to Haar measure on H, including when H is a proper subgroup of T.

**Theorem 1.2 (Hausdorff convergence implies weak convergence).**

$$\forall I \in \operatorname{FiniteTypes},\; \forall K \in \mathbb{N} \to \operatorname{ClosedSubgroups}\left(\operatorname{Circle}^{I}\right),\; \forall H \in \operatorname{ClosedSubgroups}\left(\operatorname{Circle}^{I}\right),\; \lim_{n \to \infty} \operatorname{HausdorffDistance}\left(K_{n}, H\right) = 0 \Rightarrow \mu_{K_{n}} \longrightarrow \mu_{H}\quad(n \to \infty)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite I, every sequence Hn of closed subgroups of T, and every closed subgroup H of T, Hausdorff-distance convergence of Hn to H implies convergence of muHn to muH in the weak topology of Borel probability measures on T. Equivalently, the integrals of every continuous complex-valued function on T converge. No positive dimension, connectedness, ambient density, subgroup containment, or eventual stabilization is required. Finite subgroups, proper subgroups, disconnected subgroups, and the empty product all lie in the quantified domain.

Consider a continuous character of T. If it equals one on H, uniform continuity and Hausdorff approximation make it uniformly close to one on Hn, so its Haar integrals tend to one. If it is nontrivial on H, choose a point where its value differs from one. Nearby points of Hn eventually have the same nontriviality property. Translation invariance then forces the character integral to vanish on each such subgroup and on H.

Coordinatewise circle homeomorphisms identify these characters with the multivariate Fourier monomials on the additive unit torus. Their complex linear span is dense among continuous functions. Integration against a probability has norm at most one, so convergence extends from that span to every continuous observable. This is weak convergence of the actual inclusion pushforwards.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity.ambientHaar`
- Truth anchor: `D5/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity.result`
