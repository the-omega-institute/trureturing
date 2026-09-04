# The Spectral Sharpness Negentropy Budget

## Abstract

Spectral sharpness is bounded by distance from uniform and hence by negentropy.

**Theorem 1.1 (Spectral sharpness is controlled by the entropy deficit).**

$$\begin{gathered}\forall n \in \mathbb{N}, n>0,\\r: \operatorname{Fin}(n)\to \mathbb{R}, u(i)=n^{-1},\\(\forall i, 0\le r(i)) \land \sum_ir(i)=1 \Rightarrow\\\operatorname{Sharp}(r)\le2 \operatorname{TV}(r, u) \land\ 2 \operatorname{TV}(r, u)\le\sqrt{2 (\log(n)-H(r))} \land\ \operatorname{Sharp}(u)=2 \operatorname{TV}(u, u)=\sqrt{2 (\log(n)-H(u))}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/SpectralSharpnessNegentropyBudget.spectral_sharpness_negentropy_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r be a probability spectrum on n > 0 points and let u be the uniform spectrum. Spectral sharpness is the repository's attained variational sharpness, equivalently one half of the l1 distance from r to its reversal. The theorem proves Sharp(r) <= 2 TV(r,u) <= sqrt(2(log n - H(r))).

The left inequality is the triangle inequality through the fixed point u of reversal; Equiv.sum_comp reindexes the reversed half of the sum. The right inequality is the frozen finite negentropy bound, assembled from Pinsker and the uniform entropy-divergence identity. The frozen maximum-entropy equality proves that u makes both inequalities equalities at zero, supplying the required saturation witness.

The source writes mu*(rho) and von Neumann entropy S(rho), while the available frozen interfaces expose spectralSharpness of a finite spectrum and finite Shannon entropy. The statement is therefore made at that precise spectral level. It does not assert an absent density-matrix-to-spectrum entropy bridge, forgetting-channel monotonicity, the qubit fourth-order expansion, a pure-end rank estimate, or numerical trials.

Six duplicate routes were checked before formalization: Lean keywords; notation variants including spectralSharpness, muStar, reversal distance, total variation, and entropy deficit; current accepted-event receipts; the digestion backfill by source hash; generalized fixed-point triangle and variational-duality searches; and all in-flight math lanes. The search found the two endpoint theorems but no frozen theorem composing them. The legacy Meta/Digestion/formalizations receipt directory is retired on the current branch; the accepted-event index is its current admission record.

## References

- Truth anchor: `D5/S3/TotalVariation/SpectralSharpnessNegentropyBudget.spectral_sharpness_negentropy_budget`
- Dependency: [D5/S3/Entropy/EntropyEquality](../Entropy/EntropyEquality.md)
- Dependency: [D5/S3/Quantum/Sharpness/SpectralSharpness](../Quantum/Sharpness/SpectralSharpness.md)
- Dependency: [D5/S3/TotalVariation/NegentropyBudget](NegentropyBudget.md)
