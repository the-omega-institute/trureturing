# Root-spectrum increments at late starting points

## Abstract

A lower scale for arbitrarily late root-spectrum increments

**Theorem 1.1 (The logarithmic lower scale for forward increments).**

$$\mathit{RH} \Rightarrow \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\exists d \in \mathbb{R},\; 0 < d \land \left(\exists H \in \mathbb{R},\; \left(0 < H \land H < 1\right) \land \left(\forall h \in \mathbb{R},\; \left(0 < h \land h < H\right) \Rightarrow \left(\forall U \in \mathbb{R},\; \exists u \in \mathbb{R},\; U \le u \land d \cdot h \cdot \operatorname{log}\left(\frac{1}{h}\right) \le \left|\operatorname{S}\left(r, u + h\right) - \operatorname{S}\left(r, u\right)\right|\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement.root_signal_late_increment_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S(r,u) is the centered real root spectrum, with the full actual zero series counted with analytic multiplicity. The constants depend on the real root scale r. The starting point can depend on both the shift and the prescribed lower bound.

The logarithmic cusp makes the symmetric difference about zero positive at scale h log(1/h) for small positive h. The summable root coefficient majorant makes the shifted series a continuous function of the entire vector of unit phases.

The actual phase orbit returns arbitrarily late to every neighborhood of its initial vector. At such a return the continuous symmetric difference keeps a fixed fraction of its value at zero. It is the sum of one forward difference and the negative of the adjacent forward difference. At least one of their magnitudes is at least half the transported lower bound. Choose the time threshold so that both possible starts lie in the requested tail.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement.root_signal_late_increment_lower`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootSignalCusp](RHRootSignalCusp.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder](../../RHPrimeWindowRemainder.md)
