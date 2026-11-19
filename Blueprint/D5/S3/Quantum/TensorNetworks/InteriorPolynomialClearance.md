# Exact division-free native interior clearance

## Abstract

Exact division-free native interior clearance

**Theorem 1.1 (The two full native numerator recurrences).**

$$\forall s \in Sector,\; \forall z \in Complex,\; \forall p \in Nat,\; \forall q \in Nat,\; \forall P \in Bond,\; \forall H \in Bond,\; ((Regular\left(s\right)) \land (z \neq 0)) \Rightarrow ((leftNumerator\left(s, z, p, P\right) = smul\left(ofReal\left(Gamma\left(s\right) \cdot normSq\left(z\right)\right)^{p}, trialLeft\left(s, p, P, z\right)\right)) \land (rightNumerator\left(s, z, q, H\right) = smul\left(ofReal\left(Gamma\left(s\right) \cdot normSq\left(z\right)\right)^{q} \cdot ofReal\left(d\left(s\right)^{2} \cdot normSq\left(z\right)^{2}\right), trialRight\left(s, q, H, z\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance.numerator_clear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Put J=adj(G), with rows (beta z,-z),(-alpha,1). With A=1+lambda conjugate(lambda), B=1+mu conjugate(mu), e=1+conjugate(lambda)mu and f=conjugate(e), use W=[[Bef,ABe],[ABf,Aef]] and Wstar=transpose(W). The left step is Wstar entrywise times J dagger X J; the right step is J(W entrywise X)J dagger. The right seed is J squared H (J squared) dagger, so neither central inverse-square factor is lost. Universal natural-number induction gives the exact native trialLeft and trialRight scalar identities.

**Theorem 1.2 (Exact real row factors).**

$$\forall s \in Sector,\; \forall z \in Complex,\; \forall p \in Nat,\; \forall q \in Nat,\; \forall P \in Bond,\; \forall H \in Bond,\; ((Regular\left(s\right)) \land (z \neq 0)) \Rightarrow ((re\left(det\left(leftNumerator\left(s, z, p, P\right)\right)\right) = cL\left(s, p, z\right) \cdot re\left(residual\left(s, p, q, P, H, z\right)\right)) \land (re\left(det\left(rightNumerator\left(s, z, q, H\right)\right)\right) = cR\left(s, q, z\right) \cdot im\left(residual\left(s, p, q, P, H, z\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance.determinant_clear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For d=normSq(delta), a0=1+normSq(lambda), a1=1+normSq(mu), kappa=normSq(1+conjugate(lambda)mu) and Gamma=d a0 a1 kappa, put t=normSq(z). The determinant factors are exactly cL=Gamma^(2p)t^(2p) and cR=Gamma^(2q)d^4 t^(2q+4). At every nonzero trial point in a regular sector, the cleared determinants are cL Re(residual) and cR Im(residual). Targets are arbitrary fixed matrices in this algebraic theorem.

**Theorem 1.3 (Strictly positive clearing factors).**

$$\forall s \in Sector,\; \forall z \in Complex,\; \forall p \in Nat,\; \forall q \in Nat,\; ((Regular\left(s\right)) \land (z \neq 0)) \Rightarrow ((0 < cL\left(s, p, z\right)) \land (0 < cR\left(s, q, z\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance.clearance_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Regularity makes d and kappa strictly positive; a0 and a1 are always strictly positive. Nonzero trial z gives t positive. Every displayed row factor is therefore strictly positive for every natural exterior length. This asserts no positivity preservation by inverse transfer.

These are parameter-locus statements for finite native unnormalized MPS observations. Canonical chart dominance, genericity on actual full-state or actual raw-density images, and the full Critch-Morton C9 problem remain separate obligations. No solved-open-problem credit, clock, dynamics, energy, positive physical inverse or thermodynamic cost follows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance.clearance_positive`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance.determinant_clear`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance.numerator_clear`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization](OpenBoundaryMPSInteriorRootRealization.md)
