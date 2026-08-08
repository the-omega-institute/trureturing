# Mellin Reconstruction of the Completed Zeta

## Abstract

Completed zeta is reconstructed from its symmetric theta-tail Mellin integral.

**Theorem 1.1 (Completed zeta is reconstructed from the symmetric theta tail).**

$$\text{Let } \theta(t)=\theta_{\mathrm{even}}(0,t),\ \omega=\frac{\theta-1}{2},\ M(s)=\int_{1}^{\infty}\omega(t)\,\left(t^{s/2}+t^{(1-s)/2}\right)\,\frac{dt}{t}.\ \text{Then } (\forall s,\ \Re s>1 \Rightarrow \Lambda(s)=\pi^{-s/2}\,\Gamma(\frac{s}{2})\,\zeta(s)) \land (\forall s,\ \Lambda(s)=M(s)-\frac{1}{s}-\frac{1}{1-s}) \land \operatorname{Differentiable}_{\mathbb{C}}(M) \land (\forall s,\ M(1-s)=M(s)) \land (\forall s,\ s\neq 0 \land s\neq 1 \Rightarrow \operatorname{DifferentiableAt}_{\mathbb{C}}(\Lambda,s)) \land \lim_{s\to 0}s\,\Lambda(s)=-1 \land \lim_{s\to 1}(s-1)\,\Lambda(s)=1 \land (\forall s,\ \xi(1-s)=\xi(s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction` (`✓ std3`). ∎

*Citation.* Mark W. Coffey (2007). *Theta and Riemann xi function representations from harmonic oscillator eigensolutions*. DOI: [10.1016/j.physleta.2006.10.055](https://doi.org/10.1016/j.physleta.2006.10.055).

*Commentary.*

With the theta kernel supplied by mathlib's even Hurwitz kernel at parameter zero, its halved tail omega, and the literal Mellin-type integral M over the ray beyond one, the theorem conjoins seven clauses: the Euler-factor identification of the completed reading on the convergence half-plane; the reconstruction identity expressing the completed reading as M minus the two simple pole terms at zero and one; entirety of M; the reflection symmetry of M under s to one minus s; differentiability of the completed reading away from the two exceptional points; the explicit residue ledger sending s times the completed reading to minus one at zero and s minus one times it to one at one; and the xi reflection equation. The integral M is stated as a genuine measure-theoretic integral rather than an alias of the pole-removed completion; the proof identifies it with that completion by splitting the modified weak-functional-equation profile at one and algebraizing the inversion substitution through the unconditional pointwise Mellin composition identities. The theorem introduces no public concept beyond its selector and supplies the reconstruction bridge between the theta tail and the pole ledger that the zero-symmetry route below O-6 consumes.

## References

- Truth anchor: `D5/S3/Analytic/CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction`
- Dependency: [D5/S3/Zeros/CompletedZeta](../Zeros/CompletedZeta.md)
