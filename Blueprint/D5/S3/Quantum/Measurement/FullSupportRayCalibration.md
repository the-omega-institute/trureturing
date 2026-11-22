# Support-sensitive calibration of a branch coefficient map

## Abstract

A calibration on a basis and a single full-support input determines a branch coefficient map up to one scalar relative to an injective reference.

**Theorem 1.1 (Which diagonal coefficients an additional input identifies).**

$$\mathrm{Field}(K)\land \mathrm{Finite}(I)\land \mathrm{Basis}(b,V)\land T,J\in \mathrm{Hom}(V,W)_{K}\land \mathrm{Injective}(J)\land (\forall i\in I, Tb_{i}=a_{i}Jb_{i}) \Rightarrow (Tu=cJu\iff \forall i\in \mathrm{supp}(u), a_{i}=c) \land (\mathrm{supp}(u)=I\Rightarrow (Tu=cJu\iff T=cJ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FullSupportRayCalibration.support_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be an injective linear reference map between vector spaces over a field. For a finite input basis, suppose T sends each basis vector to a scalar aᵢ times its J-image. The extra test T(u)=cJ(u) holds exactly when aᵢ=c at every nonzero coordinate of u. If all coordinates of u are nonzero, passing the test is equivalent to T=cJ on the whole input.

Expand u in the basis, push both linear maps through the finite sum, and cancel the injective J. The resulting coordinate equations are uᵢaᵢ=uᵢc. In the quantum application, J includes an outcome subspace in the output Hilbert space. Suppose the unnormalized positive branch output for each probe v is supported on the line spanned by Jv. For any w perpendicular to Jv, its quadratic form is the sum over Kraus operators A of the nonnegative numbers |⟨w,Av⟩|². This sum is zero, hence each Av belongs to the line spanned by Jv. Zero-probability Kraus contributions are included. Applying the algebraic theorem to each restricted A at the basis and the extra probe makes that A a scalar multiple of J.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FullSupportRayCalibration.support_calibration`
