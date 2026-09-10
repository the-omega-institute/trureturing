# Residual-Driven Projective Energy

## Abstract

The complete dual energy of the actual candidate residual bounds the projective ground error without an absolute lower eigenvalue premise.

**Theorem 1.1 (Candidate residual controls the same projective eigenvector).**

Lean statement: `D5/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy.residual_driven_projective_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy.residual_driven_projective_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedding and shifted action are linear on the same complex domain. The candidate is unit; the target is a nonzero embedded eigenvector of a real nonpositive shifted eigenvalue. Positive real-part coercivity is required on the candidate complement. A separate full dual-energy estimate concerns the actual residual M(k)-Re<k,M(k)>k, not the unknown eigenvector error.

The proof first derives nonzero candidate overlap from the eigen-equation and complement coercivity. For the exactly normalized error w, the eigen-equation gives q_M(w)=lambda*norm(w)^2-Re<w,M(k)>. Orthogonality identifies the residual pairing. Since lambda<=0, q_M(w)^2<=E*q_M(w), so 0<=q_M(w)<=E and norm(w)^2<=E/kappa. No absolute spectral lower endpoint is supplied.

The concrete same-scale Weil consumer sets M=A-U on the invariant even domain. Its fresh interval Schur checks supply the stronger even coercivity and independently enclose the residual and centered Fourier load in inverse energy, including all high modes. This closes a joint scale-interval/complex-disk ground-prolate estimate in the paper and executed numerical certificate. The Fourier/core, high-space and inverse-form Schur identifications remain paper bridges. Lean elaboration, Scribe emission and transitive axiom checking have not run; no all-scale Xi limit is asserted.

## References

- Truth anchor: `D5/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy.residual_driven_projective_energy`
