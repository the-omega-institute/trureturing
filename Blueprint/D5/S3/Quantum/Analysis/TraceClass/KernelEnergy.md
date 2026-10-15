# Zero spectral fibers and actual support

## Abstract

Kernel projection mass and singular logarithmic energy.

**Theorem 1.1 (Actual projection action).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, Complex, H\right), s \in \operatorname{Function}\left(w, Real\right), i \in w,\; \operatorname{EigenbasisEquation}\left(T, b, s\right) \Rightarrow \operatorname{apply}\left(\operatorname{kernelProjection}\left(T\right), \operatorname{apply}\left(b, i\right)\right) = \operatorname{ifThenElse}\left(\operatorname{apply}\left(s, i\right) = 0, \operatorname{apply}\left(b, i\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.kernelProjection_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

kernelProjection(T) is the genuine bounded orthogonal projection onto the actual closed kernel of T. On a zero eigenvector it is identity. A nonzero eigenvector is perpendicular to the kernel: self-adjointness moves T across the inner product and its nonzero eigenvalue forces that inner product to vanish. The projection is therefore zero on every nonzero eigenfiber. This argument retains the whole zero eigenspace of a full native basis.

**Theorem 1.2 (Actual zero-fiber trace mass).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, Complex, H\right), s \in \operatorname{Function}\left(w, Real\right), rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{EigenbasisEquation}\left(T, b, s\right) \Rightarrow \operatorname{HasSum}\left(\operatorname{zeroFiberDiagonal}\left(b, s, rho\right), \operatorname{kernelMass}\left(T, rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.kernelMass_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

kernelMass(T,rho) is Re Tr(kernelProjection(T) rho). The product is trace class. The unconditional basis trace theorem and the continuous real-part map give genuine summability. Self-adjointness of the orthogonal projection moves it across each inner product; its actual eigenvector action identifies the diagonal with the original rho diagonal on zero fibers and zero elsewhere. Thus the displayed HasSum has the actual bounded projection trace as its value.

**Theorem 1.3 (Positive kernel mass forces infinity).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{Nonnegative}\left(rho\right) \land \operatorname{Positive}\left(\operatorname{kernelMass}\left(T, rho\right)\right)\right) \Rightarrow \operatorname{spectralEnergy}\left(T, rho\right) = Infinity$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.spectralEnergy_eq_top_of_kernelMass_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For positive trace-class rho, strictly positive actual kernel-projection mass implies some zero-fiber diagonal is positive. That term in the nonnegative singular spectral series is infinity, so the same spectralEnergy is infinity. A zero diagonal times the infinite logarithmic coefficient remains zero.

**Theorem 1.4 (Finite energy forces actual kernel inclusion).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{Nonnegative}\left(rho\right) \land \operatorname{Finite}\left(\operatorname{spectralEnergy}\left(T, rho\right)\right)\right) \Rightarrow \operatorname{ker}\left(\operatorname{operator}\left(T\right)\right) \le \operatorname{ker}\left(\operatorname{operator}\left(rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.ker_le_ker_of_spectralEnergy_lt_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

If spectralEnergy(T,rho) is finite, every zero-fiber rho diagonal must vanish. Positivity gives Re inner(v,rho v)=norm(sqrt(rho)v)^2. Hence rho annihilates every zero eigenvector. The operator rho kernelProjection(T) annihilates every vector of the full basis, so basis density makes it the zero continuous operator. The projection is identity on ker T, which proves ker T is contained in ker rho. The reverse implication is not asserted: support inclusion alone need not give finite energy.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.ker_le_ker_of_spectralEnergy_lt_top`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.kernelMass_hasSum`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.kernelProjection_eigenvector`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/KernelEnergy.spectralEnergy_eq_top_of_kernelMass_pos`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy](SpectralEnergy.md)
