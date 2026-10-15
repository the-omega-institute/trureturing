# Full spectral energy, self entropy and domination

## Abstract

Singular logarithmic energy from complete trace-class spectral data.

**Theorem 1.1 (Actual series and bounded trace regularization).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, Complex, H\right), s \in \operatorname{Function}\left(w, Real\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{Nonnegative}\left(s\right) \land \left(\operatorname{EigenbasisEquation}\left(T, b, s\right) \land \operatorname{Nonnegative}\left(rho\right)\right)\right) \Rightarrow \operatorname{spectralSeries}\left(b, s, rho\right) = \operatorname{regularizedSupremum}\left(T, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralSeries_eq_regularizedSupremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

Let T be a positive trace-class contraction on an arbitrary complete complex Hilbert space. A complete orthonormal eigenbasis b has real nonnegative eigenvalues s. The native spectral theorem supplies such a full basis, retaining the whole zero eigenspace. No separability, finite dimension, countable full index or positive spectral gap is assumed. For positive trace-class rho, the weights are the actual real diagonals Re inner(b(i),rho b(i)). Their unconditional sum is the real trace of rho, with genuine summability supplied by the trace-class diagonal theorem.

Set ell(0)=infinity and ell(t)=ofReal(-log t) for nonzero t. The explicit spectral series is the nonnegative sum of ofReal(diagonal(i))*ell(s(i)). Every eigenvalue lies in [0,1], as follows from the actual operator contraction. The value zero times infinity is zero, so a zero weight on a zero eigenvector contributes zero.

For epsilon>0, CFC eigenvector action identifies B_epsilon(T)b(i) with [log(1+epsilon)-log(s(i)+epsilon)]b(i). Self-adjointness moves this operator across the inner product. The product B_epsilon(T)rho is genuinely trace class; its unconditional complex diagonal is summable and its sum is the actual bounded trace pairing. Mapping by the continuous real-part map yields the required summable real weighted series before conversion to ENNReal.

On epsilon_n=1/(n+1), the scalar regularizations increase to ell(t). At t=0 the real value is log(n+2), which tends to infinity; at t=1 it is zero. Finite nonnegative sums commute with synchronized increasing suprema; the finite-subset characterization of an arbitrary ENNReal sum then interchanges that sum and supremum. This proves equality with the same regularizedSupremum already defined by actual operator trace pairings.

**Theorem 1.2 (Independence of the full spectral basis).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, Complex, H\right), s \in \operatorname{Function}\left(w, Real\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{Nonnegative}\left(s\right) \land \left(\operatorname{EigenbasisEquation}\left(T, b, s\right) \land \operatorname{Nonnegative}\left(rho\right)\right)\right) \Rightarrow \operatorname{spectralSeries}\left(b, s, rho\right) = \operatorname{spectralEnergy}\left(T, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralSeries_eq_spectralEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

nativeResolution is chosen from the actual positive trace-class spectral theorem. spectralEnergy is the explicit eigenvalue series on that supplied basis. Any other full eigenbasis yields the same value because both series equal the actual operator supremum. The choice carries spectral equations only; no energy identity is included as an assumed field.

**Theorem 1.3 (Finite nonnegative first-slot linearity).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right), gamma \in \operatorname{TraceClass}\left(H\right), a \in Real, c \in Real,\; \left(\operatorname{Nonnegative}\left(rho\right) \land \left(\operatorname{Nonnegative}\left(gamma\right) \land \left(\operatorname{Nonnegative}\left(a\right) \land \operatorname{Nonnegative}\left(c\right)\right)\right)\right) \Rightarrow \operatorname{spectralEnergy}\left(T, \operatorname{add}\left(\operatorname{complexSmul}\left(a, rho\right), \operatorname{complexSmul}\left(c, gamma\right)\right)\right) = \operatorname{add}\left(\operatorname{multiply}\left(\operatorname{ofReal}\left(a\right), \operatorname{spectralEnergy}\left(T, rho\right)\right), \operatorname{multiply}\left(\operatorname{ofReal}\left(c\right), \operatorname{spectralEnergy}\left(T, gamma\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_nonneg_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

The identified singular series inherits the actual trace pairing's arbitrary two-term nonnegative linearity. Both coefficients may vanish and either energy may be infinite. This formula asserts no countable first-slot decomposition theorem.

**Theorem 1.4 (Scaling and actual trace mass).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right), w \in Real,\; \left(\operatorname{Nonnegative}\left(rho\right) \land \left(\operatorname{Positive}\left(w\right) \land w \le 1\right)\right) \Rightarrow \operatorname{spectralEnergy}\left(\operatorname{scaleReference}\left(T, w\right), rho\right) = \operatorname{add}\left(\operatorname{spectralEnergy}\left(T, rho\right), \operatorname{multiply}\left(\operatorname{ofReal}\left(\operatorname{realTrace}\left(rho\right)\right), \operatorname{ofReal}\left(\operatorname{negate}\left(\operatorname{log}\left(w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_scaleReference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For w in (0,1], scaleReference multiplies the actual reference by w. The singular energy increases by Re Tr(rho) times ofReal(-log w), without normalizing rho. The proof applies the established regularization scaling theorem only after identifying the spectral series. Strictly positive shifted operators justify every logarithm scaling law.

**Theorem 1.5 (Actual spectral entropy is self energy).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{Reference}\left(H\right),\; \operatorname{spectralEnergy}\left(rho, \operatorname{traceClassValue}\left(rho\right)\right) = \operatorname{spectralEntropy}\left(rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

spectralEntropy is the separate eigenvalue series sum of ofReal(-s(i) log s(i)), with eta(0)=0. The eigenvector equation and the unit norm of each basis vector identify the self diagonal with s(i). The zero branch uses zero times infinity equals zero; the positive branch uses the actual scalar product formula. Hence self energy equals spectral entropy for every positive trace-class contraction, in particular for normalized states.

**Theorem 1.6 (Normalized noncommuting domination).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}\left(H\right), tau \in \operatorname{Reference}\left(H\right), w \in Real,\; \left(\operatorname{Nonnegative}\left(rho\right) \land \left(\operatorname{realTrace}\left(rho\right) = 1 \land \left(\operatorname{Positive}\left(w\right) \land \left(w \le 1 \land \operatorname{complexSmul}\left(w, \operatorname{operator}\left(rho\right)\right) \le \operatorname{operator}\left(tau\right)\right)\right)\right)\right) \Rightarrow \operatorname{spectralEnergy}\left(tau, rho\right) \le \operatorname{add}\left(\operatorname{spectralEntropy}\left(\operatorname{normalizedReference}\left(rho\right)\right), \operatorname{ofReal}\left(\operatorname{negate}\left(\operatorname{log}\left(w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_le_entropy_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

Let rho be an actual positive trace-one state, tau a positive trace-class contraction, and 0<w<=1. If tau dominates w rho in Loewner order, spectral energy of rho relative to tau is at most its actual spectral entropy plus ofReal(-log w). Normalization proves that rho is a contraction. Noncommuting reference order, singular reference scaling, the actual trace mass one, and the self-entropy identity give the bound. No faithfulness or commutation premise is added.

**Theorem 1.7 (Finite entropy yields finite dominated cross energy).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}\left(H\right), tau \in \operatorname{Reference}\left(H\right), w \in Real,\; \left(\left(\operatorname{Nonnegative}\left(rho\right) \land \left(\operatorname{realTrace}\left(rho\right) = 1 \land \left(\operatorname{Positive}\left(w\right) \land \left(w \le 1 \land \operatorname{complexSmul}\left(w, \operatorname{operator}\left(rho\right)\right) \le \operatorname{operator}\left(tau\right)\right)\right)\right)\right) \land \operatorname{Finite}\left(\operatorname{spectralEntropy}\left(\operatorname{normalizedReference}\left(rho\right)\right)\right)\right) \Rightarrow \operatorname{Finite}\left(\operatorname{spectralEnergy}\left(tau, rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_lt_top_of_entropy_lt_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

Under exactly the normalized domination hypotheses, finiteness of the actual spectral entropy implies finiteness of the same singular cross energy. The finite additive logarithmic constant and the ENNReal domination bound prove this, including references with nontrivial kernel.

**Theorem 1.8 (Reference trace-norm lower semicontinuity).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{Nonnegative}\left(rho\right) \Rightarrow \operatorname{LowerSemicontinuous}\left(\operatorname{spectralEnergyAt}\left(rho, \operatorname{Reference}\left(H\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.lowerSemicontinuous_spectralEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For a fixed positive trace-class rho, the actual singular spectral energy is lower semicontinuous as a function of the positive trace-class contraction reference with its trace-norm topology. This is the established regularization supremum theorem transported through the proved spectral identity. Reference order likewise reverses without commutativity. These statements supply logarithmic energy; local entropy centers, common-reference continuity and the full unbounded Hamiltonian construction require further results.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.lowerSemicontinuous_spectralEnergy`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_le_entropy_add`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_lt_top_of_entropy_lt_top`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_nonneg_linear`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_scaleReference`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralEnergy_self`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralSeries_eq_regularizedSupremum`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.spectralSeries_eq_spectralEnergy`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/LogRegularization](LogRegularization.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Spectral](Spectral.md)
