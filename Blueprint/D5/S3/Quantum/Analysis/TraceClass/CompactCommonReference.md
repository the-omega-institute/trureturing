# Entropy centers and one common reference

## Abstract

One actual continuous spectral-energy reference on a compact convex state family.

**Theorem 1.1 (A convex entropy center controls cross energy).**

$$\forall H \in CompleteComplexHilbertSpace, C \in \operatorname{Set}\left(\operatorname{TraceClass}\left(H\right)\right), gamma \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{RealConvex}\left(C\right) \land \left(\left(\operatorname{AllPositiveTraceOne}\left(C\right) \land \operatorname{AllFiniteSpectralEntropy}\left(C\right)\right) \land \left(\operatorname{Member}\left(gamma, C\right) \land \left(\operatorname{IsMaxOn}\left(realEntropy, C, gamma\right) \land \operatorname{Member}\left(rho, C\right)\right)\right)\right)\right) \Rightarrow \operatorname{spectralEnergy}\left(gamma, rho\right) \le \operatorname{spectralEntropy}\left(gamma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/CompactCommonReference.spectralEnergy_le_entropy_of_isMaxOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be any real-convex family in the genuine trace-class Banach space of a complete complex Hilbert space. Every member is an actual positive operator with real trace one and finite spectral entropy. Let gamma be an actual Reference belonging to C and maximizing realEntropy on C. Compactness is not a premise of this center theorem.

For rho in C and 0<t<1, form the actual normalized mixture tau=(1-t)gamma+t rho. Nonnegative rho-slot linearity and self energy identify (1-t)E_tau(gamma)+t E_tau(rho) with S(tau). The actual Gibbs inequality is the consequence of spectralEntropy_add_traceNorm_sq_le_energy obtained by discarding its nonnegative reward. It gives S(gamma)<=E_tau(gamma), while maximality gives S(tau)<=S(gamma).

Rewrite the finite S(gamma) as (1-t)S(gamma)+t S(gamma). Cancel the finite first summand and the strictly positive finite coefficient t in ENNReal. Thus E_tau(rho)<=S(gamma). Along t=1/(n+2), the actual trace-class mixture converges to gamma in trace norm. Reference-slot lower semicontinuity passes the bound to E_gamma(rho). Singular zero eigenspaces and noncommuting references remain in scope.

**Theorem 1.2 (A single reference in the actual compact family).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{Set}\left(\operatorname{TraceClass}\left(H\right)\right),\; \left(\operatorname{Nonempty}\left(A\right) \land \left(\operatorname{IsCompact}\left(A\right) \land \left(\operatorname{RealConvex}\left(A\right) \land \left(\left(\operatorname{AllPositiveTraceOne}\left(A\right) \land \operatorname{AllFiniteSpectralEntropy}\left(A\right)\right) \land \operatorname{ContinuousOn}\left(realEntropy, A\right)\right)\right)\right)\right) \Rightarrow \left(\exists gamma \in \operatorname{TraceClass}\left(H\right), sigma \in \operatorname{Reference}\left(H\right),\; \operatorname{Member}\left(gamma, A\right) \land \left(\operatorname{IsMaxOn}\left(realEntropy, A, gamma\right) \land \left(\operatorname{Member}\left(sigma, A\right) \land \left(\left(\forall rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{Member}\left(rho, A\right) \Rightarrow \left(\operatorname{Finite}\left(\operatorname{spectralEnergy}\left(sigma, rho\right)\right) \land \left(\operatorname{spectralEnergy}\left(sigma, rho\right) \le \operatorname{ofReal}\left(\operatorname{add}\left(\operatorname{realEntropy}\left(gamma\right), \operatorname{log}\left(2\right)\right)\right) \land \operatorname{toReal}\left(\operatorname{spectralEnergy}\left(sigma, rho\right)\right) \le \operatorname{add}\left(\operatorname{realEntropy}\left(gamma\right), \operatorname{log}\left(2\right)\right)\right)\right)\right) \land \left(\operatorname{ContinuousOn}\left(\operatorname{spectralEnergy}\left(sigma\right), A\right) \land \operatorname{ContinuousOn}\left(\operatorname{RealSpectralEnergy}\left(sigma\right), A\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/CompactCommonReference.fullCompactCommonReference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a nonempty compact real-convex set of actual positive trace-one trace-class operators. Assume its actual spectral entropy is finite and realEntropy is continuous on A. The result constructs an actual entropy maximizer gamma in A and one actual Reference sigma whose underlying trace-class operator belongs to A. For that same sigma, genuine spectralEnergy is finite and continuous on A in both ENNReal and real value, and is everywhere at most realEntropy(gamma)+log(2).

Compact attainment constructs the global maximizer. For every scale eta=2^(-m), uniform entropy continuity supplies a positive radius r with 2r below the continuity modulus. A finite open ball cover with centers in A gives nonempty closed convex cells A intersect closedBall(c,r). Genuine compact attainment supplies every local entropy center. The center theorem controls its cross energy on its entire cell. The open ball is a neighborhood relative to A, including at endpoints of a convex family.

Average the finitely many local centers at scale m to a_m in A. With c_m=(1/4)(1/2)^m, define sigma=(1/2)gamma+sum_m c_m a_m in the genuine trace-class Banach space. Norm-one states and the geometric series give trace-norm summability. The normalized residual partial sums (1-sum_(m<N)c_m)gamma+sum_(m<N)c_m a_m all belong to A and converge to sigma. Compact closedness proves sigma belongs to A. The actual closed positive cone after operatorCLM passes finite-sum order to the limit, giving gamma/2<=sigma and (c_m/N_m)gamma_mj<=sigma.

Global reference antitonicity, scaling and the global center bound give E_sigma(rho)<=S(gamma)+log(2), hence finiteness. No cover-cardinality growth estimate is used. The local weight w=c_m/N_m may be arbitrarily small.

For the local center gamma' and P=w gamma'<=sigma, orderedEnergy P sigma is lower semicontinuous in rho. On the closed cell, scaling and positive decomposition give E_gamma'(rho)-log(w)=orderedEnergy(P,sigma,rho)+E_sigma(rho), with both terms finite. The finite logarithmic constant cancels exactly between nearby states. The local entropy oscillation, Gibbs at the base state and lower semicontinuity of the ordered increment bound the upper energy jump. The real-value lower-cut argument treats negative cuts by nonnegativity, including the zero-increment branch. All neighborhoods are relative to A.

Rho-slot spectral-energy lower semicontinuity comes from the shared lowerSemicontinuousOn_spectralEnergy_state theorem in EnergySublevelCompactness, on the full cone of actual positive trace-class operators. Composition with a continuous positive-valued map restricts this theorem to the family A. Combining its finite real-value version with the upper estimate gives real continuity, then ENNReal continuity through ofReal. This is a repository synthesis of the existing genuine entropy and operator-energy APIs, not a literature novelty claim. Compactness remains an explicit input. The original Shirokov compactness-removal and full-space Hamiltonian conclusions are not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/CompactCommonReference.fullCompactCommonReference`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/CompactCommonReference.spectralEnergy_le_entropy_of_isMaxOn`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness](EnergySublevelCompactness.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity](EntropyConcavity.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy](OrderedEnergy.md)
