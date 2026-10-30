# Constructive transport of moving logical matrix units

## Abstract

The actual noncommutative Dyson series constructs the unique solution and transports every moving logical matrix unit on a finite closed interval.

**Theorem 1.1 (Ordered integrals and complete unitary transport).**

Lean statement: `D5/S3/Quantum/Transport/MatrixUnitDyson.constructive_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/MatrixUnitDyson.constructive_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Baake; Ulrike Schlaegel (2011). *The Peano-Baker series*. DOI: [10.1134/S0081543811080098](https://doi.org/10.1134/S0081543811080098).

*Acknowledgement.* Freeman J. Dyson (1949). *The Radiation Theories of Tomonaga, Schwinger, and Feynman*. DOI: [10.1103/PhysRev.75.486](https://doi.org/10.1103/PhysRev.75.486).

*Acknowledgement.* Tosio Kato (1950). *On the Adiabatic Theorem of Quantum Mechanics*. DOI: [10.1143/JPSJ.5.435](https://doi.org/10.1143/JPSJ.5.435).

*Commentary.*

For every continuous matrix path K on [0,T] with T nonnegative, the recursive Bochner integral orderedTerm equals the independently defined closed-simplex integral simplexTerm. The simplex product is List.ofFn followed by List.prod in decreasing time order, so no commutation is imposed. Each nonnegative uniform bound M gives the estimate (Mt)^m/m!, including m=0 and T=0.

The series dysonSeries is the actual sum of these recursive terms. It converges absolutely at each point and uniformly on the closed interval, is continuous, solves G(t)=I+integral from 0 to t of K(s)G(s), has within derivative K(t)G(t) at every point including both endpoints, and satisfies G(0)=I. Every continuous solution of that integral equation agrees with G.

For a positive-length interval, finite logical indices d with d nonempty, and finite physical indices n, continuous F and D with the stated entrywise within derivatives and finite-interval matrix-unit multiplication and adjoint laws give the computed generator K=averagedVelocity(F,D)-unitSupport(F) supportVelocity(D). Its skew-adjointness, all matrix-unit and support commutators, the one-logical-index projector formula, and all analytic series clauses are conclusions. G is unitary on both sides, the transported logical matrix units have zero within derivative, and F(t)=G(t)F(0) times the conjugate transpose of G(t). The physical type n may be empty.

The Peano-Baker and Dyson constructions and projector parallel transport are classical. This declaration assembles their finite-interval realization with the repository's computed full matrix-unit generator; it claims no mathematical priority. The result concerns finite complex matrices and one time interval. It supplies neither a parameter-bundle trivialization nor a physical control-cost or adiabatic-error estimate.

ST40.1 application data and constructions. Let F and D be the actual matrix-unit path and its tangent, let P(t)=unitSupport(F t), and compute K(t)=transportGenerator(F t,D t). The logical index type d is finite and nonempty; the physical index type n is finite and may be empty. On [0,T], T>=0, F and D are continuous, D is the entrywise within derivative of F, and the matrix-unit multiplication and adjoint laws hold on the interval. For T>0 these are precisely the interval hypotheses of constructive_transport; no off-interval law is required. When T=0, the actual ambient path supplies the entrywise derivative D(0) and the matrix-unit and adjoint laws near 0. Differentiating those nearby laws supplies the zero-duration tangent identities; a derivative within a singleton is not used to identify a tangent. Given continuous Hermitian hL and hbar>0, Delta>0, put c=-i/hbar, G=dysonSeries(K), and VL=dysonSeries(c hL). The generic ordered-series branch of constructive_transport gives the continuity, initial value and within derivative of these particular series. The skew-adjointness of c hL and differentiation of VL†VL give VL†VL=VL VL†=I; the singleton case follows directly from VL(0)=I.

The representation is the literal finite sum pi_t(A)=representedMatrix(F t,A)=sum over i,j of A_ij F_ij(t). The existing represented_matrix_mul theorem gives pi_t(A)pi_t(C)=pi_t(AC); exchanging the two finite indices gives pi_t(A)†=pi_t(A†), and the diagonal sum gives pi_t(I)=P(t). Consequently P pi_t(A)=pi_t(A)P=pi_t(A), P†=P and P^2=P. The differentiated matrix-unit laws instantiate matrix_unit_transport_generator, so K†=-K even for a zero-duration interval. Therefore the actual Hphys(t)=i hbar K(t)+pi_t(hL(t))+Delta(I-P(t)) is continuous and Hermitian. No physical propagator or covariance identity is assumed in this construction.

For T>0, constructive_transport supplies both inverse equations for this G and the transported-unit equality F_ij(t)=G(t)F_ij(0)G(t)†. For T=0 these equalities are the initial identities. Summing the transported units and using G†G=I yields pi_t(A)G(t)=G(t)pi_0(A), including P(t)G(t)=G(t)P(0). Write Q0=I-P(0), z(t)=exp((-i/hbar)Delta t), B(t)=pi_0(VL(t))+z(t)Q0 and V(t)=G(t)B(t). The support relations give Q0^2=Q0 and kill both mixed products. Since conjugate(z)z=1 and pi_0(VL)†pi_0(VL)=P(0), B†B=BB†=I; the inverse equations for G then give V†V=VV†=I. The literal formulas also give B(0)=V(0)=I.

The finite-sum linear map pi_0 carries the logical derivative to the represented derivative. Together with z'=c Delta z and the support identities, this gives B'=c[pi_0(hL)+Delta Q0]B. Differentiating the literal product V=GB, using G'=KG and the already derived covariance, gives V'=c Hphys V, equivalently i hbar V'=Hphys V. These are within derivatives on the closed interval, with the usual derivative on its interior. Continuity and the fundamental theorem of calculus give V(t)=I+integral from 0 to t of (c Hphys(s))V(s); the uniqueness clause of constructive_transport for the continuous generator c Hphys then identifies this very V with dysonSeries(c Hphys). At T=0 the integral is zero and the initial identities settle uniqueness, without a singleton derivative-uniqueness inference. This is an active-control mathematical realization and supplies no control-bandwidth, energy-budget, locality or adiabatic-error estimate. The same-channel recovery identity and the closed-loop tensor consequences require their own subsequent applications.

## References

- Truth anchor: `D5/S3/Quantum/Transport/MatrixUnitDyson.constructive_transport`
- Dependency: [D5/S3/Quantum/Transport/MatrixUnitGenerator](MatrixUnitGenerator.md)
