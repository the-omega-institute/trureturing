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

ST40.1 application. Given a continuous logical Hermitian path hL, hbar>0 and Delta>0, instantiate the same ordered-series result with A_L=(-i/hbar)hL. Its series VL has the stated initial value, within derivative and unique integral equation; differentiating VL*VL and applying the interval constancy result gives both inverse identities. With P0=unitSupport(F 0), set B=representedMatrix(F 0,VL)+exp(-i Delta t/hbar)(I-P0) and V=G B. Matrix-unit transport gives representedMatrix(F t,A)=G representedMatrix(F 0,A) G*, while the matrix-unit support relations make B*B=BB*=I. Thus V(0)=I and product differentiation yields i hbar V'=Hphys V for the literal Hphys=i hbar K+representedMatrix(F t,hL t)+Delta(I-P t). The same continuous-generator uniqueness identifies V with the ordered Dyson series for (-i/hbar)Hphys; the zero-duration endpoint is inherited from the actual path tangent data rather than a singleton derivative assumption. No equality with a prescribed syndrome state, control-bandwidth estimate, locality claim, or adiabatic novelty claim is part of this application.

## References

- Truth anchor: `D5/S3/Quantum/Transport/MatrixUnitDyson.constructive_transport`
- Dependency: [D5/S3/Quantum/Transport/MatrixUnitGenerator](MatrixUnitGenerator.md)
