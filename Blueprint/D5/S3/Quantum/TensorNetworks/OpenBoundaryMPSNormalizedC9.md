# Physical-mass-one all-window reconstruction

## Abstract

Physical-mass normalization of the raw all-window supplier, with a literal polynomial certificate on full amplitude coordinates and individual mass-one ambiguity witnesses.

**Definition 1.1 (Physical squared Hilbert mass).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.physicalMass`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.physicalMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every finite chain, M(psi) is the sum over every binary word w of Complex.normSq(psi(w)). It is nonnegative, vanishes exactly at the zero amplitude, is continuous, and obeys M(z psi)=normSq(z) M(psi). In particular a real amplitude multiplier t has mass degree two. The default Pi sup norm is not used.

**Definition 1.2 (The actual physical mass-one subtype).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.MassOne`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.MassOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

MassOne N is the subtype of the literal openBoundaryMPS N image with physicalMass=1. Its topology is the induced topology on that subtype, not a topology on a closure or parameter space. Every inhabitant is nonzero.

**Theorem 1.3 (One polynomial locus for every individual window).**

$$\forall m \in Nat,\; \exists P \in MvPolynomial\left(Sum\left(Word\left(3 + m\right), Word\left(3 + m\right)\right), Real\right),\; \exists H \in MvPolynomial\left(Sum\left(Word\left(3 + m\right), Word\left(3 + m\right)\right), Real\right),\; (((((((P \neq 0) \land (H = HomogeneousComponentSOS\left(P\right))) \land (H \neq 0)) \land (Nonempty\left(MassOnePrincipalLocus\left(m, H\right)\right))) \land (IsOpen\left(MassOnePrincipalLocus\left(m, H\right)\right))) \land (Dense\left(MassOnePrincipalLocus\left(m, H\right)\right))) \land (\forall psi \in MassOne\left(3 + m\right),\; \forall z \in Complex,\; (norm\left(z\right) = 1) \Rightarrow (\exists phi \in MassOne\left(3 + m\right),\; (amplitude\left(phi\right) = smul\left(z, amplitude\left(psi\right)\right)) \land ((Member\left(phi, MassOnePrincipalLocus\left(m, H\right)\right)) \Leftrightarrow (Member\left(psi, MassOnePrincipalLocus\left(m, H\right)\right)))))) \land (\forall psi \in MassOne\left(3 + m\right),\; (Member\left(psi, MassOnePrincipalLocus\left(m, H\right)\right)) \Rightarrow (((\forall p \in Nat,\; \forall q \in Nat,\; (p + q = m) \Rightarrow (\forall h \in p + 3 + q = 3 + m,\; \forall phi \in MassOne\left(3 + m\right),\; (rawInterior\left(p, 3, q, castState\left(h, amplitude\left(phi\right)\right)\right) = rawInterior\left(p, 3, q, castState\left(h, amplitude\left(psi\right)\right)\right)) \Leftrightarrow (\exists z \in Complex,\; (norm\left(z\right) = 1) \land (amplitude\left(phi\right) = smul\left(z, amplitude\left(psi\right)\right))))) \land (\forall p \in Nat,\; \forall q \in Nat,\; (p + q = m + 1) \Rightarrow (\forall h \in p + 2 + q = 3 + m,\; \exists phi \in MassOne\left(3 + m\right),\; (rawInterior\left(p, 2, q, castState\left(h, amplitude\left(phi\right)\right)\right) = rawInterior\left(p, 2, q, castState\left(h, amplitude\left(psi\right)\right)\right)) \land (\neg (\exists z \in Complex,\; (norm\left(z\right) = 1) \land (amplitude\left(phi\right) = smul\left(z, amplitude\left(psi\right)\right))))))) \land (\forall p \in Nat,\; \forall q \in Nat,\; (p + q = m + 2) \Rightarrow (\forall h \in p + 1 + q = 3 + m,\; \exists phi \in MassOne\left(3 + m\right),\; (rawInterior\left(p, 1, q, castState\left(h, amplitude\left(phi\right)\right)\right) = rawInterior\left(p, 1, q, castState\left(h, amplitude\left(psi\right)\right)\right)) \land (\neg (\exists z \in Complex,\; (norm\left(z\right) = 1) \land (amplitude\left(phi\right) = smul\left(z, amplitude\left(psi\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In the displayed formula HomogeneousComponentSOS(P) means exactly the finite sum of (homogeneousComponent d P)^2 for d=0 through totalDegree P inclusive. MassOnePrincipalLocus(m,H) means exactly {psi in MassOne(3+m) | eval(realCoordinates(amplitude(psi)),H) is nonzero}, with its induced subtype topology. amplitude(psi) is the underlying function Word(3+m) -> Complex, forgetting both subtype proofs. For every natural m, N=3+m, including m=0, there are literal real polynomials P,H on Word N plus Word N, the independent real and imaginary amplitude coordinates. P is the polynomial supplied directly by OpenBoundaryMPSAllWindowC9.result. H=HomogeneousComponentSOS(P). Both polynomials are nonzero. This exact nonvanishing locus of H on MassOne N is nonempty, relatively open, dense and saturated under every complex scalar of norm one.

At each target in this same locus, every p,q with p+q=m and every exact equality h:(p+3)+q=N give recovery from rawInterior p 3 q against every actual mass-one competitor, exactly up to one unit phase. For each p+q=m+1, and every exact h:(p+2)+q=N, an actual mass-one competitor has the same individual two-site observation and is not a phase multiple. The corresponding assertion holds separately for every one-site window with p+q=m+2. The existential competitor follows the choice of window; no single competitor shared by windows is asserted.

The polynomial argument works for an arbitrary real multivariate P without assuming homogeneity, a nonempty variable carrier, positive total degree, or a nonzero input x. The finite homogeneous reconstruction gives the univariate polynomial F_x(T)=sum_d eval_x(P_d) T^d. A coefficient extraction and the real sum-of-squares criterion identify H(x)=0 with F_x=0. The univariate infinite-root theorem then gives H(x) nonzero exactly when P(t x) is nonzero for some positive real t. P=0, constants, an empty variable carrier and x=0 remain in the statement. The scalar t multiplies amplitudes, so raw densities scale by t^2.

The old P locus is contained in the H locus by t=1, so its density and nonemptiness pass to the saturation. Positive-ray invariance follows from the ray characterization and reciprocal scaling. Unit-phase saturation follows from the old raw phase saturation, commuting phase with positive real scaling. H itself need not be homogeneous. A continuous retraction from the positive-mass actual subtype sends psi to psi/sqrt(M(psi)); it fixes MassOne N. The positive-mass subtype is open. Pulling a nonempty open slice set back through this retraction and using density in that open subtype proves density on the actual mass-one slice. Continuity alone is never used to claim that an arbitrary image is open or dense.

For all p,k,q, rawInterior has scalar degree two. Its trace is the complex embedding of M(psi), proved by the exact bijection between (window word,left word,right word) and the original full word. Length casts preserve mass and commute with scalar action. Equal same-window observations therefore give equal physical masses, at boundaries and with zero-length exteriors as well as internally. For a normalized target choose t>0 reaching the old P locus. Apply raw all-window recovery and ambiguity there. Scale every raw ambiguity witness back by inverse t: trace equality places that very witness on the same mass-one slice, equality of observations survives, and a hypothetical phase equation would contradict the raw nonphase witness. Recovery scales each arbitrary actual mass-one competitor by t and cancels the same nonzero scalar.

Continuity of realCoordinates from OpenBoundaryMPSDensityGenericity and the actual_phase scalar-closure property supply the normalization maps and phase action. The reconstruction and gauge results include Haobo Ma and Wenlin Zhang's Conjecture 8 supplier under CC BY 4.0. Together with OpenBoundaryMPSAllWindowC9.result, this establishes the physical-mass-one slice with both target and competitors normalized for the same physical C9 reading. It does not establish independent C9 novelty or priority.

This theorem supplies neither a joint-window ambiguity witness, a neighborhood ambiguity upgrade, stability, physical recovery dynamics, a time group, energy, clock nor thermodynamics.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.MassOne`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.physicalMass`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9](OpenBoundaryMPSAllWindowC9.md)
