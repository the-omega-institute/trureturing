# Intrinsic generic interior recovery in the actual state image

## Abstract

One intrinsic observed polynomial for all interior three-site recovery windows.

**Definition 1.1 (Propositionally equal word lengths).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.castState`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.castState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For h:n=nprime and f:Word nprime to complex, castState h f at w is f of the word i mapped to w(Fin.cast h.symm i). This preserves all amplitudes and commutes with scalar multiplication; it introduces no permutation of physical sites.

**Definition 1.2 (The full intrinsic recovery property).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.intrinsicInteriorRecovery`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.intrinsicInteriorRecovery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fixed m, there exists one nonzero real polynomial R in the real and imaginary entries of the complete raw prefix Q3. Its nonvanishing defines a nonempty relatively open dense subset L of the ENTIRE actual free-boundary uniform binary bond-two state image at length 3+m. For every actual state and every unit complex scalar, its scalar multiple is actual and belongs to L exactly when the original state does. Thus this is a phase-saturated actual-image locus.

At every target psi in L, set Q=rawPrefix 3 m psi, ptheta=quotientCoordinates m Q, x=quotientCoordinates13 ptheta and theta=positiveRepresentative x. The property gives positive sigma(x), an exact unit phase between psi and state(3+m,theta), TwoSiteSpanning(core theta), injectivity of the complex-linear transfer, and positivity of BOTH actual boundary environments at every positive iterate. The left seed is vecMulVec(star(left theta),left theta); the right seed is vecMulVec(right theta,star(right theta)).

For every p,q satisfying p≥1, q≥1 and p+q=m, every length equality h:((p+3)+q)=3+m, and EVERY actual competitor phi of length 3+m, complete rawInterior p 3 q equality between the cast states is equivalent to phi being a unit complex phase multiple of psi. No competitor chart, rank, minimality, positivity, spanning, transfer or normalization assumption is present. The same polynomial R serves all these splits. R may vary with m.

**Theorem 1.3 (Original canonical positive iterate supplier).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.positive_iterates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.positive_iterates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every canonical real x with positive sigma, nonzero determinant of canonical A0 and nonzero determinant of the boundary matrix with columns Ai(1,eta), BOTH actual canonical left and right environments are positive definite at every natural iterate k at least one. The left seed is star(left) tensor left; the right seed is right tensor star(right), with the full square-root sigma right representative. This is the original helper and original complete proof, exposed for the spectral certificate's consumed environment transport.

**Theorem 1.4 (Generic sufficiency for every interior three-site window).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.intrinsic_interior_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.intrinsic_interior_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m with 2 at most m, intrinsicInteriorRecovery m holds. Hence the length range is exactly N=3+m at least five. The proof constructs one sufficient polynomial product from the existing complex polynomial core and eta variable. S has rows indexed by matrix entries (a,b), columns indexed by products (i,j), and entry (Ai Aj)ab. V has columns A0(1,eta) and A1(1,eta). The real polynomial K is the product of the squared complex moduli of det S, det A0 and det V, formed by coefficientwise real and imaginary parts squared and added. This uses thirteen real variables without duplicating conjugated variables or introducing a square root into K.

det S nonzero makes the product-column map surjective, giving exactly TwoSiteSpanning after unflattening. The canonical row identities l A0=e0 and l A1=e1 give P1=I. For r=sqrt(sigma)(1,eta), the actual column matrix W has nonzero determinant because sigma is positive and det V is nonzero; the exact transfer seed is W W dagger, hence positive definite. Invertible A0 supplies one invertible congruence at each propagation step; the A1 term is positive semidefinite. This proves both actual environments positive definite for every positive iterate. det A0 is only a sufficient generic-locus restriction; the conditional phase theorem has no such hypothesis.

Use the existing clear_polynomial once on K, with the exact quotientRealNumerator and quotientRealDenominator families under quotientIndexEquiv.symm. It gives H and B, with B nonzero on the quotient locus and K(x)=H(y)/B(y). Set R=quotientLocusPolynomial m times H. The existing full-length integer witness, witness_gauge and local quotient retraction give a single actual witness for the entire product at every m. Its canonical core coordinates are (-3,1,1/2,-1/2,2), eta=17/5, sigma=25 times (2^(2+m)) squared. The exact determinant values are det S=64, det A0=-1/2 and det V=72/25. No independent nonzero witnesses are combined. Apply actual_principal_genericity to this single witness; no new density argument, image-openness claim or closure replacement is used.

Transfer injectivity is reused from recoveryPolynomial_ne_zero for canonicalCore of the fixed observed column. Actualness supplies observed_coherent in the three-site state image. The existing canonical_shape and positive-representative alignment identify this core with core theta. This is the consumed bridge that permits omission of a separate transfer-determinant factor. The existing actual_quotient_representative supplies positive sigma and the full-state phase. Finally the accepted interior_phase_recovery is applied at every split to each unrestricted actual competitor, and the phases are composed. The reverse implication and phase saturation are exact raw-Gram scalar identities.

The canonical reconstruction and phase rigidity retain Haobo Ma and Wenlin Zhang's CC BY 4.0 C8 attribution. The Q2 supplier retains BochaoKong's Apache-2.0 LeanPool C1 attribution, commit 2b1ec889365345f19a45fa94b6457a4d92c96295; the C1 fiber theorem is not reproved here. This delivers only interior THREE-site sufficiency. Interior two-site insufficiency is supplied by InteriorSpectralAmbiguity.observed_interior_ambiguity in the same spectral exclusion unit; full Critch-Morton C9 remains open, with solved-open-problem KPI zero. No normalized reading, physical recovery operation, dynamics, time group, energy, physical clock, stability or thermodynamic cost follows.

**Lemma 1.5 (Exact state-length transport).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.cast_mps`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.cast_mps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original castState transports the MPS formula along n=nprime with the matrices and both boundary vectors unchanged. It is consumed by the observed interior two-site ambiguity theorem to move the actual competitor into length 3+m and back to the exact window length (p+2)+q.

**Lemma 1.6 (Complete interior raw observation is phase invariant).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.rawInterior_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.rawInterior_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying an amplitude by a unit complex scalar leaves the entire rawInterior matrix unchanged. The observed interior ambiguity theorem uses this original proof for the target and its window-specific actual competitor.

**Lemma 1.7 (Scalar closure of the literal actual image).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.actual_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.actual_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complex scalar multiple of an actual MPS is actual, by scaling its original left boundary. This original proof supplies actualness of the transported competitor and U(1) saturation of the principal locus.

**Lemma 1.8 (Observed principal loci are U(1) saturated).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.locus_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.locus_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix-Q3 scalar identity implies exact membership equivalence under a unit complex scalar for every real observed polynomial. The original helper is consumed by observed_interior_ambiguity.

The full-source four-slot registration remains declared_unresolved: IE-C050 ClosedTruthReadout, unclassified_form, source.selection_size. Its complete source-equivalence, variation, sensitivity and observational-dependence proofs compile, but accepted source/readout binding remains missing. This unfinished audit requires caller disclosure under https://github.com/the-omega-institute/trureturing/issues/30422. A compiled registration alone is not declared_validated.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.actual_phase`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.castState`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.cast_mps`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.intrinsicInteriorRecovery`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.intrinsic_interior_recovery`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.locus_phase`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.positive_iterates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity.rawInterior_phase`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore](OpenBoundaryMPSInteriorCommonCore.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSIntrinsicQ2Fiber](OpenBoundaryMPSIntrinsicQ2Fiber.md)
