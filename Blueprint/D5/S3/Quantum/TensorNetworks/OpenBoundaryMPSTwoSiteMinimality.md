# Two-site prefix minimality on the canonical parameter chart

## Abstract

Two-site raw prefix ambiguity on a nonempty canonical chart

**Definition 1.1 (Thirteen real parameter coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.Parameter`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.Parameter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The source is (Fin 5 to complex) times real times complex. Its coordinates are x,p,q,u,v,rho,r1. The left row is (x,1), the right column is (rho,r1), and the real positive condition on rho fixes only unit complex phase. It retains positive amplitude scale on the raw affine cone.

**Definition 1.2 (The canonical symbol matrices).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.core`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.core` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The two matrices have first rows (p,q) and (u,v), and second rows (1-xp,-xq) and (-xu,1-xv). Their products with the left row are exactly the two standard physical rows. The source model is the existing openBoundaryMPS model with independent free boundaries.

**Definition 1.3 (The twelve real raw density coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.densityRecord`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.densityRecord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Using the fixed ordering 00,01 then 10,11, retain the two real diagonal entries of the leading block H, its complex off-diagonal entry, and the complex two by two upper-right block B. This defines a twelve-real-dimensional vector space. The record map is evaluated on the actual rawPrefix density of the canonical MPS state; all its coordinates are real C-infinity.

**Theorem 1.4 (Phase rigidity at three sites).**

$$\forall (theta: \operatorname{Parameter}\left(\right)), (\forall (eta: \operatorname{Parameter}\left(\right)), ((0 < \operatorname{fst}\left(\operatorname{snd}\left(theta\right)\right)) \to ((0 < \operatorname{fst}\left(\operatorname{snd}\left(eta\right)\right)) \to (\forall (zeta: \mathbb{C}), ((\operatorname{norm}\left(zeta\right) = 1) \to ((\operatorname{state}\left(3, eta\right) = \operatorname{smul}\left(zeta, \operatorname{state}\left(3, theta\right)\right)) \to ((\neg \operatorname{eval}\left(\operatorname{state}\left(3, eta\right), \operatorname{chartPoly}\left(\right)\right) = 0) \to (theta = eta))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.three_site_phase_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For positive real rho and rho-prime, equality of two canonical three-site tensors up to a unit complex phase forces equality of every parameter, provided the second tensor lies in the supplied coherent chart. Compare the two applications of the original triple_gauge: the normalized physical rows force the two gauge matrices to agree, and the second coordinate of the left row fixes their scalar discrepancy. The right boundary is recovered by summing l_i l_j t_ijk. The resulting positive real boundary comparison eliminates unit phase. This inverse argument is attributed to Haobo Ma and Wenlin Zhang's CC BY 4.0 note Proof of Critch-Morton Conjecture 8 and its existing Lean supplier, rather than claimed as new C9 mathematics. The all-length theorem below applies the original outside_sum_exact at the prefix, with induced boundary (A0+A1)^m r.

**Theorem 1.5 (Schur completion from the fixed record).**

$$\forall (Q: \operatorname{Matrix}\left(\operatorname{Word}\left(2\right), \operatorname{Word}\left(2\right), \mathbb{C}\right)), (\forall (P: \operatorname{Matrix}\left(\operatorname{Word}\left(2\right), \operatorname{Word}\left(2\right), \mathbb{C}\right)), ((\operatorname{IsHermitian}\left(Q\right)) \to ((\operatorname{IsHermitian}\left(P\right)) \to ((\operatorname{rank}\left(Q\right) \le 2) \to ((\operatorname{rank}\left(P\right) \le 2) \to ((\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{leading}\left(Q\right)\right)\right)) \to ((\operatorname{densityRecord}\left(Q\right) = \operatorname{densityRecord}\left(P\right)) \to (Q = P))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.densityRecord_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Two Hermitian matrices on two-bit words with rank at most two are equal when their twelve-coordinate records agree and the fixed leading principal block of the first matrix is invertible. Hermitian symmetry recovers the leading block from its diagonal real parts and one complex entry. Normalize the top block of the matrix operator by an explicit input shear. The linear vertical-rank criterion kills its lower-right Schur complement, proving D equals B-dagger H-inverse B. The result includes singular matrices of rank below two in its hypotheses, although invertibility of H forces the rank to equal two. The actual-density application uses the original columns_factor: the amplitude columns factor through a two-dimensional bond, their Gram is Hermitian, and its rank is at most two.

**Definition 1.6 (The full intended phase-fixed chart).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.canonicalChart`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.canonicalChart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

At source length 3+m, require positive real rho, nonvanishing of chartPoly on the actual coherent first-three-site improper marginal, nonzero determinant of A0+A1, and nonzero determinant of the fixed Q2 leading principal block. The Q2 complement length is 1+m. Every condition refers to the actual canonical state map. The intended original problem has m at least one. The explicit uniform witness below proves nonemptiness for every natural m, in particular for every source length at least four.

**Theorem 1.7 (Openness in the actual real source).**

$$\forall (m: \mathbb{N}), (\operatorname{IsOpen}\left(\operatorname{canonicalChart}\left(m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.isOpen_canonicalChart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The full canonicalChart is open in the thirteen-dimensional real parameter space. The coherent marginal is a finite sum of actual amplitudes, all entries of the state and raw density are real smooth, and evaluation of chartPoly and the two determinants are continuous. This is an openness theorem for the parameter chart; it does not assert openness or density of its image among actual states or in a phase quotient.

**Theorem 1.8 (Actual parameter collisions in every open set).**

$$\forall (m: \mathbb{N}), (\forall (U: \operatorname{Set}\left(\operatorname{Parameter}\left(\right)\right)), ((\operatorname{IsOpen}\left(U\right)) \to ((\operatorname{Nonempty}\left(U\right)) \to (\exists (theta: \operatorname{Parameter}\left(\right)), ((theta \in U) \land (\exists (eta: \operatorname{Parameter}\left(\right)), (((eta \in U) \land (\neg theta = eta)) \land (\operatorname{record}\left(m, theta\right) = \operatorname{record}\left(m, eta\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.record_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every complement length m and every specified nonempty open subset of the actual thirteen-real-dimensional canonical parameter space, two distinct parameters have the same twelve raw Q2 record coordinates. The proof compiles the actual smooth MPS observation map and consumes the real C1 dimension obstruction. The open_subchart_collision theorem supplies the additional density and phase bridges. Neither parameter theorem establishes genericity or phase saturation in the full actual state image.

**Theorem 1.9 (All-length unit-phase rigidity).**

$$\forall (m: \mathbb{N}), (\forall (theta: \operatorname{Parameter}\left(\right)), (\forall (eta: \operatorname{Parameter}\left(\right)), ((theta \in \operatorname{canonicalChart}\left(m\right)) \to ((eta \in \operatorname{canonicalChart}\left(m\right)) \to (\forall (zeta: \mathbb{C}), ((\operatorname{norm}\left(zeta\right) = 1) \to ((\operatorname{state}\left(\operatorname{add}\left(3, m\right), eta\right) = \operatorname{smul}\left(zeta, \operatorname{state}\left(\operatorname{add}\left(3, m\right), theta\right)\right)) \to (theta = eta))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.phase_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural m, two parameters in canonicalChart m that give phase-equal actual states at length 3+m are equal. Sum the coherent complement of length m using the original outside_sum_exact. Apply the Ma-Zhang canonical three-site inverse with the induced right boundary, recover that boundary by contraction, and cancel the invertible power of S=A0+A1. The positive real first coordinate of each original right boundary forces the unit phase to be one. No equivalence under arbitrary nonzero complex scaling is used.

**Theorem 1.10 (Full raw Q2 collisions between different phase classes).**

$$\forall (m: \mathbb{N}), (\forall (U: \operatorname{Set}\left(\operatorname{Parameter}\left(\right)\right)), ((\operatorname{IsOpen}\left(U\right)) \to ((\operatorname{Nonempty}\left(U\right)) \to ((\operatorname{subset}\left(U, \operatorname{canonicalChart}\left(m\right)\right)) \to (\exists (psi: \operatorname{Function}\left(\operatorname{Word}\left(\operatorname{add}\left(2, \operatorname{add}\left(1, m\right)\right)\right), \mathbb{C}\right)), ((psi \in \operatorname{image}\left(\operatorname{state}\left(\operatorname{add}\left(2, \operatorname{add}\left(1, m\right)\right)\right), U\right)) \land (\exists (phi: \operatorname{Function}\left(\operatorname{Word}\left(\operatorname{add}\left(2, \operatorname{add}\left(1, m\right)\right)\right), \mathbb{C}\right)), ((phi \in \operatorname{image}\left(\operatorname{state}\left(\operatorname{add}\left(2, \operatorname{add}\left(1, m\right)\right)\right), U\right)) \land ((((psi \in \operatorname{openBoundaryMPS}\left(\operatorname{add}\left(2, \operatorname{add}\left(1, m\right)\right)\right)) \land (phi \in \operatorname{openBoundaryMPS}\left(\operatorname{add}\left(2, \operatorname{add}\left(1, m\right)\right)\right))) \land (\operatorname{rawPrefix}\left(2, \operatorname{add}\left(1, m\right), psi\right) = \operatorname{rawPrefix}\left(2, \operatorname{add}\left(1, m\right), phi\right))) \land (\neg \exists (zeta: \mathbb{C}), ((\operatorname{norm}\left(zeta\right) = 1) \land (phi = \operatorname{smul}\left(zeta, psi\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.open_subchart_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every m and every specified nonempty open U contained in canonicalChart m, there exist two actual free-boundary MPS states in the image of U with equal entire rawPrefix 2 (1+m) and no unit phase relating them. The C1 dimension obstruction is applied to the actual smooth twelve-real record map on the thirteen-real parameter source. The original amplitude-column factorization gives a Hermitian Gram of rank at most two; fixed-H Schur completion turns record equality into equality of all raw Q2 entries. All-length phase rigidity then turns distinct parameters into distinct phase classes. The existential witnesses remain in the actual matrix-and-boundary image. This is a local parameter-open no-fewer theorem. It does not assert a dense intrinsic real-algebraic state locus or phase saturation of arbitrary open state loci, and does not alone resolve Conjecture 9.

**Theorem 1.11 (A uniform full-length witness).**

$$\forall (m: \mathbb{N}), (\operatorname{Nonempty}\left(\operatorname{canonicalChart}\left(m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.canonicalChart_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural m, canonicalChart m is nonempty. Start from A0=[[1,2],[3,4]], A1=[[5,6],[7,8]], l=(1,0), r=(1,2). The exact full-length gauge U=[[1,2],[5,6]], s=1/2 gives canonical l=(-3,1), A0=[[1,1/2],[4,3/2]], A1=[[-1/2,2],[-3/2,7]] and right boundary 2^(2+m)(5,17), preserving every amplitude at length 3+m. The original positive sum matrix keeps the coherent right boundary (x,y) strictly positive. Direct kernel-checked Cramer and chart-factor identities have only nonzero factors x+y and 5x+8y on this positive cone. The canonical sum determinant is -2. For the Q2 complement 1+m, the first tail Gram is the Gram of columns (5,11) and (17,23), whose determinant is -72. An invertible A0 preserves positive definiteness under further transfers. The fixed prefix rows (7,10) and (19,22) have determinant -36, so the fixed leading density block is positive definite at every length. Gauge preservation transfers its invertibility to the canonical witness. No transfer-operator determinant is identified with det(A0+A1).

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.Parameter`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.canonicalChart`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.canonicalChart_nonempty`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.core`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.densityRecord`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.densityRecord_injective`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.isOpen_canonicalChart`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.open_subchart_collision`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.phase_rigidity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.record_collision`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality.three_site_phase_rigidity`
- Dependency: [D5/S3/Geometry/C1LocalFiber](../../Geometry/C1LocalFiber.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery](OpenBoundaryMPSDensityRecovery.md)
