# Off-midpoint obstruction for the original spectral mean

## Abstract

The UNTILDE spectral trace has a strict affine Jensen violation at every off-midpoint parameter, already among real symmetric faithful qubit density matrices.

SpectralNonconcavityScalars owns the pure real ordered-root algebra, exact scale identities, strict interior gap and finite-factor limits. This matrix owner consumes those original names directly in root_power, native_two_scale, actual_roots, actual_power, weightedColumns_limit and the strict density witnesses.

**Definition 1.1 (Complex qubit matrices).**

$$Mat = \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

Real symmetric witnesses are represented as complex matrices with zero imaginary entries.

**Definition 1.2 (The exact density domain).**

$$\forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{Density}\left(A\right) \Leftrightarrow ((((\operatorname{PosDef}\left(A\right)) \land (\operatorname{trace}\left(A\right) = 1)) \land (\forall i: \operatorname{Fin}\left(2\right), \forall j: \operatorname{Fin}\left(2\right), \operatorname{im}\left(A\left(i, j\right)\right) = 0)) \land (\operatorname{transpose}\left(A\right) = A))$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.Density` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

Density requires strict positive definiteness, complex trace exactly one, every entry real, and transpose symmetry. No singular witness is used.

**Definition 1.3 (The native unweighted mean).**

$$\forall p: \mathbb{R}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{nativeMean}\left(p, A, B\right) = \operatorname{geometricMean}\left(\frac{1}{2}, \operatorname{rpow}\left(A, 0 - p\right), \operatorname{rpow}\left(B, p\right)\right)$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.nativeMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The base-first geometricMean is the existing library operation. For SPD A and B and real p, put X=A^p and Y=B^p. The native mean is X^(-1/2) sqrt(X^(1/2) Y X^(1/2)) X^(-1/2). It is the unique strictly positive solution of L X L=Y. Square-root uniqueness proves this Riccati identification. Reversing A and B gives inverse(L).

**Definition 1.4 (The UNTILDE spectral trace).**

$$\forall alpha: \mathbb{R}, \forall p: \mathbb{R}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{spectralTrace}\left(alpha, p, A, B\right) = \operatorname{Re}\left(\operatorname{trace}\left(\operatorname{rpow}\left(\operatorname{rpow}\left(\operatorname{nativeMean}\left(p, A, B\right), alpha\right) \cdot \operatorname{rpow}\left(A, p\right) \cdot \operatorname{rpow}\left(\operatorname{nativeMean}\left(p, A, B\right), alpha\right), \frac{1}{p}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.spectralTrace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

This is the powered quasi-extension in equation (2.4) of the original family (2.3), with the literal outer spectral 1/p power. Equations (2.5)--(2.6) define the different TILDE family. The Riccati identity gives S(1-alpha,p,B,A)=S(alpha,p,A,B) before taking the outer power. Unitary covariance follows from InverseGeometricIdentification.unitary_rpow.

**Definition 1.5 (Diagonal density path).**

$$\forall t: \mathbb{R}, \operatorname{diagonalState}\left(t\right) = \operatorname{diag}\left(1 - t, t\right)$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.diagonalState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For 0<t<1, A(t)=diag(1-t,t) is strictly positive, real symmetric and has trace one.

**Definition 1.6 (Balanced density path).**

$$\forall s: \mathbb{R}, \operatorname{balancedState}\left(s\right) = \operatorname{sym}\left(\frac{1}{2}, \frac{1}{2} - s, \frac{1}{2}\right)$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.balancedState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For 0<s<1/2, B(s)=(1/2)[[1,1-2s],[1-2s,1]] has eigenvalues 1-s and s and is a real symmetric strictly positive density matrix. Conjugation by J=[[0,1],[1,0]] sends A(t) to A(1-t) and fixes B(s), so the two endpoint functional values agree.

**Definition 1.7 (Literal affine, faithful and noncommuting witnesses).**

$$\forall tau: \mathbb{R}, \forall s: \mathbb{R}, \forall ell: \mathbb{R}, \operatorname{WitnessGeometry}\left(tau, s, ell\right) \Leftrightarrow (((((((((((((((0 < tau) \land (tau < \frac{1}{2})) \land (0 < s)) \land (s < \frac{1}{2})) \land (s \cdot s < tau)) \land (0 < ell)) \land (ell < \frac{1}{2})) \land (\operatorname{Density}\left(\operatorname{diagonalState}\left(s \cdot s\right)\right))) \land (\operatorname{Density}\left(\operatorname{diagonalState}\left(1 - s \cdot s\right)\right))) \land (\operatorname{Density}\left(\operatorname{diagonalState}\left(tau\right)\right))) \land (\operatorname{Density}\left(\operatorname{balancedState}\left(s\right)\right))) \land (\operatorname{diagonalState}\left(tau\right) = \left(1 - ell\right) \cdot \operatorname{diagonalState}\left(s \cdot s\right) + ell \cdot \operatorname{diagonalState}\left(1 - s \cdot s\right))) \land (\operatorname{diagonalState}\left(s \cdot s\right) \cdot \operatorname{balancedState}\left(s\right) \neq \operatorname{balancedState}\left(s\right) \cdot \operatorname{diagonalState}\left(s \cdot s\right))) \land (\operatorname{diagonalState}\left(1 - s \cdot s\right) \cdot \operatorname{balancedState}\left(s\right) \neq \operatorname{balancedState}\left(s\right) \cdot \operatorname{diagonalState}\left(1 - s \cdot s\right))) \land (\operatorname{diagonalState}\left(tau\right) \cdot \operatorname{balancedState}\left(s\right) \neq \operatorname{balancedState}\left(s\right) \cdot \operatorname{diagonalState}\left(tau\right)))$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.WitnessGeometry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The affine coefficient is ell=(tau-s^2)/(1-2s^2). Every matrix in the three functional evaluations is a density matrix, and each varying diagonal matrix fails to commute with B(s). Below the midpoint B(s) is fixed; above the midpoint the complement identity fixes B(s) as the first argument.

**Theorem 1.8 (Constructive violation for every admissible pair).**

$$\forall alpha: \mathbb{R}, \forall p: \mathbb{R}, ((((0 < alpha) \land (alpha < 1)) \land (alpha \neq \frac{1}{2})) \land (0 < p)) \Rightarrow (\exists tau: \mathbb{R}, \exists s: \mathbb{R}, \exists ell: \mathbb{R}, ((\operatorname{WitnessGeometry}\left(tau, s, ell\right)) \land ((alpha < \frac{1}{2}) \Rightarrow (\operatorname{spectralTrace}\left(alpha, p, \operatorname{diagonalState}\left(tau\right), \operatorname{balancedState}\left(s\right)\right) < \left(1 - ell\right) \cdot \operatorname{spectralTrace}\left(alpha, p, \operatorname{diagonalState}\left(s \cdot s\right), \operatorname{balancedState}\left(s\right)\right) + ell \cdot \operatorname{spectralTrace}\left(alpha, p, \operatorname{diagonalState}\left(1 - s \cdot s\right), \operatorname{balancedState}\left(s\right)\right)))) \land ((\frac{1}{2} < alpha) \Rightarrow (\operatorname{spectralTrace}\left(alpha, p, \operatorname{balancedState}\left(s\right), \operatorname{diagonalState}\left(tau\right)\right) < \left(1 - ell\right) \cdot \operatorname{spectralTrace}\left(alpha, p, \operatorname{balancedState}\left(s\right), \operatorname{diagonalState}\left(s \cdot s\right)\right) + ell \cdot \operatorname{spectralTrace}\left(alpha, p, \operatorname{balancedState}\left(s\right), \operatorname{diagonalState}\left(1 - s \cdot s\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavity.off_midpoint_violation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For beta=alpha below the midpoint and beta=1-alpha above it, choose tau=min(1/4,(2^(-beta/(1-beta))-1/2)^(1/p)). Then tau>0 and m(tau)=((1-tau)^p+tau^p)/2 has m(tau)^((1-beta)/p)<2^(-beta/p). At fixed A(tau), the rank-one second-input limit is m(tau)^((1-beta)/p). The simultaneous endpoint A(s^2),B(s) has limit 2^(-beta/p). A single sufficiently small positive s gives the strict gap and s^2<tau. Exact affine coordinates and equal endpoint values give the displayed Jensen violation.

For alpha>0 and p>0, every fixed SPD matrix A and every eventually SPD net F converging to P=(1/2)[[1,1],[1,1]] satisfy the following limit. Put X=A^p and m=Re(X11+X12+X21+X22)/2. Positivity of the quadratic form at (1,1) proves m>0, and entry algebra gives P X P=m P. Square-root uniqueness yields sqrt(X^(1/2) P X^(1/2))=m^(-1/2) X^(1/2) P X^(1/2). Consequently the native mean tends to m^(-1/2) P and S(alpha,p,A,F) tends to m^((1-alpha)/p). Only positive powers of the varying matrices are continued across the rank-one limit; the inverse of X remains fixed.

Write z=s^(p/2), x=(1-s^2)^p, a=((1-s)^p+z^2)/2, b=((1-s)^p-z^2)/2, e=((1-s^2)(1-s))^(p/2), and c=sqrt(a(x+z^4)+2z^3 e). The exact native mean has entries u=(a+z^3 e/x)/c, v=b/c, w=(a+e/z)/c. Entry algebra and Riccati uniqueness identify this actual matrix, with z(uw-v^2)=e/x. The ordered scalar roots m,M satisfy z M -> sqrt(2) and m=(e/x)/(z M) -> k=1/sqrt(2).

For rho=sqrt(((u-w)/2)^2+v^2) and H=(L-(u+w)I/2)/rho, entry algebra proves H*=H and H^2=I. The existing CumulantRenyiDataProcessingRefutation.two_point_cfc gives L^beta=m^beta I+gamma(L-mI). With C=z M and q=z m/C, the exact slope is gamma=C^(beta-1) z^(1-beta)(1-q^beta)/(1-q). All factors have finite limits and gamma -> 0 because 0<beta<1.

For E=L^beta A(s^2)^(p/2), its entries are d(m^beta+gamma(u-m)), z^2 gamma v, d gamma v, and z^2 m^beta+z gamma(z w-z m), where d=(1-s^2)^(p/2). Thus E -> diag(k^beta,0), and E E* -> 2^(-beta)diag(1,0). Positive-power continuity across zero uses CFC.continuousOn_nnrpow with nnrpow_eq_rpow; continuity of the divergent geometric mean is never required. The outer 1/p spectral power and real trace give 2^(-beta/p).

**Definition 1.9 (Concavity at any off-midpoint parameter).**

$$claim \Leftrightarrow (\exists alpha: \mathbb{R}, \exists p: \mathbb{R}, ((((0 < alpha) \land (alpha < 1)) \land (alpha \neq \frac{1}{2})) \land (0 < p)) \land (\operatorname{JointlyConcaveOn}\left(\operatorname{Density}\left(\right), \operatorname{Density}\left(\right), \operatorname{spectralTrace}\left(alpha, p\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Hiai/SpectralNonconcavity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The closed Prop claim asserts existence of at least one off-midpoint admissible pair with joint concavity on the exact density domain. Negating this existential excludes every such pair.

**Theorem 1.10 (No off-midpoint pair is jointly concave).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The all-parameter constructive theorem contradicts joint concavity along the literal affine segment with its fixed argument. The midpoint alpha=1/2 is outside this theorem's parameter range.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.Density`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.Mat`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.WitnessGeometry`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.balancedState`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.claim`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.diagonalState`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.nativeMean`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.off_midpoint_violation`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.result`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavity.spectralTrace`
- Dependency: [D5/S3/Quantum/Hiai/InverseGeometricIdentification](InverseGeometricIdentification.md)
- Dependency: [D5/S3/Quantum/Hiai/SpectralNonconcavityScalars](SpectralNonconcavityScalars.md)
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](../Matrix/AlternativeMeanLinearization.md)
- Dependency: [D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation](../../QuantumChannels/CumulantRenyiDataProcessingRefutation.md)
