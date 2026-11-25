# Chebyshev identities and rational harmonics

## Abstract

Exact Chebyshev and spherical character identities for Chapter 32, section 32.8, and Appendix Q.

**Theorem 1.1 (The Pell–Chebyshev identity).**

$$\forall x \in \mathbb{Z},\; \forall n \in \mathbb{N},\; \operatorname{T}\left(n + 1, x\right)^{2} - \left(x^{2} - 1\right) \cdot \operatorname{U}\left(n, x\right)^{2} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.pell_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrence preserves the quadratic norm of the first-kind and shifted second-kind coordinates.

**Theorem 1.2 (Doubling the Chebyshev index).**

$$\forall x \in \mathbb{Z},\; \forall n \in \mathbb{N},\; \operatorname{T}\left(2 \cdot n, x\right) = 2 \cdot \operatorname{T}\left(n, x\right)^{2} - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.chebyshev_doubling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The addition formula at two equal indices and the Pell identity give the displayed square.

**Theorem 1.3 (Even characters depend on the squared input).**

$$\forall x \in \mathbb{Z},\; \forall n \in \mathbb{N},\; \operatorname{E}\left(n, x^{2}\right) = \operatorname{U}\left(2 \cdot n, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.even_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The even-index subsequence satisfies a recurrence with multiplier four times the squared input minus two. This gives the integer-spin spherical characters.

**Theorem 1.4 (Odd characters retain the signed input).**

$$\forall x \in \mathbb{Z},\; \forall n \in \mathbb{N},\; x \cdot \operatorname{oddFactor}\left(n, x^{2}\right) = \operatorname{U}\left(2 \cdot n + 1, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.odd_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial multiplying the argument only depends on its square. The signed factor distinguishes opposite arguments.

**Theorem 1.5 (The rational spin-two character).**

$$\forall k \in \mathbb{Q},\; \operatorname{E}\left(2, k\right) = 16 \cdot k^{2} - 12 \cdot k + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.spin_two_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second term of the even character recurrence is a degree-two polynomial in the squared input.

**Theorem 1.6 (Exact pentagonal closures).**

$$\operatorname{T}\left(5, \frac{\varphi}{2}\right) = -1 \land \left(\operatorname{T}\left(10, \frac{\varphi}{2}\right) = 1 \land \operatorname{T}\left(5, \frac{\varphi - 1}{2}\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.pentagonal_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Doubling each evaluation gives a recurrence entirely in integral golden coefficients.

**Theorem 1.7 (Closed and depleted orbital shells).**

$$\left(\forall a \in Axes,\; \operatorname{closedShell}\left(a\right) = 0\right) \land \left(\operatorname{deletedShell}\left(x\right) = \frac{-4}{7} \land \left(\operatorname{deletedShell}\left(y\right) = \frac{-4}{7} \land \left(\operatorname{deletedShell}\left(z\right) = \frac{8}{7} \land \operatorname{deletedShell}\left(x\right) + \operatorname{deletedShell}\left(y\right) + \operatorname{deletedShell}\left(z\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.orbital_quadrupole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Axes are the three Cartesian directions. The five real d orbitals have a vanishing total diagonal quadrupole. Deleting both electrons in the d orbital with angular polynomial x squared minus y squared leaves the displayed diagonal and zero trace.

**Theorem 1.8 (The five orbital diagonals sum to zero).**

$$\forall a \in Axes,\; \operatorname{fullShell}\left(a\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.full_orbital_quadrupole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This sum counts each real orbital once. Counting each twice gives the doubly occupied closed shell.

**Theorem 1.9 (Norm and overlap of the six generators).**

$$\forall g \in Generators,\; \operatorname{normSq}\left(g\right) = 5 \land \operatorname{kappa}\left(g\right) = \frac{1}{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_norm_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generator set consists of the six quaternions with scalar part one and exactly one nonzero vector coordinate equal to plus or minus two.

**Theorem 1.10 (Character of the six-generator average).**

$$\forall n \in \mathbb{N},\; \operatorname{averageCharacter}\left(n\right) = \frac{\operatorname{traceNumerator}\left(n\right)}{5^{n}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_hecke_trace_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rotation-character model assigns each summand E evaluated at one fifth. Its average has the same character value, with denominator five to the degree in the displayed representative.

**Theorem 1.11 (The first six exact character trace values).**

$$\operatorname{traceRepresentative}\left(1\right) = \frac{-1}{5} \land \left(\operatorname{traceRepresentative}\left(2\right) = \frac{-19}{25} \land \left(\operatorname{traceRepresentative}\left(3\right) = \frac{139}{125} \land \left(\operatorname{traceRepresentative}\left(4\right) = \frac{-359}{625} \land \left(\operatorname{traceRepresentative}\left(5\right) = \frac{-1321}{3125} \land \operatorname{traceRepresentative}\left(6\right) = \frac{16901}{15625}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_hecke_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These fractions are the scaled representatives in the preceding character trace formula. Their numerators start at one and minus one, then satisfy a recurrence with coefficients minus six and minus twenty-five.

**Theorem 1.12 (Positive Ramanujan margins in the four spin shells).**

$$\forall j \in Shells,\; \forall b \in Branches,\; \operatorname{substitutionMatrix}\left(j\right) = \operatorname{integerMatrix}\left(j\right) \land 0 < 20 - \operatorname{lambdaSquared}\left(j, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_ramanujan_margins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first equality compares each monomial coefficient against the displayed integer matrix of the six-generator sum. Dividing each generator by the positive square root of five before taking its symmetric power gives the squared-eigenvalue denominator five to the degree. The first three integer matrices are scalar and the spin-two shell has two eigenvalue branches.

**Theorem 1.13 (Eigenbasis for spin two).**

$$\left(\forall l \in Lines,\; \operatorname{action}\left(\operatorname{vector}\left(l\right)\right) = \operatorname{scaledEigenvalue}\left(\operatorname{branch}\left(l\right)\right) \cdot \operatorname{vector}\left(l\right)\right) \land \left(\forall v \in Vectors,\; \operatorname{fromEigen}\left(\operatorname{doubledEigen}\left(v\right)\right) = 2 \cdot v \land \operatorname{doubledEigen}\left(\operatorname{fromEigen}\left(v\right)\right) = 2 \cdot v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_degree_four_eigenbasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action here is the degree-four integer matrix matched in the Ramanujan margin theorem. Its two branch values 54 and −74 give squared eigenvalues 54²/625 and 74²/625 in that theorem. The five eigenlines are the sum and difference of the two outer monomials and the three interior monomials. The basis changes compose to twice the identity in both orders, giving a basis over the rationals.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.chebyshev_doubling`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.even_chebyshev`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.full_orbital_quadrupole`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_degree_four_eigenbasis`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_hecke_trace_formula`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_hecke_traces`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_norm_five`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lps_ramanujan_margins`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.odd_chebyshev`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.orbital_quadrupole`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.pell_chebyshev`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.pentagonal_chebyshev`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.spin_two_character`
