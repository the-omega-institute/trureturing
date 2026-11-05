# Singular multipartite squared-distance Laplacian

## Abstract

The singular multipartite source Laplacian has exactly the stated positive spectrum and inertia on every original part-size domain.

The source definitions and complete concluding conjecture are from `D5/L/QuadraticForms/dasmohanty2024inverse`, equation (3.6) and the concluding conjecture. The author-defined omitted-list equalities determine the hats. The inconsistent expanded hatted Psi products are not substituted for those definitions. No publisher correction, priority or worldwide literature-completeness claim is made.

For any natural t and n:Fin(t) to Nat, the vertex carrier is the dependent sum of Fin(n(i)). Set d(i)=3n(i)-4. For a finite parameter set S, phi(n,S) is the product of d(i) over S, psi(n,S) is the sum of n(i)phi(n,S without i), and theta=phi+psi. Empty products are one and empty sums zero. Restricting S therefore removes exactly the indicated parameters, including for double hats. ratio(n) is the sum of n(i)/d(i).

delta(n) has diagonal zero, within-part off-diagonal four and between-part one. For t at least two and positive part sizes these are the squared graph distances. cofactorSum is the sum of every adjugate entry, hence the sum of all cofactors, not a principal cofactor. sourceL uses the literal three source cases: its diagonal numerator is (n(i)-1)theta(hat i)/2+(n(i)-3)psi(hat i), divided by 2psi; its within-part off-diagonal entry is -(theta(hat i)/2+psi(hat i))/(2psi); its between-part entry is phi(hat i,hat j)/psi.

**Definition 1.1 (Source product with omitted parameters).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.phi`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.phi` (`✓ std3`).

*Citation.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

The source product definition, restricted to a finite set of parameters. Erasure realizes the original single and double omitted-list equalities.

**Definition 1.2 (Source cofactor polynomial with omitted parameters).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.psi`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.psi` (`✓ std3`).

*Citation.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

The source sum definition applies the same function to the retained parameter list. The inconsistent expanded hatted-Psi display is not used.

**Definition 1.3 (Source sum of the two parameter functions).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.theta`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.theta` (`✓ std3`).

*Citation.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

The source defines Theta as Phi plus Psi, also on each omitted list.

**Definition 1.4 (Squared-distance matrix of the source graph).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.delta`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.delta` (`✓ std3`).

*Citation.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

The source squared-distance matrix on the complete multipartite vertex carrier. Its graph interpretation uses at least two positive parts.

**Definition 1.5 (Source sum of all cofactors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.cofactorSum`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.cofactorSum` (`✓ std3`).

*Citation.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

The nonzero-cofactor domain preceding equation (3.6) means the sum of all cofactors. Summing the transposed cofactor matrix, the adjugate, gives the same sum.

**Definition 1.6 (The source Laplacian-like matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.sourceL`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.sourceL` (`✓ std3`).

*Citation.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

Equation (3.6), with precisely its diagonal, same-part off-diagonal and between-part cases, and the original omitted-list convention.

blockBase=3 times the partwise all-ones matrix minus 4I. Its explicit inverse has same-part coefficient 3/(4d(i)) and diagonal subtraction 1/4. A is the negative of this inverse and z has vertex value 1/d(i). All these are actual matrices on the original vertex carrier. No matrix identity, realization, classification or spectral-transfer premise is introduced.

**Theorem 1.7 (Literal source rank-one identity).**

$$\forall t \in \operatorname{Nat},\; \forall n \in \operatorname{Fin}\left(t\right) \to \operatorname{Nat},\; \operatorname{PositiveParts}\left(n\right) \Rightarrow \left(\operatorname{det}\left(\operatorname{delta}\left(n\right)\right) = 0 \Rightarrow \left(\operatorname{psi}\left(n, \operatorname{univ}\right) \neq 0 \land \left(\operatorname{pivot}\left(\operatorname{A}\left(n\right), \operatorname{oneVector}\right) = 1 \land \operatorname{sourceL}\left(n\right) = \operatorname{downdate}\left(\operatorname{A}\left(n\right), \operatorname{oneVector}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_downdate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

Positive integer sizes imply each d(i) is nonzero. The explicit block inverse is checked by multiplication. Multiplying delta by it gives I+z times the all-ones row. The existing determinant lemma then makes singularity imply ratio=-1 and psi=-phi, so every source denominator is nonzero. Separating omitted summands and substituting into all three source entry cases proves sourceL=A-zz-transpose. The quadratic pivot of A on the ones vector is one. This is a source-specific application of the existing determinant machinery.

**Theorem 1.8 (Inertia transfer and positive eigenvector families).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

The quantified conclusion supplies a Hermitian sourceL. Its positive index plus one is the positive index of A, its negative index equals that of A, and its zero eigenvalue multiplicity is exactly one. Every vector whose sum in each part is zero is an eigenvector with value 1/4. Every vector supported on singleton parts whose total sum is zero is an eigenvector with value one. The existing structured rank-one inertia theorem is applied with the actual A, the ones vector and the derived pivot one. Invertibility of A excludes zero eigenvalues before the downdate. The action identities are proved on the actual source entries. The actual partwise-zero-sum subspace has dimension N-t, by a surjective part-sum map and rank-nullity. These statements do not assume the desired spectral counts.

**Definition 1.9 (The complete target).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.completeConjecture`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.completeConjecture` (`✓ std3`).

*Citation.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

completeConjecture retains every t at least two, all positive integer sizes, nonzero sum of all cofactors and singular delta. Let N be the sum of sizes, s the number of sizes at least two and h the number equal to one. Its conclusion is the conjunction of: the positive real characteristic-root multiset equals N-t copies of 1/4 plus h-1 copies of one; and the positive, zero, negative indices equal N-s-1, one, s. Multisets preserve algebraic multiplicity, and Hermitian symmetry connects them to the indexed eigenvalues. The theorem result proves this complete conjunction. The boundary cases remain in the quantified domain.

**Theorem 1.10 (Complete singular positive spectrum and inertia).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.result` (`✓ std3`). ∎

*Resolves.* `Problems/das-mohanty-singular-squared-distance-laplacian` (proved) by `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"das-mohanty-singular-squared-distance-laplacian","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Sumit Mohanty (2024). *Inverse of the Squared Distance Matrix of a Complete Multipartite Graph*. DOI: [10.13001/ela.2024.8283](https://doi.org/10.13001/ela.2024.8283). URL: <https://arxiv.org/abs/2311.01069v2>.

*Commentary.*

For every finite t at least two and every positive integer part-size function, assume the sum of all cofactors is nonzero and the literal squared-distance matrix is singular. The positive characteristic-root multiset of the exact source matrix is N-t copies of 1/4 plus h-1 copies of one. Its positive, zero and negative indices are N-s-1, one and s. The multiplicities are algebraic. The proof keeps the dependent vertex carrier and all omitted-list conventions. On each part, use the constant column and the differences of each remaining coordinate vector with the first coordinate vector. Their change-of-basis matrix is invertible: summing a kernel vector over a part first forces its constant coordinate to vanish, then its remaining coordinates vanish. In this basis A is diagonal with value -1/d(i) on the constant column and 1/4 on each other column. Exactly the s nonsingleton constant columns are negative; there are N-s positive columns. The pivot-one downdate therefore gives the asserted absolute inertia of sourceL. The partwise-zero-sum space has dimension N-t and lies in its quarter eigenspace. Lifting functions on the singleton parts whose sum is zero injects a space of dimension at least h-1 into the one eigenspace. The standard geometric-to-algebraic multiplicity bound gives the two lower bounds on characteristic roots. Positive sizes give t=s+h; singularity forces h positive, since otherwise ratio is nonnegative. The two multiplicity lower bounds thus sum to the entire positive index N-s-1. Multiset inclusion and equal cardinality give exact equality, excluding every extra positive root or extra multiplicity. No inverse of singular delta, additional matrix identity, genericity condition or spectral-transfer premise is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.cofactorSum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.completeConjecture`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.delta`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.phi`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.psi`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_downdate`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_reduction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.sourceL`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.theta`
- Dependency: [D5/S3/QuadraticForms/StructuredRankOneInertia](../../QuadraticForms/StructuredRankOneInertia.md)
