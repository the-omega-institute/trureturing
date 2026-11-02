# Singular multipartite squared-distance Laplacian

## Abstract

The literal singular multipartite source Laplacian has a verified rank-one reduction; the complete positive multiplicity and inertia conjecture remains open.

The source is Joyentanuj Das and Sumit Mohanty, Inverse of the Squared Distance Matrix of a Complete Multipartite Graph, arXiv:2311.01069v2, equation (3.6) and the concluding conjecture; DOI 10.13001/ela.2024.8283. The author-defined omitted-list equalities determine the hats. The inconsistent expanded hatted Psi products are not substituted for those definitions. No publisher correction, priority or worldwide literature-completeness claim is made.

For any natural t and n:Fin(t) to Nat, the vertex carrier is the dependent sum of Fin(n(i)). Set d(i)=3n(i)-4. For a finite parameter set S, phi(n,S) is the product of d(i) over S, psi(n,S) is the sum of n(i)phi(n,S without i), and theta=phi+psi. Empty products are one and empty sums zero. Restricting S therefore removes exactly the indicated parameters, including for double hats. ratio(n) is the sum of n(i)/d(i).

delta(n) has diagonal zero, within-part off-diagonal four and between-part one. For t at least two and positive part sizes these are the squared graph distances. cofactorSum is the sum of every adjugate entry, hence the sum of all cofactors, not a principal cofactor. sourceL uses the literal three source cases: its diagonal numerator is (n(i)-1)theta(hat i)/2+(n(i)-3)psi(hat i), divided by 2psi; its within-part off-diagonal entry is -(theta(hat i)/2+psi(hat i))/(2psi); its between-part entry is phi(hat i,hat j)/psi.

blockBase=3 times the partwise all-ones matrix minus 4I. Its explicit inverse has same-part coefficient 3/(4d(i)) and diagonal subtraction 1/4. A is the negative of this inverse and z has vertex value 1/d(i). All these are actual matrices on the original vertex carrier. No matrix identity, realization, classification or spectral-transfer premise is introduced.

**Theorem 1.1 (Literal source rank-one identity).**

$$\forall t \in \operatorname{Nat},\; \forall n \in \operatorname{Fin}\left(t\right) \to \operatorname{Nat},\; \operatorname{PositiveParts}\left(n\right) \Rightarrow \left(\operatorname{det}\left(\operatorname{delta}\left(n\right)\right) = 0 \Rightarrow \left(\operatorname{psi}\left(n, \operatorname{univ}\right) \neq 0 \land \left(\operatorname{pivot}\left(\operatorname{A}\left(n\right), \operatorname{oneVector}\right) = 1 \land \operatorname{sourceL}\left(n\right) = \operatorname{downdate}\left(\operatorname{A}\left(n\right), \operatorname{oneVector}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_downdate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive integer sizes imply each d(i) is nonzero. The explicit block inverse is checked by multiplication. Multiplying delta by it gives I+z times the all-ones row. The existing determinant lemma then makes singularity imply ratio=-1 and psi=-phi, so every source denominator is nonzero. Separating omitted summands and substituting into all three source entry cases proves sourceL=A-zz-transpose. The quadratic pivot of A on the ones vector is one. This is a source-specific application of the existing determinant machinery.

**Theorem 1.2 (Inertia transfer and positive eigenvector families).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantified conclusion supplies a Hermitian sourceL. Its positive index plus one is the positive index of A, its negative index equals that of A, and its zero eigenvalue multiplicity is exactly one. Every vector whose sum in each part is zero is an eigenvector with value 1/4. Every vector supported on singleton parts whose total sum is zero is an eigenvector with value one. The existing structured rank-one inertia theorem is applied with the actual A, the ones vector and the derived pivot one. Invertibility of A excludes zero eigenvalues before the downdate. The action identities are proved on the actual source entries. The actual partwise-zero-sum subspace has dimension N-t, by a surjective part-sum map and rank-nullity. These statements do not assume the desired spectral counts.

**Definition 1.3 (The complete target).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.completeConjecture`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.completeConjecture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

completeConjecture retains every t at least two, all positive integer sizes, nonzero sum of all cofactors and singular delta. Let N be the sum of sizes, s the number of sizes at least two and h the number equal to one. Its conclusion is the conjunction of: the positive real characteristic-root multiset equals N-t copies of 1/4 plus h-1 copies of one; and the positive, zero, negative indices equal N-s-1, one, s. Multisets preserve algebraic multiplicity, and Hermitian symmetry connects them to the indexed eigenvalues. This definition is a target, not a proof. The remaining formal obligations are the exact sign counts of A, dimensions of the singleton-supported source eigenspace, and exhaustion of the positive spectrum. The boundary cases remain in the quantified domain. No partial result settles either complete source clause.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.completeConjecture`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_downdate`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.singular_source_reduction`
- Dependency: [D5/S3/QuadraticForms/StructuredRankOneInertia](../../QuadraticForms/StructuredRankOneInertia.md)
