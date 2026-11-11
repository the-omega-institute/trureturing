using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetPrincipalSplittingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual principal-unit complement of the odd-prime jet group.",
        H("Principal-unit and scalar-label splitting"),
        Blocks(
            Paragraph(Text("Let p be any odd prime, including 3, let F=ZMod p, and let K be a finite field in an arbitrary universe with |K|=p^n for n at least one. For every F-linear q with q(1)=0, the original group is the native subgroup of pairs of invertible F-linear operators on Polynomial.degreeLT K p and original additive-label automorphisms. The commutant kernel and its leading-unit principal subgroup are the native carriers from the preceding jet modules.")),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-field-action"),
                DeclarationHandle.Create(Owner + "fieldAction"),
                H("The actual label action on scalar units"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the coefficient presentation q=Q(n,A), the label stabilizer acts on K through the field automorphism supplied by its native coefficient formula. This action is multiplicative on labels and induces the corresponding native action on K units. The construction uses the actual label group and does not choose a lift of a larger automorphism group."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-semilinear"),
                DeclarationHandle.Create(Owner + "coherentLift_semilinear"),
                H("The coherent section is semilinear"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed canonical shear preserves every constant polynomial, while the degree lift acts semilinearly by the native field automorphism. Therefore the coherent actual label section is semilinear on the chosen K-vector-space structure. This statement concerns the constructed section only; arbitrary elements of the full original group and arbitrary End_F(K) top maps remain unrestricted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-scalar-covariance"),
                DeclarationHandle.Create(Owner + "scalar_covariance"),
                H("Scalar covariance under coherent labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine scalar operators M_a lie in the actual commutant because the original representation is K-linear before restriction to F. Conjugation by the coherent section sends M_a to M_sigma(g)(a). No centrality of scalar operators in the full commutant is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-quotient"),
                DeclarationHandle.Create(Owner + "quotientHom"),
                H("The scalar-label quotient homomorphism"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native full-group semidirect equivalence is followed by the equivariant leading-unit map on its actual commutant kernel and the identity on the actual label group. The resulting homomorphism has target K* semidirect the actual label group with the scalar action above."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-complement"),
                DeclarationHandle.Create(Owner + "complementHom"),
                H("The scalar-times-label complement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Native semidirect-product lifting combines the scalar-unit section with the coherent label section. Scalar covariance is exactly the conjugation condition required by the native lift, so the complement map is a genuine homomorphism."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-right-inverse"),
                DeclarationHandle.Create(Owner + "quotient_complement"),
                H("The complement is a right inverse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every scalar-label coordinate is sent back to an actual scalar-times-coherent-label pair, and the quotient recovers that coordinate exactly. The leading-unit retraction is the only coordinate calculation required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-kernel"),
                DeclarationHandle.Create(Owner + "quotient_kernel"),
                H("The quotient kernel is exactly the actual principal subgroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel condition forces both the actual label coordinate and the leading unit to be trivial. The native principal-unit criterion then identifies the kernel with actualPrincipalUnits mapped through the native label-kernel inclusion. Conversely every such principal unit maps to the identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-extension"),
                DeclarationHandle.Create(Owner + "principalExtension"),
                H("The native split group extension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The extension uses actualPrincipalUnits as its kernel, originalGroup as its middle group, and K* semidirect the actual label group as quotient. Its inclusion, kernel equality, and surjectivity are the native maps and the explicit complement right inverse."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-factorization"),
                DeclarationHandle.Create(Owner + "unique_principal_factorization"),
                H("Unique principal-times-scalar-times-label factorization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native GroupExtension.Splitting equivalence gives every actual group element a unique product of an actual principal unit and one scalar-label complement element. This is a factorization in the original group itself and does not replace the actual carriers by a toy semidirect product."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-principal-normalized"),
                DeclarationHandle.Create(Owner + "normalized_principal_splitting"),
                H("Splitting for every normalized parameter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native coefficient bijection transports the construction from Q(n,A) to every normalized F-linear q with q(1)=0. The result retains arbitrary finite-field universes, all odd primes including 3, unrestricted End_F(K) top coordinates, and the native actual principal-unit, original-group, and label-group carriers. No cyclicity, logarithm, trace, kernel-order invertibility, scalar centrality, or split scalar/Galois-image hypothesis is introduced."))), DescribeRole.Theorem)
        )));
}
