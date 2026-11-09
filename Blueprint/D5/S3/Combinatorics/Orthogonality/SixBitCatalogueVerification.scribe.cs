using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitCatalogueVerificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-dimensional source representation and certificate.",
        H("Complete source objects and retained trust boundaries"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-completeness-check"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.catalogue_covers"),
                H("native completeness check"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The source native_decide obligation for the complete adjoining-vector table is retained. Its actual current transitive axioms must be inspected; the historical generated native-evaluation axiom is not erased."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-properness-check"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.catalogue_proper"),
                H("native properness check"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The source native_decide obligation checks all relevant catalogue masks, colors and perpendicular relations, not a sample."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-clique-validity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.clique_valid"),
                H("native clique validity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The source native_decide obligation verifies each of the fifteen specified spaces is a nonzero XOR-closed space."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-clique-adjacency"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.clique_adjacent"),
                H("native clique adjacency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The source native_decide obligation verifies every distinct specified clique pair is adjacent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-source-chromatic-number"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.chromatic_number_six"),
                H("full source chromatic number"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The complete positive certificate and the fifteen-clique prove the source graph has chromatic number fifteen. This is the all-space graph, not the line graph. The source proof has four native-evaluation obligations; it is not a theorem with only the three standard axioms."))), DescribeRole.Theorem)),
        []));
}
