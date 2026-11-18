using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitCatalogueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-dimensional source representation and certificate.",
        H("Complete source objects and retained trust boundaries"),
        Blocks(
            Describe.Lean(DescribeId.Create("catalogue-completeness"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogue.complete"),
                H("catalogue completeness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("For every zero-containing XOR-closed subset, adjoining its vectors through the supplied extension table reaches exactly that subset. This is full completeness, without an assumed Gaussian count."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("catalogue-color-transfer"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogue.colorable"),
                H("catalogue color transfer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("For every catalogue satisfying Covers and Proper, all nonzero source spaces admit the fifteen-color assignment. Proper checks the complete perpendicular masks and all relevant pairs."))), DescribeRole.Theorem)),
        []));
}
