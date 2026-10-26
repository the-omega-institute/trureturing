using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreBoundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("Both boundary columns are occupied"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracoreboundary-0"),
                DeclarationHandle.Create(Prefix + "boundary_walk_abstract"), H("A boundary walk has an extremum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Two compatible unit-step integer walks joined by unit horizontal differences have a row with all existing neighbours uniformly higher or uniformly lower."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreboundary-1"),
                DeclarationHandle.Create(Prefix + "firstColumn_active"), H("The first column is occupied"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("In a unit-edge height function with nonempty rows and at least two columns, the first physical column contains an ambient strict extremum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreboundary-2"),
                DeclarationHandle.Create(Prefix + "lastColumn_active"), H("The last column is occupied"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The last physical column also contains an ambient strict extremum, with all existing vertical and horizontal neighbours included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreboundary-3"),
                DeclarationHandle.Create(Prefix + "boundary_columns_active"), H("Both boundary columns are occupied"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The first and last physical columns are simultaneously occupied in the same height function."))), DescribeRole.Theorem))));
}
