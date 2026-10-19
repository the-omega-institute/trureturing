using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class UpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square-root upper-bound interface for zero-one matrices.",
        H("Universal Ky Fan upper bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-bound-statement"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/Upper.upperBoundStatement"),
                H("Universal upper-bound statement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The statement bounds the Ky Fan sum of every symmetric zero-one matrix by the square-root expression."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ky-fan-zero"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_zero"),
                H("Empty prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The empty Ky Fan prefix has value zero."))), DescribeRole.Theorem))));
}
