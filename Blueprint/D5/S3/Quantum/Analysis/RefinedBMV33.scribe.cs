using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMV33Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dimension-four trace-power bound",
        H("The dimension-four trace-power bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmv33-e33"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV33.E33"),
                H("The dimension-four trace-power bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
                Blocks(Paragraph(Text(
                    "A unitary diagonalization and a shift to a zero eigenvalue allow the Schur product theorem to be applied to every group of closed walks."))),
                DescribeRole.Theorem))));
}
