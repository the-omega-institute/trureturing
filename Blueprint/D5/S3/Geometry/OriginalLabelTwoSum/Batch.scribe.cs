using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class BatchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Batch.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Batch",
            "Finite noninterfering critical fibres produce actual native sequences with exact ordered pair coverage.",
            "original-label-two-sum-batch",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Batch"),
        Blocks(
            Node("fibrelayers", "fibreLayers", "fibreLayers",
                "Literal union of indexed fibre families. Repeated indices are not needed.", DescribeRole.Definition),
            Node("mem-fibrelayers", "mem_fibreLayers", "mem_fibreLayers",
                "Membership retains the actual fibre index and local face.", DescribeRole.Theorem),
            Node("batchfibre", "batchFibre", "batchFibre",
                "A finite batch, with actual evolving base (finished N-fibres and unfinished M-fibres). The pair list is precisely the concatenation of the lifted local lists, in the supplied finite index order.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
