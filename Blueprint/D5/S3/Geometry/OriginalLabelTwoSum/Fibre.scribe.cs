using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class FibreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Fibre.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Fibre",
            "Native local sequences lift over literal fixed fibres using the existing coordinate homotopy.",
            "original-label-two-sum-fibre",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.List.Forall2")),
        H("Fibre"),
        Blocks(
            Node("liftfibre", "liftFibre", "liftFibre",
                "Non-VOID local sequences lift over a literal fibre. This is used for Gamma and filling/collar schedules; all ordinary lower faces are still nonempty even when a=empty. No homotopy or parent certificate is an input. ", DescribeRole.Definition),
            Node("liftfibre-pairs", "liftFibre_pairs", "liftFibre_pairs",
                "Exact ordered coverage for the ACTUAL native fibre list, including every pair of a supplied Gamma, filling-main or separate collar sequence. ", DescribeRole.Theorem)
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
