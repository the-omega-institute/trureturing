using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class CertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Certificates.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Certificates",
            "Collapse-only main certificates and separate collar/core sequences retain literal critical boundaries.",
            "original-label-two-sum-certificates",
            Anchor.ParseCanonical("mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic")),
        H("Certificates"),
        Blocks(
            Node("facets", "facets", "facets",
                "A finite union of raw simplices, with the empty index family equal to VOID. ", DescribeRole.Definition),
            Node("endpoint", "endpoint", "endpoint",
                "A finite union of raw simplices, with the empty index family equal to VOID. ", DescribeRole.Definition),
            Node("criticaldata", "CriticalData", "CriticalData",
                "Exact ordinary critical-cell conditions, including ALL proper subfaces. ", DescribeRole.Definition),
            Node("filling", "Filling", "Filling",
                "A local filling need not have a contractible collar. ", DescribeRole.Definition),
            Node("certificate", "Certificate", "Certificate",
                "A left input carries an actual vertex and ordinary main/core lists. ", DescribeRole.Definition),
            Node("critical-intersection", "critical_intersection", "critical_intersection",
                "Actual literal simplex/core intersection, with the empty face retained. ", DescribeRole.Theorem),
            Node("critical-overlap", "critical_overlap", "critical_overlap",
                "Distinct retained cells meet only in proper boundary faces. ", DescribeRole.Theorem)
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
