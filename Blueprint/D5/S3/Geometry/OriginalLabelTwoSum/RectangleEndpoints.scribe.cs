using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RectangleEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints",
            "Raw cuts of the two descending rectangles equal the exact changed Phi states.",
            "original-label-two-sum-rectangle-endpoints",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("RectangleEndpoints"),
        Blocks(
            Node("deletioncut", "deletionCut", "deletionCut",
                "Exact deletion-rectangle endpoint, including every empty-fibre case.", DescribeRole.Theorem),
            Node("linkcut", "linkCut", "linkCut",
                "Exact link-rectangle endpoint. L<=D accounts for the fibres already retained in D*delta(Z); an empty projected lower is handled without an ordinary move.", DescribeRole.Theorem),
            Node("deletionlift", "deletionLift", "deletionLift",
                "Endpoint-transported deletion rule consumes its proved raw equality.", DescribeRole.Definition),
            Node("linklift", "linkLift", "linkLift",
                "Endpoint-transported link rule consumes its proved raw equality.", DescribeRole.Definition)
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
