// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class VerticalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Vertical.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Vertical",
            "A genuine right Gamma yields the vertical parent collapse fixing its entire computed base.",
            "original-label-two-sum-vertical",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Vertical"),
        Blocks(
            Node("verticalgamma", "verticalGamma", "verticalGamma",
                "Source/endpoints are literal Phi states with the single maximal left fibre removed. No parent collapse, collar, or endpoint equality is an assumption. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("verticalvoid", "verticalVoid", "verticalVoid",
                "The separate VOID rule uses an original r in nonempty R. The empty right fibre emits lower=a, which is genuinely nonempty; it never collapses UNIT to VOID. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? " " : line)))))
        : Paragraph(Text(value));
}
