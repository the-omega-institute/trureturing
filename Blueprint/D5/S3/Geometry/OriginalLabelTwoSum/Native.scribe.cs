using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class NativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Native.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Native",
            "Descending finite fibres emit existing native free pairs with exact evolving endpoints and ordered coverage.",
            "original-label-two-sum-native",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.List.Sort")),
        H("Native"),
        Blocks(
            Node("cut", "cut", "cut",
                "Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair. ", DescribeRole.Definition),
            Node("cut-empty", "cut_empty", "cut_empty",
                "Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair. ", DescribeRole.Theorem),
            Node("cut-cut", "cut_cut", "cut_cut",
                "Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair. ", DescribeRole.Theorem),
            Node("emitpair", "emitPair", "emitPair",
                "Populate the actual native pair, using the whole current raw family. ", DescribeRole.Definition),
            Node("emitpair-retained", "emitPair_retained", "emitPair_retained",
                "The equality is literal deletion of the upper ideal of the lower face. ", DescribeRole.Theorem),
            Node("fibrebefore", "fibreBefore", "fibreBefore",
                "Label-order tie break. The finite enumeration is fixed once per ambient Fintype instance; cardinality is always the primary comparison. ", DescribeRole.Definition),
            Node("fibres", "fibres", "fibres",
                "Actual terminating merge-sort, not an assumed fibre schedule. ", DescribeRole.Definition),
            Node("fibres-spec", "fibres_spec", "fibres_spec",
                "Actual terminating merge-sort, not an assumed fibre schedule. ", DescribeRole.Theorem),
            Node("rectangle", "rectangle", "rectangle",
                "Public rectangle endpoint and genuine ordered native list. ", DescribeRole.Definition),
            Node("rectangle-order", "rectangle_order", "rectangle_order",
                "The list statement refers to the real pair extraction, and contains no external pair schedule assumption. ", DescribeRole.Theorem),
            Node("cut-fixed", "cut_fixed", "cut_fixed",
                "Fixed coordinate consequence of the EXISTING Sequence homotopy. ", DescribeRole.Theorem)
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
