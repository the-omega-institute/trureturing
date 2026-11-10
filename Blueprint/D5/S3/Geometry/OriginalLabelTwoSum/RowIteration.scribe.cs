using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RowIterationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/RowIteration",
            "Coupled original path-row substitutions recursively construct native certificates and critical statistics on arbitrary retained labels.",
            "original-label-two-sum-row-iteration",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("RowIteration"),
        Blocks(
            Node("renamerows", "renameRows", "renameRows",
                "Indexed path rows transported injectively; chord indices are not discarded.", DescribeRole.Definition),
            Node("renamerows-root", "renameRows_root", "renameRows_root",
                "Raw root transport preserves VOID, UNIT and every original indexed row.", DescribeRole.Theorem),
            Node("appendwheelrows", "appendWheelRows", "appendWheelRows",
                "The exact coupled row update. Old rows containing e are substituted; old rows avoiding e and every non-interface right chord index are retained.", DescribeRole.Definition),
            Node("rowhistory", "RowHistory", "RowHistory",
                "Finite coupled row construction with arbitrary retained-edge choices. No parent endpoint, critical formula, collapse or graph substitution is a field.", DescribeRole.Definition),
            Node("rowhistorycertificate", "rowHistoryCertificate", "rowHistoryCertificate",
                "Recursive native main/core lists for the coupled row class. Both lists are those of the real compiler; there is no separate assumed schedule or critical endpoint in this construction.", DescribeRole.Definition),
            Node("rowhistory-statistics", "rowHistory_statistics", "rowHistory_statistics",
                "At EVERY finite row stage there are exactly two distinct critical faces, each of size 2n+1. This is a row-level statement. Its interpretation for graph data uses the separate graph and physical-history correspondence.", DescribeRole.Theorem),
            Node("rowhistorycriticalschedule", "rowHistoryCriticalSchedule", "rowHistoryCriticalSchedule",
                "Critical labels are recursively specified from the actual K4 seed and literal wheel label substitution, independently of rowHistoryCertificate.", DescribeRole.Definition),
            Node("rowhistoryvertexschedule", "rowHistoryVertexSchedule", "rowHistoryVertexSchedule",
                "The original terminal vertex recursion, starting at the renamed seed 0.", DescribeRole.Definition),
            Node("rowhistorycertificate-schedule-data", "rowHistoryCertificate_schedule_data", "rowHistoryCertificate_schedule_data",
                "The certificate's critical labels and vertex satisfy the independent seed recursions; these equations transport the input data in both list inductions.", DescribeRole.Theorem),
            Node("rowhistorymainschedule", "rowHistoryMainSchedule", "rowHistoryMainSchedule",
                "Seed-based all-n main enumeration. The K4 main is an actual reflexive operation, so its pair list is empty even after the original label map. Each attach flatMaps the previous independently enumerated list.", DescribeRole.Definition),
            Node("rowhistoryseparateschedule", "rowHistorySeparateSchedule", "rowHistorySeparateSchedule",
                "Seed-based all-n core enumeration, including recursively computed critical labels and vertex. Neither attach reads a previous certificate's native pairs.", DescribeRole.Definition),
            Node("rowhistorycertificate-main-orderedpairs", "rowHistoryCertificate_main_orderedPairs", "rowHistoryCertificate_main_orderedPairs",
                "The main induction consumes the previous list equality through the raw wheel substitution, together with the independent critical-label recursion.", DescribeRole.Theorem),
            Node("rowhistorycertificate-separate-orderedpairs", "rowHistoryCertificate_separate_orderedPairs", "rowHistoryCertificate_separate_orderedPairs",
                "The separate induction consumes its own previous-list hypothesis, and both critical/vertex transports. It preserves collars/replay/terminal append order.", DescribeRole.Theorem),
            Node("rowhistorycertificate-expansion", "rowHistoryCertificate_expansion", "rowHistoryCertificate_expansion",
                "A certificate consumer keeps BOTH all-n list expansions and the actual whole-endpoint coordinate-fixed homotopy. No graph identification is assumed.", DescribeRole.Theorem),
            Node("rowhistory-fixed-seed-fresh-wheel", "rowHistory_fixed_seed_fresh_wheel", "rowHistory_fixed_seed_fresh_wheel",
                "The fixed K4 seed/fresh-wheel construction consumes both genuine recursive expansions. Actual graph G2/history/closed-chain binding is still separate.", DescribeRole.Theorem)
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
