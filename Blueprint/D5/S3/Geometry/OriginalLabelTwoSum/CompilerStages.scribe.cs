using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class CompilerStagesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages",
            "The original filling-main and separate collar stages assemble native lists on their actual computed parent families.",
            "original-label-two-sum-compiler-stages",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("CompilerStages"),
        Blocks(
            Node("selectfilling", "selectFilling", "selectFilling",
                "Select the actual P0/P1 or Q0/Q1 filling from the original critical-face interface test. ", DescribeRole.Definition),
            Node("parentfillingstage", "parentFillingStage", "parentFillingStage",
                "Construct the filling-main stage on the ACTUAL parent after child replay. The list is assembled from all P0/P1 lists; its target families are computed. ", DescribeRole.Definition),
            Node("parentcollarstage", "parentCollarStage", "parentCollarStage",
                "Construct all Q0/Q1 collar lists on Cout ALONE. Every emitted coface is checked against the other collars; the retained parent critical cells are absent from the domain of this Sequence. ", DescribeRole.Definition),
            Node("parentfillingstage-orderedpairs", "parentFillingStage_orderedPairs", "parentFillingStage_orderedPairs",
                "Global ordered expansion of the filling-main batch. `fibres` is the real cardinality/finite-enumeration comparator, so this records descending critical order rather than an arbitrary permutation. ", DescribeRole.Theorem),
            Node("parentcollarstage-orderedpairs", "parentCollarStage_orderedPairs", "parentCollarStage_orderedPairs",
                "Global ordered expansion of the collar batch. Its domain is `Cout` alone; the retained critical simplices are not silently inserted into this list. ", DescribeRole.Theorem)
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
