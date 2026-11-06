// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class CompilerStagesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/CompilerStages"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("CompilerStages"),
        Blocks(
            Node("selectfilling", "selectFilling", "selectFilling",
                "Select the actual P0/P1 or Q0/Q1 filling from the original critical-face interface test. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("parentfillingstage", "parentFillingStage", "parentFillingStage",
                "Construct the filling-main stage on the ACTUAL parent after child replay. The list is assembled from all P0/P1 lists; its target families are computed. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("parentcollarstage", "parentCollarStage", "parentCollarStage",
                "Construct all Q0/Q1 collar lists on Cout ALONE. Every emitted coface is checked against the other collars; the retained parent critical cells are absent from the domain of this Sequence. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("parentfillingstage-orderedpairs", "parentFillingStage_orderedPairs", "parentFillingStage_orderedPairs",
                "Global ordered expansion of the filling-main batch. `fibres` is the real cardinality/finite-enumeration comparator, so this records descending critical order rather than an arbitrary permutation. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("parentcollarstage-orderedpairs", "parentCollarStage_orderedPairs", "parentCollarStage_orderedPairs",
                "Global ordered expansion of the collar batch. Its domain is `Cout` alone; the retained critical simplices are not silently inserted into this list. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
