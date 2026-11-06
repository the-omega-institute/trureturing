// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class WheelSupplierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/WheelSupplier"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("WheelSupplier"),
        Blocks(
            Node("onestep", "oneStep", "oneStep",
                "Witness the right Gamma permission by the original four pairs, install both filling records and the separate 13/123 collar on fresh labels, then RUN the parent compiler. Its Prop-valued permission makes a classical Gamma choice; the exact expansion below records that choice, without identifying it with its witness. There is no restriction excluding e=current core vertex. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("onestep_critical", "oneStep_critical", "oneStep_critical",
                "The computed critical family has the exact original two-branch transform. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("onestep_statistics", "oneStep_statistics", "oneStep_statistics",
                "The native one-step supplier preserves the number of critical faces and increases the size of EACH by exactly two, also when the interface is a critical singleton or the current core vertex. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("onestepmainfrom", "oneStepMainFrom", "oneStepMainFrom",
                "Raw-face main substitution. Only previous pair data and critical labels are inputs; filling lists are the actual renamed original wheel operations. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("onestepseparatefrom", "oneStepSeparateFrom", "oneStepSeparateFrom",
                "Raw-face separate substitution: standalone collars, previous core faces, then the full-ground terminal formula. No previous certificate is consulted. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("onestepmainschedule", "oneStepMainSchedule", "oneStepMainSchedule",
                "The compiler instance of the main raw-face substitution. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("onestepseparateschedule", "oneStepSeparateSchedule", "oneStepSeparateSchedule",
                "The compiler instance of the separate raw-face substitution. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("onestep_main_orderedpairs", "oneStep_main_orderedPairs", "oneStep_main_orderedPairs",
                "Both one-step formulas use the Gamma actually chosen by the existing Prop-valued compiler permission, rather than identifying choice with its witness. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("onestep_separate_orderedpairs", "oneStep_separate_orderedPairs", "oneStep_separate_orderedPairs",
                "Original-label source declaration consumed by the native compiler and row construction. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("onestep_vertex", "oneStep_vertex", "oneStep_vertex",
                "The exact terminal choice used by the independent row vertex recursion. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
