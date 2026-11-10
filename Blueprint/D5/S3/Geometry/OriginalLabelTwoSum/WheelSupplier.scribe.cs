using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class WheelSupplierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier",
            "Fresh original wheel labels instantiate the native Gamma/two-filling compiler and preserve critical count with size increment two.",
            "original-label-two-sum-wheel-supplier",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("WheelSupplier"),
        Blocks(
            Node("onestep", "oneStep", "oneStep",
                "Witness the right Gamma permission by the original four pairs, install both filling records and the separate 13/123 collar on fresh labels, then RUN the parent compiler. Its Prop-valued permission makes a classical Gamma choice; the exact expansion below records that choice, without identifying it with its witness. There is no restriction excluding e=current core vertex. ", DescribeRole.Definition),
            Node("onestep-critical", "oneStep_critical", "oneStep_critical",
                "The computed critical family has the exact original two-branch transform. ", DescribeRole.Theorem),
            Node("onestep-statistics", "oneStep_statistics", "oneStep_statistics",
                "The native one-step supplier preserves the number of critical faces and increases the size of EACH by exactly two, also when the interface is a critical singleton or the current core vertex. ", DescribeRole.Theorem),
            Node("onestepmainfrom", "oneStepMainFrom", "oneStepMainFrom",
                "Raw-face main substitution. Only previous pair data and critical labels are inputs; filling lists are the actual renamed original wheel operations. ", DescribeRole.Definition),
            Node("onestepseparatefrom", "oneStepSeparateFrom", "oneStepSeparateFrom",
                "Raw-face separate substitution: standalone collars, previous core faces, then the full-ground terminal formula. No previous certificate is consulted. ", DescribeRole.Definition),
            Node("onestepmainschedule", "oneStepMainSchedule", "oneStepMainSchedule",
                "The compiler instance of the main raw-face substitution. ", DescribeRole.Definition),
            Node("onestepseparateschedule", "oneStepSeparateSchedule", "oneStepSeparateSchedule",
                "The compiler instance of the separate raw-face substitution. ", DescribeRole.Definition),
            Node("onestep-main-orderedpairs", "oneStep_main_orderedPairs", "oneStep_main_orderedPairs",
                "Both one-step formulas use the Gamma actually chosen by the existing Prop-valued compiler permission, rather than identifying choice with its witness. ", DescribeRole.Theorem),
            Node("onestep-separate-orderedpairs", "oneStep_separate_orderedPairs", "oneStep_separate_orderedPairs",
                "Original-label source declaration consumed by the native compiler and row construction. ", DescribeRole.Theorem),
            Node("onestep-vertex", "oneStep_vertex", "oneStep_vertex",
                "The exact terminal choice used by the independent row vertex recursion. ", DescribeRole.Theorem)
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
