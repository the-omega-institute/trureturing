using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class SurjectiveSensorReindexKernelEqualityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/SurjectiveSensorReindexKernelEquality."
            + "surjective_reindex_preserves_family_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective reindexing preserves the joint sensor kernel.",
        H("Surjective Sensor Reindexing"),
        Blocks(Describe.Lean(
            DescribeId.Create("surjective-sensor-reindex-kernel-equality"),
            DeclarationHandle.Create(Declaration),
            H("Surjective Sensor Reindexing"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A reindexed family observes the original sensors through a map of index types.")),
                Paragraph(Text(
                    "Surjectivity ensures every original sensor remains represented, giving equality of the two family kernels."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("surjective_sensor_reindexing"), Sp, Rightarrow, Sp,
            F.Id("equal_family_kernels"), Dot));
}
