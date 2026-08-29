using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class SensorFamilyExtensionStrictRefinementDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/SensorFamilyExtensionStrictRefinement."
            + "separating_extension_witnesses_strict_refinement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adding a separating sensor strictly refines a sensor-family kernel.",
        H("Sensor Family Extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("sensor-family-extension-strict-refinement"),
            DeclarationHandle.Create(Declaration),
            H("Sensor Family Extension"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Extending a sensor family can only add equality constraints to its joint kernel.")),
                Paragraph(Text(
                    "When the new sensor separates a pair previously collapsed by all old sensors, the refinement is strict."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("old_collision_and_new_separation"), Sp, Rightarrow, Sp,
            F.Id("strict_kernel_refinement"), Dot));
}
